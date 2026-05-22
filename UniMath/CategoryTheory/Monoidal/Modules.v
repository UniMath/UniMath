Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Import BifunctorNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section Modules.
  Context (C : monoidal_cat).

  Definition m : monoidal C := monoidal_cat_to_monoidal  C.
  Definition I : C := monoidal_unit m.
  Definition lu : leftunitor_data m (monoidal_unit m) := monoidal_leftunitordata m.
  Definition luinv : leftunitorinv_data m (monoidal_unit m) := monoidal_leftunitorinvdata m.
  Definition ru : rightunitor_data m (monoidal_unit m) := monoidal_rightunitordata m.
  Definition ruinv : rightunitorinv_data m (monoidal_unit m) := monoidal_rightunitorinvdata m.
  Definition α : associator_data m := monoidal_associatordata m.
  Definition αinv : associatorinv_data m := monoidal_associatorinvdata m.

  Notation "x ⊗l f" := (x ⊗^{m}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{m}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{m} g) (at level 31).

  Context (R : C) (R_m : monoid m R).
  Definition μ : C⟦R ⊗ R, R⟧ := pr1 (pr1 R_m).
  Definition η : C⟦I, R⟧ := pr2 (pr1 R_m).

  Definition module_subst (M : C) : UU := C⟦ M ⊗ R, M ⟧.


  Definition module_object {M : C} (p : module_subst M) : C := M.
  Coercion module_object : module_subst >-> ob.

  Definition module_laws_assoc {M : C} (p : module_subst M) : UU
    := α M R R · (M ⊗l μ) · p = p ⊗r R · p.

  Definition module_laws_unit {M : C} (p : module_subst M) : UU
    := M ⊗l η · p = ru M. 

  Definition module_laws {M : C} (p : module_subst M) : UU
    := module_laws_assoc p × module_laws_unit p.

  Definition module (M : C): UU := ∑ p : module_subst M, module_laws p.

  Definition make_module
    {M : C} (p : C⟦M ⊗ R, M⟧)
    (p_unit : M ⊗l η · p = ru M)
    (p_assoc : α M R R · (M ⊗l μ) · p = p ⊗r R · p)
    : module M 
    := (p ,, p_assoc ,, p_unit).

  Definition module_to_module_subst (M : C) (p : module M) : C⟦ M ⊗ R, M ⟧ := pr1 p.
  Coercion module_to_module_subst : module >-> precategory_morphisms.

  Definition is_module_mor {M M' : C} (p : module M) (p' : module M') (r : M --> M') : UU
    := r ⊗r R · p' = p · r.

  Lemma isaprop_is_module_mor {M M' : C} (p : module M) (p' : module M') (r : C⟦M,M'⟧)
      : isaprop (is_module_mor p p' r).
  Proof.
    use homset_property.
  Qed.

  Lemma id_is_module_mor (M : C) (p : module M) : is_module_mor p p (identity M).
  Proof.
    unfold is_module_mor.
    rewrite id_right, (bifunctor_rightid m).
    use id_left.
  Qed.

  Lemma comp_is_module_mor (M M' M'' : C) 
    (p : module M) (p' : module M') (p'' : module M'')
    (r : C⟦M,M'⟧) (r' : C⟦M',M''⟧)
    (Hr : is_module_mor p p' r) (Hr' : is_module_mor p' p'' r')
    : is_module_mor p p'' (r·r').
  Proof.
    unfold is_module_mor in * |- *.
    rewrite (bifunctor_rightcomp m), assoc, <- Hr.
    do 2 rewrite <- assoc.
    now use maponpaths.
  Qed.

  Definition module_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists module.
    exact (λ _ _, is_module_mor).
  Defined.


  Definition module_disp_cat_id_comp : disp_cat_id_comp C module_disp_cat_ob_mor.
  Proof.
    split; intros; [now use id_is_module_mor|now use comp_is_module_mor].
  Defined.


  Definition module_disp_cat_data : disp_cat_data C 
    := module_disp_cat_ob_mor ,, module_disp_cat_id_comp.


  Definition module_disp_cat_axioms : disp_cat_axioms C module_disp_cat_data.
  Proof.
    repeat split ; intros ; try apply isaprop_is_module_mor.
    use isasetaprop ; use isaprop_is_module_mor.
  Qed.


  Definition module_disp_cat : disp_cat C := module_disp_cat_data ,, module_disp_cat_axioms.

  Definition MOD : category := total_category module_disp_cat.

  Definition trivial_module : MOD :=
    let l := pr2 (monoid_to_monoid_laws m R_m) in
    R ,, μ ,, pr2 l ,, pr1 l.

  Lemma product_module_unit (M D : C) (p : module M) : 
    module_laws_unit (α D M R · D ⊗l p).
  Proof.
    unfold module_laws_unit.
    assert (α D M I · D ⊗l ru M = ru (D ⊗_{m} M)) as H by exact (left_whisker_with_runitor m D M).
    rewrite <- H, assoc.
    etrans.
    use (maponpaths (λ x, x · D ⊗l p)); [exact (α D M I · D ⊗l (M ⊗l η))|now rewrite monoidal_associatornatleft].
    rewrite <- assoc; use maponpaths.
    induction p as [p [H' H'']]; cbn.
    now rewrite <- H'', (bifunctor_leftcomp m).
  Qed.

  Lemma product_module_assoc (M D : C) (p : module M) : 
    module_laws_assoc (α D M R · D ⊗l p).
  Proof.
    unfold module_laws_assoc.
    etrans.
    2: use (maponpaths (λ x, x · (α D M R · D ⊗^{ m}_{l} p))); [exact (α D M R ⊗r R · (D ⊗l p) ⊗r R) | now rewrite (bifunctor_rightcomp m)].
    do 2 rewrite assoc.
    transitivity (α (D ⊗ M) R R · ((D ⊗ M) ⊗l μ · α D M R) · D ⊗l p); [now rewrite assoc|].
    transitivity (α (D ⊗ M) R R · (α D M (R ⊗ R) · D ⊗l (M ⊗l μ)) · D ⊗l p); [use (maponpaths (λ x, α (D ⊗ M) R R · x · D ⊗l p)); now rewrite monoidal_associatornatleft|].
    transitivity (α D M R ⊗r R · (α _ _ _ · D ⊗l (p ⊗r R)) · D ⊗l p).
    2: transitivity (α D M R ⊗r R · ((D ⊗l p) ⊗r R · α _ _ _) · D ⊗l p); [
        use (maponpaths (λ x, α D M R ⊗r R · x · D ⊗l p));
        now rewrite monoidal_associatornatleftright
        |now rewrite assoc].
    do 2 rewrite assoc.
    transitivity (α _ _ _ ⊗r R · α _ _ _ · D ⊗l α _ _ _ · D ⊗l (M ⊗l μ) · D ⊗l p); [
      use (maponpaths (λ x, x · D ⊗l (M ⊗l μ) · D ⊗l p));
      now rewrite (monoidal_pentagonidentity m)|].
    transitivity (α D M R ⊗r R · α D (M ⊗ R) R · (D ⊗l α M R R · D ⊗l (M ⊗l μ) · D ⊗l p)); [ now do 2 rewrite assoc|].
    etrans.
    use (maponpaths (λ x, α D M R ⊗r R · α D (M ⊗ R) R · x)).
    exact (D ⊗l (p ⊗r R) · D ⊗l p).
    induction p as [p [H' H'']]; cbn.
    do 3 rewrite <- (bifunctor_leftcomp m).
    now use maponpaths.
    now rewrite assoc.
  Qed.

  Definition product_module (M D : C) (p : module M) : MOD.
  Proof.
    exists (D ⊗ M).
    exists (α _ _ _ · D ⊗l p).
    split; [use product_module_assoc | use product_module_unit].
  Defined.

  (* There is something weird with Lims_of_shape ... *)
  (*      (lims_g : Lims_of_shape g C). *)

  Definition forgetful_functor_data : functor_data MOD C.
  Proof.
    use make_functor_data.
    - intros [M p]; exact M.
    - intros [M p] [M' p'] [f _]; exact f.
  Defined.

  Lemma forgetful_is_functor : is_functor forgetful_functor_data.
  Proof.
    now idtac.
  Qed.

  Definition forgetful : MOD ⟶ C
    := make_functor forgetful_functor_data forgetful_is_functor.

  Section Colimits.
    Context {g : graph}.
    Context (colims_g : Colims_of_shape g C).
    Context (HR : preserves_colimits_of_shape (rightwhiskering_functor C R) g).

    Variable (F : diagram g MOD).

    Let F' := mapdiagram forgetful F : diagram g C.
    Let L : C := pr11 (colims_g F').
    Let cc : cocone F' L := pr21 (colims_g F').
    Let c : isColimCocone F' L cc := pr2 (colims_g F').
    Let r := HR F' L cc c.

    Definition colim_module_subst : L ⊗ R --> L.
    Proof.
      use (colimOfArrows (make_ColimCocone _ _ _ r) (make_ColimCocone F' L cc c)); simpl.
      - intro u; exact (pr1 (pr2 (dob F u))).
      - intros u v e; simpl. exact (pr2 (dmor F e)).
    Defined.

    Let p := colim_module_subst.

    Let q (v : vertex g): module_subst (dob F' v) := pr12 (dob F v).
    Let f (v : vertex g): dob F' v --> L := colimIn _ v.

    Lemma colim_module_mor (v : vertex g) : f v ⊗r R · p = q v · f v.
    Proof.
      use (colimOfArrowsIn _ _ (make_ColimCocone _ _ _ r) _ _ _ v).
    Qed.

    Lemma rw_unit_is_left_adjoint : is_left_adjoint (rightwhiskering_functor C I).
    Proof.
      exists (functor_identity C); use make_are_adjoints; [| |use make_form_adjunction].
      - exists ruinv; intros A B h; cbn; symmetry; use monoidal_rightunitorinvnat.
      - exists ru; intros A B h; cbn; use monoidal_rightunitornat.
      - intro A. cbn.
        assert (ru A ⊗r I = ru (A ⊗_{m} I)) by (
          rewrite <- id_right; unfold I; rewrite <- (pr1 (monoidal_rightunitorisolaw m A)), assoc;
          unfold ru, I in *;
          now rewrite <- (monoidal_rightunitornat m _ _ (monoidal_rightunitordata m A)), <- assoc, (pr1 (monoidal_rightunitorisolaw m A)), id_right
        ).
        change (ruinv A ⊗r I · ru (A ⊗_{m} I) = identity _).
        rewrite <- X.
        transitivity (ruinv A #⊗ identity I · ru A #⊗ identity I).
        now do 2 rewrite @tensor_mor_right.
        rewrite <- tensor_comp_id_r.
        unfold ruinv, ru; rewrite (pr2 (monoidal_rightunitorisolaw m A));
        use tensor_id_id.
      - intro A; cbn; use (pr2 (monoidal_rightunitorisolaw m A)).
    Qed.

    Definition isCC_unit := @left_adjoint_preserves_colimit C C (rightwhiskering_functor C I) rw_unit_is_left_adjoint g F' L cc c.



    Lemma colim_rightunitor : ru L = colimOfArrows (make_ColimCocone _ _ _ isCC_unit) (make_ColimCocone _ _ _ c) (λ _, ru _) (λ _ _ _, monoidal_rightunitornat _ _ _ _).
    Proof.
      unfold colimOfArrows.
      simpl.
      pose (make_ColimCocone _ _ _ isCC_unit) as CC.
      assert (forms_cocone (mapdiagram (rightwhiskering_functor C I) F') (λ v : vertex g, ru (dob F' v) · f v)) as H_cc' by (
        intros v w e; simpl;
        rewrite assoc, monoidal_rightunitornat, <- assoc;
        use maponpaths; change (dmor F' e · f w = f v); 
        use (coconeInCommutes cc)
      ).
      pose (make_cocone _ H_cc') as cc'.
      assert (∏ (u : vertex g), colimIn CC u · ru L = coconeIn cc' u) as H_unique by (intro; cbn; use monoidal_rightunitornat).
      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      unfold CC, cc'.
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.

    Local Lemma η_swap : ∏ (u v : vertex g) (e : edge u v),
       pr1 (dmor F e) ⊗^{ C}_{r} I · pr1 (dob F v) ⊗^{ m}_{l} η =
       pr1 (dob F u) ⊗^{ m}_{l} η · pr1 (dmor F e) ⊗^{ C}_{r} R.
    Proof.
      intros.
      do 2 rewrite tensor_mor_right, @tensor_mor_left;
      use tensor_swap.
    Qed.

    Lemma colim_unit : L ⊗l η = colimOfArrows (make_ColimCocone _ _ _ isCC_unit) (make_ColimCocone _ _ _ r) (λ _, _ ⊗l η) η_swap.
    Proof.
      unfold colimOfArrows.
      simpl.
      pose (make_ColimCocone _ _ _ isCC_unit) as CC.
      assert (forms_cocone (mapdiagram (rightwhiskering_functor C I) F') (λ v, _ ⊗l η · f v ⊗r _)) as H_cc' by (
        intros u v e; cbn; rewrite assoc;
        change (dmor F' e ⊗r I · dob F' v ⊗l η · f v ⊗r R = dob F' u ⊗l η · f u ⊗r R); unfold f;
        rewrite <- (colimInCommutes _ _ _ e), !@tensor_mor_right, tensor_comp_id_r, assoc;
        use (maponpaths (λ x, x · _)); rewrite !@tensor_mor_left; use tensor_swap
      ).
      pose (make_cocone _ H_cc') as cc'.
      assert (∏ (u : vertex g), colimIn CC u · L ⊗l η = coconeIn cc' u) as H_unique by (
        intro; cbn; do 2 rewrite @tensor_mor_right, @tensor_mor_left; use tensor_swap
      ).
      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      unfold CC, cc'.
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.

    Lemma colim_module_unit : L ⊗l η · p = ru L.
    Proof.
      rewrite colim_unit, colim_rightunitor.
      unfold p, colim_module_subst; simpl.
      change (
        colimOfArrows
          (make_ColimCocone (mapdiagram (rightwhiskering_functor C I) F')
             (L ⊗ I) (mapcocone (rightwhiskering_functor C I) F' cc) isCC_unit)
          (make_ColimCocone (mapdiagram (rightwhiskering_functor C R) F')
             (L ⊗ R) (mapcocone (rightwhiskering_functor C R) F' cc) r)
          (λ u : vertex g, dob F' u ⊗l η) η_swap
        · colimOfArrows
            (make_ColimCocone (mapdiagram (rightwhiskering_functor C R) F')
               (L ⊗ R) (mapcocone (rightwhiskering_functor C R) F' cc) r)
            (make_ColimCocone F' L cc c) (λ u : vertex g, pr12 (dob F u))
            (λ (u v : vertex g) (e : edge u v), pr2 (dmor F e)) = 
        colimOfArrows
          (make_ColimCocone (mapdiagram (rightwhiskering_functor C I) F')
             (L ⊗ I) (mapcocone (rightwhiskering_functor C I) F' cc) isCC_unit)
          (make_ColimCocone F' L cc c) (λ u : vertex g, ru (pr1 (dob F u)))
          (λ (u v : vertex g) (e : edge u v),
           monoidal_rightunitornat C (dob F' u) (dob F' v) (dmor F' e))
      ).
      simpl.
      erewrite colimOfArrows_comp.
      use two_arg_paths_f.
      use funextsec; intro; use (pr222 (dob F x)).
      do 3 (use funextsec; intro).
      use proofirrelevance; use homset_property.
      Unshelve.
      intros; cbn.
      rewrite <- !assoc, assoc.
      transitivity (_ ⊗l η · dmor F' e ⊗r _ · pr12 (dob F v)).
      use (maponpaths (λ u, u · _)); do 2 rewrite @tensor_mor_left, @tensor_mor_right; use tensor_swap.
      rewrite <- assoc; use maponpaths; use (pr2 (dmor F e)).
    Qed.

    Let rr := HR _ _ _ r.

    Local Lemma lemma1 : 
       (∏ (u v : vertex g) (e : edge u v),
        (dmor F' e ⊗r R) ⊗r R · pr12 (dob F v) ⊗r R =
        pr12 (dob F u) ⊗r R · dmor F' e ⊗r R).
    Proof.
      intros.
      do 4 rewrite @tensor_mor_right.
      transitivity ((pr12 (dob F u) · dmor F' e) #⊗ identity R); [|now rewrite tensor_comp_id_r].
      transitivity ((dmor F' e #⊗ identity R · pr12 (dob F v)) #⊗ identity R); [now rewrite tensor_comp_id_r|].
      assert (dmor F' e #⊗ identity R · pr12 (dob F v) = pr12 (dob F u) · dmor F' e) as H by (rewrite <- tensor_mor_right; use (pr2 (dmor F e))).
      now rewrite H.
    Qed.


    Lemma colim_module_subst_tens_r : p ⊗r R = colimOfArrows (make_ColimCocone _ _ _ rr) (make_ColimCocone _ _ _ r) _ lemma1.
    Proof.
      unfold colimOfArrows; simpl.
      pose (make_ColimCocone _ _ _ rr) as CC.

      assert (
        forms_cocone
          (mapdiagram (rightwhiskering_functor C R)
             (mapdiagram (rightwhiskering_functor C R) F'))
          (λ v : vertex g, (pr12 (dob F v) · f v) ⊗^{ m}_{r} R)
      ) as H_cc'.
        intros x y e; cbn.
        do 4 rewrite @tensor_mor_right.
        transitivity ((pr1 (dmor F e) #⊗ identity R · pr12 (dob F y) · f y) #⊗ identity R).
        symmetry; do 3 rewrite tensor_comp_id_r; now rewrite assoc.
        use (maponpaths (λ u, u #⊗ identity R)).
        etrans.
        eapply (maponpaths (λ u, u · _)).
        pose (pr2 (dmor F e)) as H.
        cbn in H.
        unfold is_module_mor in H.
        rewrite @tensor_mor_right in H.
        use H.
        rewrite <- assoc.
        use maponpaths.
        unfold f.
        change (dmor F' e · colimIn (colims_g F') y = colimIn (colims_g F') x).
        use colimInCommutes.

      pose (make_cocone _ H_cc') as cc'.

      assert (∏ u : vertex g, colimIn CC u · p ⊗^{ m}_{r} R = coconeIn cc' u) as H_unique by (
        intro u; cbn; do 4 rewrite @tensor_mor_right;
        transitivity ((coconeIn cc u #⊗ identity R · p) #⊗ identity R); [now rewrite tensor_comp_id_r|];
        use (maponpaths (λ u, u #⊗ identity R));
        transitivity (f u ⊗r R · p); [now rewrite @tensor_mor_right|use colim_module_mor]
      ).

      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).


      unfold CC, cc'.
      cbn.
      use maponpaths.
      use two_arg_paths_f.
      use funextsec; intro; cbn.
      do 3 rewrite @tensor_mor_right.
      now rewrite tensor_comp_id_r.

      use proofirrelevance.
      use isaprop_forms_cocone.
    Qed.

    Local Lemma lemma2 : ∏ u v e,
      (dmor F' e ⊗r R) ⊗r R
      · (α (dob F' v) R R · dob F' v ⊗l μ) =
      α (dob F' u) R R · dob F' u ⊗l μ
      · dmor F' e ⊗r R.
    Proof.
      intros.
      transitivity (α _ _ _ · (dmor F' e) ⊗r (R ⊗ R) · _ ⊗l μ); [now rewrite assoc, monoidal_associatornatright|].
      do 2 rewrite <- assoc; use maponpaths.
      do 2 rewrite @tensor_mor_right, @tensor_mor_left.
      use tensor_swap.
    Qed.

    Lemma colim_associator_mult : α L R R · L ⊗l μ = colimOfArrows (make_ColimCocone _ _ _ rr) (make_ColimCocone _ _ _ r) _ lemma2.
    Proof.
      unfold colimOfArrows.
      pose (make_ColimCocone _ _ _ rr) as CC.

      assert (
        forms_cocone
          (mapdiagram (rightwhiskering_functor C R)
             (mapdiagram (rightwhiskering_functor C R) F'))
          (λ v : vertex g,
           α (dob F' v) R R · dob F' v ⊗^{ m}_{l} μ · f v ⊗^{ m}_{r} R)
      ) as H_cc'. {
        intros x y e; cbn; do 2 rewrite assoc.
        symmetry.
        1: transitivity (α _ _ _ · _ ⊗l μ · (dmor F' e) ⊗r R · pr1 cc y ⊗r R) .
        2: transitivity (α _ _ _ · (dmor F' e) ⊗r (R ⊗ R) · _ ⊗l μ · pr1 cc y ⊗r R) .
        - do 2 rewrite <- assoc.
          assert (dmor F' e ⊗r R · pr1 cc y ⊗r R = pr1 cc x ⊗r R) as H by
          now rewrite <- (pr2 cc x y e), @tensor_mor_right, @tensor_mor_right, @tensor_mor_right, tensor_comp_id_r.
          now rewrite H, assoc.
        - use (maponpaths (λ u, u · _)). 
          do 2 rewrite <- assoc.
          use maponpaths.
          do 2 rewrite @tensor_mor_right, @tensor_mor_left.
          etrans; [use tensor_swap'|easy].
        - now rewrite monoidal_associatornatright.
      }

      pose (make_cocone _ H_cc') as cc'.

      assert (∏ u : vertex g, colimIn CC u · (α L R R · L ⊗^{ m}_{l} μ) = coconeIn cc' u) as H_unique. {
        intro; cbn; rewrite assoc; symmetry.
        transitivity (α _ _ _ · f u ⊗r _ · L ⊗l μ). 
        do 2 rewrite <- assoc; use maponpaths.
        do 2 rewrite @tensor_mor_right, @tensor_mor_left.
        etrans; [use tensor_swap'|easy].
        now rewrite monoidal_associatornatright.
      }

      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      unfold CC, cc'.
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.


    Lemma colim_module_assoc : α L R R · L ⊗l μ · p = p ⊗r R · p.
    Proof.
      rewrite colim_associator_mult, colim_module_subst_tens_r.
      unfold p, colim_module_subst; cbn.
      assert ( ∏ (u v : vertex g) (e : edge u v),
        (dmor F' e ⊗r R) ⊗r R · (α _ R R · dob F' v ⊗l μ · pr12 (dob F v)) =
        α _ R R · dob F' u ⊗l μ · pr12 (dob F u) · dmor F' e) as H1.
      {
        intros.
        do 2 rewrite assoc.
        transitivity (α _ _ _ · _ ⊗l μ · (dmor F' e) ⊗r R · pr12 (dob F v)).
        transitivity (α _ _ _ · (dmor F' e) ⊗r (R⊗R) · _ ⊗l μ · pr12 (dob F v)).
        - use (maponpaths (λ u, u · _)); now rewrite monoidal_associatornatright.
        - use (maponpaths (λ u, u ·_)); do 2 rewrite <- assoc; use maponpaths.
          do 2 rewrite @tensor_mor_left, @tensor_mor_right; use tensor_swap.
        - do 4 rewrite <- assoc; do 2 use maponpaths; use (pr2 (dmor F e)).
      }

      assert (∏ (u v : vertex g) (e : edge u v),
         (pr1 (dmor F e) ⊗^{ C}_{r} R) ⊗^{ C}_{r} R
         · (pr12 (dob F v) ⊗^{ m}_{r} R · pr12 (dob F v)) =
         pr12 (dob F u) ⊗^{ m}_{r} R · pr12 (dob F u) · pr1 (dmor F e)
      ) as H2.
      {
        intros; rewrite assoc.
        transitivity (pr12 (dob F u) ⊗^{ m}_{r} R · (dmor F' e) ⊗r R · pr12 (dob F v)).
        - use (maponpaths (λ u, u · _)).
          do 5 rewrite @tensor_mor_right.
          transitivity ((pr1 (dmor F e) #⊗ identity R · pr12 (dob F v)) #⊗ identity R); [symmetry; use tensor_comp_id_r|].
          transitivity ((pr12 (dob F u) · dmor F' e) #⊗ identity R); [| use tensor_comp_id_r].
          use (maponpaths (λ u, u #⊗ _)); rewrite <- tensor_mor_right; use (pr2 (dmor F e)).
        - do 2 rewrite <- assoc; use (maponpaths (λ u, _ · u)); use (pr2 (dmor F e)).
      }

      pose (make_ColimCocone _ _ _ rr) as CC1.
      pose (make_ColimCocone _ _ _ r) as CC2.
      pose (make_ColimCocone _ _ _ c) as CC3.


      transitivity (colimOfArrows CC1 CC3 (λ u, pr12 (dob F u) ⊗r R · pr12 (dob F u)) H2).
      transitivity (colimOfArrows CC1 CC3 (λ u, α _ _ _ · _ ⊗l μ · pr12 (dob F u)) H1).
      {
        change (
          colimOfArrows CC1 CC2 (λ u, α (dob F' u) R R · dob F' u ⊗l μ) lemma2
          · colimOfArrows CC2 CC3 (λ u : vertex g, pr12 (dob F u)) (λ _ _ e, pr2 (dmor F e)) =
          colimOfArrows CC1 CC3 (λ u, α (dob F' u) R R · dob F' u ⊗l μ · pr12 (dob F u)) H1
        ); use colimOfArrows_comp.
      }

      {
        use two_arg_paths_f; [|use proofirrelevance;do 3 (use impred; intro);use homset_property].
        use funextsec; intro u; use (pr122 (dob F u)).
      }

      {
        symmetry.
        change (
          colimOfArrows CC1 CC2 (λ u, pr12 (dob F u) ⊗r R) lemma1
          · colimOfArrows CC2 CC3 (λ u : vertex g, pr12 (dob F u)) (λ _ _ e, pr2 (dmor F e)) =
          colimOfArrows CC1 CC3 (λ u, pr12 (dob F u) ⊗r R · pr12 (dob F u)) H2
        ); use colimOfArrows_comp.
      }
    Qed.

    Definition colim_module : module L
      := make_module p colim_module_unit colim_module_assoc.

    Definition colim_module_cocone : cocone F (L,, colim_module).
    Proof.
      use make_cocone.
      - intro u; exists (f u); use colim_module_mor.
      - intros u v e.
        use invmap; [|use path_sigma_hprop|]. use isaprop_is_module_mor.
        change (dmor F' e · f v = f u); use colimInCommutes.
    Defined.

  End Colimits.
End Modules.
