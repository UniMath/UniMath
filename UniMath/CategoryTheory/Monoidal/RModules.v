(***************************************************************************

 (Right) Modules over a monoid

 In this file, we define the category of (right) modules MOD R over a given
 monoid R in some fixed monoidal category C.

 Contents
 1. Definitions
 2. Two examples of modules
 3. Colimits in MOD R are inherited from colimits in C
 4. Limits in MOD R are inherited from limits in C

 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section RModules.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  Context (R : C) (R_m : monoid C R).
  Definition μ : C⟦R ⊗ R, R⟧ := pr1 (pr1 R_m).
  Definition η : C⟦I_{C}, R⟧ := pr2 (pr1 R_m).

  (**
     1. Definitions
   *)

  Definition module_subst (M : C) : UU := C⟦ M ⊗ R, M ⟧.


  Definition module_object {M : C} (p : module_subst M) : C := M.
  Coercion module_object : module_subst >-> ob.

  Definition module_laws_assoc {M : C} (p : module_subst M) : UU
    := α^{C}_{M,R,R} · (M ⊗l μ) · p = p ⊗r R · p.

  Definition module_laws_unit {M : C} (p : module_subst M) : UU
    := M ⊗l η · p = ru^{C}_{M}.

  Definition module_laws {M : C} (p : module_subst M) : UU
    := module_laws_assoc p × module_laws_unit p.

  Lemma isaprop_module_laws {M : C} (p : module_subst M)
    : isaprop (module_laws p).
  Proof.
    use isapropdirprod; use homset_property.
  Qed.

  Definition module (M : C): UU := ∑ p : module_subst M, module_laws p.

  Definition make_module
    {M : C} (p : C⟦M ⊗ R, M⟧)
    (p_unit : M ⊗l η · p = ru^{C}_{M})
    (p_assoc : α^{C}_{M,R,R} · (M ⊗l μ) · p = p ⊗r R · p)
    : module M
    := (p ,, p_assoc ,, p_unit).

  Definition module_to_module_subst {M : C} (p : module M) : C⟦ M ⊗ R, M ⟧ := pr1 p.
  Coercion module_to_module_subst : module >-> precategory_morphisms.

  Definition module_laws_assoc_from_module {M : C} (p : module M) :
    module_laws_assoc (module_to_module_subst p)
    := pr12 p.

  Definition module_laws_unit_from_module {M : C} (p : module M) :
    module_laws_unit (module_to_module_subst p)
    := pr22 p.

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
    rewrite id_right, (bifunctor_rightid C).
    use id_left.
  Qed.

  Lemma comp_is_module_mor (M M' M'' : C)
    (p : module M) (p' : module M') (p'' : module M'')
    (r : C⟦M,M'⟧) (r' : C⟦M',M''⟧)
    (Hr : is_module_mor p p' r) (Hr' : is_module_mor p' p'' r')
    : is_module_mor p p'' (r·r').
  Proof.
    unfold is_module_mor in * |- *.
    rewrite (bifunctor_rightcomp C), assoc, <- Hr.
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

  Lemma module_disp_cat_data_is_locally_propositional : locally_propositional module_disp_cat_data.
  Proof.
    red; intros; use isaprop_is_module_mor.
  Qed.

  Definition module_disp_cat : disp_cat C
    := make_disp_cat_locally_prop module_disp_cat_data_is_locally_propositional.

  Definition MOD : category := total_category module_disp_cat.

  Definition MOD_to_C (M : MOD) : C := pr1 M.

  Lemma MOD_mor_eq {M M' : MOD} (r r' : MOD⟦M,M'⟧) : pr1 r = pr1 r' -> r = r'.
  Proof.
    apply mor_eq_total_category_when_locally_prop.
    exact module_disp_cat_data_is_locally_propositional.
  Qed.

  (**
     2. Two examples of modules
   *)

  Definition trivial_module : MOD :=
    let l := pr2 (monoid_to_monoid_laws C R_m) in
    R ,, μ ,, pr2 l ,, pr1 l.

  Definition product_module_subst {M : C} (D : C) (p : module M) : module_subst (D ⊗_{C} M)
    := α^{C}_{D,M,R} · D ⊗l p.

  Lemma product_module_unit (M D : C) (p : module M) :
    module_laws_unit (product_module_subst D p).
  Proof.
    unfold product_module_subst, module_laws_unit.
    rewrite assoc, <- (monoidal_associatornatleft C).
    etrans.
    - rewrite <- assoc; refine (maponpaths _ _).
      rewrite <- (bifunctor_leftcomp C).
      refine (maponpaths _ _).
      use (module_laws_unit_from_module p).
    - use left_whisker_with_runitor.
  Qed.

  Lemma product_module_assoc (M D : C) (p : module M) :
    module_laws_assoc (product_module_subst D p).
  Proof.
    unfold module_laws_assoc; symmetry.
    etrans; etrans. etrans. etrans.
    - unfold product_module_subst. refine (maponpaths (λ x, x · _) _). use (bifunctor_rightcomp C).
    - rewrite <- assoc; refine (maponpaths _ _); rewrite assoc.
      refine (!maponpaths (λ x, x · _) _).
      use monoidal_associatornatleftright.
    - rewrite <- assoc.
      do 2 refine (maponpaths _ _).
      rewrite <- (bifunctor_leftcomp C).
      refine (!maponpaths _ _); use (module_laws_assoc_from_module p).
    - do 2 rewrite bifunctor_leftcomp; do 3 rewrite assoc.
      refine (maponpaths (λ x, x · _ · _) _).
      use monoidal_pentagonidentity.
    - do 2 rewrite <- assoc.
      refine (maponpaths _ _).
      rewrite assoc.
      refine (maponpaths (λ x, x · _) _).
      use monoidal_associatornatleft.
    - unfold product_module_subst. now do 3 rewrite assoc.
  Qed.

  Definition product_module (M D : C) (p : module M) : MOD.
  Proof.
    exists (D ⊗ M).
    exists (product_module_subst D p).
    split; [use product_module_assoc | use product_module_unit].
  Defined.

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

  (**
     3. Colimits in MOD R are inherited from colimits in C
   *)

  Section Colimits.
    Context {g : graph}.
    Context (colims_g : Colims_of_shape g C).
    Context (HR : preserves_colimits_of_shape (rightwhiskering_functor C R) g).

    Context (F : diagram g MOD).

    Let F' := mapdiagram forgetful F : diagram g C.
    Let L : C := pr11 (colims_g F').
    Let cc : cocone F' L := pr21 (colims_g F').
    Let c : isColimCocone F' L cc := pr2 (colims_g F').

    (* Colimit cocone over L *)
    Definition ColimCocone_L := colims_g F'.

    (* Colimit cocone over L ⊗ R *)
    Definition ColimCocone_L_R := make_ColimCocone _ _ _ (HR F' L cc c).

    (* Colimit cocone over (L ⊗ R) ⊗ R *)
    Definition ColimCocone_L_R_R := make_ColimCocone _ _ _ (HR _ _ _ (HR F' L cc c)).

    Let q (v : vertex g): module_subst (dob F' v) := pr12 (dob F v).
    Let f (v : vertex g): dob F' v --> L := colimIn _ v.

    Definition colim_module_subst : L ⊗ R --> L.
    Proof.
      use (colimOfArrows ColimCocone_L_R ColimCocone_L); simpl.
      - intro u; use (q u).
      - intros u v e; simpl. exact (pr2 (dmor F e)).
    Defined.

    Let p := colim_module_subst.

    Lemma colim_module_mor (v : vertex g) : f v ⊗r R · p = q v · f v.
    Proof.
      use (colimOfArrowsIn _ _ ColimCocone_L_R _ _ _ v).
    Defined.

    Lemma rw_unit_is_left_adjoint
      : is_left_adjoint (rightwhiskering_functor C I_{C}).
    Proof.
      exists (functor_identity C); use make_are_adjoints.
      3: use make_form_adjunction.
      - eexists; intros A B h; symmetry; use monoidal_rightunitorinvnat.
      - eexists; intros A B h; use monoidal_rightunitornat.
      - intro A. cbn; symmetry.
        transitivity (ruinv^{C}_{A} ⊗r I_{C} · ru^{C}_{A} ⊗r I_{C}); [etrans|]; swap 1 2.
        + use (bifunctor_rightcomp C).
        + etrans; [symmetry; use tensor_id_id|].
          now rewrite @tensor_mor_right, (pr2 (monoidal_rightunitorisolaw C A)).
        + use maponpaths.
          do 2 (symmetry; rewrite <- id_right; rewrite <- (pr1 (monoidal_rightunitorisolaw C A)), assoc).
          now rewrite <- monoidal_rightunitornat.
      - intro A; cbn; use (pr2 (monoidal_rightunitorisolaw C A)).
    Qed.

    (* Colimit cocone over L ⊗ I *)
    Definition ColimCocone_L_I := make_ColimCocone _ _ _ (left_adjoint_preserves_colimit _ rw_unit_is_left_adjoint _ _ _ c).

    Lemma colim_rightunitor : ru^{C}_{L} = colimOfArrows ColimCocone_L_I ColimCocone_L (λ _, ru^{C}_{_}) (λ _ _ _, monoidal_rightunitornat _ _ _ _).
    Proof.
      assert (forms_cocone (mapdiagram (rightwhiskering_functor C I_{C}) F') (λ v, ru^{C}_{dob F' v} · f v)) as H_cc'
      by (
        intros v w e; simpl;
        rewrite assoc, monoidal_rightunitornat, <- assoc;
        use maponpaths; use (coconeInCommutes cc)
      ).
      pose (make_cocone _ H_cc') as cc'.
      assert (∏ (u : vertex g), colimIn ColimCocone_L_I u · ru^{C}_{L} = coconeIn cc' u) as H_unique
      by (intro; cbn; use monoidal_rightunitornat).
      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.

    Local Lemma η_swap : ∏ (u v : vertex g) (e : edge u v),
       pr1 (dmor F e) ⊗^{ C}_{r} I_{C} · pr1 (dob F v) ⊗^{ C}_{l} η =
       pr1 (dob F u) ⊗^{ C}_{l} η · pr1 (dmor F e) ⊗^{ C}_{r} R.
    Proof.
      intros.
      do 2 rewrite tensor_mor_right, @tensor_mor_left;
      use tensor_swap.
    Qed.

    Lemma colim_unit : L ⊗l η = colimOfArrows ColimCocone_L_I ColimCocone_L_R (λ _, _ ⊗l η) η_swap.
    Proof.
      assert (forms_cocone (mapdiagram (rightwhiskering_functor C I_{C}) F') (λ v, _ ⊗l η · f v ⊗r _)) as H_cc' by (
        intros u v e; cbn; rewrite assoc;
        change (dmor F' e ⊗r I_{C} · dob F' v ⊗l η · f v ⊗r R = dob F' u ⊗l η · f u ⊗r R); unfold f;
        rewrite <- (colimInCommutes _ _ _ e), !@tensor_mor_right, tensor_comp_id_r, assoc;
        use (maponpaths (λ x, x · _)); rewrite !@tensor_mor_left; use tensor_swap
      ).
      pose (make_cocone _ H_cc') as cc'.
      assert (∏ (u : vertex g), colimIn ColimCocone_L_I u · L ⊗l η = coconeIn cc' u) as H_unique by (
        intro; cbn; do 2 rewrite @tensor_mor_right, @tensor_mor_left; use tensor_swap
      ).
      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.

    Lemma colim_module_unit : L ⊗l η · p = ru^{C}_{L}.
    Proof.
      rewrite colim_unit, colim_rightunitor.
      unfold p, colim_module_subst; simpl.
      simpl.
      assert (∏ u v (e : edge u v),
        dmor F' e ⊗r I_{ C} · (dob F' v ⊗l η · q v)
        = dob F' u ⊗l η · q u · dmor F' e
      ) as H.
      {
        intros; cbn; symmetry; etrans.
        - rewrite <- assoc; refine (maponpaths (λ x, _ · x) _).
          symmetry; use (pr2 (dmor F e)).
        - do 2 rewrite assoc; use (maponpaths (λ u, u · _)).
          do 2 rewrite @tensor_mor_left, @tensor_mor_right.
          use tensor_swap'.
      }
      change (
        colimOfArrows ColimCocone_L_I ColimCocone_L_R _ η_swap
        · colimOfArrows ColimCocone_L_R ColimCocone_L _ (λ _ _ e, pr2 (dmor F e))
        = colimOfArrows ColimCocone_L_I ColimCocone_L _
          (λ _ _ e, monoidal_rightunitornat _ _ _ (dmor F' e))
      ).
      rewrite (colimOfArrows_comp ColimCocone_L_I ColimCocone_L_R ColimCocone_L _ _ _ _ H).
      use two_arg_paths_f; [use funextsec; intro; use (pr222 (dob F x))|].
      do 3 (use funextsec; intro).
      use proofirrelevance; use homset_property.
    Qed.

    Local Lemma lemma_R_R_to_R_nat :
       (∏ u v e,
        (dmor F' e ⊗r R) ⊗r R · q v ⊗r R =
        q u ⊗r R · dmor F' e ⊗r R).
    Proof.
      intros.
      do 2 rewrite <- (bifunctor_rightcomp C).
      use maponpaths.
      use (pr2 (dmor F e)).
    Qed.


    Lemma colim_module_subst_tens_r : p ⊗r R = colimOfArrows ColimCocone_L_R_R ColimCocone_L_R _ lemma_R_R_to_R_nat.
    Proof.
      unfold colimOfArrows; simpl.
      assert (
        forms_cocone
          (mapdiagram (rightwhiskering_functor C R)
             (mapdiagram (rightwhiskering_functor C R) F'))
          (λ v, (q v · f v) ⊗r R)
      ) as H_cc'.
      {
        intros x y e; cbn.
        rewrite <- (bifunctor_rightcomp C), assoc.
        use maponpaths.
        etrans.
        - refine (maponpaths (λ u, u · f y) (pr2 (dmor F e))).
        - rewrite <- assoc; use (maponpaths (λ u, q x · u)).
          use colimInCommutes.
      }

      pose (make_cocone _ H_cc') as cc'.

      assert (∏ u, colimIn ColimCocone_L_R_R u · p ⊗r R = coconeIn cc' u)
      as H_unique.
      {
        intro u; cbn; rewrite <- (bifunctor_rightcomp C).
        use maponpaths; use colim_module_mor.
      }

      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).

      cbn.
      use maponpaths.
      use two_arg_paths_f.
      use funextsec; intro; cbn.
      do 3 rewrite @tensor_mor_right.
      now rewrite tensor_comp_id_r.

      use proofirrelevance.
      use isaprop_forms_cocone.
    Qed.

    Local Lemma lemma_R_R_to_R_nat2 : ∏ u v e,
      (dmor F' e ⊗r R) ⊗r R
      · (α^{C}_{dob F' v,R,R} · dob F' v ⊗l μ) =
      α^{C}_{dob F' u,R,R} · dob F' u ⊗l μ
      · dmor F' e ⊗r R.
    Proof.
      intros; rewrite assoc; etrans.
      - refine (!maponpaths (λ x, x · _) _).
        use monoidal_associatornatright.
      - do 2 rewrite <- assoc.
        use maponpaths.
        do 2 rewrite @tensor_mor_right, @tensor_mor_left.
        use tensor_swap.
    Qed.

    Lemma colim_associator_mult : α^{C}_{L,R,R} · L ⊗l μ = colimOfArrows ColimCocone_L_R_R ColimCocone_L_R _ lemma_R_R_to_R_nat2.
    Proof.
      unfold colimOfArrows.

      assert (
        forms_cocone
          (mapdiagram (rightwhiskering_functor C R)
             (mapdiagram (rightwhiskering_functor C R) F'))
          (λ v : vertex g,
           α^{C}_{dob F' v,R,R} · dob F' v ⊗^{ C}_{l} μ · f v ⊗^{ C}_{r} R)
      ) as H_cc'. {
        intros x y e; cbn; do 2 rewrite assoc.
        etrans; [etrans|]; swap 2 3.
        - now rewrite <- assoc, <- (monoidal_associatornatright C), <- assoc.
        - do 2 (refine (maponpaths _ _)); use (colimInCommutes _ _ _ e).
        - rewrite <- assoc; use (maponpaths (λ u, _ · u)).
          rewrite (bifunctor_rightcomp C).
          do 2 rewrite assoc.
          use (maponpaths (λ u, u · _)).
          do 2 rewrite @tensor_mor_right, @tensor_mor_left.
          use tensor_swap.
      }

      pose (make_cocone _ H_cc') as cc'.

      assert (∏ u : vertex g, colimIn ColimCocone_L_R_R u · (α^{C}_{_,_,_} · L ⊗^{ C}_{l} μ) = coconeIn cc' u) as H_unique. {
        intro; cbn; rewrite assoc; etrans.
        - refine (!maponpaths (λ x, x · _) _).
          use monoidal_associatornatright.
        - do 2 rewrite <- assoc; use maponpaths.
          do 2 rewrite @tensor_mor_right, @tensor_mor_left.
          use tensor_swap.
      }

      etrans.
      use (colimArrowUnique _ _ _ _ H_unique).
      do 2 use maponpaths.
      use proofirrelevance;
      use isaprop_forms_cocone.
    Qed.


    Lemma colim_module_assoc : α^{C}_{L,R,R} · L ⊗l μ · p = p ⊗r R · p.
    Proof.
      rewrite colim_associator_mult, colim_module_subst_tens_r.
      unfold p, colim_module_subst; cbn.
      assert ( ∏ u v e,
        (dmor F' e ⊗r R) ⊗r R · (α^{C}_{_,_,_} · dob F' v ⊗l μ · q v) =
        α^{C}_{_,R,R} · dob F' u ⊗l μ · q u · dmor F' e) as H1.
      {
        intros.
        do 2 rewrite assoc.
        etrans; cycle 1.
        - rewrite <- assoc; refine (maponpaths _ (pr2 (dmor F e))).
        - rewrite <- (monoidal_associatornatright C).
          rewrite assoc; use (maponpaths (λ x, x · _)).
          do 2 rewrite <- assoc; use maponpaths.
          do 2 rewrite  @tensor_mor_left, @tensor_mor_right.
          use tensor_swap.
      }

      assert (∏ u v e,
         (pr1 (dmor F e) ⊗^{ C}_{r} R) ⊗^{ C}_{r} R
         · (q v ⊗^{ C}_{r} R · q v) =
         q u ⊗^{ C}_{r} R · q u · pr1 (dmor F e)
      ) as H2.
      {
        intros; rewrite assoc.
        etrans; cycle 1.
        - rewrite <- assoc. refine (maponpaths (λ x, _ · x) (pr2 (dmor F e))).
        - rewrite assoc. use (maponpaths (λ x, x · _)).
          do 2 rewrite <- (bifunctor_rightcomp C).
          use maponpaths.
          use (pr2 (dmor F e)).
      }

      transitivity (colimOfArrows ColimCocone_L_R_R ColimCocone_L _ H2).
      transitivity (colimOfArrows ColimCocone_L_R_R ColimCocone_L _ H1).
      - change (
          colimOfArrows ColimCocone_L_R_R ColimCocone_L_R _ lemma_R_R_to_R_nat2
          · colimOfArrows ColimCocone_L_R ColimCocone_L _ (λ _ _ e, pr2 (dmor F e))
          = colimOfArrows ColimCocone_L_R_R ColimCocone_L _ H1
        );
        use colimOfArrows_comp.
      - use two_arg_paths_f; cycle 1.
        + use proofirrelevance; do 3 (use impred; intro); use homset_property.
        + use funextsec; intro u; use (module_laws_assoc_from_module (pr2 (dob F u))).
      - symmetry.
        change (
          colimOfArrows ColimCocone_L_R_R ColimCocone_L_R _ lemma_R_R_to_R_nat
          · colimOfArrows ColimCocone_L_R ColimCocone_L _ (λ _ _ e, pr2 (dmor F e))
          = colimOfArrows ColimCocone_L_R_R ColimCocone_L _ H2
        );
        use colimOfArrows_comp.
    Qed.

    Definition colim_module : module L
      := make_module p colim_module_unit colim_module_assoc.

    Definition colim_module_cocone : cocone F (L,, colim_module).
    Proof.
      use make_cocone.
      - intro u; exists (f u); use colim_module_mor.
      - intros u v e.
        apply MOD_mor_eq.
        change (dmor F' e · f v = f u); use colimInCommutes.
    Defined.

    Lemma colim_module_colimArrow_is_module_mor (M : MOD) (cc' : cocone F M)
      : is_module_mor colim_module (pr2 M)
        (colimArrow (colims_g F') (pr1 M) (mapcocone forgetful F cc')).
    Proof.
      use (colimArrowUnique' ColimCocone_L_R).
      intro u; cbn; do 2 rewrite assoc.
      symmetry; etrans; etrans.
      - refine (maponpaths (λ x, x · _) _); use colim_module_mor.
      - rewrite <- assoc; use maponpaths; [|use colimArrowCommutes].
      - symmetry; use (pr2 (coconeIn cc' u)).
      - symmetry; rewrite <- (bifunctor_rightcomp C).
        use (maponpaths (λ x, x · _)); use maponpaths.
        use (colimArrowCommutes _ _ (mapcocone forgetful _ cc')).
    Qed.

    Section FixACocone.
      Context (M : MOD).
      Context (cc' : cocone F M).

      Definition colim_module_colimArrow
        : MOD⟦(L ,, colim_module) , M⟧.
      Proof.
        use tpair; [use colimArrow; now use mapcocone|].
        use colim_module_colimArrow_is_module_mor.
      Defined.

      Lemma colim_module_colimArrow_is_cocone_mor
        : is_cocone_mor colim_module_cocone cc' colim_module_colimArrow.
      Proof.
        intro u; apply MOD_mor_eq; use (colimArrowCommutes _ _ (mapcocone forgetful _ cc')).
      Qed.

      Context (pair : ∑ (u: MOD⟦(L ,, colim_module), M⟧),
            is_cocone_mor colim_module_cocone cc' u).

      Let u : MOD⟦(L ,, colim_module), M⟧ := pr1 pair.
      Let H : is_cocone_mor colim_module_cocone cc' u := pr2 pair.

      Lemma colim_module_colimArrow_unique
        : u = colim_module_colimArrow.
      Proof.
        apply MOD_mor_eq; use colimArrowUnique; intro v; cbn.
        now rewrite <- H.
      Qed.

      Lemma colim_module_colimArrow_uniqueness
        : pair = (colim_module_colimArrow ,, colim_module_colimArrow_is_cocone_mor).
      Proof.
        use subtypePath.
        use isaprop_is_cocone_mor.
        use colim_module_colimArrow_unique.
      Qed.
    End FixACocone.

    Definition colim_module_isColimCocone
      : isColimCocone F (L,, colim_module) colim_module_cocone
      := λ M cc', _ ,, colim_module_colimArrow_uniqueness M cc'.

    Definition colim_module_ColimCocone : ColimCocone F.
    Proof.
      use make_ColimCocone.
      - exists L; use colim_module.
      - use colim_module_cocone.
      - use colim_module_isColimCocone.
    Defined.
  End Colimits.

  Theorem MOD_inherits_colimits (g : graph) (_ : Colims_of_shape g C)
    (_ : preserves_colimits_of_shape (rightwhiskering_functor C R) g)
    : Colims_of_shape g MOD.
  Proof.
    now use colim_module_ColimCocone.
  Defined.

  (**
     4. Limits in MOD R are inherited from colimits in C
   *)

  Section limits.
    Context {g : graph}.
    Context (lims_g : Lims_of_shape g C).

    Context (F : diagram g MOD).

    Let F' := mapdiagram forgetful F : diagram g C.
    Let L : C := pr11 (lims_g F').
    Let cc : cone F' L := pr21 (lims_g F').
    Let c : isLimCone F' L cc := pr2 (lims_g F').

    Let q (v : vertex g): module_subst (dob F' v) := pr12 (dob F v).
    Let f (v : vertex g): L --> dob F' v := limOut _ v.

    Local Lemma lim_module_forms_cone_tens_R
      : forms_cone F' (λ v, f v ⊗r R · q v).
    Proof.
      intros u v e.
      symmetry; etrans.
      - refine (maponpaths (λ x, x ⊗r _ · _) _).
        unfold f; now rewrite <- (limOutCommutes _ _ _ e).
      - rewrite (bifunctor_rightcomp C), <- assoc, <- assoc.
        use maponpaths; use (pr2 (dmor F e)).
    Qed.

    Definition lim_module_subst : module_subst L
      := limArrow _ _ (make_cone _ lim_module_forms_cone_tens_R).

    Local Lemma lim_module_forms_cone_tens_I
      : forms_cone F' (λ v, f v ⊗r I_{ C} · dob F' v ⊗l η · q v).
    Proof.
      intros u v e.
      etrans; [etrans|]; swap 2 3.
      - rewrite <- assoc.
        refine (!maponpaths (λ x, _ · _ · x) _).
        use (pr2 (dmor F e)).
      - refine (maponpaths (λ x, x ⊗r _ · _ · _) _).
        use (limOutCommutes _ _ _ e).
      - rewrite (bifunctor_rightcomp C).
        do 3 rewrite <- assoc; use maponpaths.
        do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
        do 2 rewrite @tensor_mor_left, @tensor_mor_right; use tensor_swap'.
    Qed.

    Lemma lim_module_unit
      : module_laws_unit lim_module_subst.
    Proof.
      etrans.
      - use limArrowUnique.
        use (make_cone _ lim_module_forms_cone_tens_I).
        intro u; unfold lim_module_subst; cbn; etrans.
        + rewrite <- assoc; refine (maponpaths _ _).
          use (limArrowCommutes (lims_g F')).
        + cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
          do 2 rewrite @tensor_mor_left, @tensor_mor_right; use tensor_swap'.
      - symmetry; use limArrowUnique; intro u; cbn; symmetry; etrans.
        + rewrite <- assoc; refine (maponpaths _ _).
          use module_laws_unit_from_module.
        + use monoidal_rightunitornat.
    Qed.

    Local Lemma lim_module_forms_cone_tens_R_R
      : forms_cone F' (λ v, (f v ⊗r R) ⊗r R · q v ⊗r R · q v).
    Proof.
      intros u v e; symmetry; etrans; [etrans|].
      - refine (!maponpaths (λ x, (x ⊗r R) ⊗r R · _ · _) _).
        use (limOutCommutes _ _ _ e).
      - do 2 rewrite (bifunctor_rightcomp C).
        do 2 rewrite <- assoc; refine (maponpaths _ _).
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        rewrite <- @bifunctor_rightcomp; refine (maponpaths _ _).
        use (pr2 (dmor F e)).
      - rewrite bifunctor_rightcomp;
        do 3 rewrite <- assoc;
        do 2 use maponpaths.
        use (pr2 (dmor F e)).
    Qed.

    Lemma lim_module_assoc
      : module_laws_assoc lim_module_subst.
    Proof.
      unfold module_laws_assoc; symmetry; etrans.
      - use limArrowUnique.
        use (make_cone _ lim_module_forms_cone_tens_R_R).
        intro u; unfold lim_module_subst; cbn; etrans.
        + rewrite <- assoc; refine (maponpaths _ _).
          use (limArrowCommutes (lims_g F')).
        + cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
          do 2 rewrite <- (bifunctor_rightcomp C).
          use maponpaths; use (limArrowCommutes (lims_g F')).
      - symmetry; use limArrowUnique; intro u; cbn.
        symmetry; do 2 etrans; swap 3 4.
        + rewrite <- assoc; refine (maponpaths _ _).
          symmetry; use module_laws_assoc_from_module.
        + do 2 rewrite assoc; refine (maponpaths (λ x, x · _ · _) _).
          symmetry; use monoidal_associatornatright.
        + symmetry; rewrite <- assoc; refine (maponpaths _ _).
          use (limArrowCommutes (lims_g F')).
        + cbn.
          do 3 rewrite <- assoc; use maponpaths.
          do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
          do 2 rewrite @tensor_mor_right, @tensor_mor_left; use tensor_swap.
    Qed.


    Definition lim_module : module L
      := make_module lim_module_subst lim_module_unit lim_module_assoc.

    Lemma lim_module_cone : cone F (L ,, lim_module).
    Proof.
      use make_cone.
      - intro v; exists (f v).
        abstract (
          cbn; unfold is_module_mor; symmetry;
          use (limArrowCommutes (lims_g F'))
        ).
      - abstract(
          intros u v e; apply MOD_mor_eq; use limOutCommutes).
    Defined.

    Lemma lim_module_limArrow_is_module_mor (M : MOD) (cc' : cone F M)
      : is_module_mor (pr2 M) lim_module
        (limArrow (lims_g F') (pr1 M) (mapcone forgetful F cc')).
    Proof.
      unfold is_module_mor; cbn; etrans.
      - use limArrowUnique; [use make_cone|].
        + intro v; use (module_to_module_subst (pr2 M) · pr1 (coneOut cc' v)).
        + abstract (
            intros u v e; rewrite <- assoc; use maponpaths;
            now rewrite <- (coneOutCommutes _ _ _ e)
          ).
        + intro u; cbn; etrans; [etrans|].
          * rewrite <- assoc; refine (maponpaths _ _).
            use (limArrowCommutes (lims_g F')).
          * cbn; rewrite assoc, <- (bifunctor_rightcomp C);
            refine (maponpaths (λ x, x ⊗r R · _) _).
            use (limArrowCommutes (lims_g F')).
          * use (pr2 (coneOut cc' _)).
      - symmetry; use limArrowUnique; intro u; cbn.
        rewrite <- assoc; use maponpaths.
        use (limArrowCommutes (lims_g F')).
    Qed.

    Section FixACone.

      Context (M : MOD).
      Context (cc' : cone F M).

      Definition lim_module_limArrow
        : MOD⟦M, (L ,, lim_module)⟧.
      Proof.
        use tpair; [use limArrow; now use mapcone|].
        use lim_module_limArrow_is_module_mor.
      Defined.

      Lemma lim_module_limArrow_is_cone_mor
        : is_cone_mor cc' lim_module_cone lim_module_limArrow.
      Proof.
        intro v.
        apply MOD_mor_eq.
        use (limArrowCommutes (lims_g F')).
      Qed.

      Context (pair : ∑ (u: MOD⟦M, (L ,, lim_module)⟧),
            is_cone_mor cc' lim_module_cone u).

      Let u : MOD⟦M, (L ,, lim_module)⟧ := pr1 pair.
      Let H : is_cone_mor cc' lim_module_cone u := pr2 pair.

      Lemma lim_module_limArrow_unique
        : u = lim_module_limArrow.
      Proof.
        apply MOD_mor_eq.
        use limArrowUnique; intro v; cbn.
        now rewrite <- H.
      Qed.

      Lemma lim_module_limArrow_uniqueness
        : pair = (lim_module_limArrow ,, lim_module_limArrow_is_cone_mor).
      Proof.
        use subtypePath.
        use isaprop_is_cone_mor.
        use lim_module_limArrow_unique.
      Qed.

    End FixACone.

    Definition lim_module_isLimCone
      : isLimCone F (L,, lim_module) lim_module_cone
      := λ M cc', _ ,, lim_module_limArrow_uniqueness M cc'.

    Definition lim_module_LimCone : LimCone F.
    Proof.
      use make_LimCone.
      - eexists; exact lim_module.
      - use lim_module_cone.
      - use lim_module_isLimCone.
    Defined.
  End limits.

  Theorem MOD_inherits_limits (g : graph) (_ : Lims_of_shape g C)
    : Lims_of_shape g MOD.
  Proof.
    now use lim_module_LimCone.
  Defined.
End RModules.
