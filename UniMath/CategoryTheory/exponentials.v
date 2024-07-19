(**************************************************************************************************

  Exponential objects

  The exponential object b^a is defined via a left adjoint to the functor a × _. Since this functor
  is not definitionally equal to _ × a, we have to show that having a left adjoint to one of these
  functors also gives a left adjoint to the other. Furthermore, we give accessors for all aspects of
  both of these adjunctions, define what it means for a functor to preserve exponentials, and show
  that exponentials can be transported along an adjoint equivalence.

  Anders Mörtberg, 2016
  Section [ExponentialsCarriedThroughAdjointEquivalence] added by Ralph Matthes in 2023

  Contents:
  1. Definition of exponentials [Exponentials]
  2. Accessors [exp] [exp_eval(_alt)] [exp_lam] [exp_app] [exp_beta] [exp_eta]
  3. Preservation [preserves_exponentials]
  4. Transport along an adjoint equivalence
    [is_expDd0_adjunction_laws] [exponentials_through_adj_equivalence_univalent_cats]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.BinProducts.

(* for Section [ExponentialsCarriedThroughAdjointEquivalence] *)
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.


(** * 1. Definition of exponentials *)
Section Exponentials.

  Context {C : category} (PC : BinProducts C).

  (* The functor "a × _" and "_ × a" *)
  Definition constprod_functor1 (a : C) : functor C C :=
    BinProduct_of_functors C C PC (constant_functor C C a) (functor_identity C).

  Definition constprod_functor2 (a : C) : functor C C :=
    BinProduct_of_functors C C PC (functor_identity C) (constant_functor C C a).

  Definition is_exponentiable (a : C) : UU := is_left_adjoint (constprod_functor1 a).

  Definition Exponentials : UU := ∏ (a : C), is_exponentiable a.
  Definition hasExponentials : UU := ∏ (a : C), ∥ is_exponentiable a ∥.

  Definition flip_z_iso a : @z_iso [C,C] (constprod_functor1 a) (constprod_functor2 a)
    := z_iso_from_nat_z_iso _
      (BinProduct_of_functors_commutes C C PC (constant_functor C C a) (functor_identity C)).

  Definition is_exponentiable_to_is_exponentiable'
    (a : C)
    (HF : is_exponentiable a)
    : is_left_adjoint (constprod_functor2 a)
    := is_left_adjoint_closed_under_iso _ _ (flip_z_iso a) HF.

  Definition is_exponentiable'_to_is_exponentiable
    (a : C)
    (HF : is_left_adjoint (constprod_functor2 a))
    : is_exponentiable a
    := is_left_adjoint_closed_under_iso _ _ (z_iso_inv (flip_z_iso a)) HF.

End Exponentials.

(** * 2. Accessors *)
Section Accessors.

  Context {C : category}
          {prodC : BinProducts C}
          (expC : Exponentials prodC).

  Let expC' (a : C)
    : is_left_adjoint (constprod_functor2 _ a)
    := is_exponentiable_to_is_exponentiable' _ _ (expC _).

  Definition exp
             (x y : C)
    : C
    := pr1 (expC x) y.

  Definition exp_eval
             (x y : C)
    : prodC x (exp x y) --> y
    := counit_from_are_adjoints (pr2 (expC x)) y.

  Definition exp_eval_alt
             (x y : C)
    : prodC (exp x y) x --> y
    := counit_from_are_adjoints (pr2 (expC' x)) y.

  Definition exp_lam
             {x y z : C}
             (f : prodC y x --> z)
    : x --> exp y z
    := φ_adj (pr2 (expC y)) f.

  Definition exp_lam_alt
             {x y z : C}
             (f : prodC z x --> y)
    : z --> exp x y
    := φ_adj (pr2 (expC' x)) f.

  Definition exp_app
             {x y z : C}
             (f : x --> exp y z)
    : prodC y x --> z
    := φ_adj_inv ((pr2 (expC y))) f.

  Definition exp_app_alt
             {x y z : C}
             (f : z --> exp x y)
    : prodC z x --> y
    := φ_adj_inv (pr2 (expC' x)) f.

  Definition exp_lam_app
             {x y z : C}
             (f : x --> exp y z)
    : exp_lam (exp_app f) = f
    := φ_adj_after_φ_adj_inv _ _.

  Definition exp_lam_app_alt
             {x y z : C}
             (f : x --> exp y z)
    : exp_lam_alt (exp_app_alt f) = f
    := φ_adj_after_φ_adj_inv _ _.

  Definition exp_app_lam
             {x y z : C}
             (f : prodC y x --> z)
    : exp_app (exp_lam f) = f
    := φ_adj_inv_after_φ_adj (pr2 (expC _)) _.

  Definition exp_app_lam_alt
             {x y z : C}
             (f : prodC z x --> y)
    : exp_app_alt (exp_lam_alt f) = f
    := φ_adj_inv_after_φ_adj (pr2 (expC' _)) _.

  Proposition exp_beta
              {x y z : C}
              (f : prodC y x --> z)
    : BinProductOfArrows _ _ _ (identity _) (exp_lam f)
      · exp_eval _ _
      =
      f.
  Proof.
    refine (!maponpaths (λ x, x · _) (BinProductOfArrows_idxcomp _ _ _ _) @ _).
    rewrite !assoc'.
    refine (maponpaths _ (nat_trans_ax (counit_from_are_adjoints (pr2 (expC y))) _ _ f) @ _).
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (triangle_id_left_ad (pr2 (expC y))).
  Qed.

  Proposition exp_beta_alt
              {x y z : C}
              (f : prodC z x --> y)
    : BinProductOfArrows _ _ _ (exp_lam_alt f) (identity x)
      · exp_eval_alt x y
      =
      f.
  Proof.
    refine (!maponpaths (λ x, x · _) (BinProductOfArrows_compxid _ _ _ _) @ _).
    rewrite !assoc'.
    refine (maponpaths _ (nat_trans_ax (counit_from_are_adjoints (pr2 (expC' x))) _ _ f) @ _).
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (triangle_id_left_ad (pr2 (expC' x))).
  Qed.

  Proposition exp_eta
              {x y z : C}
              (f : z --> exp x y)
    : f
      =
      exp_lam (BinProductOfArrows C _ _ (identity x) f · exp_eval x y).
  Proof.
    refine (_ @ !maponpaths (λ x, _ · x) (functor_comp _ _ _)).
    rewrite !assoc.
    refine (!_ @ maponpaths_2 _ ((nat_trans_ax (unit_from_are_adjoints (pr2 (expC x))) _ _ f)) _).
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_id_right_ad (pr2 (expC x)) _).
  Qed.

  Proposition exp_eta_alt
              {x y z : C}
              (f : z --> exp x y)
    : f
      =
      exp_lam_alt (BinProductOfArrows C _ _ f (identity x) · exp_eval_alt x y).
  Proof.
    refine (_ @ !maponpaths (λ x, _ · x) (functor_comp _ _ _)).
    rewrite !assoc.
    refine (!_ @ maponpaths_2 _ ((nat_trans_ax (unit_from_are_adjoints (pr2 (expC' x))) _ _ f)) _).
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_id_right_ad (pr2 (expC' x)) _).
  Qed.

  Proposition exp_funext
              {x y z : C}
              {f g : z --> exp x y}
              (p : ∏ (a : C)
                     (h : a --> x),
                   BinProductOfArrows C _ (prodC a z) h f · exp_eval x y
                   =
                   BinProductOfArrows C _ (prodC a z) h g · exp_eval x y)
    : f = g.
  Proof.
    refine (exp_eta f @ _ @ !(exp_eta g)).
    apply maponpaths.
    apply p.
  Qed.

  Proposition exp_funext_alt
              {x y z : C}
              {f g : z --> exp x y}
              (p : ∏ (a : C)
                     (h : a --> x),
                   BinProductOfArrows C _ (prodC z a) f h · exp_eval_alt x y
                   =
                   BinProductOfArrows C _ (prodC z a) g h · exp_eval_alt x y)
    : f = g.
  Proof.
    refine (exp_eta_alt f @ _ @ !(exp_eta_alt g)).
    apply maponpaths.
    apply p.
  Qed.

  Definition exp_lam_natural
              {w x y z : C}
              (f : prodC y x --> z)
              (s : w --> x)
    : s · exp_lam f
      =
      exp_lam (BinProductOfArrows _ _ _ (identity _ ) s · f)
    := !φ_adj_natural_precomp _ _ _ _ _ _.

  Definition exp_lam_natural_alt
              {w x y z : C}
              (f : prodC x y --> z)
              (s : w --> x)
    : s · exp_lam_alt f
      =
      exp_lam_alt (BinProductOfArrows _ _ _ s (identity _ ) · f)
    := !φ_adj_natural_precomp _ _ _ _ _ _.

End Accessors.

(** * 3. Preservation *)
Section Preservation.

  (** * Preservation of exponentials by functors *)
  Definition preserves_exponentials_map
            {C₁ C₂ : category}
            {BC₁ : BinProducts C₁}
            {BC₂ : BinProducts C₂}
            (E₁ : Exponentials BC₁)
            (E₂ : Exponentials BC₂)
            {F : C₁ ⟶ C₂}
            (HF : preserves_binproduct F)
            (x y : C₁)
    : F(exp E₁ x y) --> exp E₂ (F x) (F y).
  Proof.
    use exp_lam.
    pose (preserves_binproduct_to_z_iso
            F HF
            (BC₁ x (exp E₁ x y))
            (BC₂ (F x) (F (exp E₁ x y))))
      as f.
    refine (inv_from_z_iso f · #F _).
    apply exp_eval.
  Defined.

  Definition preserves_exponentials
            {C₁ C₂ : category}
            {BC₁ : BinProducts C₁}
            {BC₂ : BinProducts C₂}
            (E₁ : Exponentials BC₁)
            (E₂ : Exponentials BC₂)
            {F : C₁ ⟶ C₂}
            (HF : preserves_binproduct F)
    : UU
    := ∏ (x y : C₁), is_z_isomorphism (preserves_exponentials_map E₁ E₂ HF x y).

End Preservation.

(** * 4. Transport along an adjoint equivalence *)
Section ExponentialsCarriedThroughAdjointEquivalence.

  Context {C : category} (PC : BinProducts C) {D : category} (PD : BinProducts D)
    (ExpC : Exponentials PC) (adjeq : adj_equiv C D).

  Let F : functor C D := adjeq.
  Let G : functor D C := adj_equivalence_inv adjeq.
  Let η_z_iso : ∏ (c : C), z_iso c (G (F c)) := unit_pointwise_z_iso_from_adj_equivalence adjeq.
  Let ε_z_iso : ∏ (d : D), z_iso (F (G d)) d := counit_pointwise_z_iso_from_adj_equivalence adjeq.
  Let η_nat_z_iso : nat_z_iso (functor_identity C) (functor_composite F G) :=
        unit_nat_z_iso_from_adj_equivalence_of_cats adjeq.
  Let ε_nat_z_iso : nat_z_iso  (functor_composite G F) (functor_identity D) :=
        counit_nat_z_iso_from_adj_equivalence_of_cats adjeq.

  Let FC (c : C) : functor C C := constprod_functor1 PC c.
  Let GC (c : C) : functor C C := right_adjoint (ExpC c).
  Let ηC (c : C) : functor_identity C ⟹ (FC c) ∙ (GC c) := unit_from_left_adjoint (ExpC c).
  Let εC (c : C) : functor_composite (GC c) (FC c) ⟹ functor_identity C := counit_from_left_adjoint (ExpC c).

  Section FixAnObject.

    Context (d0 : D).

    Let Fd0 : functor D D := constprod_functor1 PD d0.
    Let Gd0 : functor D D := functor_composite (functor_composite G (GC (G d0))) F.

    Local Definition inherited_BP_on_C (d : D) : BinProduct C (G d0) (G d).
    Proof.
      use tpair.
      - exists (G (pr1 (pr1 (PD d0 d)))).
        exact (# G (pr1 (pr2 (pr1 (PD d0 d)))),,# G (pr2 (pr2 (pr1 (PD d0 d))))).
      - set (Hpres := right_adjoint_preserves_binproduct adjeq adjeq : preserves_binproduct G).
        exact (Hpres _ _ _ _ _ (pr2 (PD d0 d))).
    Defined.

    Local Definition μ_nat_trans_data : nat_trans_data (G ∙ FC (G d0)) (Fd0 ∙ G).
    Proof.
      intro d.
      exact (BinProductOfArrows _ (inherited_BP_on_C d) (PC (G d0) (G d)) (identity _) (identity _)).
    Defined.

    Local Lemma μ_nat_trans_law : is_nat_trans _ _ μ_nat_trans_data.
    Proof.
      intros d' d f.
      apply (BinProductArrowsEq _ _ _ (inherited_BP_on_C d)).
      - etrans.
        { rewrite assoc'.
          apply maponpaths.
          apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
        rewrite id_right.
        etrans.
        2: { cbn.
            rewrite assoc'.
            etrans.
            2: { apply maponpaths.
                  apply functor_comp. }
            unfold BinProduct_of_functors_mor.
            cbn.
            etrans.
            2: { do 2 apply maponpaths.
                  apply pathsinv0, BinProductOfArrowsPr1. }
            rewrite id_right.
            unfold BinProductPr1.
            apply pathsinv0, (BinProductOfArrowsPr1 _ (inherited_BP_on_C d') (PC (G d0) (G d'))).
        }
        rewrite id_right.
        cbn.
        unfold BinProduct_of_functors_mor, constant_functor, functor_identity.
        cbn.
        etrans.
        { apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (PC (G d0) (G d'))). }
        apply id_right.
      - etrans.
        { rewrite assoc'.
          apply maponpaths.
          apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
        rewrite id_right.
        etrans.
        2: { cbn.
            rewrite assoc'.
            etrans.
            2: { apply maponpaths.
                  apply functor_comp. }
            unfold BinProduct_of_functors_mor.
            cbn.
            etrans.
            2: { do 2 apply maponpaths.
                  apply pathsinv0, BinProductOfArrowsPr2. }
            rewrite functor_comp.
            rewrite assoc.
            apply cancel_postcomposition.
            unfold BinProductPr2.
            apply pathsinv0, (BinProductOfArrowsPr2 _ (inherited_BP_on_C d') (PC (G d0) (G d'))).
        }
        rewrite id_right.
        cbn.
        unfold BinProduct_of_functors_mor, constant_functor, functor_identity.
        cbn.
        etrans.
        { apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (PC (G d0) (G d'))). }
        apply idpath.
    Qed.

    Local Definition μ_nat_trans : nat_trans (G ∙ FC (G d0)) (Fd0 ∙ G) := _,,μ_nat_trans_law.

    Local Definition μ_nat_trans_inv_pointwise (d : D) : C ⟦ (Fd0 ∙ G) d, (G ∙ FC (G d0)) d ⟧.
    Proof.
      exact (BinProductOfArrows _ (PC (G d0) (G d)) (inherited_BP_on_C d) (identity _) (identity _)).
    Defined.

    Local Lemma μ_nat_trans_is_inverse (d : D): is_inverse_in_precat (μ_nat_trans d) (μ_nat_trans_inv_pointwise d).
    Proof.
      split; cbn.
      - apply pathsinv0, BinProduct_endo_is_identity.
        + rewrite assoc'.
          etrans.
          { apply maponpaths.
            cbn.
            apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
          rewrite id_right.
          etrans.
          { cbn.
            apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
          apply id_right.
        + rewrite assoc'.
          etrans.
          { apply maponpaths.
            cbn.
            apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
          rewrite id_right.
          etrans.
          { cbn.
            apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
          apply id_right.
      - unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
        cbn.
        apply pathsinv0. apply (BinProduct_endo_is_identity _ _ _ (inherited_BP_on_C d)).
        + rewrite assoc'.
          etrans.
          { apply maponpaths.
            apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
          rewrite id_right.
          etrans.
          { apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
          apply id_right.
        + rewrite assoc'.
          etrans.
          { apply maponpaths.
            apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
          rewrite id_right.
          etrans.
          { apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
          apply id_right.
    Qed.

    Local Definition μ : nat_z_iso (functor_composite G (FC (G d0))) (functor_composite Fd0 G).
    Proof.
      use make_nat_z_iso.
      - exact μ_nat_trans.
      - intro d.
        use tpair.
        + exact (μ_nat_trans_inv_pointwise d).
        + exact (μ_nat_trans_is_inverse d).
    Defined.

    Local Definition ηDd0 : functor_identity D ⟹ Fd0 ∙ Gd0.
    Proof.
      simple refine (nat_trans_comp _ _ _ (nat_z_iso_to_trans_inv ε_nat_z_iso) _).
      unfold Gd0.
      change ((functor_composite G (functor_identity C)) ∙ F ⟹ (Fd0 ∙ (G ∙ GC (G d0))) ∙ F).
      apply post_whisker.
      refine (nat_trans_comp _ _ _ _ _).
      - apply (pre_whisker G (ηC (G d0))).
      - change (functor_composite (functor_composite G (FC (G d0))) (GC (G d0)) ⟹
                  functor_composite (Fd0 ∙ G) (GC (G d0))).
        apply post_whisker.
        apply μ.
    Defined.

    Local Definition εDd0 : Gd0 ∙ Fd0 ⟹ functor_identity D.
    Proof.
      simple refine (nat_trans_comp _ _ _ _ ε_nat_z_iso).
      change (functor_composite (functor_composite Gd0 Fd0) (functor_identity D) ⟹ G ∙ F).
      refine (nat_trans_comp _ _ _ _ _).
      - apply (pre_whisker _ (nat_z_iso_to_trans_inv ε_nat_z_iso)).
      - change ((functor_composite (Gd0 ∙ Fd0) G) ∙ F ⟹ G ∙ F).
        apply post_whisker.
        unfold Gd0.
        change (((G ∙ GC (G d0)) ∙ F) ∙ (Fd0 ∙ G) ⟹ G).
        refine (nat_trans_comp _ _ _ _ _).
        + apply (pre_whisker _ (nat_z_iso_to_trans_inv μ)).
        + change ((((G ∙ GC (G d0)) ∙ F) ∙ G) ∙ FC (G d0) ⟹ G).
          refine (nat_trans_comp _ _ _ _ _).
          * use (post_whisker _ (FC (G d0))).
            -- exact (G ∙ GC (G d0)).
            -- change (functor_composite (G ∙ GC (G d0)) (functor_composite F G) ⟹
                        functor_composite (G ∙ GC (G d0)) (functor_identity C)).
              apply (pre_whisker _ (nat_z_iso_to_trans_inv η_nat_z_iso)).
          * change (functor_composite G (functor_composite (GC (G d0)) (FC (G d0))) ⟹ G).
            apply (pre_whisker _ (εC (G d0))).
    Defined.

    Definition is_expDd0_adjunction_data : adjunction_data D D.
    Proof.
      use make_adjunction_data.
      - exact Fd0.
      - exact Gd0.
      - exact ηDd0.
      - exact εDd0.
    Defined.

    Lemma is_expDd0_adjunction_laws : form_adjunction' is_expDd0_adjunction_data.
    Proof.
      split.
      - intro d.
        change (# Fd0 (ηDd0 d) · εDd0 (Fd0 d) = identity (Fd0 d)).
        unfold ηDd0.
        etrans.
        { apply cancel_postcomposition.
          etrans.
          { apply functor_comp. }
          do 2 apply maponpaths.
          assert (Hpost := post_whisker_composition _ _ _ F _ _ _ (pre_whisker G (ηC (G d0))) (post_whisker (pr1 μ) (GC (G d0)))).
          refine (toforallpaths _ _ _ (maponpaths pr1 Hpost) d).
        }
        etrans.
        { apply cancel_postcomposition.
          apply maponpaths.
          apply functor_comp. }
        unfold εDd0.
    (* so it is in principle possible to work with this definition, but every step takes an effort,
      requiring a perfect proof on paper before

        rewrite functor_comp.
        use BinProductArrowsEq.
        + rewrite id_left.


          cbn. unfold BinProduct_of_functors_mor.
          rewrite id_left.
          unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
          cbn.
          etrans.
          { apply cancel_postcomposition.
            apply
          admit.
        + cbn. unfold BinProduct_of_functors_mor.
          rewrite id_left.
          unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
          cbn.
          (* is this supposed to be analogous? *)
          admit.
      - intro d. show_id_type. (* F-images in source and target of the morphisms *)
        cbn.
        admit.
    *)
    Abort.

    (*
    Definition is_expDd0_adjunction : adjunction D D := _,,is_expDd0_adjunction_laws.

    Local Definition is_expDd0 : is_exponentiable PD d0.
    Proof.
      exists Gd0.
      exact is_expDd0_adjunction.
    Defined.
    *)

    (* an experiment towards using univalence for this proof
    Lemma is_expDd0_adjunction_laws_equal_cats (Heq : C = D) (*(PCeq : transportf _ Heq PC = PD)*) :
      form_adjunction' is_expDd0_adjunction_data.
    Proof.
      induction Heq.
    *)

  End FixAnObject.
  (*
  Definition exponentials_through_adj_equivalence : Exponentials PD.
  Proof.
    intro d0. exact (is_expDd0 d0).
  Defined.
  *)

End ExponentialsCarriedThroughAdjointEquivalence.

Section AlternativeWithUnivalence.

  Context {C : category} (PC : BinProducts C) {D : category} (PD : BinProducts D)
    (ExpC : Exponentials PC) (adjeq : adj_equiv C D) (Cuniv : is_univalent C) (Duniv : is_univalent D).

  Local Lemma CDeq : C = D.
  Proof.
    assert (aux : category_to_precategory C = category_to_precategory D).
    { apply (invmap (catiso_is_path_precat C D D)).
      apply (adj_equivalence_of_cats_to_cat_iso adjeq); assumption. }
    apply subtypePath. intro. apply isaprop_has_homsets.
    exact aux.
  Qed.

  Definition exponentials_through_adj_equivalence_univalent_cats : Exponentials PD.
  Proof.
    induction CDeq.
    clear adjeq.
    assert (aux : PC = PD).
    2: { rewrite <- aux. exact ExpC. }
    apply funextsec.
    intro c1.
    apply funextsec.
    intro c2.
    apply isaprop_BinProduct; exact Cuniv.
  Defined.

End AlternativeWithUnivalence.
