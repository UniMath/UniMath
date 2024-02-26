(*******************************************************************************************

 Preservation of isomorphic functors

 In this file, we show that two functors that are equivalent in the arrow bicategory, share
 the same preservation properties regarding finite limits. More specifically, we show two
 statements.

 First, we show that whenever we have a natural isomorphism from `F` to `G`, then `G`
 preserves terminal objects/binary products/equalizers whenever `F` does. Using this, we show
 that whenever a functor `G : D₁ ⟶ D₂` is equivalent to some functor `F : C₁ ⟶ C₂` in the
 arrow bicategory, then `G` preserves terminal objects/binary products/equalizers if `F` does.
 An equivalence between `F` and `G` in the arrow bicategory amounts to adjoint equivalences
 `C₁ ≃ D₁` and `C₂ ≃ D₂` such that the resulting square commutes.

 Contents
 1. Preservation and natural isomorphisms
 2. Preservation and equivalences in the arrow bicategory

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.EquivalencePreservation.
Require Import UniMath.CategoryTheory.Limits.LimitIso.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * 1. Preservation and natural isomorphisms *)
Section PreservationNatIso.
  Context {C D : category}
          {F G : C ⟶ D}
          (τ : nat_z_iso F G).

  Definition preserves_terminal_nat_z_iso_f
             (HF : preserves_terminal F)
    : preserves_terminal G.
  Proof.
    intros x Hx.
    use (iso_to_Terminal (make_Terminal _ (HF _ Hx))).
    cbn.
    exact (nat_z_iso_pointwise_z_iso τ x).
  Defined.

  Definition preserves_binproduct_nat_z_iso_f
             (HF : preserves_binproduct F)
    : preserves_binproduct G.
  Proof.
    intros x y p π₁ π₂ H.
    pose (prod := make_BinProduct _ _ _ _ _ _ (HF _ _ _ _ _ H)).
    use (isBinProduct_z_iso
           (isBinProduct_BinProduct _ (BinProduct_z_iso_lr prod _ _))).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ y)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ p)).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
  Defined.

  Definition preserves_equalizer_nat_z_iso_f
             (HF : preserves_equalizer F)
    : preserves_equalizer G.
  Proof.
    intros x y e f g h p Fp H.
    assert (q : # F h · # F f = # F h · # F g).
    {
      abstract
        (rewrite <- !functor_comp ;
         exact (maponpaths #F p)).
    }
    pose (eq := make_Equalizer _ _ _ q (HF _ _ _ _ _ _ _ _ H)).
    use (isEqualizer_z_iso
           (isEqualizer_Equalizer (Equalizer_z_iso_lr eq _ _ _ _))).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ y)).
    - abstract
        (cbn ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         cbn ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         apply nat_trans_ax).
    - abstract
        (cbn ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         cbn ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         apply nat_trans_ax).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ e)).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
  Defined.
End PreservationNatIso.

Definition preserves_terminal_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_terminal G)
  : preserves_terminal F.
Proof.
  exact (preserves_terminal_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_binproduct_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_binproduct G)
  : preserves_binproduct F.
Proof.
  exact (preserves_binproduct_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_equalizer_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_equalizer G)
  : preserves_equalizer F.
Proof.
  exact (preserves_equalizer_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

(** *  2. Preservation and equivalences in the arrow bicategory *)
Section EquivalencePreservation.
  Context {C₁ C₂ D₁ D₂ : category}
          (EC : C₁ ⟶ C₂)
          (ED : D₁ ⟶ D₂)
          (HEC : adj_equivalence_of_cats EC)
          (HED : adj_equivalence_of_cats ED)
          (F : C₁ ⟶ D₁)
          (G : C₂ ⟶ D₂)
          (τ : nat_z_iso (F ∙ ED) (EC ∙ G)).

  Let R : C₂ ⟶ C₁ := right_adjoint HEC.

  Let θ : nat_z_iso (R ∙ F ∙ ED) G
    := nat_z_iso_comp
         (pre_whisker_nat_z_iso R τ)
         (post_whisker_nat_z_iso (counit_nat_z_iso_from_adj_equivalence_of_cats HEC) G).

  Definition preserves_terminal_equivalence_f
             (HF : preserves_terminal F)
    : preserves_terminal G.
  Proof.
    use (preserves_terminal_nat_z_iso_f θ).
    use composition_preserves_terminal.
    - use composition_preserves_terminal.
      + exact (right_adjoint_preserves_terminal _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_terminal _ (adj_equivalence_of_cats_inv HED)).
  Defined.

  Definition preserves_binproduct_equivalence_f
             (HF : preserves_binproduct F)
    : preserves_binproduct G.
  Proof.
    use (preserves_binproduct_nat_z_iso_f θ).
    use composition_preserves_binproduct.
    - use composition_preserves_binproduct.
      + exact (right_adjoint_preserves_binproduct _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_binproduct _ (adj_equivalence_of_cats_inv HED)).
  Defined.

  Definition preserves_equalizer_equivalence_f
             (HF : preserves_equalizer F)
    : preserves_equalizer G.
  Proof.
    use (preserves_equalizer_nat_z_iso_f θ).
    use composition_preserves_equalizer.
    - use composition_preserves_equalizer.
      + exact (right_adjoint_preserves_equalizer _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_equalizer _ (adj_equivalence_of_cats_inv HED)).
  Defined.
End EquivalencePreservation.

Section EquivalencePreservation.
  Context {C₁ C₂ D₁ D₂ : category}
          (EC : C₁ ⟶ C₂)
          (ED : D₁ ⟶ D₂)
          (HEC : adj_equivalence_of_cats EC)
          (HED : adj_equivalence_of_cats ED)
          (F : C₁ ⟶ D₁)
          (G : C₂ ⟶ D₂)
          (τ : nat_z_iso (F ∙ ED) (EC ∙ G)).

  Let RC : C₂ ⟶ C₁ := right_adjoint HEC.
  Let RD : D₂ ⟶ D₁ := right_adjoint HED.

  Let θ : nat_z_iso (G ∙ RD) (RC ∙ F)
    := nat_z_iso_comp
         (post_whisker_nat_z_iso
            (nat_z_iso_inv
               (counit_nat_z_iso_from_adj_equivalence_of_cats HEC))
            (G ∙ RD))
         (nat_z_iso_comp
            (post_whisker_nat_z_iso
               (pre_whisker_nat_z_iso
                  RC
                  (nat_z_iso_inv τ))
               RD)
            (pre_whisker_nat_z_iso
               (RC ∙ F)
               (nat_z_iso_inv (unit_nat_z_iso_from_adj_equivalence_of_cats HED)))).

  Definition preserves_terminal_equivalence_b
             (HG : preserves_terminal G)
    : preserves_terminal F
    := preserves_terminal_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_binproduct_equivalence_b
             (HG : preserves_binproduct G)
    : preserves_binproduct F
    := preserves_binproduct_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_equalizer_equivalence_b
             (HG : preserves_equalizer G)
    : preserves_equalizer F
    := preserves_equalizer_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.
End EquivalencePreservation.
