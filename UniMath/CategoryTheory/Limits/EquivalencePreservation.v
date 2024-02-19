(*******************************************************************************************

 Equivalences and (co)limits

 Whenever we have two categories and equivalence between them, then they inherit limits and
 colimits from each other. We show this for several classes of limits and colimits.

 Contents
 1. Equivalences and limits (backward preservation)
 2. Equivalences and colimits (forward preservation)
 3. Equivalences and limits (forward preservation)
 4. Equivalences and colimits (backward preservation)

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
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.LimitIso.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Local Open Scope cat.

Section Equivalence.
  Context {C₁ C₂ : category}
          {L : C₁ ⟶ C₂}
          (HL : adj_equivalence_of_cats L).

  Let R : C₂ ⟶ C₁ := right_adjoint HL.
  Let ε : nat_z_iso (R ∙ L) (functor_identity C₂)
    := counit_nat_z_iso_from_adj_equivalence_of_cats HL.
  Let η : nat_z_iso (functor_identity C₁) (L ∙ R)
    := unit_nat_z_iso_from_adj_equivalence_of_cats HL.

  (** * 1. Equivalences and limits (backward preservation) *)
  Definition adj_equiv_preserves_terminal_b
             (T : Terminal C₂)
    : Terminal C₁
    := make_Terminal
         _
         (right_adjoint_preserves_terminal _ HL _ (pr2 T)).

  Definition adj_equiv_preserves_binproducts_b
             (P : BinProducts C₂)
    : BinProducts C₁.
  Proof.
    intros x y.
    pose (H := pr2 (P (L x) (L y))).
    pose (prod := make_BinProduct
                    _ _ _ _ _ _
                    (right_adjoint_preserves_binproduct _ HL _ _ _ _ _ H)).
    use (BinProduct_z_iso_lr prod).
    - apply (nat_z_iso_pointwise_z_iso η).
    - apply (nat_z_iso_pointwise_z_iso η).
  Defined.

  Definition adj_equiv_preserves_equalizers_b
             (E : Equalizers C₂)
    : Equalizers C₁.
  Proof.
    intros x y f g.
    use (Equalizer_z_iso_lr
           (make_Equalizer
              _ _ _ _
              (right_adjoint_preserves_equalizer
                 _ HL
                 _ _ _ _ _ _ _ _
                 (isEqualizer_Equalizer (E (L x) (L y) (#L f) (#L g)))))).
    - rewrite <- !functor_comp.
      apply maponpaths.
      apply EqualizerEqAr.
    - apply (nat_z_iso_pointwise_z_iso η).
    - apply (nat_z_iso_pointwise_z_iso η).
    - abstract
        (exact (!(nat_trans_ax η _ _ f))).
    - abstract
        (exact (!(nat_trans_ax η _ _ g))).
  Defined.

  (** * 2. Equivalences and colimits (forward preservation) *)
  Definition adj_equiv_preserves_initial_f
             (I : Initial C₁)
    : Initial C₂
    := make_Initial
         _
         (left_adjoint_preserves_initial _ HL _ (pr2 I)).

  Definition adj_equiv_preserves_bincoproducts_f
             (P : BinCoproducts C₁)
    : BinCoproducts C₂.
  Proof.
    intros x y.
    pose (H := pr2 (P (R x) (R y))).
    pose (prod := make_BinCoproduct
                    _ _ _ _ _ _
                    (left_adjoint_preserves_bincoproduct _ HL _ _ _ _ _ H)).
    use (BinCoproduct_z_iso_lr prod).
    - apply (nat_z_iso_pointwise_z_iso ε).
    - apply (nat_z_iso_pointwise_z_iso ε).
  Defined.
End Equivalence.

Section Equivalence.
  Context {C₁ C₂ : category}
          {L : C₂ ⟶ C₁}
          (HL : adj_equivalence_of_cats L).

  (** * 3. Equivalences and limits (forward preservation) *)
  Definition adj_equiv_preserves_terminal_f
             (T : Terminal C₂)
    : Terminal C₁
    := adj_equiv_preserves_terminal_b
         (adj_equivalence_of_cats_inv HL)
         T.

  Definition adj_equiv_preserves_binproducts_f
             (P : BinProducts C₂)
    : BinProducts C₁
    := adj_equiv_preserves_binproducts_b
         (adj_equivalence_of_cats_inv HL)
         P.

  Definition adj_equiv_preserves_equalizers_f
             (E : Equalizers C₂)
    : Equalizers C₁
    := adj_equiv_preserves_equalizers_b
         (adj_equivalence_of_cats_inv HL)
         E.

  (** * 4. Equivalences and colimits (backward preservation) *)
  Definition adj_equiv_preserves_initial_b
             (I : Initial C₁)
    : Initial C₂
    := adj_equiv_preserves_initial_f
         (adj_equivalence_of_cats_inv HL)
         I.

  Definition adj_equiv_preserves_bincoproducts_b
             (P : BinCoproducts C₁)
    : BinCoproducts C₂
    := adj_equiv_preserves_bincoproducts_f
         (adj_equivalence_of_cats_inv HL)
         P.
End Equivalence.
