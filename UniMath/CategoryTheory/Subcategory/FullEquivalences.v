Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Local Open Scope cat.

(**
 Equivalences between full subcategories
 *)
Section EquivalenceFullSub.
  Context {C₁ C₂ : category}
          {P : hsubtype C₁}
          {Q : hsubtype C₂}
          (L : C₁ ⟶ C₂)
          (L_equiv : adj_equivalence_of_cats L)
          (HL : ∏ (x : C₁), P x → Q (L x))
          (HR : ∏ (x : C₂), Q x → P (right_adjoint L_equiv x)).

  Let L' : full_sub_category C₁ P ⟶ full_sub_category C₂ Q
    := full_sub_category_functor P Q L HL.
  Let R' : full_sub_category C₂ Q ⟶ full_sub_category C₁ P
    := full_sub_category_functor Q P _ HR.

  Definition full_sub_category_equivalence_unit_data
    : nat_trans_data
        (functor_identity (full_sub_category C₁ P))
        (L' ∙ R')
    := λ y, unit_from_left_adjoint L_equiv (pr1 y) ,, tt.

  Definition full_sub_category_equivalence_unit_is_nat_trans
    : is_nat_trans
        _ _
        full_sub_category_equivalence_unit_data.
  Proof.
    intros y₁ y₂ f ; cbn.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    cbn.
    apply (nat_trans_ax (unit_from_left_adjoint L_equiv)).
  Qed.

  Definition full_sub_category_equivalence_unit
    : functor_identity _ ⟹ L' ∙ R'.
  Proof.
    use make_nat_trans.
    - exact full_sub_category_equivalence_unit_data.
    - exact full_sub_category_equivalence_unit_is_nat_trans.
  Defined.

  Definition full_sub_category_equivalence_counit_data
    : nat_trans_data
        (R' ∙ L')
        (functor_identity _)
    := λ y, counit_from_left_adjoint L_equiv (pr1 y) ,, tt.

  Definition full_sub_category_equivalence_counit_is_nat_trans
    : is_nat_trans
        _ _
        full_sub_category_equivalence_counit_data.
  Proof.
    intros y₁ y₂ f ; cbn.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    cbn.
    apply (nat_trans_ax (counit_from_left_adjoint L_equiv)).
  Qed.

  Definition full_sub_category_equivalence_counit
    : R' ∙ L' ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact full_sub_category_equivalence_counit_data.
    - exact full_sub_category_equivalence_counit_is_nat_trans.
  Defined.

  Definition full_sub_category_equivalence
    : equivalence_of_cats
        (full_sub_category C₁ P)
        (full_sub_category C₂ Q).
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact L'.
      + exact R'.
      + exact full_sub_category_equivalence_unit.
      + exact full_sub_category_equivalence_counit.
    - split.
      + intro.
        apply is_iso_full_sub.
        apply unit_nat_z_iso_from_adj_equivalence_of_cats.
      + intro.
        apply is_iso_full_sub.
        apply counit_nat_z_iso_from_adj_equivalence_of_cats.
  Defined.

  Definition full_sub_category_adj_equivalence
    : adj_equivalence_of_cats (full_sub_category_functor P Q L HL)
    := adjointificiation
         full_sub_category_equivalence.
End EquivalenceFullSub.
