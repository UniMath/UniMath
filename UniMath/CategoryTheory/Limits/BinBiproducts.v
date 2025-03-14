Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Zero.

Local Open Scope cat.

Section BinBiproducts.

  Context {C : category}.
  Context {A B : C}.

  Definition bin_biproduct_data
    : UU
    := ∑ (P : C),
      (P --> A) ×
      (P --> B) ×
      (A --> P) ×
      (B --> P).

  Coercion bin_biproduct_object
    (P : bin_biproduct_data)
    : C
    := pr1 P.

  Definition make_bin_biproduct_data
    (P : C)
    (pr1 : P --> A)
    (pr2 : P --> B)
    (i1 : A --> P)
    (i2 : B --> P)
    : bin_biproduct_data
    := P ,, pr1 ,, pr2 ,, i1 ,, i2.

  Section Accessors.

    Context (P : bin_biproduct_data).

    Definition bin_biproduct_pr1
      : (pr1 P) --> A
      := pr12 P.

    Definition bin_biproduct_pr2
      : (pr1 P) --> B
      := pr122 P.

    Definition bin_biproduct_i1
      : A --> (pr1 P)
      := pr1 (pr222 P).

    Definition bin_biproduct_i2
      : B --> (pr1 P)
      := pr2 (pr222 P).

  End Accessors.

  Context {Z : Zero C}.

  Section Axioms.
    Context (P : bin_biproduct_data).

    Definition bin_biproduct_i1_pr1_ax
      : UU
      := bin_biproduct_i1 P · bin_biproduct_pr1 P = identity A.

    Definition bin_biproduct_i1_pr2_ax
      : UU
      := bin_biproduct_i1 P · bin_biproduct_pr2 P = ZeroArrow Z A B.

    Definition bin_biproduct_i2_pr2_ax
      : UU
      := bin_biproduct_i2 P · bin_biproduct_pr2 P = identity B.

    Definition bin_biproduct_i2_pr1_ax
      : UU
      := bin_biproduct_i2 P · bin_biproduct_pr1 P = ZeroArrow Z B A.

  End Axioms.

  Definition is_bin_biproduct
    (P : bin_biproduct_data)
    : UU
    := (isBinProduct _ _ _ P (bin_biproduct_pr1 P) (bin_biproduct_pr2 P)) ×
      (isBinCoproduct _ _ _ P (bin_biproduct_i1 P) (bin_biproduct_i2 P)) ×
      (bin_biproduct_i1_pr1_ax P) ×
      (bin_biproduct_i1_pr2_ax P) ×
      (bin_biproduct_i2_pr1_ax P) ×
      (bin_biproduct_i2_pr2_ax P).

  Definition make_is_bin_biproduct
  (P : bin_biproduct_data)
  (H1 : isBinProduct _ _ _ P (bin_biproduct_pr1 P) (bin_biproduct_pr2 P))
  (H2 : isBinCoproduct _ _ _ P (bin_biproduct_i1 P) (bin_biproduct_i2 P))
  (H3 : bin_biproduct_i1_pr1_ax P)
  (H4 : bin_biproduct_i1_pr2_ax P)
  (H5 : bin_biproduct_i2_pr1_ax P)
  (H6 : bin_biproduct_i2_pr2_ax P)
  : is_bin_biproduct P 
  := H1 ,, H2 ,, H3 ,, H4 ,, H5 ,, H6.

  Definition bin_biproduct
    : UU
    := ∑ P, is_bin_biproduct P.

  Coercion bin_biproduct_to_data
    (P : bin_biproduct)
    : bin_biproduct_data
    := pr1 P.

  Coercion bin_biproduct_to_bin_product
    (P : bin_biproduct)
    : BinProduct C A B
    := make_BinProduct _ _ _ P (bin_biproduct_pr1 P) (bin_biproduct_pr2 P) (pr12 P).

  Coercion bin_biproduct_to_bin_coproduct
    (P : bin_biproduct)
    : BinCoproduct A B
    := make_BinCoproduct _ _ _ P (bin_biproduct_i1 P) (bin_biproduct_i2 P) (pr122 P).

  Definition make_bin_biproduct
    (P : bin_biproduct_data)
    (H0 : is_bin_biproduct P)
    : bin_biproduct
    := P ,, H0.

  Definition bin_biproduct_i1_pr1
    (P : bin_biproduct)
    : bin_biproduct_i1_pr1_ax P
    := pr1 (pr222 P).

  Definition bin_biproduct_i1_pr2
  (P : bin_biproduct)
  : bin_biproduct_i1_pr2_ax P
  := pr12 (pr222 P).

  Definition bin_biproduct_i2_pr1
  (P : bin_biproduct)
  : bin_biproduct_i2_pr1_ax P
  := pr122 (pr222 P).

  Definition bin_biproduct_i2_pr2
  (P : bin_biproduct)
  : bin_biproduct_i2_pr2_ax P
  := pr222 (pr222 P).


End BinBiproducts.

Arguments bin_biproduct_data {C} (A B).

Arguments bin_biproduct_i2_pr1_ax {C} (A B) (Z).
Arguments bin_biproduct_i1_pr2_ax {C} (A B) (Z).

Arguments bin_biproduct {C} (A B) (Z).
