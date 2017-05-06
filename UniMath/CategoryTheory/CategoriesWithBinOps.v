(** ** Precategories such that spaces of morphisms have a binary operation *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.


Section def_precategory_with_binops.

  (** Definition of precategories such that homs are binops. *)
  Definition precategoryWithBinOpsData (C : precategory) : UU := ∏ (x y : C), binop (C⟦x, y⟧).

  Definition precategoryWithBinOps : UU := ∑ C : precategory, precategoryWithBinOpsData C.

  Definition precategoryWithBinOps_precategory (P : precategoryWithBinOps) : precategory := pr1 P.
  Coercion precategoryWithBinOps_precategory : precategoryWithBinOps >-> precategory.

  Definition mk_precategoryWithBinOps (C : precategory) (H : precategoryWithBinOpsData C) :
    precategoryWithBinOps := tpair _ C H.

  (** Gives the binop of the homs from x to y. *)
  Definition to_binop {BC : precategoryWithBinOps} (x y : BC) : binop (BC⟦x, y⟧) := (pr2 BC) x y.

  Lemma to_binop_eq {BC : precategoryWithBinOps} {x y : BC} {f1 f2 g1 g2 : x --> y}
        (e1 : f1 = f2) (e2 : g1 = g2) : to_binop _ _ f1 g1 = to_binop _ _ f2 g2.
  Proof.
    induction e1, e2. apply idpath.
  Qed.

End def_precategory_with_binops.
