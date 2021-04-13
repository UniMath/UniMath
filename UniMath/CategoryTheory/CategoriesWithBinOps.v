(** ** Precategories such that spaces of morphisms have a binary operation *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

Section def_precategory_with_binops.

  (** Definition of precategories such that homs are binops. *)
  Definition precategoryWithBinOpsData (C : precategory) : UU := ∏ (x y : C), binop (C⟦x, y⟧).

  Definition precategoryWithBinOps : UU := ∑ C : precategory, precategoryWithBinOpsData C.

  Definition precategoryWithBinOps_precategory (P : precategoryWithBinOps) : precategory := pr1 P.
  Coercion precategoryWithBinOps_precategory : precategoryWithBinOps >-> precategory.

  Definition make_precategoryWithBinOps (C : precategory) (H : precategoryWithBinOpsData C) :
    precategoryWithBinOps := tpair _ C H.

  (** Gives the binop of the homs from x to y. *)
  Definition to_binop {BC : precategoryWithBinOps} (x y : BC) : binop (BC⟦x, y⟧) := (pr2 BC) x y.

End def_precategory_with_binops.

Definition oppositePrecategoryWithBinOps (M : precategoryWithBinOps) : precategoryWithBinOps
  := make_precategoryWithBinOps
       (opp_precat M)
       (λ A B f g, @to_binop M (rm_opp_ob B) (rm_opp_ob A) (rm_opp_mor f) (rm_opp_mor g)).

Definition induced_precategoryWithBinOps (M : precategoryWithBinOps) {X:Type} (j : X -> ob M)
  : precategoryWithBinOps.
Proof.
  exists (induced_precategory M j). intros a b. exact (@to_binop M (j a) (j b)).
Defined.
