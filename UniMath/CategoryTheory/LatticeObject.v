(** Internal lattice objects in a category *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Lattice.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.

Section LatticeObject_def.

Context {C : precategory} {BPC : BinProducts C}.

Local Notation "c '⊗' d" := (BinProductObject C (BPC c d)) (at level 75) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.

Definition binprod_delta (x : C) : C⟦x,x ⊗ x⟧ :=
  BinProductArrow _ _ (identity x) (identity x).
Let δ {x} : C⟦x,x ⊗ x⟧ := binprod_delta x.

Definition binprod_swap (x y : C) : C⟦x ⊗ y,y ⊗ x⟧ :=
  BinProductArrow _ _ (BinProductPr2 _ _) (BinProductPr1 _ _).
Let τ {x y} : C⟦x ⊗ y,y ⊗ x⟧ := binprod_swap x y.

Let π1 {x y} : C⟦x ⊗ y,x⟧ := BinProductPr1 _ (BPC x y).

Local Notation "1" := (identity _) : cat.


(** Equation witnessing that a morphism is associative as illustrated by diagram:
<<
               1×f
 L ⊗ (L ⊗ L) -------> L ⊗ L
     |                  |
   τ |                  |
     V                  |
 (L ⊗ L) ⊗ L            | f
     |                  |
 f×1 |                  |
     V                  V
   L ⊗ L ----------->   L
              f
>>
*)

Definition isassoc_cat {L} (f : C⟦L ⊗ L,L⟧) : UU := (1 ×× f) · f = τ · (f ×× 1) · f.


(** Equation witnessing that a morphism is commutative as illustrated by diagram:
<<
             1
   L ⊗ L -------> L ⊗ L
     |              |
   τ |              | f
     V              V
   L ⊗ L ---------> L
             f
>>
*)
Definition iscomm_cat {L} (f : C⟦L ⊗ L,L⟧) : UU := 1 · f = τ · f.


(** Equation witnessing the absorbtion law as illustrated by diagram:
<<
           δ×1                  τ
   L ⊗ L ------> (L ⊗ L) ⊗ L ------> L ⊗ (L ⊗ L)
     |                                   |
  π1 |                                   | 1×g
     V                                   V
     L <------------------------------ L ⊗ L
                       f
>>

If f is ∧ and g is ∨ this expresses: x ∧ (x ∨ y) = x

*)

Definition isabsorb_cat {L} (f g : C⟦L ⊗ L,L⟧) : UU :=
  (δ ×× 1) · τ · (1 ×× g) · f = π1.


Definition latticeop_cat {L} (meet_mor join_mor : C⟦L ⊗ L,L⟧) :=
    (isassoc_cat meet_mor × iscomm_cat meet_mor)
  × (isassoc_cat join_mor × iscomm_cat join_mor)
  × (isabsorb_cat meet_mor join_mor × isabsorb_cat join_mor meet_mor).

Definition latticeob (L : C) : UU :=
  ∑ (meet_mor join_mor : C⟦L ⊗ L,L⟧), latticeop_cat meet_mor join_mor.

Definition mklatticeob {L : C} {meet_mor join_mor : C⟦L ⊗ L,L⟧} :
  latticeop_cat meet_mor join_mor → latticeob L :=
    λ (isL : latticeop_cat meet_mor join_mor), meet_mor,, join_mor ,, isL.

Definition meet_mor {L : C} (isL : latticeob L) : C⟦L ⊗ L,L⟧ := pr1 isL.
Definition join_mor {L : C} (isL : latticeob L) : C⟦L ⊗ L,L⟧ := pr1 (pr2 isL).

End LatticeObject_def.

Arguments latticeob {_} _ _.

Section LatticeObject_theory.

Context {C : precategory} (BPC : BinProducts C) {L : C} (isL : latticeob BPC L).

Local Notation "c '⊗' d" := (BinProductObject C (BPC c d)) (at level 75) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.
Let δ {x} : C⟦x,x ⊗ x⟧ := binprod_delta x.
Let τ {x y} : C⟦x ⊗ y,y ⊗ x⟧ := binprod_swap x y.
Let π1 {x y} : C⟦x ⊗ y,x⟧ := BinProductPr1 _ (BPC x y).

Local Notation "1" := (identity _) : cat.

Definition isassoc_meet_mor : isassoc_cat (meet_mor isL) :=
  pr1 (pr1 (pr2 (pr2 isL))).
Definition iscomm_meet_mor : iscomm_cat (meet_mor isL) :=
  pr2 (pr1 (pr2 (pr2 isL))).
Definition isassoc_join_mor : isassoc_cat (join_mor isL) :=
  pr1 (pr1 (pr2 (pr2 (pr2 isL)))).
Definition iscomm_join_mor : iscomm_cat (join_mor isL) :=
  pr2 (pr1 (pr2 (pr2 (pr2 isL)))).
Definition meet_mor_absorb_join_mor : isabsorb_cat (meet_mor isL) (join_mor isL) :=
  pr1 (pr2 (pr2 (pr2 (pr2 isL)))).
Definition join_mor_absorb_meet_mor : isabsorb_cat (join_mor isL) (meet_mor isL) :=
  pr2 (pr2 (pr2 (pr2 (pr2 isL)))).

(** This corresponds to the equation: x ∧ x = x *)
Lemma meet_mor_id : δ · meet_mor isL = 1.
Proof.
generalize isassoc_meet_mor.
generalize iscomm_meet_mor.
generalize isassoc_join_mor.
generalize iscomm_join_mor.
generalize meet_mor_absorb_join_mor.
generalize join_mor_absorb_meet_mor.
unfold isassoc_cat, iscomm_cat, isabsorb_cat.
intros h1 h2 h3 h4 h5 h6.
assert (H : δ · π1 = identity L).
admit.
rewrite <- H.
Abort.

End LatticeObject_theory.

Section SublatticeObject.

Context {C : precategory} (BPC : BinProducts C) (M L : C) (i : Monic _ M L)
        (isL : latticeob BPC L).

Local Notation "c '⊗' d" := (BinProductObject C (BPC c d)) (at level 75) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.

(* Is this the correct way of expressing this or is too strong? *)
(* I think this asserts that i is a lattice morphism internally *)
Variables (meet_mor_M : C⟦M ⊗ M,M⟧) (Hmeet : meet_mor_M · i = (i ×× i) · meet_mor isL).

Definition sublatticeob : latticeob BPC M.
Proof.
use mklatticeob.
- apply meet_mor_M.
- admit.
- repeat split.
  + admit.
  + unfold iscomm_cat.
    set (Hcomm := iscomm_meet_mor _ isL).
    destruct i as [j Hj].
    simpl in *.
    unfold isMonic in *.
    rewrite id_left.
    apply Hj.
    rewrite <- !assoc.
    rewrite !Hmeet.
    unfold iscomm_cat in *.
    rewrite id_left in Hcomm.
    etrans.
    eapply maponpaths.
    apply Hcomm.
    rewrite !assoc.
    apply cancel_postcomposition.
    unfold binprod_swap.
    rewrite postcompWithBinProductArrow.
    apply BinProductArrowUnique.
    rewrite <- assoc.
    rewrite BinProductPr1Commutes.
    now rewrite BinProductOfArrowsPr2.
    rewrite <- assoc.
    rewrite BinProductPr2Commutes.
    now rewrite BinProductOfArrowsPr1.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

End SublatticeObject.