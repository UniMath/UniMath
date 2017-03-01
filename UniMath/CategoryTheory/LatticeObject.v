(** *****************************************************************************

Internal lattice objects in a category

Contents:

- Lattice objects ([latticeob])
- Proof that a subobject of a lattice object is a lattice object ([sublatticeob])

Written by: Anders Mörtberg, 2017

*********************************************************************************)

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

Let π1 {x y} : C⟦x ⊗ y,x⟧ := BinProductPr1 _ (BPC x y).
Let π2 {x y} : C⟦x ⊗ y,y⟧ := BinProductPr2 _ (BPC x y).

Definition binprod_assoc (x y z : C) : C⟦(x ⊗ y) ⊗ z,x ⊗ (y ⊗ z)⟧ :=
  BinProductArrow _ _ (π1 · π1) (BinProductArrow _ _ (π1 · π2) π2).
Let α {x y z} : C⟦(x ⊗ y) ⊗ z,x ⊗ (y ⊗ z)⟧ := binprod_assoc x y z.

Definition binprod_delta (x : C) : C⟦x,x ⊗ x⟧ :=
  BinProductArrow _ _ (identity x) (identity x).
Let δ {x} : C⟦x,x ⊗ x⟧ := binprod_delta x.

Definition binprod_swap (x y : C) : C⟦x ⊗ y,y ⊗ x⟧ :=
  BinProductArrow _ _ (BinProductPr2 _ _) (BinProductPr1 _ _).
Let τ {x y} : C⟦x ⊗ y,y ⊗ x⟧ := binprod_swap x y.


Local Notation "1" := (identity _) : cat.


(** Equation witnessing that a morphism representing a binary operation is
    associative as illustrated by diagram:
<<
               f×1
 (L ⊗ L) ⊗ L -------> L ⊗ L
     |                  |
   α |                  |
     V                  |
 L ⊗ (L ⊗ L)            | f
     |                  |
 1×f |                  |
     V                  V
   L ⊗ L ----------->   L
              f
>>
*)
Definition isassoc_cat {L} (f : C⟦L ⊗ L,L⟧) : UU := (f ×× 1) · f = α · (1 ×× f) · f.


(** Equation witnessing that a morphism representing a binary operation is
    commutative as illustrated by diagram:
<<
   L ⊗ L
     |   \
     |     \
   τ |       \ f
     |         \
     |          V
   L ⊗ L -----> L
           f
>>
*)
Definition iscomm_cat {L} (f : C⟦L ⊗ L,L⟧) : UU := f = τ · f.


(** Equation witnessing the absorbtion law as illustrated by diagram:
<<
           δ×1                   α
   L ⊗ L ------> (L ⊗ L) ⊗ L -------> L ⊗ (L ⊗ L)
     |                                    |
  π1 |                                    | 1×g
     V                                    V
     L <------------------------------- L ⊗ L
                       f
>>

If f is ∧ and g is ∨ this expresses: x ∧ (x ∨ y) = x

*)
Definition isabsorb_cat {L} (f g : C⟦L ⊗ L,L⟧) : UU :=
  (δ ×× 1) · α · (1 ×× g) · f = π1.

Definition latticeop_cat {L} (meet_mor join_mor : C⟦L ⊗ L,L⟧) :=
    (isassoc_cat meet_mor × iscomm_cat meet_mor)
  × (isassoc_cat join_mor × iscomm_cat join_mor)
  × (isabsorb_cat meet_mor join_mor × isabsorb_cat join_mor meet_mor).

(** A lattice object L has operation meet and join satisfying the above laws *)
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

End LatticeObject_theory.

Section SublatticeObject.

Context {C : precategory} (BPC : BinProducts C) (M L : C) (i : C⟦M,L⟧) (Hi : isMonic i)
        (isL : latticeob BPC L).

Local Notation "c '⊗' d" := (BinProductObject C (BPC c d)) (at level 75) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 90) : cat.

(* Is this the correct way of expressing this or is too strong? *)
(* I think this asserts that i is a lattice morphism internally *)
Variables (meet_mor_M : C⟦M ⊗ M,M⟧) (Hmeet : meet_mor_M · i = (i ×× i) · meet_mor isL).
Variables (join_mor_M : C⟦M ⊗ M,M⟧) (Hjoin : join_mor_M · i = (i ×× i) · join_mor isL).

Local Lemma identity_comm : identity M · i = i · identity L.
Proof.
now rewrite id_left, id_right.
Qed.

Local Lemma binprod_assoc_comm :
  ((i ×× i) ×× i) · @binprod_assoc _ BPC L L L =
  @binprod_assoc _ BPC M M M · (i ×× (i ×× i)).
Proof.
unfold binprod_assoc; rewrite postcompWithBinProductArrow.
apply BinProductArrowUnique.
- rewrite <-assoc, BinProductPr1Commutes.
  now rewrite assoc, BinProductOfArrowsPr1, <- assoc, BinProductOfArrowsPr1, assoc.
- rewrite postcompWithBinProductArrow.
  apply BinProductArrowUnique.
  + etrans; [ apply cancel_postcomposition; rewrite <-assoc;
              apply maponpaths, BinProductPr2Commutes |].
    rewrite <- assoc, BinProductPr1Commutes.
    now rewrite assoc, BinProductOfArrowsPr1, <- assoc, BinProductOfArrowsPr2, assoc.
  + etrans; [ apply cancel_postcomposition; rewrite <-assoc;
              apply maponpaths, BinProductPr2Commutes |].
    now rewrite <- assoc, BinProductPr2Commutes, BinProductOfArrowsPr2.
Qed.

Local Lemma binprod_delta_comm :
  i · @binprod_delta _ BPC L = @binprod_delta _ BPC M · (i ×× i).
Proof.
unfold binprod_delta; rewrite postcompWithBinProductArrow.
apply BinProductArrowUnique.
now rewrite <-assoc, BinProductPr1Commutes, identity_comm.
now rewrite <-assoc, BinProductPr2Commutes, identity_comm.
Qed.

Local Lemma isassoc_cat_comm {f : C⟦M ⊗ M,M⟧} {g : C⟦L ⊗ L,L⟧} (Hfg : f · i = (i ×× i) · g) :
  isassoc_cat g → isassoc_cat f.
Proof.
unfold isassoc_cat; intros H; apply Hi.
rewrite <-!assoc, !Hfg, !assoc, BinProductOfArrows_comp, Hfg, <- !assoc, identity_comm.
rewrite <- BinProductOfArrows_comp, <- assoc, H, !assoc.
apply cancel_postcomposition.
rewrite <-!assoc, BinProductOfArrows_comp, Hfg, identity_comm.
now rewrite <- BinProductOfArrows_comp, !assoc, binprod_assoc_comm.
Qed.

Local Lemma iscomm_cat_comm {f : C⟦M ⊗ M,M⟧} {g : C⟦L ⊗ L,L⟧} (Hfg : f · i = (i ×× i) · g) :
  iscomm_cat g → iscomm_cat f.
Proof.
unfold iscomm_cat; intros H; apply Hi.
rewrite <- !assoc, !Hfg.
etrans; [eapply maponpaths, H|].
rewrite !assoc; apply cancel_postcomposition.
unfold binprod_swap; rewrite postcompWithBinProductArrow.
apply BinProductArrowUnique; rewrite <- assoc.
* now rewrite BinProductPr1Commutes, BinProductOfArrowsPr2.
* now rewrite BinProductPr2Commutes, BinProductOfArrowsPr1.
Qed.

Local Lemma isabsorb_cat_comm {f1 f2 : C⟦M ⊗ M,M⟧} {g1 g2 : C⟦L ⊗ L,L⟧}
  (Hfg1 : f1 · i = (i ×× i) · g1) (Hfg2 : f2 · i = (i ×× i) · g2) :
  isabsorb_cat g1 g2  → isabsorb_cat f1 f2.
Proof.
unfold isabsorb_cat; intros H; apply Hi.
assert (HH : BinProductPr1 C (BPC M M) · i = (i ×× i) · BinProductPr1 C (BPC L L)).
{ now rewrite BinProductOfArrowsPr1. }
rewrite HH, <- H, <-!assoc, Hfg1, !assoc.
apply cancel_postcomposition.
rewrite <-!assoc, BinProductOfArrows_comp, Hfg2, identity_comm, !assoc.
rewrite BinProductOfArrows_comp, <-identity_comm, binprod_delta_comm.
etrans; [| eapply pathsinv0; do 2 apply cancel_postcomposition;
           now rewrite <-BinProductOfArrows_comp].
rewrite <-!assoc; apply maponpaths.
rewrite assoc, binprod_assoc_comm, <-assoc; apply maponpaths.
now rewrite identity_comm, BinProductOfArrows_comp.
Qed.

Definition sublatticeob : latticeob BPC M.
Proof.
use mklatticeob.
- apply meet_mor_M.
- apply join_mor_M.
- repeat split.
  + now apply (isassoc_cat_comm Hmeet), (isassoc_meet_mor _ isL).
  + now apply (iscomm_cat_comm Hmeet), (iscomm_meet_mor _ isL).
  + now apply (isassoc_cat_comm Hjoin), (isassoc_join_mor _ isL).
  + now apply (iscomm_cat_comm Hjoin), (iscomm_join_mor _ isL).
  + now apply (isabsorb_cat_comm Hmeet Hjoin), (meet_mor_absorb_join_mor _ isL).
  + now apply (isabsorb_cat_comm Hjoin Hmeet), (join_mor_absorb_meet_mor _ isL).
Qed.

End SublatticeObject.