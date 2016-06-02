(*

Direct implementation of arbitrary coproducts.

Written by: Anders Mörtberg 2016

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ArbitraryProductPrecategory.

(** * Definition of arbitrary coproducts of objects in a precategory *)
Section coproduct_def.

Variables (I : UU) (C : precategory).

Definition isArbitraryCoproductCocone (a : I -> C) (co : C)
  (ia : forall i, a i --> co) :=
  forall (c : C) (f : forall i, a i --> c),
    iscontr (total2 (fun (g : co --> c) => forall i, ia i ;; g = f i)).

Definition ArbitraryCoproductCocone (a : I -> C) :=
   Σ coia : (Σ co : C, forall i, a i --> co),
          isArbitraryCoproductCocone a (pr1 coia) (pr2 coia).

Definition ArbitraryCoproducts := ∀ (a : I -> C), ArbitraryCoproductCocone a.
Definition hasArbitraryCoproducts := ishinh ArbitraryCoproducts.

Definition ArbitraryCoproductObject {a : I -> C} (CC : ArbitraryCoproductCocone a) : C := pr1 (pr1 CC).
Definition ArbitraryCoproductIn {a : I -> C} (CC : ArbitraryCoproductCocone a): forall i, a i --> ArbitraryCoproductObject CC :=
  pr2 (pr1 CC).

Definition isArbitraryCoproductCocone_ArbitraryCoproductCocone {a : I -> C} (CC : ArbitraryCoproductCocone a) :
   isArbitraryCoproductCocone a (ArbitraryCoproductObject CC) (ArbitraryCoproductIn CC).
Proof.
  exact (pr2 CC).
Defined.

Definition ArbitraryCoproductArrow {a : I -> C} (CC : ArbitraryCoproductCocone a) {c : C} (f : forall i, a i --> c) :
      ArbitraryCoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isArbitraryCoproductCocone_ArbitraryCoproductCocone CC _ f))).
Defined.

Lemma ArbitraryCoproductInCommutes (a : I -> C) (CC : ArbitraryCoproductCocone a) :
     ∀ (c : C) (f : forall i, a i --> c) i, ArbitraryCoproductIn CC i ;; ArbitraryCoproductArrow CC f = f i.
Proof.
  intros c f i.
  exact (pr2 (pr1 (isArbitraryCoproductCocone_ArbitraryCoproductCocone CC _ f)) i).
Qed.

Lemma ArbitraryCoproductArrowUnique (a : I -> C) (CC : ArbitraryCoproductCocone a) (x : C)
    (f : forall i, a i --> x) (k : ArbitraryCoproductObject CC --> x)
    (Hk : forall i, ArbitraryCoproductIn CC i ;; k = f i) :
  k = ArbitraryCoproductArrow CC f.
Proof.
  set (H' := pr2 (isArbitraryCoproductCocone_ArbitraryCoproductCocone CC _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Lemma ArbitraryCoproductArrowEta (a : I -> C) (CC : ArbitraryCoproductCocone a) (x : C)
    (f : ArbitraryCoproductObject CC --> x) :
    f = ArbitraryCoproductArrow CC (fun i => ArbitraryCoproductIn CC i ;; f).
Proof.
  now apply ArbitraryCoproductArrowUnique.
Qed.


Definition ArbitraryCoproductOfArrows {a : I -> C} (CCab : ArbitraryCoproductCocone a) {c : I -> C}
    (CCcd : ArbitraryCoproductCocone c) (f : forall i, a i --> c i) :
          ArbitraryCoproductObject CCab --> ArbitraryCoproductObject CCcd :=
    ArbitraryCoproductArrow CCab (fun i => f i ;; ArbitraryCoproductIn CCcd i).

Lemma ArbitraryCoproductOfArrowsIn {a : I -> C} (CCab : ArbitraryCoproductCocone a) {c : I -> C}
    (CCcd : ArbitraryCoproductCocone c) (f : forall i, a i --> c i) :
    forall i, ArbitraryCoproductIn CCab i ;; ArbitraryCoproductOfArrows CCab CCcd f = f i ;; ArbitraryCoproductIn CCcd i.
Proof.
  unfold ArbitraryCoproductOfArrows; intro i.
  apply ArbitraryCoproductInCommutes.
Qed.

Definition mk_ArbitraryCoproductCocone (a : I -> C) (c : C) (f : forall i, a i --> c) :
   isArbitraryCoproductCocone _ _ f →  ArbitraryCoproductCocone a.
Proof.
intro H.
mkpair.
- apply (tpair _ c f).
- apply H.
Defined.

Definition mk_isArbitraryCoproductCocone (hsC : has_homsets C) (a : I -> C) (co : C)
  (f : forall i, a i --> co) : (∀ (c : C) (g : forall i, a i --> c),
                                  ∃! k : C ⟦co, c⟧, forall i, f i ;; k = g i)
   →    isArbitraryCoproductCocone a co f.
Proof.
  intros H c cc.
  apply H.
Defined.

Lemma precompWithArbitraryCoproductArrow {a : I -> C} (CCab : ArbitraryCoproductCocone a) {c : I -> C}
    (CCcd : ArbitraryCoproductCocone c) (f : forall i, a i --> c i)
    {x : C} (k : forall i, c i --> x) :
        ArbitraryCoproductOfArrows CCab CCcd f ;; ArbitraryCoproductArrow CCcd k =
         ArbitraryCoproductArrow CCab (fun i => f i ;; k i).
Proof.
apply ArbitraryCoproductArrowUnique; intro i.
now rewrite assoc, ArbitraryCoproductOfArrowsIn, <- assoc, ArbitraryCoproductInCommutes.
Qed.

Lemma postcompWithArbitraryCoproductArrow {a : I -> C} (CCab : ArbitraryCoproductCocone a) {c : C}
    (f : forall i, a i --> c) {x : C} (k : c --> x)  :
       ArbitraryCoproductArrow CCab f ;; k = ArbitraryCoproductArrow CCab (fun i => f i ;; k).
Proof.
apply ArbitraryCoproductArrowUnique; intro i.
now rewrite assoc, ArbitraryCoproductInCommutes.
Qed.

Lemma ArbitraryCoproduct_endo_is_identity (a : I -> C) (CC : ArbitraryCoproductCocone a)
  (k : ArbitraryCoproductObject CC --> ArbitraryCoproductObject CC)
  (H1 : forall i, ArbitraryCoproductIn CC i ;; k = ArbitraryCoproductIn CC i)
  : identity _ = k.
Proof.
apply pathsinv0.
eapply pathscomp0; [apply ArbitraryCoproductArrowEta|].
apply pathsinv0, ArbitraryCoproductArrowUnique; intro i; apply pathsinv0.
now rewrite id_right, H1.
Defined.

End coproduct_def.

Section Coproducts.

Variables (I : UU) (C : precategory) (CC : ArbitraryCoproducts I C).

(* Lemma ArbitraryCoproductArrow_eq (f f' : a --> c) (g g' : b --> c) *)
(*   : f = f' → g = g' → *)
(*       ArbitraryCoproductArrow _ (CC _ _) f g = ArbitraryCoproductArrow _ _ f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

Definition ArbitraryCoproductOfArrows_comp (a b c : I -> C)
  (f : forall i, a i --> b i) (g : forall i, b i --> c i) :
   ArbitraryCoproductOfArrows _ _ _ _ f ;; ArbitraryCoproductOfArrows _ _ (CC _) (CC _) g
   = ArbitraryCoproductOfArrows _ _ (CC _) (CC _)(fun i => f i ;; g i).
Proof.
apply ArbitraryCoproductArrowUnique; intro i.
rewrite assoc, ArbitraryCoproductOfArrowsIn.
now rewrite <- assoc, ArbitraryCoproductOfArrowsIn, assoc.
Qed.

Definition ArbitraryCoproductOfArrows_eq (a c : I -> C) (f f' : forall i, a i --> c i) : f = f' ->
  ArbitraryCoproductOfArrows _ _ _ _ f = ArbitraryCoproductOfArrows _ _ (CC _) (CC _) f'.
Proof.
now induction 1.
Qed.

End Coproducts.

Section functors.

Definition arbitrary_indexed_coproduct_functor_data (I : UU) {C : precategory}
  (PC : ArbitraryCoproducts I C) : functor_data (arbitrary_product_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (ArbitraryCoproductObject _ _ (PC p)).
- simpl; intros p q f.
  apply (ArbitraryCoproductOfArrows _ _ _ _ f).
Defined.

(* The arbitrary coproduct functor: C^I -> C *)
Definition arbitrary_indexed_coproduct_functor (I : UU) {C : precategory}
  (PC : ArbitraryCoproducts I C) : functor (arbitrary_product_precategory I C) C.
Proof.
apply (tpair _ (arbitrary_indexed_coproduct_functor_data _ PC)).
split.
  - intro x; simpl; apply pathsinv0, ArbitraryCoproduct_endo_is_identity.
    now intro i; rewrite ArbitraryCoproductOfArrowsIn, id_left.
  - now intros x y z f g; simpl; rewrite ArbitraryCoproductOfArrows_comp .
Defined.

End functors.

(* Defines the arbitrary copropuct of a family of functors *)
Definition arbitrary_coproduct_of_functors (I : UU) {C D : precategory}
  (HD : ArbitraryCoproducts I D) (F : I -> functor C D) : functor C D :=
  functor_composite (arbitrary_delta_functor I C)
     (functor_composite (arbitrary_pair_functor _ F)
                        (arbitrary_indexed_coproduct_functor _ HD)).
