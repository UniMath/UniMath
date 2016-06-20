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
Require Import UniMath.CategoryTheory.ProductPrecategory.

(** * Definition of arbitrary coproducts of objects in a precategory *)
Section coproduct_def.

Variables (I : UU) (C : precategory).

Definition isCoproductCocone (a : I -> C) (co : C)
  (ia : forall i, a i --> co) :=
  forall (c : C) (f : forall i, a i --> c),
    iscontr (total2 (fun (g : co --> c) => forall i, ia i ;; g = f i)).

Definition CoproductCocone (a : I -> C) :=
   Σ coia : (Σ co : C, forall i, a i --> co),
          isCoproductCocone a (pr1 coia) (pr2 coia).

Definition Coproducts := ∀ (a : I -> C), CoproductCocone a.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a : I -> C} (CC : CoproductCocone a) : C := pr1 (pr1 CC).
Definition CoproductIn {a : I -> C} (CC : CoproductCocone a): forall i, a i --> CoproductObject CC :=
  pr2 (pr1 CC).

Definition isCoproductCocone_CoproductCocone {a : I -> C} (CC : CoproductCocone a) :
   isCoproductCocone a (CoproductObject CC) (CoproductIn CC).
Proof.
  exact (pr2 CC).
Defined.

Definition CoproductArrow {a : I -> C} (CC : CoproductCocone a) {c : C} (f : forall i, a i --> c) :
      CoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isCoproductCocone_CoproductCocone CC _ f))).
Defined.

Lemma CoproductInCommutes (a : I -> C) (CC : CoproductCocone a) :
     ∀ (c : C) (f : forall i, a i --> c) i, CoproductIn CC i ;; CoproductArrow CC f = f i.
Proof.
  intros c f i.
  exact (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f)) i).
Qed.

Lemma CoproductArrowUnique (a : I -> C) (CC : CoproductCocone a) (x : C)
    (f : forall i, a i --> x) (k : CoproductObject CC --> x)
    (Hk : forall i, CoproductIn CC i ;; k = f i) :
  k = CoproductArrow CC f.
Proof.
  set (H' := pr2 (isCoproductCocone_CoproductCocone CC _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Lemma CoproductArrowEta (a : I -> C) (CC : CoproductCocone a) (x : C)
    (f : CoproductObject CC --> x) :
    f = CoproductArrow CC (fun i => CoproductIn CC i ;; f).
Proof.
  now apply CoproductArrowUnique.
Qed.


Definition CoproductOfArrows {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : forall i, a i --> c i) :
          CoproductObject CCab --> CoproductObject CCcd :=
    CoproductArrow CCab (fun i => f i ;; CoproductIn CCcd i).

Lemma CoproductOfArrowsIn {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : forall i, a i --> c i) :
    forall i, CoproductIn CCab i ;; CoproductOfArrows CCab CCcd f = f i ;; CoproductIn CCcd i.
Proof.
  unfold CoproductOfArrows; intro i.
  apply CoproductInCommutes.
Qed.

Definition mk_CoproductCocone (a : I -> C) (c : C) (f : forall i, a i --> c) :
   isCoproductCocone _ _ f →  CoproductCocone a.
Proof.
intro H.
mkpair.
- apply (tpair _ c f).
- apply H.
Defined.

Definition mk_isCoproductCocone (hsC : has_homsets C) (a : I -> C) (co : C)
  (f : forall i, a i --> co) : (∀ (c : C) (g : forall i, a i --> c),
                                  ∃! k : C ⟦co, c⟧, forall i, f i ;; k = g i)
   →    isCoproductCocone a co f.
Proof.
  intros H c cc.
  apply H.
Defined.

Lemma precompWithCoproductArrow {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : forall i, a i --> c i)
    {x : C} (k : forall i, c i --> x) :
        CoproductOfArrows CCab CCcd f ;; CoproductArrow CCcd k =
         CoproductArrow CCab (fun i => f i ;; k i).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductOfArrowsIn, <- assoc, CoproductInCommutes.
Qed.

Lemma postcompWithCoproductArrow {a : I -> C} (CCab : CoproductCocone a) {c : C}
    (f : forall i, a i --> c) {x : C} (k : c --> x)  :
       CoproductArrow CCab f ;; k = CoproductArrow CCab (fun i => f i ;; k).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductInCommutes.
Qed.

Lemma Coproduct_endo_is_identity (a : I -> C) (CC : CoproductCocone a)
  (k : CoproductObject CC --> CoproductObject CC)
  (H1 : forall i, CoproductIn CC i ;; k = CoproductIn CC i)
  : identity _ = k.
Proof.
apply pathsinv0.
eapply pathscomp0; [apply CoproductArrowEta|].
apply pathsinv0, CoproductArrowUnique; intro i; apply pathsinv0.
now rewrite id_right, H1.
Defined.

End coproduct_def.

Section Coproducts.

Variables (I : UU) (C : precategory) (CC : Coproducts I C).

(* Lemma CoproductArrow_eq (f f' : a --> c) (g g' : b --> c) *)
(*   : f = f' → g = g' → *)
(*       CoproductArrow _ (CC _ _) f g = CoproductArrow _ _ f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

Definition CoproductOfArrows_comp (a b c : I -> C)
  (f : forall i, a i --> b i) (g : forall i, b i --> c i) :
   CoproductOfArrows _ _ _ _ f ;; CoproductOfArrows _ _ (CC _) (CC _) g
   = CoproductOfArrows _ _ (CC _) (CC _)(fun i => f i ;; g i).
Proof.
apply CoproductArrowUnique; intro i.
rewrite assoc, CoproductOfArrowsIn.
now rewrite <- assoc, CoproductOfArrowsIn, assoc.
Qed.

Definition CoproductOfArrows_eq (a c : I -> C) (f f' : forall i, a i --> c i) : f = f' ->
  CoproductOfArrows _ _ _ _ f = CoproductOfArrows _ _ (CC _) (CC _) f'.
Proof.
now induction 1.
Qed.

End Coproducts.

Section functors.

Definition indexed_coproduct_functor_data (I : UU) {C : precategory}
  (PC : Coproducts I C) : functor_data (product_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (CoproductObject _ _ (PC p)).
- simpl; intros p q f.
  apply (CoproductOfArrows _ _ _ _ f).
Defined.

(* The arbitrary coproduct functor: C^I -> C *)
Definition indexed_coproduct_functor (I : UU) {C : precategory}
  (PC : Coproducts I C) : functor (product_precategory I C) C.
Proof.
apply (tpair _ (indexed_coproduct_functor_data _ PC)).
split.
  - intro x; simpl; apply pathsinv0, Coproduct_endo_is_identity.
    now intro i; rewrite CoproductOfArrowsIn, id_left.
  - now intros x y z f g; simpl; rewrite CoproductOfArrows_comp .
Defined.

End functors.

(* Defines the arbitrary copropuct of a family of functors *)
Definition coproduct_of_functors_alt (I : UU) {C D : precategory}
  (HD : Coproducts I D) (F : I -> functor C D) : functor C D :=
  functor_composite (delta_functor I C)
     (functor_composite (pair_functor _ F)
                        (indexed_coproduct_functor _ HD)).
