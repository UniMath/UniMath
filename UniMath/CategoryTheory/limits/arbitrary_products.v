(* Direct implementation of products *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ArbitraryProductPrecategory.
(* Require Import UniMath.CategoryTheory.ProductPrecategory. *)

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section product_def.

Variable (I : UU) (C : precategory).

Definition isArbitraryProductCone (c : forall (i : I), C) (p : C)
  (pi : forall i, p --> c i) :=
  forall (a : forall i, C) (f : forall i, a i --> c i),
    iscontr (total2 (fun (faip : forall i, a i --> p) => forall i, faip i ;; pi i = f i)).

Definition ArbitraryProductCone (ci : forall i, C) :=
   total2 (fun pp1p2 : total2 (fun p : C => forall i, p --> ci i) =>
             isArbitraryProductCone ci (pr1 pp1p2) (pr2 pp1p2)).

Definition ArbitraryProducts := forall (ci : forall i, C), ArbitraryProductCone ci.
Definition hasArbitraryProducts := ishinh ArbitraryProducts.

Definition ArbitraryProductObject {c : forall i, C} (P : ArbitraryProductCone c) : C := pr1 (pr1 P).
Definition ArbitraryProductPr {c : forall i, C} (P : ArbitraryProductCone c) : forall i, ArbitraryProductObject P --> c i :=
  pr2 (pr1 P).
(* Definition ProductPr2 {c d : C} (P : ProductCone c d) : ProductObject P --> d := *)
(*    pr2 (pr2 (pr1 P)). *)

Definition isArbitraryProductCone_ArbitraryProductCone {c : forall i, C} (P : ArbitraryProductCone c) :
   isArbitraryProductCone c (ArbitraryProductObject P) (ArbitraryProductPr P).
Proof.
  exact (pr2 P).
Defined.

Definition ArbitraryProductArrow {c : forall i, C} (P : ArbitraryProductCone c) {a : forall i, C} (f : forall i, a i --> c i)
  : forall i, a i --> ArbitraryProductObject P.
Proof.
  exact (pr1 (pr1 (isArbitraryProductCone_ArbitraryProductCone P _ f))).
Defined.

Lemma ArbitraryProductPrCommutes (c : forall i, C) (P : ArbitraryProductCone c) :
     forall (a : forall i, C) (f : forall i, a i --> c i), forall i, ArbitraryProductArrow P f i ;; ArbitraryProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isArbitraryProductCone_ArbitraryProductCone P _ f)) i).
Qed.

(* Lemma ProductPr2Commutes (c d : C) (P : ProductCone c d): *)
(*      forall (a : C) (f : a --> c) g, ProductArrow P f g ;; ProductPr2 P = g. *)
(* Proof. *)
(*   intros a f g. *)
(*   exact (pr2 (pr2 (pr1 (isProductCone_ProductCone P _ f g)))). *)
(* Qed. *)

Lemma ArbitraryProductArrowUnique (c : forall i, C) (P : ArbitraryProductCone c) (x : forall i, C)
    (f : forall i, x i --> c i) (k : forall i, x i --> ArbitraryProductObject P)
    (Hk : forall i, k i ;; ArbitraryProductPr P i = f i) : k = ArbitraryProductArrow P f.
Proof.
  set (H' := pr2 (isArbitraryProductCone_ArbitraryProductCone P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition mk_ArbitraryProductCone (a : forall i, C) :
  ∀ (c : C) (f : forall i, C⟦c,a i⟧), isArbitraryProductCone _ _ f -> ArbitraryProductCone a.
Proof.
  intros c f X.
  simple refine (tpair _ (c,,f) X).
Defined.

(* Definition mk_isProductCone (hsC : has_homsets C) (a b p : C) *)
(*   (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) : *)
(*   (∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧), *)
(*     ∃! k : C⟦c,p⟧, k ;; pa = f × k ;; pb = g) -> *)
(*   isProductCone a b p pa pb. *)
(* Proof. *)
(*   intros H c cc g. *)
(*   apply H. *)
(* Defined. *)

(* Lemma ProductArrowEta (c d : C) (P : ProductCone c d) (x : C) *)
(*     (f : x --> ProductObject P) : *)
(*     f = ProductArrow P (f ;; ProductPr1 P) (f ;; ProductPr2 P). *)
(* Proof. *)
(*   apply ProductArrowUnique; *)
(*   apply idpath. *)
(* Qed. *)


Definition ArbitraryProductOfArrows {c : forall i, C} (Pcd : ArbitraryProductCone c) {a : forall i, C}
    (Pab : ArbitraryProductCone a) (f : forall i, a i --> c i) :
      forall (i : I), ArbitraryProductObject Pab --> ArbitraryProductObject Pcd :=
    ArbitraryProductArrow Pcd (fun i => ArbitraryProductPr Pab i ;; f i).

Lemma ArbitraryProductOfArrowsPr {c : forall i, C} (Pcd : ArbitraryProductCone c) {a : forall i, C}
    (Pab : ArbitraryProductCone a) (f : forall i, a i --> c i) :
    forall i, ArbitraryProductOfArrows Pcd Pab f i ;; ArbitraryProductPr Pcd i = ArbitraryProductPr Pab i ;; f i.
Proof.
  unfold ArbitraryProductOfArrows; intro i.
  now rewrite (ArbitraryProductPrCommutes _ _ _ _ i).
Qed.

(* Lemma postcompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a b : C} *)
(*     (Pab : ProductCone a b) (f : a --> c) (g : b --> d) *)
(*     {x : C} (k : x --> a) (h : x --> b) : *)
(*         ProductArrow Pab k h ;; ProductOfArrows Pcd Pab f g = *)
(*          ProductArrow Pcd (k ;; f) (h ;; g). *)
(* Proof. *)
(*   apply ProductArrowUnique. *)
(*   - rewrite <- assoc, ProductOfArrowsPr1. *)
(*     rewrite assoc, ProductPr1Commutes. *)
(*     apply idpath. *)
(*   - rewrite <- assoc, ProductOfArrowsPr2. *)
(*     rewrite assoc, ProductPr2Commutes. *)
(*     apply idpath. *)
(* Qed. *)

(* Lemma precompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a : C} *)
(*     (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  : *)
(*        k ;; ProductArrow Pcd f g  = ProductArrow Pcd (k ;; f) (k ;; g). *)
(* Proof. *)
(*   apply ProductArrowUnique. *)
(*   -  rewrite <- assoc, ProductPr1Commutes; *)
(*      apply idpath. *)
(*   -  rewrite <- assoc, ProductPr2Commutes; *)
(*      apply idpath. *)
(* Qed. *)

End product_def.

(* Section Products. *)

(* Variable C : precategory. *)
(* Variable CC : Products C. *)
(* Variables a b c d x y : C. *)

(* Definition ProductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y) *)
(*   : ProductOfArrows _ (CC c d) (CC a b) f f' ;; *)
(*     ProductOfArrows _ (CC _ _) (CC _ _) g g' *)
(*     = *)
(*     ProductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g'). *)
(* Proof. *)
(*   apply ProductArrowUnique. *)
(*   - rewrite <- assoc. *)
(*     rewrite ProductOfArrowsPr1. *)
(*     rewrite assoc. *)
(*     rewrite ProductOfArrowsPr1. *)
(*     apply pathsinv0. *)
(*     apply assoc. *)
(*   - rewrite <- assoc. *)
(*     rewrite ProductOfArrowsPr2. *)
(*     rewrite assoc. *)
(*     rewrite ProductOfArrowsPr2. *)
(*     apply pathsinv0. *)
(*     apply assoc. *)
(* Qed. *)

(* Definition ProductOfArrows_eq (f f' : a --> c) (g g' : b --> d) *)
(*   : f = f' → g = g' → *)
(*       ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

(* End Products. *)

(* Section Product_unique. *)

(* Variable C : precategory. *)
(* Variable CC : Products C. *)
(* Variables a b : C. *)

(* Lemma Product_endo_is_identity (P : ProductCone _ a b) *)
(*   (k : ProductObject _ P --> ProductObject _ P) *)
(*   (H1 : k ;; ProductPr1 _ P = ProductPr1 _ P) *)
(*   (H2 : k ;; ProductPr2 _ P = ProductPr2 _ P) *)
(*   : identity _ = k. *)
(* Proof. *)
(*   apply pathsinv0. *)
(*   eapply pathscomp0. *)
(*   apply ProductArrowEta. *)
(*   apply pathsinv0. *)
(*   apply ProductArrowUnique; apply pathsinv0. *)
(*   + rewrite id_left. exact H1. *)
(*   + rewrite id_left. exact H2. *)
(* Qed. *)

(* End Product_unique. *)

(* The arbitrary product functor: C^I -> C *)
Section abitrary_product_functor.

Context (I : UU) {C : precategory} (PC : ArbitraryProducts I C).

Definition arbitrary_product_functor_data (i : I) :
  functor_data (arbitrary_product_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (ArbitraryProductObject _ _ (PC p)).
- simpl; intros p q f.
  simple refine (ArbitraryProductOfArrows _ _ _ _ _ _).
  apply f.
  apply i.
  (* apply (ArbitraryProductOfArrows _ (PC (pr1 q) (pr2 q)) *)
  (*                          (PC (pr1 p) (pr2 p)) (pr1 f) (pr2 f)). *)
Defined.

Definition arbitrary_product_functor (i : I) : functor (arbitrary_product_precategory I C) C.
Proof.
apply (tpair _ (arbitrary_product_functor_data i)).
split.
intro x; simpl.
  [ intro x; simpl; apply pathsinv0, Product_endo_is_identity;
    [ now rewrite ProductOfArrowsPr1, id_right
    | now rewrite ProductOfArrowsPr2, id_right ]
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End binproduct_functor.

(* Defines the product of two functors by:
    x -> (x,x) -> (F x,G x) -> F x * G x

  For a direct definition see FunctorsPointwiseProduct.v

*)
Definition product_of_functors {C D : precategory} (HD : Products D)
  (F G : functor C D) : functor C D :=
  functor_composite (delta_functor C)
     (functor_composite (pair_functor F G) (binproduct_functor HD)).
