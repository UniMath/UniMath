Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.aux_lemmas_HoTT.
Require Import RezkCompletion.limits.terminal.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section product_def.

Variable C : precategory.

Definition isProductCone (c d p: C) (p1 : p --> c) (p2 : p --> d) := 
  forall (a : C) (f : a --> c) (g : a --> d),
    iscontr (total2 (fun fg : a --> p => dirprod (fg ;; p1 == f) 
                                                 (fg ;; p2 == g))).

Definition ProductCone (c d : C) := 
   total2 (fun pp1p2 : total2 (fun p : C => dirprod (p --> c) (p --> d)) =>
             isProductCone c d (pr1 pp1p2) (pr1 (pr2 pp1p2)) (pr2 (pr2 pp1p2))).


Definition Products := forall (c d : C), ProductCone c d.
Definition hasProducts := ishinh Products.

Definition ProductObject {c d : C} (P : ProductCone c d) : C := pr1 (pr1 P).
Definition ProductPr1 {c d : C} (P : ProductCone c d): ProductObject P --> c :=
  pr1 (pr2 (pr1 P)).
Definition ProductPr2 {c d : C} (P : ProductCone c d) : ProductObject P --> d :=
   pr2 (pr2 (pr1 P)).

Definition isProductCone_ProductCone {c d : C} (P : ProductCone c d) : 
   isProductCone c d (ProductObject P) (ProductPr1 P) (ProductPr2 P).
Proof.
  exact (pr2 P).
Defined.

Definition ProductArrow {c d : C} (P : ProductCone c d) {a : C} (f : a --> c) (g : a --> d) : 
       a --> ProductObject P.
Proof.
  exact (pr1 (pr1 (isProductCone_ProductCone P _ f g))).
Defined.

Lemma ProductPr1Commutes (c d : C) (P : ProductCone c d):
     forall (a : C) (f : a --> c) g, ProductArrow P f g ;; ProductPr1 P == f.
Proof.
  intros a f g.
  exact (pr1 (pr2 (pr1 (isProductCone_ProductCone P _ f g)))).
Qed.

Lemma ProductPr2Commutes (c d : C) (P : ProductCone c d):
     forall (a : C) (f : a --> c) g, ProductArrow P f g ;; ProductPr2 P == g.
Proof.
  intros a f g.
  exact (pr2 (pr2 (pr1 (isProductCone_ProductCone P _ f g)))).
Qed.

Lemma ProductArrowUnique (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> ProductObject P) :
    k ;; ProductPr1 P == f -> k ;; ProductPr2 P == g ->
      k == ProductArrow P f g.
Proof.
  intros H1 H2.
  set (H := tpair (fun h => dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isProductCone_ProductCone P _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Lemma ProductArrowEta (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> ProductObject P) : 
    f == ProductArrow P (f ;; ProductPr1 P) (f ;; ProductPr2 P).
Proof.
  apply ProductArrowUnique;
  apply idpath.
Qed.
  

Definition ProductOfArrows {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) : 
          ProductObject Pab --> ProductObject Pcd :=
    ProductArrow Pcd (ProductPr1 Pab ;; f) (ProductPr2 Pab ;; g).

Lemma ProductOfArrowsPr1 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) : 
    ProductOfArrows Pcd Pab f g ;; ProductPr1 Pcd == ProductPr1 Pab ;; f.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr1Commutes.
  apply idpath.
Qed.

Lemma ProductOfArrowsPr2 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) : 
    ProductOfArrows Pcd Pab f g ;; ProductPr2 Pcd == ProductPr2 Pab ;; g.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) 
    {x : C} (k : x --> a) (h : x --> b) : 
        ProductArrow Pab k h ;; ProductOfArrows Pcd Pab f g == 
         ProductArrow Pcd (k ;; f) (h ;; g).
Proof.
  apply ProductArrowUnique.
  - rewrite <- assoc, ProductOfArrowsPr1.
    rewrite assoc, ProductPr1Commutes.
    apply idpath.
  - rewrite <- assoc, ProductOfArrowsPr2.
    rewrite assoc, ProductPr2Commutes.
    apply idpath.
Qed.


Lemma precompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a : C}
    (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  : 
       k ;; ProductArrow Pcd f g  == ProductArrow Pcd (k ;; f) (k ;; g).
Proof.
  apply ProductArrowUnique.
  -  rewrite <- assoc, ProductPr1Commutes;
     apply idpath.
  -  rewrite <- assoc, ProductPr2Commutes;
     apply idpath.
Qed.

End product_def.



Section test.

Variable C : precategory.
Variable H : Products C.
Arguments ProductObject [C] c d {_}.
Local Notation "c 'x' d" := (ProductObject  c d )(at level 5).
(*
Check (fun c d : C => c x d).
*)
End test.












