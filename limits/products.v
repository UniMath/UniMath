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
   total2 (fun p : C => total2 (
            fun p1p2 : dirprod (p --> c) (p --> d) =>
             isProductCone c d p (pr1 p1p2) (pr2 p1p2))).


Definition Products := forall (c d : C), ProductCone c d.
Definition hasProducts := ishinh Products.

Definition ProductObject {c d : C} (P : ProductCone c d) : C := pr1 P.
Definition ProductPr1 {c d : C} (P : ProductCone c d): ProductObject P --> c :=
   pr1 (pr1 (pr2 P)).
Definition ProductPr2 {c d : C} (P : ProductCone c d) : ProductObject P --> d :=
   pr2 (pr1 (pr2 P)).

Definition isProductCone_ProductCone {c d : C} (P : ProductCone c d) : 
   isProductCone c d (ProductObject P) (ProductPr1 P) (ProductPr2 P).
Proof.
  exact (pr2 (pr2 P)).
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





















