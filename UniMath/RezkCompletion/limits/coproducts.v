Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.total2_paths.
Require Import RezkCompletion.precategories.
Require Import RezkCompletion.UnicodeNotations.

Section coproduct_def.

Variable C : precategory.

Definition isCoproductCocone (a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) := 
  ∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
    iscontr (Σ fg : co ⇒ c, (ia ;; fg = f) × (ib ;; fg = g)).

Definition CoproductCocone (a b : C) := 
   Σ coiaib : (Σ co : C, a ⇒ co × b ⇒ co),
          isCoproductCocone a b (pr1 coiaib) (pr1 (pr2 coiaib)) (pr2 (pr2 coiaib)).


Definition Coproducts := ∀ (a b : C), CoproductCocone a b.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a b : C} (CC : CoproductCocone a b) : C := pr1 (pr1 CC).
Definition CoproductIn1 {a b : C} (CC : CoproductCocone a b): a ⇒ CoproductObject CC :=
  pr1 (pr2 (pr1 CC)).
Definition CoproductIn2 {a b : C} (CC : CoproductCocone a b) : b ⇒ CoproductObject CC :=
   pr2 (pr2 (pr1 CC)).

Definition isCoproductCocone_CoproductCocone {a b : C} (CC : CoproductCocone a b) : 
   isCoproductCocone a b  (CoproductObject CC) (CoproductIn1 CC) (CoproductIn2 CC).
Proof.
  exact (pr2 CC).
Defined.

Definition CoproductArrow {a b : C} (CC : CoproductCocone a b) {c : C} (f : a ⇒ c) (g : b ⇒ c) : 
      CoproductObject CC ⇒ c.
Proof.
  exact (pr1 (pr1 (isCoproductCocone_CoproductCocone CC _ f g))).
Defined.

Lemma CoproductIn1Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn1 CC ;; CoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (pr1 (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f g)))).
Qed.

Lemma CoproductIn2Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn2 CC ;; CoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (pr2 (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f g)))).
Qed.

Lemma ProductArrowUnique (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> ProductObject P) :
    k ;; ProductPr1 P = f -> k ;; ProductPr2 P = g ->
      k = ProductArrow P f g.
Proof.
  intros H1 H2.
  set (H := tpair (fun h => dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isProductCone_ProductCone P _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Lemma ProductArrowEta (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> ProductObject P) : 
    f = ProductArrow P (f ;; ProductPr1 P) (f ;; ProductPr2 P).
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
    ProductOfArrows Pcd Pab f g ;; ProductPr1 Pcd = ProductPr1 Pab ;; f.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr1Commutes.
  apply idpath.
Qed.

Lemma ProductOfArrowsPr2 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) : 
    ProductOfArrows Pcd Pab f g ;; ProductPr2 Pcd = ProductPr2 Pab ;; g.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) 
    {x : C} (k : x --> a) (h : x --> b) : 
        ProductArrow Pab k h ;; ProductOfArrows Pcd Pab f g = 
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
       k ;; ProductArrow Pcd f g  = ProductArrow Pcd (k ;; f) (k ;; g).
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












