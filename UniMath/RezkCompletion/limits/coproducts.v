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

Lemma CoproductArrowUnique (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : a ⇒ x) (g : b ⇒ x) (k : CoproductObject CC ⇒ x) :
    CoproductIn1 CC ;; k = f → CoproductIn2 CC ;; k = g →
      k = CoproductArrow CC f g.
Proof.
  intros H1 H2.
  set (H := tpair (fun h => dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isCoproductCocone_CoproductCocone CC _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Lemma CoproductArrowEta (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : CoproductObject CC ⇒ x) : 
    f = CoproductArrow CC (CoproductIn1 CC ;; f) (CoproductIn2 CC ;; f).
Proof.
  apply CoproductArrowUnique;
  apply idpath.
Qed.
  

Definition CoproductOfArrows {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) : 
          CoproductObject CCab ⇒ CoproductObject CCcd :=
    CoproductArrow CCab (f ;; CoproductIn1 CCcd) (g ;; CoproductIn2 CCcd).

Lemma CoproductOfArrowsIn1 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) : 
    CoproductIn1 CCab ;; CoproductOfArrows CCab CCcd f g = f ;; CoproductIn1 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductOfArrowsIn2 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) : 
    CoproductIn2 CCab ;; CoproductOfArrows CCab CCcd f g = g ;; CoproductIn2 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn2Commutes.
Qed.


Lemma precompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) 
    {x : C} (k : c ⇒ x) (h : d ⇒ x) : 
        CoproductOfArrows CCab CCcd f g ;; CoproductArrow CCcd k h = 
         CoproductArrow CCab (f ;; k) (g ;; h).
Proof.
  apply CoproductArrowUnique.
  - rewrite assoc. rewrite CoproductOfArrowsIn1.
    rewrite <- assoc, CoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, CoproductOfArrowsIn2.
    rewrite <- assoc, CoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c : C}
    (f : a ⇒ c) (g : b ⇒ c) {x : C} (k : c ⇒ x)  : 
       CoproductArrow CCab f g ;; k = CoproductArrow CCab (f ;; k) (g ;; k).
Proof.
  apply CoproductArrowUnique.
  -  rewrite assoc, CoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, CoproductIn2Commutes;
     apply idpath.
Qed.

End coproduct_def.












