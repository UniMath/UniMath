
(** ******************************************
Benedikt Ahrens, March 2015
*********************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

(** * Definition of binary coproduct of objects in a precategory *)

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
  set (H := tpair (λ h, dirprod _ _ ) k (dirprodpair H1 H2)).
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


(** * Proof that coproducts are unique when the precategory [C] is a category *)

Section coproduct_unique.

Hypothesis H : is_category C.

Variables a b : C.

Definition from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b) 
  : CoproductObject CC ⇒ CoproductObject CC'.
Proof.
  apply (CoproductArrow CC  (CoproductIn1 _ ) (CoproductIn2 _ )).
Defined.  


Lemma Coproduct_endo_is_identity (CC : CoproductCocone a b) 
  (k : CoproductObject CC ⇒ CoproductObject CC) 
  (H1 : CoproductIn1 CC ;; k = CoproductIn1 CC)
  (H2 : CoproductIn2 CC ;; k = CoproductIn2 CC) 
  : identity _ = k.
Proof.
  set (H' := pr2 CC _ (CoproductIn1 CC) (CoproductIn2 CC) ); simpl in *.
  set (X := (Σ fg : pr1 (pr1 CC) ⇒ CoproductObject CC,
          pr1 (pr2 (pr1 CC));; fg = CoproductIn1 CC
          × pr2 (pr2 (pr1 CC));; fg = CoproductIn2 CC)).
  set (t1 := tpair _ k (dirprodpair H1 H2) : X).
  set (t2 := tpair _ (identity _ ) (dirprodpair (id_right _ _ _ _ ) (id_right _ _ _ _ ) ) : X).
  assert (X' : t1 = t2).
  { apply proofirrelevance.
    apply isapropifcontr.
    apply H'.
  }
  apply pathsinv0.
  apply (base_paths _ _ X').
Defined.
  

Lemma is_iso_from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b) 
  : is_iso (from_Coproduct_to_Coproduct CC CC').
Proof.
  apply is_iso_from_is_z_iso.
  exists (from_Coproduct_to_Coproduct CC' CC).
  split; simpl.
  - apply pathsinv0. 
    apply Coproduct_endo_is_identity.
    + rewrite assoc. unfold from_Coproduct_to_Coproduct. 
      rewrite CoproductIn1Commutes.
      rewrite CoproductIn1Commutes.
      apply idpath.
    + rewrite assoc. unfold from_Coproduct_to_Coproduct. 
      rewrite CoproductIn2Commutes.
      rewrite CoproductIn2Commutes.
      apply idpath.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    + rewrite assoc; unfold from_Coproduct_to_Coproduct.
      repeat rewrite CoproductIn1Commutes; apply idpath.
    + rewrite assoc; unfold from_Coproduct_to_Coproduct.
      repeat rewrite CoproductIn2Commutes; apply idpath.
Defined.
      
Definition iso_from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b) 
  : iso (CoproductObject CC) (CoproductObject CC') 
  := isopair _ (is_iso_from_Coproduct_to_Coproduct CC CC').

Lemma transportf_isotoid' (c d d': C) (p : iso d d') (f : c ⇒ d) : 
  transportf (λ a0 : C, c ⇒ a0) (isotoid C H p) f = f ;; p .
Proof.
  rewrite <- idtoiso_postcompose.
  rewrite idtoiso_isotoid.
  apply idpath.
Defined.

Lemma isaprop_CoproductCocone : isaprop (CoproductCocone a b).
Proof.
  apply invproofirrelevance.
  intros CC CC'.
  apply total2_paths_isaprop.
  + intros.
    do 3 (apply impred; intro); apply isapropiscontr.
  + apply (total2_paths (isotoid _ H (iso_from_Coproduct_to_Coproduct CC CC'))).
    rewrite transportf_dirprod. 
    rewrite transportf_isotoid'. simpl.
    rewrite transportf_isotoid'.
    destruct CC as [CC bla].
    destruct CC' as [CC' bla']; simpl in *.
    destruct CC as [CC [CC1 CC2]].
    destruct CC' as [CC' [CC1' CC2']]; simpl in *.
    unfold from_Coproduct_to_Coproduct.
    rewrite CoproductIn1Commutes.
    rewrite CoproductIn2Commutes.
    apply idpath.
Qed.

End coproduct_unique.  
End coproduct_def.












