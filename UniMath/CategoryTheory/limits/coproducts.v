(** ******************************************
Benedikt Ahrens, March 2015
*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

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


Definition mk_CoproductCocone (a b : C) :
  ∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
   isCoproductCocone _ _ _ f g →  CoproductCocone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    exists f.
    exact g.
  - apply X.
Defined.

Definition mk_isCoproductCocone (hsC : has_homsets C)(a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) :
   (∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
    ∃! k : C ⟦co, c⟧,
      ia ;; k = f ×
      ib ;; k = g)
   →
   isCoproductCocone a b co ia ib.
Proof.
  intros H c cc.
  apply H.
Defined.



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
  apply subtypeEquality.
  + intros.
    intro. do 3 (apply impred; intro); apply isapropiscontr.
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


Section Coproducts.

Variable C : precategory.
Variable CC : Coproducts C.
Variables a b c d x y : C.

Lemma CoproductArrow_eq (f f' : a ⇒ c) (g g' : b ⇒ c)
  : f = f' → g = g' →
      CoproductArrow _ (CC _ _) f g = CoproductArrow _ _ f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma CoproductArrow_eq_cor (f f' : CoproductObject C (CC a b) ⇒ c)
  : CoproductIn1 _ _;; f = CoproductIn1 _ _;; f' → CoproductIn2 _ _;; f = CoproductIn2 _ _;; f' →
      f = f' .
Proof.
  intros Hyp1 Hyp2.
  rewrite (CoproductArrowEta _ _ _ _ _ f).
  rewrite (CoproductArrowEta _ _ _ _ _ f').
  apply CoproductArrow_eq; assumption.
Qed.

(** specialized versions of beta rules for coproducts *)
(* all the following lemmas for manipulation of the hypothesis
Lemma CoproductIn1Commutes_left (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> f = h.
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = f.
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_left (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> g = h.
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = g.
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_left_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> f ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = f ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_left_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> g ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx (g0 : x ⇒ b)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g0 ;; g ;; h.
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.
*)


(* optimized versions in direct style *)
Lemma CoproductIn1Commutes_right_dir (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): h = f -> h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductIn2Commutes_right_dir (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): h = g -> h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn2Commutes.
Qed.

Lemma CoproductIn1Commutes_right_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): h' = f ;; h -> h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): h' = g ;; h -> h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_left_dir (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): f = h -> CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductIn2Commutes_left_dir (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): g = h -> CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn2Commutes.
Qed.

Lemma CoproductIn1Commutes_left_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): f ;; h = h' -> CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_left_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): g ;; h = h' -> CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_right_in_double_ctx_dir (g0 : x ⇒ a)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; f ;; h -> h' = g0 ;; CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx_dir (g0 : x ⇒ b)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; g ;; h -> h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.
(** end of specialized versions of the beta laws for coproducts *)


(* do we ever want to create a multitude of similar lemmas for other rewrite rules?
Lemma id_left_to_the_right (C': precategory)(a b : C')(f h : C' ⟦ a, b ⟧): h = f -> h = identity a;; f.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, id_left.
Qed.

Lemma id_left_to_the_right_in_ctx (C': precategory)(a b c: C')(f : C' ⟦ a, b ⟧)(g : C' ⟦ b, c ⟧)(h : C' ⟦ a, c ⟧): h = f ;; g -> h = identity a ;; f ;; g.
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite id_left.
  apply idpath.
Qed.


Lemma assoc_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f;; g;; h -> res = f;; (g;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, assoc.
Qed.

Lemma assoc_back_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f;; (g;; h) -> res = f;; g;; h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply assoc.
Qed.
*)

Definition CoproductOfArrows_comp (f : a ⇒ c) (f' : b ⇒ d) (g : c ⇒ x) (g' : d ⇒ y)
  : CoproductOfArrows _ (CC a b) (CC c d) f f' ;;
    CoproductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    CoproductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply CoproductArrowUnique.
  - rewrite assoc.
    rewrite CoproductOfArrowsIn1.
    rewrite <- assoc.
    rewrite CoproductOfArrowsIn1.
    apply assoc.
  - rewrite assoc.
    rewrite CoproductOfArrowsIn2.
    rewrite <- assoc.
    rewrite CoproductOfArrowsIn2.
    apply assoc.
Qed.

Definition CoproductOfArrows_eq (f f' : a ⇒ c) (g g' : b ⇒ d)
  : f = f' → g = g' →
      CoproductOfArrows _ _ _ f g = CoproductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma precompWithCoproductArrow_eq  (CCab : CoproductCocone _ a b)
    (CCcd : CoproductCocone _ c d) (f : a ⇒ c) (g : b ⇒ d)
     (k : c ⇒ x) (h : d ⇒ x) (fk : a ⇒ x) (gh : b ⇒ x):
      fk = f ;; k → gh = g ;; h →
        CoproductOfArrows _ CCab CCcd f g ;; CoproductArrow _ CCcd k h =
         CoproductArrow _ CCab (fk) (gh).
Proof.
  intros H H'.
  rewrite H.
  rewrite H'.
  apply precompWithCoproductArrow.
Qed.

End Coproducts.

Section Coproducts_from_Colims.

Require Import UniMath.CategoryTheory.colimits.colimits.

Variable C : precategory.
Variable hsC : has_homsets C.

Definition two_graph : graph.
Proof.
  exists bool.
  exact (fun _ _ => empty).
Defined.

Definition coproduct_diagram (a b : C) : diagram two_graph C.
Proof.
  exists (fun x : bool => if x then a else b).
  intros u v F.
  induction F.
Defined.

Definition CoprodCocone {a b c : C} (ac : a ⇒ c) (bc : b ⇒ c) :
   cocone (coproduct_diagram a b) c.
Proof.
simple refine (tpair _ _ _ ).
+ intro v; induction v; [ exact ac | exact bc ].
+ abstract (intros u v e; induction e).
Defined.

Lemma Coproducts_from_Colims : Colims C -> Coproducts C.
Proof.
intros H a b.
case (H _ (coproduct_diagram a b)); simpl.
intros t; destruct t as [ab cc]; simpl; intros iscc.
apply (mk_CoproductCocone _ _ _ ab (coconeIn cc true) (coconeIn cc false)).
apply (mk_isCoproductCocone _ hsC); simpl; intros c f g.
case (iscc c (CoprodCocone f g)); simpl; intros t Ht.
simple refine (tpair _ _ _).
+ apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ].
+ intros t0.
  apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl.
  simple refine (let X : Σ x : C ⟦ ab, c ⟧, ∀ v, coconeIn cc v ;; x =
            bool_rect (λ v0, C ⟦ if v0 then a else b, c ⟧) f g v := _ in _).
  { apply (tpair _ (pr1 t0)); intro x; case x;
    [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. }
apply (maponpaths pr1 (Ht X)).
Defined.

End Coproducts_from_Colims.