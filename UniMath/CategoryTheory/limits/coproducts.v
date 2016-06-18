(** ******************************************
Benedikt Ahrens, March 2015

Direct implementation of coproducts

*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.
Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

(** * Definition of binary coproduct of objects in a precategory *)
Section coproduct_def.

Variable C : precategory.

Definition isCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :=
  ∀ (c : C) (f : a --> c) (g : b --> c),
    iscontr (Σ fg : co --> c, (ia ;; fg = f) × (ib ;; fg = g)).

Definition CoproductCocone (a b : C) :=
   Σ coiaib : (Σ co : C, a --> co × b --> co),
          isCoproductCocone a b (pr1 coiaib) (pr1 (pr2 coiaib)) (pr2 (pr2 coiaib)).


Definition Coproducts := ∀ (a b : C), CoproductCocone a b.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a b : C} (CC : CoproductCocone a b) : C := pr1 (pr1 CC).
Definition CoproductIn1 {a b : C} (CC : CoproductCocone a b): a --> CoproductObject CC :=
  pr1 (pr2 (pr1 CC)).
Definition CoproductIn2 {a b : C} (CC : CoproductCocone a b) : b --> CoproductObject CC :=
   pr2 (pr2 (pr1 CC)).

Definition isCoproductCocone_CoproductCocone {a b : C} (CC : CoproductCocone a b) :
   isCoproductCocone a b  (CoproductObject CC) (CoproductIn1 CC) (CoproductIn2 CC).
Proof.
  exact (pr2 CC).
Defined.

Definition CoproductArrow {a b : C} (CC : CoproductCocone a b) {c : C} (f : a --> c) (g : b --> c) :
      CoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isCoproductCocone_CoproductCocone CC _ f g))).
Defined.

Lemma CoproductIn1Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a --> c) g, CoproductIn1 CC ;; CoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (pr1 (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f g)))).
Qed.

Lemma CoproductIn2Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a --> c) g, CoproductIn2 CC ;; CoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (pr2 (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f g)))).
Qed.

Lemma CoproductArrowUnique (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : a --> x) (g : b --> x) (k : CoproductObject CC --> x) :
    CoproductIn1 CC ;; k = f → CoproductIn2 CC ;; k = g →
      k = CoproductArrow CC f g.
Proof.
  intros H1 H2.
  set (H := tpair (λ h, dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isCoproductCocone_CoproductCocone CC _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Lemma CoproductArrowEta (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : CoproductObject CC --> x) :
    f = CoproductArrow CC (CoproductIn1 CC ;; f) (CoproductIn2 CC ;; f).
Proof.
  apply CoproductArrowUnique;
  apply idpath.
Qed.


Definition CoproductOfArrows {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
          CoproductObject CCab --> CoproductObject CCcd :=
    CoproductArrow CCab (f ;; CoproductIn1 CCcd) (g ;; CoproductIn2 CCcd).

Lemma CoproductOfArrowsIn1 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
    CoproductIn1 CCab ;; CoproductOfArrows CCab CCcd f g = f ;; CoproductIn1 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductOfArrowsIn2 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
    CoproductIn2 CCab ;; CoproductOfArrows CCab CCcd f g = g ;; CoproductIn2 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn2Commutes.
Qed.


Definition mk_CoproductCocone (a b : C) :
  ∀ (c : C) (f : a --> c) (g : b --> c),
   isCoproductCocone _ _ _ f g →  CoproductCocone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    exists f.
    exact g.
  - apply X.
Defined.

Definition mk_isCoproductCocone (hsC : has_homsets C)(a b co : C) (ia : a --> co) (ib : b --> co) :
   (∀ (c : C) (f : a --> c) (g : b --> c),
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
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d)
    {x : C} (k : c --> x) (h : d --> x) :
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
    (f : a --> c) (g : b --> c) {x : C} (k : c --> x)  :
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
  : CoproductObject CC --> CoproductObject CC'.
Proof.
  apply (CoproductArrow CC  (CoproductIn1 _ ) (CoproductIn2 _ )).
Defined.


Lemma Coproduct_endo_is_identity (CC : CoproductCocone a b)
  (k : CoproductObject CC --> CoproductObject CC)
  (H1 : CoproductIn1 CC ;; k = CoproductIn1 CC)
  (H2 : CoproductIn2 CC ;; k = CoproductIn2 CC)
  : identity _ = k.
Proof.
  set (H' := pr2 CC _ (CoproductIn1 CC) (CoproductIn2 CC) ); simpl in *.
  set (X := (Σ fg : pr1 (pr1 CC) --> CoproductObject CC,
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

Lemma transportf_isotoid' (c d d': C) (p : iso d d') (f : c --> d) :
  transportf (λ a0 : C, c --> a0) (isotoid C H p) f = f ;; p .
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

Lemma CoproductArrow_eq (f f' : a --> c) (g g' : b --> c)
  : f = f' → g = g' →
      CoproductArrow _ (CC _ _) f g = CoproductArrow _ _ f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma CoproductArrow_eq_cor (f f' : CoproductObject C (CC a b) --> c)
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
Lemma CoproductIn1Commutes_left (f : a --> c)(g : b --> c)(h : a --> c): CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> f = h.
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right (f : a --> c)(g : b --> c)(h : a --> c): h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = f.
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_left (f : a --> c)(g : b --> c)(h : b --> c): CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> g = h.
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right (f : a --> c)(g : b --> c)(h : b --> c): h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = g.
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> f ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = f ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> g ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx (g0 : x --> b)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g0 ;; g ;; h.
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
Lemma CoproductIn1Commutes_right_dir (f : a --> c)(g : b --> c)(h : a --> c): h = f -> h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductIn2Commutes_right_dir (f : a --> c)(g : b --> c)(h : b --> c): h = g -> h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn2Commutes.
Qed.

Lemma CoproductIn1Commutes_right_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): h' = f ;; h -> h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): h' = g ;; h -> h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_left_dir (f : a --> c)(g : b --> c)(h : a --> c): f = h -> CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductIn2Commutes_left_dir (f : a --> c)(g : b --> c)(h : b --> c): g = h -> CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn2Commutes.
Qed.

Lemma CoproductIn1Commutes_left_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): f ;; h = h' -> CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_left_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): g ;; h = h' -> CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_right_in_double_ctx_dir (g0 : x --> a)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; f ;; h -> h' = g0 ;; CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx_dir (g0 : x --> b)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; g ;; h -> h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
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

Definition CoproductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
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

Definition CoproductOfArrows_eq (f f' : a --> c) (g g' : b --> d)
  : f = f' → g = g' →
      CoproductOfArrows _ _ _ f g = CoproductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma precompWithCoproductArrow_eq  (CCab : CoproductCocone _ a b)
    (CCcd : CoproductCocone _ c d) (f : a --> c) (g : b --> d)
     (k : c --> x) (h : d --> x) (fk : a --> x) (gh : b --> x):
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

(** In this section we construct a coproduct from an arbitrary coproduct and an
  arbitrary coproduct from a coproduct. *)
Section Coproducts_ArbitraryCoproducts.
  (** Variables and definitions we are going to use in the proofs. *)
  Variable C : precategory.
  Hypothesis hs : has_homsets C.
  Definition stn0 : stn 2 := stnpair 2 0 (natlthtolths _ _ (natlthnsn 0)).
  Definition stn1 : stn 2 := stnpair 2 1 (natlthnsn 1).

  (** We will use the following two definitions to do induction. *)
  Definition tworec (n : nat) (H' : n < 2) : (n = 0) ⨿ (n = 1).
  Proof.
    destruct n.
    exact (ii1 (idpath 0)).
    destruct n.
    exact (ii2 (idpath 1)).
    exact (fromempty (nopathsfalsetotrue H')).
  Defined.
  Definition stn2ind (i : stn 2) : (i = stn0) ⨿ (i = stn1).
  Proof.
    induction (tworec (pr1 i)).
    apply ii1. apply isinjstntonat, a.
    apply ii2. apply isinjstntonat, b.
    exact (pr2 i).
  Defined.

  (** Construct a family of 2 objects from a pair of objects. *)
  Definition pair_to_stn2 (c1 c2 : C) : (stn 2) -> C.
  Proof.
    intros X.
    induction (stn2ind X).
    exact c1.
    exact c2.
  Defined.

  (** The following lemmas check that the above definition is correct.*)
  Lemma pair_to_stn2_1 (c1 c2 : C) : pair_to_stn2 c1 c2 stn0 = c1.
  Proof. apply idpath. Defined.
  Lemma pair_to_stn2_2 (c1 c2 : C) : pair_to_stn2 c1 c2 stn1 = c2.
  Proof. apply idpath. Defined.

  (** Construct a family of 2 morphisms with the same target from 2 morphisms
    with the same target. *)
  Definition pair_to_stn2_mors (c : C) (a : stn 2 -> C) (f : C⟦a stn0, c⟧)
             (g : C⟦a stn1, c⟧) : forall i : stn 2, C⟦a i, c⟧.
  Proof.
    intros i. induction (stn2ind i).
    rewrite <- a0 in f. apply f.
    rewrite <- b in g. apply g.
  Defined.

  (** The following lemmas check that the above definition is correct. *)
  Lemma pair_to_stn2_mors_1 (c : C) (a : stn 2 -> C) (f : C⟦a stn0, c⟧)
        (g : C⟦a stn1, c⟧) :
    pair_to_stn2_mors c a f g stn0 = f.
  Proof. apply idpath. Defined.
  Lemma pair_to_stn2_mors_2 (c : C) (a : stn 2 -> C) (f : C⟦a stn0, c⟧)
        (g : C⟦a stn1, c⟧) :
    pair_to_stn2_mors c a f g stn1 = g.
  Proof. apply idpath. Defined.

  (** Construction of a coproduct from an arbitrary coproduct of 2 objects. *)
  Definition coproduct_from_arbitrary_coproduct
             (a : stn 2 -> C) (Cone : ArbitraryCoproductCocone (stn 2) C a) :
    CoproductCocone C (a stn0) (a stn1).
  Proof.
    set (in1 := ArbitraryCoproductIn _ _ Cone stn0).
    set (in2 := ArbitraryCoproductIn _ _ Cone stn1).
    set (Coneob := (ArbitraryCoproductObject _ _ Cone)).
    refine (mk_CoproductCocone _ (a stn0) (a stn1) Coneob in1 in2 _).
    refine (mk_isCoproductCocone _ hs _ _ _ _ _ _).
    intros c f g.
    set (mors := pair_to_stn2_mors c a f g).
    set (com1 := ArbitraryCoproductInCommutes _ _ a Cone c mors stn0).
    set (com2 := ArbitraryCoproductInCommutes _ _ a Cone c mors stn1).
    set (ar := (ArbitraryCoproductArrow _ _ Cone mors)).
    refine (tpair _ (tpair _ ar _)  _).
    intros t; eapply total2_paths.
    apply proofirrelevance, isapropdirprod; apply hs.

    Unshelve.

    (* Commutativity *)
    split.
    rewrite <- (pair_to_stn2_mors_1 c a f g). apply com1.
    rewrite <- (pair_to_stn2_mors_2 c a f g). apply com2.

    (* Uniqueness *)
    eapply ArbitraryCoproductArrowUnique. intros i. induction (stn2ind i).
    rewrite a0. fold in1. rewrite <- (pair_to_stn2_mors_1 c a f g).
    apply (dirprod_pr1 (pr2 t)).
    rewrite b. fold in2. rewrite <- (pair_to_stn2_mors_2 c a f g).
    apply (dirprod_pr2 (pr2 t)).
  Defined.

  (** Construction of an arbitrary coproduct from a coproduct. *)
  Definition arbitrary_coproduct_from_coproduct (c1 c2 : C)
             (Cone : CoproductCocone C c1 c2) :
    ArbitraryCoproductCocone (stn 2) C (pair_to_stn2 c1 c2).
  Proof.
    set (a := pair_to_stn2 c1 c2).
    set (in1 := CoproductIn1 _ Cone).
    set (in2 := CoproductIn2 _ Cone).
    set (ConeOb := CoproductObject _ Cone).
    set (f := pair_to_stn2_mors ConeOb a in1 in2).
    refine (mk_ArbitraryCoproductCocone _ _ a ConeOb f _ ).
    refine (mk_isArbitraryCoproductCocone _ _ hs _ _ _ _).
    intros c g.
    set (f1 := g stn0).
    set (f2 := g stn1).
    set (ar := CoproductArrow _ Cone f1 f2).
    set (com1 := CoproductIn1Commutes _ _ _ Cone _ f1 f2).
    set (com2 := CoproductIn2Commutes _ _ _ Cone _ f1 f2).
    refine (tpair _ (tpair _ ar _ ) _).
    intros t. eapply total2_paths. apply proofirrelevance.
    apply impred_isaprop. intros t0. apply hs.

    Unshelve.
    (* Commutativity *)
    intros i. induction (stn2ind i).
    rewrite a0. unfold f. rewrite (pair_to_stn2_mors_1 ConeOb a in1 in2).
    apply com1.
    rewrite b. unfold f. rewrite (pair_to_stn2_mors_2 ConeOb a in1 in2).
    apply com2.

    (* Uniqueness *)
    apply CoproductArrowUnique.
    fold in1. rewrite <- (pair_to_stn2_mors_1 ConeOb a in1 in2). fold f.
    apply (pr2 t stn0).
    fold in2. rewrite <- (pair_to_stn2_mors_2 ConeOb a in1 in2). fold f.
    apply (pr2 t stn1).
  Defined.
End Coproducts_ArbitraryCoproducts.

(** In this section we construct an arbitrary coproduct from two arbitrary
  coproducts by taking the disjoint union of the objects. We need to assume that
  the coproduct of the given two arbitrary coproducts exists. *)
Section coproduct_from_coproducts.
  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Disjoint union of the objects a1 and a2. *)
  Definition coprod_families {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C):
    I1 ⨿ I2 -> C.
  Proof.
    intros X.
    induction X.
    apply (a1 a).
    apply (a2 b).
  Defined.

  (** Verify that we have the same objects. *)
  Lemma coprod_families_1 {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C) (i : I1):
    coprod_families a1 a2 (ii1 i) = a1 i.
  Proof. apply idpath. Defined.
  Lemma coprod_families_2 {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C) (i : I2):
    coprod_families a1 a2 (ii2 i) = a2 i.
  Proof. apply idpath. Defined.

  (** Construction of an arbitrary coproduct from two arbitrary coproducts and a
    coproduct of the two arbitrary coproducts. *)
  Theorem arbitrary_coproduct_from_arbitrary_coproducts :
    forall (I1 I2 : UU) (a1 : I1 -> C) (a2 : I2 -> C)
      (A1 : ArbitraryCoproductCocone _ C a1)
      (A2 : ArbitraryCoproductCocone _ C a2)
      (Cone : CoproductCocone C (ArbitraryCoproductObject _ _ A1)
                              (ArbitraryCoproductObject _ _ A2)),
      ArbitraryCoproductCocone _ C (coprod_families a1 a2).
  Proof.
    intros I1 I2 a1 a2 A1 A2 Cone.

    (* Set names from useful terms *)
    set (A1in := ArbitraryCoproductIn _ _ A1).
    set (A2in := ArbitraryCoproductIn _ _ A2).
    set (in1 := CoproductIn1 _ Cone).
    set (in2 := CoproductIn2 _ Cone).

    eapply (mk_ArbitraryCoproductCocone _ _ _ (CoproductObject _ Cone)).
    eapply mk_isArbitraryCoproductCocone.
    apply hs.
    intros c g.

    (* Set names for useful terms *)
    set (g1 := fun i : I1 => g (ii1 i)).
    set (g2 := fun i : I2 => g (ii2 i)).
    set (ar1 := ArbitraryCoproductArrow _ _ A1 g1).
    set (ar2 := ArbitraryCoproductArrow _ _ A2 g2).
    set (ar := CoproductArrow _ Cone ar1 ar2).
    set (com1 := CoproductIn1Commutes _ _ _ Cone c ar1 ar2).
    set (com2 := CoproductIn2Commutes _ _ _ Cone c ar1 ar2).

    refine (tpair _ _ _).
    intros t.
    eapply total2_paths. apply proofirrelevance.
    apply impred_isaprop. intros t0. apply hs.

    Unshelve.

    (* Morphisms from objects to the cone *)
    intros i. unfold coprod_families, coprod_rect. induction i.
    apply (A1in a ;; in1).
    apply (A2in b ;; in2).

    (* The unique arrow from the cone to c *)
    refine (tpair _ ar _ ).

    (* Commutativity of morphisms *)
    intros i. unfold coprod_rect. induction i.

    set (com'1 := ArbitraryCoproductInCommutes _ _ _ A1 c g1 a).
    unfold A1in. unfold in1. unfold ar. rewrite <- assoc. rewrite com1.
    unfold ar1. rewrite -> com'1. apply idpath.


    set (com'2 := ArbitraryCoproductInCommutes _ _ _ A2 c g2 b).
    unfold A2in, in2, ar. rewrite <- assoc. rewrite com2.
    unfold ar2. rewrite com'2. apply idpath.

    simpl.
    (* Uniqueness of the morphism from the cone *)
    eapply CoproductArrowUnique.
    eapply ArbitraryCoproductArrowUnique.
    intros i. simpl in t. set (t2 := pr2 t (ii1 i)). simpl in t2.
    fold A1in. rewrite assoc. apply t2.

    eapply ArbitraryCoproductArrowUnique.
    intros i. simpl in t. set (t2 := pr2 t (ii2 i)). simpl in t2.
    fold A2in. rewrite assoc. apply t2.
  Defined.
End coproduct_from_coproducts.

(* Section Coproducts_from_Colims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)

(* Variable C : precategory. *)
(* Variable hsC : has_homsets C. *)

(* Definition two_graph : graph. *)
(* Proof. *)
(*   exists bool. *)
(*   exact (fun _ _ => empty). *)
(* Defined. *)

(* Definition coproduct_diagram (a b : C) : diagram two_graph C. *)
(* Proof. *)
(*   exists (fun x : bool => if x then a else b). *)
(*   intros u v F. *)
(*   induction F. *)
(* Defined. *)

(* Definition CoprodCocone {a b c : C} (ac : a --> c) (bc : b --> c) : *)
(*    cocone (coproduct_diagram a b) c. *)
(* Proof. *)
(* simple refine (tpair _ _ _ ). *)
(* + intro v; induction v; [ exact ac | exact bc ]. *)
(* + abstract (intros u v e; induction e). *)
(* Defined. *)

(* Lemma Coproducts_from_Colims : Colims C -> Coproducts C. *)
(* Proof. *)
(* intros H a b. *)
(* case (H _ (coproduct_diagram a b)); simpl. *)
(* intros t; destruct t as [ab cc]; simpl; intros iscc. *)
(* apply (mk_CoproductCocone _ _ _ ab (coconeIn cc true) (coconeIn cc false)). *)
(* apply (mk_isCoproductCocone _ hsC); simpl; intros c f g. *)
(* case (iscc c (CoprodCocone f g)); simpl; intros t Ht. *)
(* simple refine (tpair _ _ _). *)
(* + apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ]. *)
(* + intros t0. *)
(*   apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl. *)
(*   simple refine (let X : Σ x : C ⟦ ab, c ⟧, ∀ v, coconeIn cc v ;; x = *)
(*             bool_rect (λ v0, C ⟦ if v0 then a else b, c ⟧) f g v := _ in _). *)
(*   { apply (tpair _ (pr1 t0)); intro x; case x; *)
(*     [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. } *)
(* apply (maponpaths pr1 (Ht X)). *)
(* Defined. *)

(* End Coproducts_from_Colims. *)

Section functors.

Definition bincoproduct_functor_data {C : precategory} (PC : Coproducts C) :
  functor_data (product_precategory C C) C.
Proof.
mkpair.
- intros p.
  apply (CoproductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (CoproductOfArrows _ (PC (pr1 p) (pr2 p))
                             (PC (pr1 q) (pr2 q)) (pr1 f) (pr2 f)).
Defined.

(* The binary coproduct functor: C * C -> C *)
Definition bincoproduct_functor {C : precategory} (PC : Coproducts C) :
  functor (product_precategory C C) C.
Proof.
apply (tpair _ (bincoproduct_functor_data PC)).
abstract (split;
  [ intro x; simpl; apply pathsinv0, Coproduct_endo_is_identity;
    [ now rewrite CoproductOfArrowsIn1, id_left
    | now rewrite CoproductOfArrowsIn2, id_left ]
  | now intros x y z f g; simpl; rewrite CoproductOfArrows_comp ]).
Defined.

(* Defines the copropuct of two functors by:
    x -> (x,x) -> (F x,G x) -> F x + G x

  For a direct and equal definition see FunctorsPointwiseCoproduct.v

*)
Definition coproduct_of_functors {C D : precategory} (HD : Coproducts D)
  (F G : functor C D) : functor C D :=
  functor_composite (delta_functor C)
     (functor_composite (pair_functor F G) (bincoproduct_functor HD)).

End functors.