(** ******************************************
Benedikt Ahrens, March 2015

Direct implementation of binary coproducts

*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.

(** * Definition of binary coproduct of objects in a precategory *)
Section coproduct_def.

Variable C : precategory.

Definition isBinCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :=
  Π (c : C) (f : a --> c) (g : b --> c),
    iscontr (Σ fg : co --> c, (ia ;; fg = f) × (ib ;; fg = g)).

Definition BinCoproductCocone (a b : C) :=
   Σ coiaib : (Σ co : C, a --> co × b --> co),
      isBinCoproductCocone a b (pr1 coiaib) (pr1 (pr2 coiaib)) (pr2 (pr2 coiaib)).


Definition BinCoproducts := Π (a b : C), BinCoproductCocone a b.
Definition hasBinCoproducts := ishinh BinCoproducts.

Definition BinCoproductObject {a b : C} (CC : BinCoproductCocone a b) : C := pr1 (pr1 CC).
Definition BinCoproductIn1 {a b : C} (CC : BinCoproductCocone a b): a --> BinCoproductObject CC :=
  pr1 (pr2 (pr1 CC)).
Definition BinCoproductIn2 {a b : C} (CC : BinCoproductCocone a b) : b --> BinCoproductObject CC :=
   pr2 (pr2 (pr1 CC)).

Definition isBinCoproductCocone_BinCoproductCocone {a b : C} (CC : BinCoproductCocone a b) :
   isBinCoproductCocone a b  (BinCoproductObject CC) (BinCoproductIn1 CC) (BinCoproductIn2 CC).
Proof.
  exact (pr2 CC).
Defined.

Definition BinCoproductArrow {a b : C} (CC : BinCoproductCocone a b) {c : C} (f : a --> c) (g : b --> c) :
      BinCoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isBinCoproductCocone_BinCoproductCocone CC _ f g))).
Defined.

Lemma BinCoproductIn1Commutes (a b : C) (CC : BinCoproductCocone a b):
     Π (c : C) (f : a --> c) g, BinCoproductIn1 CC ;; BinCoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (pr1 (pr2 (pr1 (isBinCoproductCocone_BinCoproductCocone CC _ f g)))).
Qed.

Lemma BinCoproductIn2Commutes (a b : C) (CC : BinCoproductCocone a b):
     Π (c : C) (f : a --> c) g, BinCoproductIn2 CC ;; BinCoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (pr2 (pr2 (pr1 (isBinCoproductCocone_BinCoproductCocone CC _ f g)))).
Qed.

Lemma BinCoproductArrowUnique (a b : C) (CC : BinCoproductCocone a b) (x : C)
    (f : a --> x) (g : b --> x) (k : BinCoproductObject CC --> x) :
    BinCoproductIn1 CC ;; k = f → BinCoproductIn2 CC ;; k = g →
      k = BinCoproductArrow CC f g.
Proof.
  intros H1 H2.
  set (H := tpair (λ h, dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isBinCoproductCocone_BinCoproductCocone CC _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Lemma BinCoproductArrowEta (a b : C) (CC : BinCoproductCocone a b) (x : C)
    (f : BinCoproductObject CC --> x) :
    f = BinCoproductArrow CC (BinCoproductIn1 CC ;; f) (BinCoproductIn2 CC ;; f).
Proof.
  apply BinCoproductArrowUnique;
  apply idpath.
Qed.


Definition BinCoproductOfArrows {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
          BinCoproductObject CCab --> BinCoproductObject CCcd :=
    BinCoproductArrow CCab (f ;; BinCoproductIn1 CCcd) (g ;; BinCoproductIn2 CCcd).

Lemma BinCoproductOfArrowsIn1 {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn1 CCab ;; BinCoproductOfArrows CCab CCcd f g = f ;; BinCoproductIn1 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductOfArrowsIn2 {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn2 CCab ;; BinCoproductOfArrows CCab CCcd f g = g ;; BinCoproductIn2 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn2Commutes.
Qed.


Definition mk_BinCoproductCocone (a b : C) :
  Π (c : C) (f : a --> c) (g : b --> c),
   isBinCoproductCocone _ _ _ f g →  BinCoproductCocone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    exists f.
    exact g.
  - apply X.
Defined.

Definition mk_isBinCoproductCocone (hsC : has_homsets C)(a b co : C) (ia : a --> co) (ib : b --> co) :
   (Π (c : C) (f : a --> c) (g : b --> c),
    ∃! k : C ⟦co, c⟧,
      ia ;; k = f ×
      ib ;; k = g)
   →
   isBinCoproductCocone a b co ia ib.
Proof.
  intros H c cc.
  apply H.
Defined.



Lemma precompWithBinCoproductArrow {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d)
    {x : C} (k : c --> x) (h : d --> x) :
        BinCoproductOfArrows CCab CCcd f g ;; BinCoproductArrow CCcd k h =
         BinCoproductArrow CCab (f ;; k) (g ;; h).
Proof.
  apply BinCoproductArrowUnique.
  - rewrite assoc. rewrite BinCoproductOfArrowsIn1.
    rewrite <- assoc, BinCoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, BinCoproductOfArrowsIn2.
    rewrite <- assoc, BinCoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithBinCoproductArrow {a b : C} (CCab : BinCoproductCocone a b) {c : C}
    (f : a --> c) (g : b --> c) {x : C} (k : c --> x)  :
       BinCoproductArrow CCab f g ;; k = BinCoproductArrow CCab (f ;; k) (g ;; k).
Proof.
  apply BinCoproductArrowUnique.
  -  rewrite assoc, BinCoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, BinCoproductIn2Commutes;
     apply idpath.
Qed.


(** * Proof that coproducts are unique when the precategory [C] is a category *)

Section coproduct_unique.

Hypothesis H : is_category C.

Variables a b : C.

Definition from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : BinCoproductObject CC --> BinCoproductObject CC'.
Proof.
  apply (BinCoproductArrow CC  (BinCoproductIn1 _ ) (BinCoproductIn2 _ )).
Defined.


Lemma BinCoproduct_endo_is_identity (CC : BinCoproductCocone a b)
  (k : BinCoproductObject CC --> BinCoproductObject CC)
  (H1 : BinCoproductIn1 CC ;; k = BinCoproductIn1 CC)
  (H2 : BinCoproductIn2 CC ;; k = BinCoproductIn2 CC)
  : identity _ = k.
Proof.
  set (H' := pr2 CC _ (BinCoproductIn1 CC) (BinCoproductIn2 CC) ); simpl in *.
  set (X := (Σ fg : pr1 (pr1 CC) --> BinCoproductObject CC,
          pr1 (pr2 (pr1 CC));; fg = BinCoproductIn1 CC
          × pr2 (pr2 (pr1 CC));; fg = BinCoproductIn2 CC)).
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


Lemma is_iso_from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : is_iso (from_BinCoproduct_to_BinCoproduct CC CC').
Proof.
  apply is_iso_from_is_z_iso.
  exists (from_BinCoproduct_to_BinCoproduct CC' CC).
  split; simpl.
  - apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + rewrite assoc. unfold from_BinCoproduct_to_BinCoproduct.
      rewrite BinCoproductIn1Commutes.
      rewrite BinCoproductIn1Commutes.
      apply idpath.
    + rewrite assoc. unfold from_BinCoproduct_to_BinCoproduct.
      rewrite BinCoproductIn2Commutes.
      rewrite BinCoproductIn2Commutes.
      apply idpath.
  - apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + rewrite assoc; unfold from_BinCoproduct_to_BinCoproduct.
      repeat rewrite BinCoproductIn1Commutes; apply idpath.
    + rewrite assoc; unfold from_BinCoproduct_to_BinCoproduct.
      repeat rewrite BinCoproductIn2Commutes; apply idpath.
Defined.

Definition iso_from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : iso (BinCoproductObject CC) (BinCoproductObject CC')
  := isopair _ (is_iso_from_BinCoproduct_to_BinCoproduct CC CC').

Lemma transportf_isotoid' (c d d': C) (p : iso d d') (f : c --> d) :
  transportf (λ a0 : C, c --> a0) (isotoid C H p) f = f ;; p .
Proof.
  rewrite <- idtoiso_postcompose.
  rewrite idtoiso_isotoid.
  apply idpath.
Defined.

Lemma isaprop_BinCoproductCocone : isaprop (BinCoproductCocone a b).
Proof.
  apply invproofirrelevance.
  intros CC CC'.
  apply subtypeEquality.
  + intros.
    intro. do 3 (apply impred; intro); apply isapropiscontr.
  + apply (total2_paths (isotoid _ H (iso_from_BinCoproduct_to_BinCoproduct CC CC'))).
    rewrite transportf_dirprod.
    rewrite transportf_isotoid'. simpl.
    rewrite transportf_isotoid'.
    destruct CC as [CC bla].
    destruct CC' as [CC' bla']; simpl in *.
    destruct CC as [CC [CC1 CC2]].
    destruct CC' as [CC' [CC1' CC2']]; simpl in *.
    unfold from_BinCoproduct_to_BinCoproduct.
    rewrite BinCoproductIn1Commutes.
    rewrite BinCoproductIn2Commutes.
    apply idpath.
Qed.

End coproduct_unique.
End coproduct_def.


Section BinCoproducts.

Variable C : precategory.
Variable CC : BinCoproducts C.
Variables a b c d x y : C.

Lemma BinCoproductArrow_eq (f f' : a --> c) (g g' : b --> c)
  : f = f' → g = g' →
      BinCoproductArrow _ (CC _ _) f g = BinCoproductArrow _ _ f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma BinCoproductArrow_eq_cor (f f' : BinCoproductObject C (CC a b) --> c)
  : BinCoproductIn1 _ _;; f = BinCoproductIn1 _ _;; f' → BinCoproductIn2 _ _;; f = BinCoproductIn2 _ _;; f' →
      f = f' .
Proof.
  intros Hyp1 Hyp2.
  rewrite (BinCoproductArrowEta _ _ _ _ _ f).
  rewrite (BinCoproductArrowEta _ _ _ _ _ f').
  apply BinCoproductArrow_eq; assumption.
Qed.

(** specialized versions of beta rules for coproducts *)
(* all the following lemmas for manipulation of the hypothesis
Lemma BinCoproductIn1Commutes_left (f : a --> c)(g : b --> c)(h : a --> c): BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h -> f = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right (f : a --> c)(g : b --> c)(h : a --> c): h = BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g -> h = f.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_left (f : a --> c)(g : b --> c)(h : b --> c): BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h -> g = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right (f : a --> c)(g : b --> c)(h : b --> c): h = BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g -> h = g.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h' -> f ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): h' = BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  -> h' = f ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h' -> g ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): h' = BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  -> h' = g ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_right_in_double_ctx (g0 : x --> b)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  -> h' = g0 ;; g ;; h.
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.
*)


(* optimized versions in direct style *)
Lemma BinCoproductIn1Commutes_right_dir (f : a --> c)(g : b --> c)(h : a --> c): h = f -> h = BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_right_dir (f : a --> c)(g : b --> c)(h : b --> c): h = g -> h = BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): h' = f ;; h -> h' = BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): h' = g ;; h -> h' = BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_left_dir (f : a --> c)(g : b --> c)(h : a --> c): f = h -> BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_left_dir (f : a --> c)(g : b --> c)(h : b --> c): g = h -> BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d): f ;; h = h' -> BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx_dir (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d): g ;; h = h' -> BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_right_in_double_ctx_dir (g0 : x --> a)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; f ;; h -> h' = g0 ;; BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_right_in_double_ctx_dir (g0 : x --> b)(f : a --> c)(g : b --> c)(h : c --> d)(h' : x --> d): h' = g0 ;; g ;; h -> h' = g0 ;; BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
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

Definition BinCoproductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
  : BinCoproductOfArrows _ (CC a b) (CC c d) f f' ;;
    BinCoproductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    BinCoproductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply BinCoproductArrowUnique.
  - rewrite assoc.
    rewrite BinCoproductOfArrowsIn1.
    rewrite <- assoc.
    rewrite BinCoproductOfArrowsIn1.
    apply assoc.
  - rewrite assoc.
    rewrite BinCoproductOfArrowsIn2.
    rewrite <- assoc.
    rewrite BinCoproductOfArrowsIn2.
    apply assoc.
Qed.

Definition BinCoproductOfArrows_eq (f f' : a --> c) (g g' : b --> d)
  : f = f' → g = g' →
      BinCoproductOfArrows _ _ _ f g = BinCoproductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma precompWithBinCoproductArrow_eq  (CCab : BinCoproductCocone _ a b)
    (CCcd : BinCoproductCocone _ c d) (f : a --> c) (g : b --> d)
     (k : c --> x) (h : d --> x) (fk : a --> x) (gh : b --> x):
      fk = f ;; k → gh = g ;; h →
        BinCoproductOfArrows _ CCab CCcd f g ;; BinCoproductArrow _ CCcd k h =
         BinCoproductArrow _ CCab (fk) (gh).
Proof.
  intros H H'.
  rewrite H.
  rewrite H'.
  apply precompWithBinCoproductArrow.
Qed.

End BinCoproducts.

(* Section BinCoproducts_from_Colims. *)

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

(* Lemma BinCoproducts_from_Colims : Colims C -> BinCoproducts C. *)
(* Proof. *)
(* intros H a b. *)
(* case (H _ (coproduct_diagram a b)); simpl. *)
(* intros t; destruct t as [ab cc]; simpl; intros iscc. *)
(* apply (mk_BinCoproductCocone _ _ _ ab (coconeIn cc true) (coconeIn cc false)). *)
(* apply (mk_isBinCoproductCocone _ hsC); simpl; intros c f g. *)
(* case (iscc c (CoprodCocone f g)); simpl; intros t Ht. *)
(* simple refine (tpair _ _ _). *)
(* + apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ]. *)
(* + intros t0. *)
(*   apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl. *)
(*   simple refine (let X : Σ x : C ⟦ ab, c ⟧, Π v, coconeIn cc v ;; x = *)
(*             bool_rect (λ v0, C ⟦ if v0 then a else b, c ⟧) f g v := _ in _). *)
(*   { apply (tpair _ (pr1 t0)); intro x; case x; *)
(*     [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. } *)
(* apply (maponpaths pr1 (Ht X)). *)
(* Defined. *)

(* End BinCoproducts_from_Colims. *)

Section functors.

Definition bincoproduct_functor_data {C : precategory} (PC : BinCoproducts C) :
  functor_data (precategory_binproduct C C) C.
Proof.
mkpair.
- intros p.
  apply (BinCoproductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (BinCoproductOfArrows _ (PC (pr1 p) (pr2 p))
                             (PC (pr1 q) (pr2 q)) (pr1 f) (pr2 f)).
Defined.

(* The binary coproduct functor: C * C -> C *)
Definition bincoproduct_functor {C : precategory} (PC : BinCoproducts C) :
  functor (precategory_binproduct C C) C.
Proof.
apply (tpair _ (bincoproduct_functor_data PC)).
abstract (split;
  [ intro x; simpl; apply pathsinv0, BinCoproduct_endo_is_identity;
    [ now rewrite BinCoproductOfArrowsIn1, id_left
    | now rewrite BinCoproductOfArrowsIn2, id_left ]
  | now intros x y z f g; simpl; rewrite BinCoproductOfArrows_comp ]).
Defined.

(* Defines the copropuct of two functors by:
    x -> (x,x) -> (F x,G x) -> F x + G x

  For a direct and equal definition see FunctorsPointwiseBinCoproduct.v

*)
Definition BinCoproduct_of_functors_alt {C D : precategory}
  (HD : BinCoproducts D) (F G : functor C D) : functor C D :=
  functor_composite (bindelta_functor C)
     (functor_composite (binproduct_pair_functor F G) (bincoproduct_functor HD)).

End functors.
