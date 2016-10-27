(** ******************************************

Direct implementation of binary coproducts togther with:

- Proof that binary coproduct(cocone) is a property in a category ([isaprop_BinCoproductCocone])
- Specialized versions of beta rules for coproducts
- Definition of binary coproduct functor ([bincoproduct_functor])
- Definition of a coproduct structure on a functor category by taking pointwise coproducts in the
  target category ([BinCoproducts_functor_precat])
- Definition of the option functor ([option_functor])

Written by Benedikt Ahrens, March 2015
Extended by Anders Mörtberg and Tomi Pannila, 2016

*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(** * Definition of binary coproduct of objects in a precategory *)
Section coproduct_def.

Variable C : precategory.

Definition isBinCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :=
  Π (c : C) (f : a --> c) (g : b --> c),
  iscontr (Σ fg : co --> c, (ia ;; fg = f) × (ib ;; fg = g)).

Lemma isaprop_isBinCoproductCocone {a b co : C} {ia : a --> co} {ib : b --> co} :
  isaprop (isBinCoproductCocone a b co ia ib).
Proof.
  apply impred_isaprop. intros t.
  apply impred_isaprop. intros t0.
  apply impred_isaprop. intros g.
  apply isapropiscontr.
Qed.

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

Definition BinCoproductArrow {a b : C} (CC : BinCoproductCocone a b)
  {c : C} (f : a --> c) (g : b --> c) : BinCoproductObject CC --> c.
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

Lemma BinCoproductArrowsEq (c d : C) (CC : BinCoproductCocone c d) (x : C)
      (k1 k2 : BinCoproductObject CC --> x) :
  BinCoproductIn1 CC ;; k1 = BinCoproductIn1 CC ;; k2 ->
  BinCoproductIn2 CC ;; k1 = BinCoproductIn2 CC ;; k2 ->
  k1 = k2.
Proof.
  intros H1 H2.
  set (p1 := BinCoproductIn1 CC ;; k1).
  set (p2 := BinCoproductIn2 CC ;; k1).
  rewrite (BinCoproductArrowUnique _ _ CC _ p1 p2 k1).
  apply pathsinv0.
  apply BinCoproductArrowUnique.
  unfold p1. apply pathsinv0. apply H1.
  unfold p2. apply pathsinv0. apply H2.
  apply idpath. apply idpath.
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

Definition mk_isBinCoproductCocone (hsC : has_homsets C) (a b co : C)
   (ia : a --> co) (ib : b --> co) :
   (Π (c : C) (f : a --> c) (g : b --> c),
    ∃! k : C ⟦co, c⟧,
      ia ;; k = f ×
      ib ;; k = g)
   → isBinCoproductCocone a b co ia ib.
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
  set (t2 := tpair _ (identity _ ) (dirprodpair (id_right _ ) (id_right _ ) ) : X).
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
Lemma BinCoproductIn1Commutes_left (f : a --> c)(g : b --> c)(h : a --> c):
  BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h -> f = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right (f : a --> c)(g : b --> c)(h : a --> c):
  h = BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g -> h = f.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_left (f : a --> c)(g : b --> c)(h : b --> c):
  BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h -> g = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right (f : a --> c)(g : b --> c)(h : b --> c):
  h = BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g -> h = g.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d):
  BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h' -> f ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d):
  h' = BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  -> h' = f ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d):
  BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h' -> g ;; h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d):
  h' = BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  -> h' = g ;; h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_right_in_double_ctx (g0 : x --> b)(f : a --> c)(g : b --> c)
 (h : c --> d)(h' : x --> d):
  h' = g0 ;; BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h)  ->
  h' = g0 ;; g ;; h.
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
Lemma BinCoproductIn1Commutes_right_dir (f : a --> c) (g : b --> c) (h : a --> c) :
  h = f -> h = BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_right_dir (f : a --> c) (g : b --> c) (h : b --> c) :
  h = g -> h = BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx_dir (f : a --> c) (g : b --> c) (h : c --> d) (h' : a --> d) :
  h' = f ;; h -> h' = BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx_dir (f : a --> c) (g : b --> c) (h : c --> d) (h' : b --> d) :
  h' = g ;; h -> h' = BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_left_dir (f : a --> c) (g : b --> c) (h : a --> c) :
  f = h -> BinCoproductIn1 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_left_dir (f : a --> c) (g : b --> c) (h : b --> c) :
  g = h -> BinCoproductIn2 C (CC _ _) ;; BinCoproductArrow C (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx_dir (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : a --> d) :
  f ;; h = h' -> BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx_dir (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : b --> d) :
  g ;; h = h' -> BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_right_in_double_ctx_dir (g0 : x --> a) (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : x --> d) : h' = g0 ;; f ;; h ->
  h' = g0 ;; BinCoproductIn1 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_right_in_double_ctx_dir (g0 : x --> b) (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : x --> d) : h' = g0 ;; g ;; h ->
  h' = g0 ;; BinCoproductIn2 C (CC _ _) ;; (BinCoproductArrow C (CC _ _) f g ;; h).
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

Lemma id_left_to_the_right_in_ctx (C': precategory)(a b c: C')(f : C' ⟦ a, b ⟧)(g : C' ⟦ b, c ⟧)
  (h : C' ⟦ a, c ⟧): h = f ;; g -> h = identity a ;; f ;; g.
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
     (functor_composite (pair_functor F G) (bincoproduct_functor HD)).

End functors.

(** In the following section we show that if the morphism to components are
    zero, then the unique morphism factoring through the bincoproduct is the
    zero morphism. *)
Section BinCoproduct_zeroarrow.

  Variable C : precategory.
  Variable Z : Zero C.

  Lemma BinCoproductArrowZero {x y z: C} {BP : BinCoproductCocone C x y} (f : x --> z) (g : y --> z) :
    f = ZeroArrow Z _ _ -> g = ZeroArrow Z _ _ -> BinCoproductArrow C BP f g = ZeroArrow Z _ _ .
  Proof.
    intros X X0. apply pathsinv0.
    use BinCoproductArrowUnique.
    rewrite X. apply ZeroArrow_comp_right.
    rewrite X0. apply ZeroArrow_comp_right.
  Qed.

End BinCoproduct_zeroarrow.


(** Goal: lift coproducts from the target (pre)category to the functor (pre)category *)

Section def_functor_pointwise_coprod.

Variable C D : precategory.
Variable HD : BinCoproducts D.
Variable hsD : has_homsets D.

Section BinCoproduct_of_functors.

Variables F G : functor C D.

Local Notation "c ⊗ d" := (BinCoproductObject _ (HD c d))(at level 45).

Definition BinCoproduct_of_functors_ob (c : C) : D := F c ⊗ G c.

Definition BinCoproduct_of_functors_mor (c c' : C) (f : c --> c')
  : BinCoproduct_of_functors_ob c --> BinCoproduct_of_functors_ob c'
  := BinCoproductOfArrows _ _ _ (#F f) (#G f).

Definition BinCoproduct_of_functors_data : functor_data C D.
Proof.
  exists BinCoproduct_of_functors_ob.
  exact BinCoproduct_of_functors_mor.
Defined.

Lemma is_functor_BinCoproduct_of_functors_data : is_functor BinCoproduct_of_functors_data.
Proof.
  split; simpl; intros.
  - unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + unfold BinCoproduct_of_functors_mor.
      rewrite BinCoproductOfArrowsIn1.
      rewrite functor_id.
      apply id_left.
    + unfold BinCoproduct_of_functors_mor.
      rewrite BinCoproductOfArrowsIn2.
      rewrite functor_id.
      apply id_left.
  - unfold functor_compax, BinCoproduct_of_functors_mor;
    intros; simpl in *.
    unfold BinCoproduct_of_functors_mor.
    do 2 rewrite functor_comp.
    rewrite <- BinCoproductOfArrows_comp.
    apply idpath.
(* former proof:
    unfold BinCoproductOfArrows.
    apply pathsinv0.
    apply BinCoproductArrowUnique.
    + rewrite assoc. simpl in *.
      set (H:= BinCoproductIn1Commutes ).
      set (H2 := H D _ _ (HD (F a) (G a))).
      rewrite H2.
      rewrite <- assoc.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn1Commutes.
    + rewrite assoc.
      set (H:= BinCoproductIn2Commutes D _ _ (HD (F a) (G a))).
      rewrite H.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn2Commutes.
*)
Qed.

Definition BinCoproduct_of_functors : functor C D :=
  tpair _ _ is_functor_BinCoproduct_of_functors_data.

Lemma BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors :
  BinCoproduct_of_functors_alt HD F G = BinCoproduct_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition coproduct_nat_trans_in1_data : Π c, F c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn1 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in1_data
  : is_nat_trans _ _ coproduct_nat_trans_in1_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in1_data.
  unfold BinCoproduct_of_functors. simpl.
  unfold BinCoproduct_of_functors_mor.
  assert (XX:= BinCoproductOfArrowsIn1).
  assert (X1 := XX _ (F c) (G c) (HD (F c) (G c))).
  assert (X2 := X1 _ _ (HD (F c') (G c'))).
  rewrite X2.
  apply idpath.
Qed.

Definition coproduct_nat_trans_in1 : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_in1_data.

Definition coproduct_nat_trans_in2_data : Π c, G c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn2 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in2_data
  : is_nat_trans _ _ coproduct_nat_trans_in2_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in2_data.
  unfold BinCoproduct_of_functors. simpl.
  unfold BinCoproduct_of_functors_mor.
  assert (XX:= BinCoproductOfArrowsIn2).
  assert (X1 := XX _ (F c) (G c) (HD (F c) (G c))).
  assert (X2 := X1 _ _ (HD (F c') (G c'))).
  rewrite X2.
  apply idpath.
Qed.

Definition coproduct_nat_trans_in2 : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_in2_data.


Section vertex.

(** The coproduct morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : F ⟶ A.
Variable g : G ⟶ A.

Definition coproduct_nat_trans_data : Π c, BinCoproduct_of_functors c --> A c.
Proof.
  intro c.
  apply BinCoproductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_coproduct_nat_trans_data : is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold BinCoproduct_of_functors_mor.
  unfold coproduct_nat_trans_data.
  simpl.
  set (XX:=precompWithBinCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  set (X2 := X1 _ _ (HD (F b) (G b))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=postcompWithBinCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition coproduct_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_data.

Lemma coproduct_nat_trans_In1Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in1 coproduct_nat_trans = f.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply BinCoproductIn1Commutes.
Qed.

Lemma coproduct_nat_trans_In2Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in2 coproduct_nat_trans = g.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply BinCoproductIn2Commutes.
Qed.

End vertex.


Lemma coproduct_nat_trans_univ_prop (A : [C, D, hsD])
  (f : (F : [C,D,hsD]) --> A) (g : (G : [C,D,hsD]) --> A) :
   Π
   t : Σ fg : (BinCoproduct_of_functors:[C,D,hsD]) --> A,
       (coproduct_nat_trans_in1 : (F:[C,D,hsD]) --> BinCoproduct_of_functors);; fg = f
      ×
       (coproduct_nat_trans_in2: (G : [C,D,hsD]) --> BinCoproduct_of_functors);; fg = g,
   t =
   tpair
     (λ fg : (BinCoproduct_of_functors:[C,D,hsD]) --> A,
      (coproduct_nat_trans_in1 : (F:[C,D,hsD]) --> BinCoproduct_of_functors);; fg = f
   ×
      (coproduct_nat_trans_in2 : (G:[C,D,hsD]) --> BinCoproduct_of_functors) ;; fg = g)
     (coproduct_nat_trans A f g)
     (dirprodpair (coproduct_nat_trans_In1Commutes A f g)
        (coproduct_nat_trans_In2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypeEquality.
  - intro.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply hsD.
  - simpl.
    apply nat_trans_eq.
    + apply hsD.
    + intro c.
      unfold coproduct_nat_trans.
      simpl.
      unfold coproduct_nat_trans_data.
      simpl.
      apply BinCoproductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.


Definition functor_precat_coproduct_cocone
  : BinCoproductCocone [C, D, hsD] F G.
Proof.
  simple refine (mk_BinCoproductCocone _ _ _ _ _ _ _ ).
  - apply BinCoproduct_of_functors.
  - apply coproduct_nat_trans_in1.
  - apply coproduct_nat_trans_in2.
  - simple refine (mk_isBinCoproductCocone _ _ _ _ _ _ _ _ ).
    + apply functor_category_has_homsets.
    + intros A f g.
     exists (tpair _ (coproduct_nat_trans A f g)
             (dirprodpair (coproduct_nat_trans_In1Commutes _ _ _ )
                          (coproduct_nat_trans_In2Commutes _ _ _ ))).
     simpl.
     apply coproduct_nat_trans_univ_prop.
Defined.

End BinCoproduct_of_functors.

Definition BinCoproducts_functor_precat : BinCoproducts [C, D, hsD].
Proof.
  intros F G.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.

Section option_functor.

Context {C : precategory} (CC : BinCoproducts C) (TC : Terminal C).
Let one : C := TerminalObject TC.

Definition option_functor : functor C C :=
  BinCoproduct_of_functors C C CC (constant_functor _ _ one) (functor_identity C).

End option_functor.

(** ** Construction of isBinCoproduct from an isomorphism to BinCoproduct. *)
Section BinCoproduct_from_iso.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Local Lemma iso_to_isBinCoproductCocone_comm {x y z : C} (BP : BinCoproductCocone C x y)
        (i : iso z (BinCoproductObject C BP)) (w : C) (f : x --> w) (g : y --> w) :
    (BinCoproductIn1 C BP ;; inv_from_iso i ;; (i ;; BinCoproductArrow C BP f g) = f)
      × (BinCoproductIn2 C BP ;; inv_from_iso i ;; (i ;; BinCoproductArrow C BP f g) = g).
  Proof.
    split.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinCoproductIn1Commutes.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinCoproductIn2Commutes.
  Qed.

  Local Lemma iso_to_isBinCoproductCocone_unique {x y z : C} (BP : BinCoproductCocone C x y)
        (i : iso z (BinCoproductObject C BP)) (w : C) (f : x --> w) (g : y --> w) (y0 : C ⟦ z, w ⟧)
        (T : (BinCoproductIn1 C BP ;; inv_from_iso i ;; y0 = f)
               × (BinCoproductIn2 C BP ;; inv_from_iso i ;; y0 = g)) :
    y0 = i ;; BinCoproductArrow C BP f g.
  Proof.
    apply (pre_comp_with_iso_is_inj C _ _ w (iso_inv_from_iso i) (pr2 (iso_inv_from_iso i))).
    rewrite assoc. cbn. rewrite (iso_after_iso_inv i). rewrite id_left.
    apply BinCoproductArrowUnique.
    - rewrite assoc. apply (dirprod_pr1 T).
    - rewrite assoc. apply (dirprod_pr2 T).
  Qed.

  Lemma iso_to_isBinCoproductCocone {x y z : C} (BP : BinCoproductCocone C x y)
        (i : iso z (BinCoproductObject C BP)) :
    isBinCoproductCocone C _ _ z
                         ((BinCoproductIn1 C BP) ;; (iso_inv_from_iso i))
                         ((BinCoproductIn2 C BP) ;; (iso_inv_from_iso i)).
  Proof.
    intros w f g.
    use unique_exists.
    (* The arrow *)
    - exact (i ;; (BinCoproductArrow C BP f g)).
    (* Commutativity *)
    - exact (iso_to_isBinCoproductCocone_comm BP i w f g).
    (* Equality on equalities of morphisms. *)
    - intros y0. apply isapropdirprod. apply hs. apply hs.
    (* Uniqueness *)
    - intros y0 T. exact (iso_to_isBinCoproductCocone_unique BP i w f g y0 T).
  Defined.
  Opaque iso_to_isBinCoproductCocone.

  Definition iso_to_BinCoproductCocone {x y z : C} (BP : BinCoproductCocone C x y)
             (i : iso z (BinCoproductObject C BP)) :
    BinCoproductCocone C x y := mk_BinCoproductCocone
                                  C _ _ z
                                  ((BinCoproductIn1 C BP) ;; (iso_inv_from_iso i))
                                  ((BinCoproductIn2 C BP) ;; (iso_inv_from_iso i))
                                  (iso_to_isBinCoproductCocone BP i).

End BinCoproduct_from_iso.
