(** ******************************************

Direct implementation of binary coproducts togther with:

- Proof that binary coproduct(cocone) is a property in a univalent_category ([isaprop_BinCoproductCocone])
- Specialized versions of beta rules for coproducts
- Definition of binary coproduct functor ([bincoproduct_functor])
- Definition of a coproduct structure on a functor category by taking pointwise coproducts in the
  target category ([BinCoproducts_functor_precat])
- Definition of the option functor ([option_functor])
- Binary coproducts from colimits ([BinCoproducts_from_Colims])
- Equivalent universal property: (A --> C) × (B --> C) ≃ (A + B --> C)

Written by Benedikt Ahrens, March 2015
Extended by Anders Mörtberg and Tomi Pannila, 2016
Extended by Langston Barrett (@siddharthist), 2018

*********************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.

Local Open Scope cat.

(** * Definition of binary coproduct of objects in a precategory *)
Section coproduct_def.

Variable C : category.

Definition isBinCoproduct (a b co : C) (ia : a --> co) (ib : b --> co) :=
  ∏ (c : C) (f : a --> c) (g : b --> c),
  ∃! (fg : co --> c), (ia · fg = f) × (ib · fg = g).

Lemma isaprop_isBinCoproduct {a b co : C} {ia : a --> co} {ib : b --> co} :
  isaprop (isBinCoproduct a b co ia ib).
Proof.
  apply impred_isaprop. intros t.
  apply impred_isaprop. intros t0.
  apply impred_isaprop. intros g.
  apply isapropiscontr.
Qed.

Definition BinCoproduct (a b : C) :=
   ∑ coiaib : (∑ co : C, a --> co × b --> co),
      isBinCoproduct a b (pr1 coiaib) (pr1 (pr2 coiaib)) (pr2 (pr2 coiaib)).

Definition BinCoproducts := ∏ (a b : C), BinCoproduct a b.
Definition hasBinCoproducts := ∏ (a b : C), ∥ BinCoproduct a b ∥.

Definition BinCoproductObject {a b : C} (CC : BinCoproduct a b) : C := pr1 (pr1 CC).
Coercion BinCoproductObject : BinCoproduct >-> ob.
Definition BinCoproductIn1 {a b : C} (CC : BinCoproduct a b): a --> BinCoproductObject CC :=
  pr1 (pr2 (pr1 CC)).
Definition BinCoproductIn2 {a b : C} (CC : BinCoproduct a b) : b --> BinCoproductObject CC :=
   pr2 (pr2 (pr1 CC)).

Definition isBinCoproduct_BinCoproduct {a b : C} (CC : BinCoproduct a b) :
   isBinCoproduct a b  (BinCoproductObject CC) (BinCoproductIn1 CC) (BinCoproductIn2 CC).
Proof.
  exact (pr2 CC).
Defined.

Definition BinCoproductArrow {a b : C} (CC : BinCoproduct a b)
  {c : C} (f : a --> c) (g : b --> c) : BinCoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isBinCoproduct_BinCoproduct CC _ f g))).
Defined.

Lemma BinCoproductIn1Commutes (a b : C) (CC : BinCoproduct a b):
     ∏ (c : C) (f : a --> c) g, BinCoproductIn1 CC · BinCoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (pr1 (pr2 (pr1 (isBinCoproduct_BinCoproduct CC _ f g)))).
Qed.

Lemma BinCoproductIn2Commutes (a b : C) (CC : BinCoproduct a b):
     ∏ (c : C) (f : a --> c) g, BinCoproductIn2 CC · BinCoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (pr2 (pr2 (pr1 (isBinCoproduct_BinCoproduct CC _ f g)))).
Qed.

Lemma BinCoproductArrowUnique (a b : C) (CC : BinCoproduct a b) (x : C)
    (f : a --> x) (g : b --> x) (k : BinCoproductObject CC --> x) :
    BinCoproductIn1 CC · k = f → BinCoproductIn2 CC · k = g →
      k = BinCoproductArrow CC f g.
Proof.
  intros H1 H2.
  set (H := tpair (λ h, dirprod _ _ ) k (make_dirprod H1 H2)).
  set (H' := (pr2 (isBinCoproduct_BinCoproduct CC _ f g)) H).
  apply (base_paths _ _ H').
Qed.

Lemma BinCoproductArrowsEq (c d : C) (CC : BinCoproduct c d) (x : C)
      (k1 k2 : BinCoproductObject CC --> x) :
  BinCoproductIn1 CC · k1 = BinCoproductIn1 CC · k2 ->
  BinCoproductIn2 CC · k1 = BinCoproductIn2 CC · k2 ->
  k1 = k2.
Proof.
  intros H1 H2.
  set (p1 := BinCoproductIn1 CC · k1).
  set (p2 := BinCoproductIn2 CC · k1).
  rewrite (BinCoproductArrowUnique _ _ CC _ p1 p2 k1).
  apply pathsinv0.
  apply BinCoproductArrowUnique.
  unfold p1. apply pathsinv0. apply H1.
  unfold p2. apply pathsinv0. apply H2.
  apply idpath. apply idpath.
Qed.

Lemma BinCoproductArrowEta (a b : C) (CC : BinCoproduct a b) (x : C)
    (f : BinCoproductObject CC --> x) :
    f = BinCoproductArrow CC (BinCoproductIn1 CC · f) (BinCoproductIn2 CC · f).
Proof.
  apply BinCoproductArrowUnique;
  apply idpath.
Qed.


Definition BinCoproductOfArrows {a b : C} (CCab : BinCoproduct a b) {c d : C}
    (CCcd : BinCoproduct c d) (f : a --> c) (g : b --> d) :
          BinCoproductObject CCab --> BinCoproductObject CCcd :=
    BinCoproductArrow CCab (f · BinCoproductIn1 CCcd) (g · BinCoproductIn2 CCcd).

Lemma BinCoproductOfArrowsIn1 {a b : C} (CCab : BinCoproduct a b) {c d : C}
    (CCcd : BinCoproduct c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn1 CCab · BinCoproductOfArrows CCab CCcd f g = f · BinCoproductIn1 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductOfArrowsIn2 {a b : C} (CCab : BinCoproduct a b) {c d : C}
    (CCcd : BinCoproduct c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn2 CCab · BinCoproductOfArrows CCab CCcd f g = g · BinCoproductIn2 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn2Commutes.
Qed.


Definition make_BinCoproduct (a b : C) :
  ∏ (c : C) (f : a --> c) (g : b --> c),
   isBinCoproduct _ _ _ f g →  BinCoproduct a b.
Proof.
  intros.
  use tpair.
  - exists c.
    exists f.
    exact g.
  - apply X.
Defined.

Definition make_isBinCoproduct (hsC : has_homsets C) (a b co : C)
   (ia : a --> co) (ib : b --> co) :
   (∏ (c : C) (f : a --> c) (g : b --> c),
    ∃! k : C ⟦co, c⟧,
      ia · k = f ×
      ib · k = g)
   → isBinCoproduct a b co ia ib.
Proof.
  intros H c cc.
  apply H.
Defined.



Lemma precompWithBinCoproductArrow {a b : C} (CCab : BinCoproduct a b) {c d : C}
    (CCcd : BinCoproduct c d) (f : a --> c) (g : b --> d)
    {x : C} (k : c --> x) (h : d --> x) :
        BinCoproductOfArrows CCab CCcd f g · BinCoproductArrow CCcd k h =
         BinCoproductArrow CCab (f · k) (g · h).
Proof.
  apply BinCoproductArrowUnique.
  - rewrite assoc. rewrite BinCoproductOfArrowsIn1.
    rewrite <- assoc, BinCoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, BinCoproductOfArrowsIn2.
    rewrite <- assoc, BinCoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithBinCoproductArrow {a b : C} (CCab : BinCoproduct a b) {c : C}
    (f : a --> c) (g : b --> c) {x : C} (k : c --> x)  :
       BinCoproductArrow CCab f g · k = BinCoproductArrow CCab (f · k) (g · k).
Proof.
  apply BinCoproductArrowUnique.
  -  rewrite assoc, BinCoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, BinCoproductIn2Commutes;
     apply idpath.
Qed.



Lemma BinCoproduct_endo_is_identity {a b : C} (CC : BinCoproduct a b)
  (k : BinCoproductObject CC --> BinCoproductObject CC)
  (H1 : BinCoproductIn1 CC · k = BinCoproductIn1 CC)
  (H2 : BinCoproductIn2 CC · k = BinCoproductIn2 CC)
  : identity _ = k.
Proof.
  set (H' := pr2 CC _ (BinCoproductIn1 CC) (BinCoproductIn2 CC) ); simpl in *.
  set (X := (∑ fg : pr1 (pr1 CC) --> BinCoproductObject CC,
          pr1 (pr2 (pr1 CC))· fg = BinCoproductIn1 CC
          × pr2 (pr2 (pr1 CC))· fg = BinCoproductIn2 CC)).
  set (t1 := tpair _ k (make_dirprod H1 H2) : X).
  set (t2 := tpair _ (identity _ ) (make_dirprod (id_right _ ) (id_right _ ) ) : X).
  assert (X' : t1 = t2).
  { apply proofirrelevancecontr. apply H'. }
  apply pathsinv0.
  apply (base_paths _ _ X').
Defined.

Definition from_BinCoproduct_to_BinCoproduct {a b : C} (CC CC' : BinCoproduct a b)
  : BinCoproductObject CC --> BinCoproductObject CC'.
Proof.
  apply (BinCoproductArrow CC  (BinCoproductIn1 _ ) (BinCoproductIn2 _ )).
Defined.


Lemma is_z_iso_from_BinCoproduct_to_BinCoproduct {a b : C} (CC CC' : BinCoproduct a b)
  : is_z_isomorphism (from_BinCoproduct_to_BinCoproduct CC CC').
Proof.
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

Definition z_iso_from_BinCoproduct_to_BinCoproduct {a b : C} (CC CC' : BinCoproduct a b)
  : z_iso (BinCoproductObject CC) (BinCoproductObject CC')
  := _ ,, is_z_iso_from_BinCoproduct_to_BinCoproduct CC CC'.


End coproduct_def.

Arguments BinCoproduct [_] _ _.
Arguments BinCoproductObject [_ _ _] _ .
Arguments BinCoproductArrow [_ _ _] _ [_] _ _.
Arguments BinCoproductIn1 [_ _ _] _.
Arguments BinCoproductIn2 [_ _ _] _.

(** * Proof that coproducts are unique when the precategory [C] is a univalent_category *)

Section coproduct_unique.

  Variable C : category.
Hypothesis H : is_univalent C.

Variables a b : C.

(* TODO: upstream *)
Lemma transportf_isotoid' (c d d': C) (p : z_iso d d') (f : c --> d) :
  transportf (λ a0 : C, c --> a0) (isotoid C H p) f = f · p .
Proof.
  rewrite <- idtoiso_postcompose.
  rewrite idtoiso_isotoid.
  apply idpath.
Defined.

Lemma isaprop_BinCoproduct : isaprop (BinCoproduct a b).
Proof.
  apply invproofirrelevance.
  intros CC CC'.
  apply subtypePath.
  + intros.
    intro. do 3 (apply impred; intro); apply isapropiscontr.
  + apply (total2_paths_f (isotoid _ H (z_iso_from_BinCoproduct_to_BinCoproduct _ CC CC'))).
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



Section BinCoproducts.

Variable C : category.
Variable CC : BinCoproducts C.
Variables a b c d x y : C.

Lemma BinCoproductArrow_eq_cor (f f' : BinCoproductObject (CC a b) --> c)
  : BinCoproductIn1 _· f = BinCoproductIn1 _· f' → BinCoproductIn2 _· f = BinCoproductIn2 _· f' →
      f = f' .
Proof.
  intros Hyp1 Hyp2.
  rewrite (BinCoproductArrowEta _ _ _ _ _ f).
  rewrite (BinCoproductArrowEta _ _ _ _ _ f').
  apply maponpaths_12; assumption.
Qed.

(** specialized versions of beta rules for coproducts *)
(* all the following lemmas for manipulation of the hypothesis
Lemma BinCoproductIn1Commutes_left (f : a --> c)(g : b --> c)(h : a --> c):
  BinCoproductIn1 C (CC _ _) · BinCoproductArrow C (CC _ _) f g = h -> f = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right (f : a --> c)(g : b --> c)(h : a --> c):
  h = BinCoproductIn1 C (CC _ _) · BinCoproductArrow C (CC _ _) f g -> h = f.
Proof.
  intro Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_left (f : a --> c)(g : b --> c)(h : b --> c):
  BinCoproductIn2 C (CC _ _) · BinCoproductArrow C (CC _ _) f g = h -> g = h.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right (f : a --> c)(g : b --> c)(h : b --> c):
  h = BinCoproductIn2 C (CC _ _) · BinCoproductArrow C (CC _ _) f g -> h = g.
Proof.
  intro Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d):
  BinCoproductIn1 C (CC _ _) · (BinCoproductArrow C (CC _ _) f g · h) = h' -> f · h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn1Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : a --> d):
  h' = BinCoproductIn1 C (CC _ _) · (BinCoproductArrow C (CC _ _) f g · h)  -> h' = f · h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d):
  BinCoproductIn2 C (CC _ _) · (BinCoproductArrow C (CC _ _) f g · h) = h' -> g · h = h'.
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite BinCoproductIn2Commutes in Hyp.
  exact Hyp.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx (f : a --> c)(g : b --> c)(h : c --> d)(h' : b --> d):
  h' = BinCoproductIn2 C (CC _ _) · (BinCoproductArrow C (CC _ _) f g · h)  -> h' = g · h.
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (BinCoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma BinCoproductIn2Commutes_right_in_double_ctx (g0 : x --> b)(f : a --> c)(g : b --> c)
 (h : c --> d)(h' : x --> d):
  h' = g0 · BinCoproductIn2 C (CC _ _) · (BinCoproductArrow C (CC _ _) f g · h)  ->
  h' = g0 · g · h.
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
  h = f -> h = BinCoproductIn1 (CC _ _) · BinCoproductArrow (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_right_dir (f : a --> c) (g : b --> c) (h : b --> c) :
  h = g -> h = BinCoproductIn2 (CC _ _) · BinCoproductArrow (CC _ _) f g.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_right_in_ctx_dir (f : a --> c) (g : b --> c) (h : c --> d) (h' : a --> d) :
  h' = f · h -> h' = BinCoproductIn1 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_right_in_ctx_dir (f : a --> c) (g : b --> c) (h : c --> d) (h' : b --> d) :
  h' = g · h -> h' = BinCoproductIn2 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h).
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_left_dir (f : a --> c) (g : b --> c) (h : a --> c) :
  f = h -> BinCoproductIn1 (CC _ _) · BinCoproductArrow (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductIn2Commutes_left_dir (f : a --> c) (g : b --> c) (h : b --> c) :
  g = h -> BinCoproductIn2 (CC _ _) · BinCoproductArrow (CC _ _) f g = h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply BinCoproductIn2Commutes.
Qed.

Lemma BinCoproductIn1Commutes_left_in_ctx_dir (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : a --> d) :
  f · h = h' -> BinCoproductIn1 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn1Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn2Commutes_left_in_ctx_dir (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : b --> d) :
  g · h = h' -> BinCoproductIn2 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h) = h'.
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  apply idpath.
Qed.

Lemma BinCoproductIn1Commutes_right_in_double_ctx_dir (g0 : x --> a) (f : a --> c) (g : b --> c)
  (h : c --> d) (h' : x --> d) : h' = g0 · f · h ->
  h' = g0 · BinCoproductIn1 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h).
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
  (h : c --> d) (h' : x --> d) : h' = g0 · g · h ->
  h' = g0 · BinCoproductIn2 (CC _ _) · (BinCoproductArrow (CC _ _) f g · h).
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
Lemma id_left_to_the_right (C': precategory)(a b : C')(f h : C' ⟦ a, b ⟧): h = f -> h = identity a· f.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, id_left.
Qed.

Lemma id_left_to_the_right_in_ctx (C': precategory)(a b c: C')(f : C' ⟦ a, b ⟧)(g : C' ⟦ b, c ⟧)
  (h : C' ⟦ a, c ⟧): h = f · g -> h = identity a · f · g.
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite id_left.
  apply idpath.
Qed.


Lemma assoc_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f· g· h -> res = f· (g· h).
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, assoc.
Qed.

Lemma assoc_back_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f· (g· h) -> res = f· g· h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply assoc.
Qed.
*)

Definition BinCoproductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
  : BinCoproductOfArrows _ (CC a b) (CC c d) f f' ·
    BinCoproductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    BinCoproductOfArrows _ (CC _ _) (CC _ _)(f · g) (f' · g').
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

Lemma precompWithBinCoproductArrow_eq  (CCab : BinCoproduct a b)
    (CCcd : BinCoproduct c d) (f : a --> c) (g : b --> d)
     (k : c --> x) (h : d --> x) (fk : a --> x) (gh : b --> x):
      fk = f · k → gh = g · h →
        BinCoproductOfArrows _ CCab CCcd f g · BinCoproductArrow CCcd k h =
         BinCoproductArrow CCab (fk) (gh).
Proof.
  intros H H'.
  rewrite H.
  rewrite H'.
  apply precompWithBinCoproductArrow.
Qed.

End BinCoproducts.

(** * Binary coproducts from colimits *)
Section BinCoproducts_from_Colims.

Variables (C : category).

Definition two_graph : graph := (bool,,λ _ _,empty).

Definition bincoproduct_diagram (a b : C) : diagram two_graph C.
Proof.
exists (λ x : bool, if x then a else b).
abstract (intros u v F; induction F).
Defined.

Definition BinCoprod {a b c : C} (ac : a --> c) (bc : b --> c) :
   cocone (bincoproduct_diagram a b) c.
Proof.
use make_cocone; simpl.
+ intros x; induction x; assumption.
+ abstract (intros x y e; destruct e).
Defined.

Lemma BinCoproducts_from_Colims : Colims_of_shape two_graph C -> BinCoproducts C.
Proof.
intros H a b.
set (CC := H (bincoproduct_diagram a b)); simpl.
use make_BinCoproduct.
+ apply (colim CC).
+ apply (colimIn CC true).
+ apply (colimIn CC false).
+ apply (make_isBinCoproduct _ C); simpl; intros c f g.
  use unique_exists; simpl.
  - apply colimArrow, (BinCoprod f g).
  - abstract (split;
      [ apply (colimArrowCommutes CC c (BinCoprod f g) true)
      | apply (colimArrowCommutes CC c (BinCoprod f g) false) ]).
  - abstract (intros h; apply isapropdirprod; apply C).
  - abstract (now intros h [H1 H2]; apply colimArrowUnique; intro x; induction x).
Defined.

End BinCoproducts_from_Colims.

(** * Coproducts over bool from binary coproducts *)
Section CoproductsBool.

Lemma CoproductsBool {C : category}
  (HC : BinCoproducts C) : Coproducts bool C.
Proof.
intros H.
use make_Coproduct.
- apply (HC (H true) (H false)).
- induction i; apply (pr1 (HC (H true) (H false))).
- use (make_isCoproduct _ _ C); intros c f.
  induction (pr2 (HC (H true) (H false)) c (f true) (f false)) as [[x1 [x2 x3]] x4].
  use unique_exists.
  + apply x1.
  + cbn; induction i; assumption.
  + intros x; apply impred; intros; apply C.
  + intros h1 h2.
    apply (maponpaths pr1 (x4 (h1,,(h2 true,,h2 false)))).
Defined.

End CoproductsBool.

Section functors.

Definition bincoproduct_functor_data {C : category} (PC : BinCoproducts C) :
  functor_data (category_binproduct C C) C.
Proof.
use tpair.
- intros p.
  apply (BinCoproductObject (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (BinCoproductOfArrows _ (PC (pr1 p) (pr2 p))
                             (PC (pr1 q) (pr2 q)) (pr1 f) (pr2 f)).
Defined.

(* The binary coproduct functor: C * C -> C *)

Lemma is_functor_bincoproduct_functor_data {C : category} (PC : BinCoproducts C)
  : is_functor (bincoproduct_functor_data PC).
Proof.
  split.
  - intro x; simpl; apply pathsinv0.
    use BinCoproduct_endo_is_identity.
    + now rewrite BinCoproductOfArrowsIn1, id_left.
    + now rewrite BinCoproductOfArrowsIn2, id_left.
  -  now intros x y z f g; simpl; rewrite BinCoproductOfArrows_comp.
Qed.

Definition bincoproduct_functor {C : category} (PC : BinCoproducts C)
  : functor (category_binproduct C C) C
  := make_functor _ (is_functor_bincoproduct_functor_data PC).

(* Defines the copropuct of two functors *)
Definition BinCoproduct_of_functors_alt {C D : category}
           (HD : BinCoproducts D) (F G : C ⟶ D) : C ⟶ D :=
    tuple_functor (λ b, bool_rect (λ _, C ⟶ D) F G b) ∙
    coproduct_functor bool (CoproductsBool HD).

(* Defines the copropuct of two functors by:
    x -> (x,x) -> (F x,G x) -> F x + G x

  For a direct and equal definition see FunctorsPointwiseBinCoproduct.v

  Above is a slightly simpler definition
*)
Definition BinCoproduct_of_functors_alt2 {C D : category}
  (HD : BinCoproducts D) (F G : functor C D) : functor C D :=
    bindelta_functor C ∙ (pair_functor F G ∙ bincoproduct_functor HD).

End functors.

(** In the following section we show that if the morphism to components are
    zero, then the unique morphism factoring through the bincoproduct is the
    zero morphism. *)
Section BinCoproduct_zeroarrow.

  Variable C : category.
  Variable Z : Zero C.

  Lemma BinCoproductArrowZero {x y z: C} {BP : BinCoproduct x y} (f : x --> z) (g : y --> z) :
    f = ZeroArrow Z _ _ -> g = ZeroArrow Z _ _ -> BinCoproductArrow BP f g = ZeroArrow Z _ _ .
  Proof.
    intros X X0. apply pathsinv0.
    use BinCoproductArrowUnique.
    rewrite X. apply ZeroArrow_comp_right.
    rewrite X0. apply ZeroArrow_comp_right.
  Qed.

End BinCoproduct_zeroarrow.


(** Goal: lift coproducts from the target (pre)category to the functor (pre)category *)

Section def_functor_pointwise_coprod.

Variable C D : category.
Variable HD : BinCoproducts D.

Section BinCoproduct_of_functors.

Variables F G : functor C D.

Local Notation "c ⊗ d" := (BinCoproductObject (HD c d)).

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

Lemma BinCoproduct_of_functors_alt2_eq_BinCoproduct_of_functors :
  BinCoproduct_of_functors_alt2 HD F G = BinCoproduct_of_functors.
Proof.
now apply (functor_eq _ _ D).
Defined.

Lemma BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors :
  BinCoproduct_of_functors_alt HD F G = BinCoproduct_of_functors.
Proof.
now apply (functor_eq _ _ D).
Defined.

Lemma BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors_alt2 :
  BinCoproduct_of_functors_alt  HD F G = BinCoproduct_of_functors_alt2 HD F G.
Proof.
now apply (functor_eq _ _ D).
Defined.

Definition coproduct_nat_trans_in1_data : ∏ c, F c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn1 (HD (F c) (G c)).

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

Definition coproduct_nat_trans_in2_data : ∏ c, G c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn2 (HD (F c) (G c)).

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
Variable f : F ⟹ A.
Variable g : G ⟹ A.

Definition coproduct_nat_trans_data : ∏ c, BinCoproduct_of_functors c --> A c.
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
  - apply D.
  - intro c; simpl.
    apply BinCoproductIn1Commutes.
Qed.

Lemma coproduct_nat_trans_In2Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in2 coproduct_nat_trans = g.
Proof.
  apply nat_trans_eq.
  - apply D.
  - intro c; simpl.
    apply BinCoproductIn2Commutes.
Qed.

End vertex.


Lemma coproduct_nat_trans_univ_prop (A : [C, D])
  (f : (F : [C,D]) --> A) (g : (G : [C,D]) --> A) :
   ∏
   t : ∑ fg : (BinCoproduct_of_functors:[C,D]) --> A,
       (coproduct_nat_trans_in1 : (F:[C,D]) --> BinCoproduct_of_functors)· fg = f
      ×
       (coproduct_nat_trans_in2: (G : [C,D]) --> BinCoproduct_of_functors)· fg = g,
   t =
   tpair
     (λ fg : (BinCoproduct_of_functors:[C,D]) --> A,
      (coproduct_nat_trans_in1 : (F:[C,D]) --> BinCoproduct_of_functors)· fg = f
   ×
      (coproduct_nat_trans_in2 : (G:[C,D]) --> BinCoproduct_of_functors) · fg = g)
     (coproduct_nat_trans A f g)
     (make_dirprod (coproduct_nat_trans_In1Commutes A f g)
        (coproduct_nat_trans_In2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypePath.
  - intro.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply D.
  - simpl.
    apply nat_trans_eq.
    + apply D.
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
  : @BinCoproduct [C, D] F G.
Proof.
  use make_BinCoproduct.
  - apply BinCoproduct_of_functors.
  - apply coproduct_nat_trans_in1.
  - apply coproduct_nat_trans_in2.
  - use make_isBinCoproduct.
    + apply functor_category_has_homsets.
    + intros A f g.
     exists (tpair _ (coproduct_nat_trans A f g)
             (make_dirprod (coproduct_nat_trans_In1Commutes _ _ _ )
                          (coproduct_nat_trans_In2Commutes _ _ _ ))).
     simpl.
     apply coproduct_nat_trans_univ_prop.
Defined.

End BinCoproduct_of_functors.

Definition BinCoproducts_functor_precat : BinCoproducts [C, D].
Proof.
  intros F G.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.


Section generalized_option_functors.

Context {C : category} (CC : BinCoproducts C).

(* The functors "a + _" and "_ + a" *)
Definition constcoprod_functor1 (a : C) : functor C C :=
  BinCoproduct_of_functors C C CC (constant_functor C C a) (functor_identity C).

Definition constcoprod_functor2 (a : C) : functor C C :=
  BinCoproduct_of_functors C C CC (functor_identity C) (constant_functor C C a).


Section option_functor.

Context (TC : Terminal C).
Let one : C := TerminalObject TC.

Definition option_functor : functor C C :=
  constcoprod_functor1 one.

End option_functor.

End generalized_option_functors.

(** ** Construction of isBinCoproduct from an isomorphism to BinCoproduct. *)
Section BinCoproduct_from_z_iso.

  Variable C : category.

  Local Lemma z_iso_to_isBinCoproduct_comm {x y z : C} (BP : BinCoproduct x y)
        (i : z_iso z (BinCoproductObject BP)) (w : C) (f : x --> w) (g : y --> w) :
    (BinCoproductIn1 BP · inv_from_z_iso i · (i · BinCoproductArrow BP f g) = f)
      × (BinCoproductIn2 BP · inv_from_z_iso i · (i · BinCoproductArrow BP f g) = g).
  Proof.
    split.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (z_iso_after_z_iso_inv i). rewrite id_left.
      apply BinCoproductIn1Commutes.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (z_iso_after_z_iso_inv i). rewrite id_left.
      apply BinCoproductIn2Commutes.
  Qed.

  Local Lemma z_iso_to_isBinCoproduct_unique {x y z : C} (BP : BinCoproduct x y)
        (i : z_iso z (BinCoproductObject BP)) (w : C) (f : x --> w) (g : y --> w) (y0 : C ⟦ z, w ⟧)
        (T : (BinCoproductIn1 BP · inv_from_z_iso i · y0 = f)
               × (BinCoproductIn2 BP · inv_from_z_iso i · y0 = g)) :
    y0 = i · BinCoproductArrow BP f g.
  Proof.
    apply (pre_comp_with_z_iso_is_inj (z_iso_inv_from_z_iso i)).
    rewrite assoc. cbn. rewrite (z_iso_after_z_iso_inv i). rewrite id_left.
    apply BinCoproductArrowUnique.
    - rewrite assoc. apply (dirprod_pr1 T).
    - rewrite assoc. apply (dirprod_pr2 T).
  Qed.

  Lemma z_iso_to_isBinCoproduct {x y z : C} (BP : BinCoproduct x y)
        (i : z_iso z (BinCoproductObject BP)) :
    isBinCoproduct C _ _ z
                         ((BinCoproductIn1 BP) · (z_iso_inv_from_z_iso i))
                         ((BinCoproductIn2 BP) · (z_iso_inv_from_z_iso i)).
  Proof.
    intros w f g.
    use unique_exists.
    (* The arrow *)
    - exact (i · (BinCoproductArrow BP f g)).
    (* Commutativity *)
    - exact (z_iso_to_isBinCoproduct_comm BP i w f g).
    (* Equality on equalities of morphisms. *)
    - intros y0. apply isapropdirprod. apply C. apply C.
    (* Uniqueness *)
    - intros y0 T. exact (z_iso_to_isBinCoproduct_unique BP i w f g y0 T).
  Defined.
  Opaque z_iso_to_isBinCoproduct.

  Definition z_iso_to_BinCoproduct {x y z : C} (BP : BinCoproduct x y)
             (i : z_iso z (BinCoproductObject BP)) :
    BinCoproduct x y := make_BinCoproduct
                                  C _ _ z
                                  ((BinCoproductIn1 BP) · (z_iso_inv_from_z_iso i))
                                  ((BinCoproductIn2 BP) · (z_iso_inv_from_z_iso i))
                                  (z_iso_to_isBinCoproduct BP i).

End BinCoproduct_from_z_iso.

(** Equivalent universal property: (A --> C) × (B --> C) ≃ (A + B --> C)

 Compare to [weqfunfromcoprodtoprod].
 *)

Section EquivalentDefinition.
  Context {C : category} {a b co : ob C} (i1 : a --> co) (i2 : b --> co) .

  Definition precomp_with_injections (c : ob C) (f : co --> c) : (a --> c) × (b --> c) :=
    make_dirprod (i1 · f)  (i2 · f).

  Definition isBinCoproduct' : UU :=
    ∏ c : ob C, isweq (precomp_with_injections c).

  Definition isBinCoproduct'_weq (is : isBinCoproduct') :
    ∏ c, (co --> c) ≃ (a --> c) × (b --> c) :=
    λ a, make_weq (precomp_with_injections a) (is a).

  Lemma isBinCoproduct'_to_isBinCoproduct :
    isBinCoproduct' -> isBinCoproduct _ _ _ co i1 i2.
  Proof.
    intros isBCP' ? f g.
    apply (@iscontrweqf (hfiber (isBinCoproduct'_weq isBCP' _)
                                (make_dirprod f g))).
    - use weqfibtototal; intro; cbn.
      unfold precomp_with_injections.
      apply pathsdirprodweq.
    - apply weqproperty.
  Defined.

  Lemma isBinCoproduct_to_isBinCoproduct' :
    isBinCoproduct _ _ _ co i1 i2 -> isBinCoproduct'.
  Proof.
    intros isBCP ? fg.
    unfold hfiber, precomp_with_injections.
    apply (@iscontrweqf (∑ u : C ⟦ co, c ⟧, i1 · u = pr1 fg × i2 · u = pr2 fg)).
    - use weqfibtototal; intros to_prod; cbn.
      apply invweq, pathsdirprodweq.
    - exact (isBCP c (pr1 fg) (pr2 fg)). (* apply universal property *)
  Defined.

  (* TODO: prove that [isBinCoproduct'_to_isBinCoproduct] is an equivalence *)

End EquivalentDefinition.

(** Match non-implicit arguments of [isBinCoproduct] *)
Arguments isBinCoproduct' _ _ _ _ _ : clear implicits.
