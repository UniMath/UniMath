(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :

Precomposition with a full and
           essentially surjective functor yields
           a full and faithful, i.e. a fully faithful,
           functor



************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Local Open Scope cat.

Ltac simp_rew lem := let H:=fresh in
     assert (H:= lem); simpl in *; rewrite H; clear H.
Ltac simp_rerew lem := let H:=fresh in
     assert (H:= lem); simpl in *; rewrite <- H; clear H.


Local Notation "G 'O' F" := (functor_compose _ _ _ F G : functor _ _ ) (at level 25).

Section pre_composition.

(** Section variables *)

Variables A B C : precategory.
Variable hsB: has_homsets B.
Variable hsC: has_homsets C.
Variable H : functor A B.

(** * Precomposition with an essentially surjective functor is faithful. *)

Lemma pre_composition_with_ess_surj_is_faithful (p : essentially_surjective H) :
           faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  intros F G.
  apply isinclbetweensets.
  - apply isaset_nat_trans. apply hsC.
  - apply isaset_nat_trans. apply hsC.
  - simpl in *.
    intros gamma delta ex.
    apply nat_trans_eq.
    + apply hsC.
    + intro b.
      apply (p b (make_hProp _ (hsC _ _ _ _))).
      intro t; induction t as [a f]; simpl.
      apply (pre_comp_with_iso_is_inj _ _ _ _ (# F f)
         (functor_on_iso_is_iso _ _ _ _ _ f)).
      rewrite 2 nat_trans_ax.
      apply cancel_postcomposition.
      apply (nat_trans_eq_pointwise ex a).
Defined.


(** * Precomposition with an essentially surjective and full functor is full *)

Section precomp_with_ess_surj_full_functor_is_full.

Hypothesis p : essentially_surjective H.
Hypothesis Hf : full H.


(** We prove that [_ O H] yields a full functor. *)

Section full.

Variables F G : functor B C.

(** We have to show that for [F] and [G], the map
     [(_ O H) (F,G) : (F --> G) -> (F O H --> G O H)]  is surjective. *)

(** Fixing a [gamma], we produce its preimage. *)

Variable gamma : nat_trans
     (functor_composite H F)
     (functor_composite H G).


Lemma iscontr_aux_space (b : B) :
   iscontr (total2 (fun g : F b --> G b =>
      ∏ a : A, ∏ f : iso (H a) b,
           g = functor_on_iso F (iso_inv_from_iso f) · gamma a · #G f)).
Proof.
  apply (p b (make_hProp _ (isapropiscontr _))).
  intro t; induction t as [anot h]; simpl.
  set (g := functor_on_iso F (iso_inv_from_iso h) · gamma anot · #G h).
  assert (gp : ∏ (a : A) (f : iso (H a) b),
                 g = #F (inv_from_iso f) · gamma a · #G f).
  - intros a f.
    apply (Hf _ _ (h · inv_from_iso f) (make_hProp _ (hsC _ _ _ _))).
    intro sur.
    simpl.
    unfold g.
    rewrite functor_on_iso_inv; simpl.
    rewrite <- assoc.
    apply iso_inv_on_right.
    rewrite 2 assoc.
    simpl.
    rewrite <- functor_comp.
    rewrite <- (pr2 sur).
    simp_rew (nat_trans_ax gamma).
    rewrite (pr2 sur).
    rewrite <- assoc.
    apply cancel_precomposition.
    rewrite <- functor_comp.
    apply maponpaths.
    rewrite <- assoc.
    rewrite iso_after_iso_inv.
    apply pathsinv0, id_right.
  - exists (g,, gp).
    intro t; induction t as [g' gp'].
    apply subtypePath.
    { intro; do 2 (apply impred; intro).
      apply hsC. }
    simpl.
    rewrite (gp anot h).
    rewrite (gp' anot h).
    apply idpath.
Defined.

Definition pdelta : ∏ b : B, F b --> G b :=
         λ b, pr1 (pr1 (iscontr_aux_space b)).

Lemma is_nat_trans_pdelta :
     is_nat_trans F G pdelta.
Proof.
  intros b b' f.
  apply (p b (make_hProp _ (hsC _ _ _ _) )).
  intro t; induction t as [a h]; simpl.
  apply (p b' (make_hProp _ (hsC _ _ _ _) )).
  intro t; induction t as [a' h']; simpl.
  unfold pdelta.
  rewrite (pr2 ((pr1 (iscontr_aux_space b))) a h).
  rewrite (pr2 ((pr1 (iscontr_aux_space b'))) a' h').
  rewrite <- 3 assoc.
  apply pathsinv0.
  rewrite functor_on_iso_inv.
  apply iso_inv_on_right.
  rewrite 4 assoc.
  simpl.
  rewrite <- 2 functor_comp.
  apply (Hf _ _ (h · f · (inv_from_iso h')) (make_hProp _ (hsC _ _ _ _))).
  intro sur.
  simpl.
  rewrite <- (pr2 sur).
  simp_rew (nat_trans_ax gamma).
  rewrite (pr2 sur).
  rewrite <- 3 assoc.
  rewrite <- 2 functor_comp.
  apply cancel_precomposition, maponpaths.
  rewrite <- 2 assoc.
  rewrite iso_after_iso_inv.
  rewrite id_right.
  apply idpath.
Defined.

Definition delta : nat_trans F G :=
  (pdelta,, is_nat_trans_pdelta).

Lemma pdelta_preimage : pre_whisker H delta = gamma.
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro a.
    intermediate_path (pr1 (pr1 (iscontr_aux_space (H a)))).
    + apply idpath.
    + rewrite (pr2 (pr1 (iscontr_aux_space (H a))) a (identity_iso _)).
      rewrite iso_inv_of_iso_id.
      simpl.
      rewrite 2 functor_id.
      rewrite id_right.
      apply id_left.
Defined.

End full.

(** * Precomposition with an essentially surjective and full functor is fully faithful *)

Lemma pre_composition_with_ess_surj_and_full_is_full :
  full (pre_composition_functor A B C hsB hsC H).
Proof.
  intros F G gamma.
  apply hinhpr.
  exists (delta F G gamma).
  apply pdelta_preimage.
Defined.

Lemma pre_composition_with_ess_surj_and_full_is_full_and_faithful :
   full_and_faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  split.
  apply pre_composition_with_ess_surj_and_full_is_full.
  apply pre_composition_with_ess_surj_is_faithful. assumption.
Defined.

Lemma pre_composition_with_ess_surj_and_full_is_fully_faithful :
   fully_faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  apply full_and_faithful_implies_fully_faithful.
  apply pre_composition_with_ess_surj_and_full_is_full_and_faithful.
Defined.

End precomp_with_ess_surj_full_functor_is_full.


Lemma pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful
  (p : essentially_surjective H) (Hff : fully_faithful H):
  fully_faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  apply pre_composition_with_ess_surj_and_full_is_fully_faithful.
  - exact p.
  - apply fully_faithful_implies_full_and_faithful.
    exact Hff.
Defined.

End pre_composition.
