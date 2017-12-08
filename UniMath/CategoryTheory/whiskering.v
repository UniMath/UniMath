(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :

- Precomposition with a functor for
   - functors and
   - natural transformations (whiskering)

- Functoriality of precomposition

- Precomposition with an essentially surjective
	   functor yields a faithful functor

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.

Definition functor_compose {A B C : precategory} (hsB: has_homsets B)
                           (hsC: has_homsets C) (F : ob [A, B, hsB])
      (G : ob [B , C, hsC]) : ob [A , C, hsC] :=
   functor_composite F G.

(*
Local Notation "G 'O' F '{' hsB  hsC '}'" :=
        (functor_compose hsB hsC F G) (at level 200).
Local Notation "G 'o' F '{' hsB  hsC '}'" :=
        (functor_compose hsB hsC  F G : functor _ _ ) (at level 200).
*)
(** * Whiskering: Composition of a natural transformation with a functor *)

(** Prewhiskering *)

Lemma is_nat_trans_pre_whisker (A B C : precategory_data)
   (F : functor_data A B) (G H : functor_data B C) (gamma : nat_trans G H) :
   is_nat_trans
        (functor_composite_data F G)
        (functor_composite_data F H)
   (λ a : A, gamma (F a)).
Proof.
  intros a b f; simpl.
  apply nat_trans_ax.
Defined.


Definition pre_whisker {A B C : precategory_data}
   (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H) :
   nat_trans (functor_composite_data F G)  (functor_composite_data F H).
Proof.
  exists (λ a, pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.

Lemma pre_whisker_iso_is_iso {A B C : precategory_data}
    (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H)
    (X : (forall b : B, is_iso (gamma b)))
  : (forall a : A, is_iso (pre_whisker F gamma a)).
Proof.
  intros a.
  apply X.
Qed.

(** Postwhiskering *)

Lemma is_nat_trans_post_whisker (B C D : precategory_data)
   (G H : functor_data B C) (gamma : nat_trans G  H)
        (K : functor C D):
  is_nat_trans (functor_composite_data  G K)
                         (functor_composite_data H K)
     (λ b : B, #K (gamma b)).
Proof.
  unfold is_nat_trans.
  simpl in *.
  intros;
  repeat rewrite <- functor_comp.
  rewrite (nat_trans_ax gamma).
  apply idpath.
Qed.

Definition post_whisker {B C D : precategory_data}
   {G H : functor_data B C} (gamma : nat_trans G H)
        (K : functor C D)
  : nat_trans (functor_composite_data G K) (functor_composite_data H K).
Proof.
  exists (λ a : ob B, #(pr1 K) (pr1 gamma  a)).
  apply is_nat_trans_post_whisker.
Defined.

Lemma post_whisker_iso_is_iso {B C D : precategory}
   {G H : functor_data B C} (gamma : nat_trans G H)
   (K : functor C D)
   (X : (forall b : B, is_iso (gamma b)))
  : (forall b : B, is_iso (post_whisker gamma K b)).
Proof.
  intros b.
  unfold post_whisker.
  simpl.
  set ( gammab := isopair (gamma b) (X b) ).
  apply (functor_on_iso_is_iso C D K _ _ gammab).
Qed.

(** Precomposition with a functor is functorial *)

Definition pre_composition_functor_data (A B C : precategory)
  (hsB: has_homsets B) (hsC: has_homsets C)
      (H : ob [A, B, hsB]) : functor_data [B,C,hsC] [A,C,hsC].
Proof.
  exists (λ G, functor_compose _ _ H G).
  exact (λ a b gamma, pre_whisker (pr1 H)  gamma).
Defined.


Lemma pre_whisker_identity (A B : precategory_data) (C : precategory)(hsC : has_homsets C)
  (H : functor_data A B) (G : functor_data B C)
  : pre_whisker H (nat_trans_id G) =
   nat_trans_id (functor_composite_data H G).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro a. apply idpath.
Qed.

Lemma pre_whisker_composition (A B : precategory_data) (C : precategory)
  (hsC : has_homsets C)
  (H : functor_data A B) (a b c : functor_data B C)
  (f : nat_trans a b) (g : nat_trans b c)
  : pre_whisker H (nat_trans_comp _ _ _ f g) =
     nat_trans_comp _ _ _ (pre_whisker H f) (pre_whisker H g).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro; simpl.
    apply idpath.
Qed.

Lemma pre_composition_is_functor (A B C : precategory) (hsB: has_homsets B)
  (hsC: has_homsets C)  (H : [A, B, hsB]) :
    is_functor (pre_composition_functor_data A B C hsB hsC H).
Proof.
  split; simpl in *.
  - unfold functor_idax .
    intros.
    apply pre_whisker_identity.
    assumption.
  - unfold functor_compax .
    intros.
    apply pre_whisker_composition.
    assumption.
Qed.

Definition pre_composition_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C)
   (H : [A , B, hsB]) : functor [B, C, hsC] [A, C, hsC].
Proof.
  exists (pre_composition_functor_data A B C hsB hsC H).
  apply pre_composition_is_functor.
Defined.

(** Postcomposition with a functor is functorial *)


Definition post_composition_functor_data (A B C : precategory)
  (hsB: has_homsets B) (hsC: has_homsets C)
      (H : ob [B, C, hsC]) : functor_data [A,B,hsB] [A,C,hsC].
Proof.
  exists (λ G, functor_compose _ _ G H).
  exact (λ a b gamma, post_whisker gamma H).
Defined.


Lemma post_whisker_identity (A B : precategory) (C : precategory)(hsC : has_homsets C)
  (H : functor B C) (G : functor_data A B)
  : post_whisker (nat_trans_id G) H =
   nat_trans_id (functor_composite_data G H).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro a. unfold post_whisker.  simpl.
    apply functor_id.
Qed.

Lemma post_whisker_composition (A B : precategory) (C : precategory)
  (hsC : has_homsets C)
  (H : functor B C) (a b c : functor_data A B)
  (f : nat_trans a b) (g : nat_trans b c)
  : post_whisker (nat_trans_comp _ _ _ f g) H =
     nat_trans_comp _ _ _ (post_whisker f H) (post_whisker g H).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro; simpl.
    apply functor_comp.
Qed.

Lemma post_composition_is_functor (A B C : precategory) (hsB: has_homsets B)
  (hsC: has_homsets C)  (H : [B, C, hsC]) :
    is_functor (post_composition_functor_data A B C hsB hsC H).
Proof.
  split; simpl in *.
  - unfold functor_idax .
    intros.
    apply post_whisker_identity.
    assumption.
  - unfold functor_compax .
    intros.
    apply post_whisker_composition.
    assumption.
Qed.

Definition post_composition_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C)
   (H : [B , C, hsC]) : functor [A, B, hsB] [A, C, hsC].
Proof.
  exists (post_composition_functor_data A B C hsB hsC H).
  apply post_composition_is_functor.
Defined.
