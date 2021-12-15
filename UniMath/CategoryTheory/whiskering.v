(** * Whiskering

  Benedikt Ahrens, Chris Kapulkin, Mike Shulman

  January 2013
*)


(** ** Contents :

  - Precomposition with a functor for
    - functors and
    - natural transformations (whiskering)

  - Functoriality of precomposition / postcomposition

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.

Definition functor_compose {A B C : category} (F : ob [A, B])
      (G : ob [B , C]) : ob [A , C] :=
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
Qed.


Definition pre_whisker {A B C : precategory_data}
   (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H) :
   nat_trans (functor_composite_data F G)  (functor_composite_data F H).
Proof.
  exists (λ a, pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.

Lemma pre_whisker_iso_is_iso {A B C : precategory_data}
    (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H)
    (X : is_nat_iso gamma)
  : is_nat_iso (pre_whisker F gamma).
Proof.
  intros a.
  apply X.
Defined.

Lemma pre_whisker_on_nat_z_iso {A B C : precategory_data}
    (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H)
    (X : is_nat_z_iso gamma)
  : is_nat_z_iso (pre_whisker F gamma).
Proof.
  intros a.
  apply X.
Defined.

Definition pre_whisker_in_funcat (A B C : category)
           (F : [A, B]) {G H : [B, C]} (γ : [B, C]⟦G, H⟧) :
  [A, C]⟦functor_compose F G, functor_compose F H⟧.
Proof.
  exact (pre_whisker (F: A ⟶ B) γ).
Defined.

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
   (X : is_nat_iso gamma)
  : is_nat_iso (post_whisker gamma K).
Proof.
  intros b.
  unfold post_whisker.
  simpl.
  set ( gammab := make_iso (gamma b) (X b) ).
  apply (functor_on_iso_is_iso C D K _ _ gammab).
Defined.

Lemma post_whisker_z_iso_is_z_iso {B C D : precategory}
   {G H : functor_data B C} (gamma : nat_trans G H)
   (K : functor C D)
   (X : is_nat_z_iso gamma)
  : is_nat_z_iso (post_whisker gamma K).
Proof.
  intros b.
  unfold post_whisker.
  simpl.
  apply (functor_on_is_z_isomorphism K (X b)).
Defined.

Definition post_whisker_in_funcat (B C D : category)
            {G H : [B, C]} (γ : [B, C]⟦G, H⟧) (K : [C, D]) :
  [B, D]⟦functor_compose G K, functor_compose H K⟧.
Proof.
  exact (post_whisker γ (K: C ⟶ D)).
Defined.

(** Precomposition with a functor is functorial *)

Definition pre_composition_functor_data (A B C : category)
      (H : ob [A, B]) : functor_data [B, C] [A, C].
Proof.
  exists (λ G, functor_compose H G).
  exact (λ a b gamma, pre_whisker_in_funcat _ _ _ H gamma).
Defined.


Lemma pre_whisker_identity (A B : precategory_data) (C : category)
  (H : functor_data A B) (G : functor_data B C)
  : pre_whisker H (nat_trans_id G) =
   nat_trans_id (functor_composite_data H G).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro a. apply idpath.
Qed.

Lemma pre_whisker_composition (A B : precategory_data) (C : category)
  (H : functor_data A B) (a b c : functor_data B C)
  (f : nat_trans a b) (g : nat_trans b c)
  : pre_whisker H (nat_trans_comp _ _ _ f g) =
     nat_trans_comp _ _ _ (pre_whisker H f) (pre_whisker H g).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro; simpl.
    apply idpath.
Qed.

Lemma pre_composition_is_functor (A B C : category) (H : [A, B]) :
    is_functor (pre_composition_functor_data A B C H).
Proof.
  split; simpl in *.
  - unfold functor_idax .
    intros.
    apply pre_whisker_identity.
  - unfold functor_compax .
    intros.
    apply pre_whisker_composition.
Qed.

Definition pre_composition_functor (A B C : category) (H : [A , B]) : functor [B, C] [A, C].
Proof.
  exists (pre_composition_functor_data A B C H).
  apply pre_composition_is_functor.
Defined.

(* Variation with more implicit arguments *)
Definition pre_comp_functor {A B C: category} :
  [A, B] → [B, C] ⟶ [A, C] :=
    pre_composition_functor _ _ _.

(** Postcomposition with a functor is functorial *)

Definition post_composition_functor_data (A B C : category)
      (H : ob [B, C]) : functor_data [A, B] [A, C].
Proof.
  exists (λ G, functor_compose G H).
  exact (λ a b gamma, post_whisker_in_funcat _ _ _ gamma H).
Defined.


Lemma post_whisker_identity (A B : precategory) (C : category)
  (H : functor B C) (G : functor_data A B)
  : post_whisker (nat_trans_id G) H =
   nat_trans_id (functor_composite_data G H).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro a. unfold post_whisker. simpl.
    apply functor_id.
Qed.

Lemma post_whisker_composition (A B : precategory) (C : category)
  (H : functor B C) (a b c : functor_data A B)
  (f : nat_trans a b) (g : nat_trans b c)
  : post_whisker (nat_trans_comp _ _ _ f g) H =
     nat_trans_comp _ _ _ (post_whisker f H) (post_whisker g H).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro; simpl.
    apply functor_comp.
Qed.

Lemma post_composition_is_functor (A B C : category) (H : [B, C]) :
    is_functor (post_composition_functor_data A B C H).
Proof.
  split; simpl in *.
  - unfold functor_idax .
    intros.
    apply post_whisker_identity.
  - unfold functor_compax .
    intros.
    apply post_whisker_composition.
Qed.

Definition post_composition_functor (A B C : category) (H : [B , C]) : functor [A, B] [A, C].
Proof.
  exists (post_composition_functor_data A B C H).
  apply post_composition_is_functor.
Defined.

(* Variation with more implicit arguments *)
Definition post_comp_functor {A B C : category} :
  [B, C] → [A, B] ⟶ [A, C] :=
    post_composition_functor _ _ _.
