(** * Natural transformations

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)


(** ** Contents
  - Definition of natural transformations
  - Equality is pointwise equality
  - Identity natural transformation
  - Composition of natural transformations
  - Natural isomorphisms
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.
Section nat_trans.

  (** ** Definition of natural transformations *)

Definition nat_trans_data {C C' : precategory_ob_mor} (F F' : functor_data C C'): UU :=
  ∏ x : ob C, F x -->  F' x.

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') (t : nat_trans_data F F') :=
  ∏ (x x' : ob C)(f : x --> x'), # F f · t x' = t x · #F' f.


Lemma isaprop_is_nat_trans (C C' : precategory_data) (hs: has_homsets C')
  (F F' : functor_data C C') (t : nat_trans_data F F'):
  isaprop (is_nat_trans F F' t).
Proof.
  repeat (apply impred; intro).
  apply hs.
Qed.

Definition nat_trans {C C' : precategory_data} (F F' : functor_data C C') : UU :=
  total2 (fun t : nat_trans_data F F' => is_nat_trans F F' t).

Notation "F ⟹ G" := (nat_trans F G) (at level 39) : cat.
(* to input: type "\==>" with Agda input method *)

Definition make_nat_trans {C C' : precategory_data} (F F' : functor_data C C')
           (t : nat_trans_data F F') (H : is_nat_trans F F' t) :
           nat_trans F F'.
Proof.
exists t.
exact H.
Defined.

Lemma isaset_nat_trans {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C') : isaset (nat_trans F F').
Proof.
  apply (isofhleveltotal2 2).
  + apply impred; intro t; apply hs.
  + intro x; apply isasetaprop, isaprop_is_nat_trans, hs.
Qed.

Definition nat_trans_data_from_nat_trans {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') :
  nat_trans_data F F' := pr1 a.

Definition nat_trans_data_from_nat_trans_funclass {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') :
  ∏ x : ob C, F x -->  F' x := pr1 a.
Coercion nat_trans_data_from_nat_trans_funclass : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  {F F' : functor_data C C'} (a : nat_trans F F') :
  ∏ (x x' : ob C)(f : x --> x'),
    #F f · a x' = a x · #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma nat_trans_eq {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_nat_trans, hs.
Qed.


Section nat_trans_eq.

  Context {C D : precategory}.
  Variable hsD : has_homsets D.
  Context {F G : functor C D}.
  Variables alpha beta : nat_trans F G.

  Definition nat_trans_eq_weq : (alpha = beta) ≃ (∏ c, alpha c = beta c).
  Proof.
    eapply weqcomp.
    - apply subtypeInjectivity.
      intro x. apply isaprop_is_nat_trans. apply hsD.
    - apply weqtoforallpaths.
  Defined.

End nat_trans_eq.

(* Can be given as an instance of general equality lemmas,
but useful to have specifically defined. *)
Definition nat_trans_eq_pointwise {C C' : precategory_data}
   {F F' : functor_data C C'} {a a' : nat_trans F F'}:
      a = a' -> ∏ x, a x = a' x.
Proof.
  intro. apply toforallpaths, maponpaths. assumption.
Qed.

(** a more intuitive variant of [functor_data_eq] *)
Lemma functor_data_eq_from_nat_trans (C C': precategory) (F F' : functor_data C C')
      (H : F ~ F') (H1 : is_nat_trans F F' (fun c:C => idtomor _ _ (H c))) :
      F = F'.
Proof.
  apply (functor_data_eq _ _ _ _ H).
  intros c1 c2 f.
  rewrite double_transport_idtoiso.
  rewrite <- assoc.
  apply iso_inv_on_right.
(* make the coercion visible: *)
  unfold morphism_from_iso.
  do 2 rewrite eq_idtoiso_idtomor.
  apply H1.
Qed.

(** ** Identity natural transformation *)

Lemma is_nat_trans_id {C : precategory_data}{C' : precategory}
  (F : functor_data C C') : is_nat_trans F F
     (λ c : ob C, identity (F c)).
Proof.
  intros ? ? ? .
  now rewrite id_left, id_right.
Qed.

Definition nat_trans_id {C:precategory_data}{C' : precategory}
  (F : functor_data C C') : nat_trans F F :=
    tpair _ _ (is_nat_trans_id F).

(** ** Composition of natural transformations *)

Lemma is_nat_trans_comp {C : precategory_data}{C' : precategory}
  {F G H : functor_data C C'}
  (a : nat_trans F G)
  (b : nat_trans G H): is_nat_trans F H
     (λ x : ob C, a x · b x).
Proof.
  intros ? ? ?.
  now rewrite assoc, nat_trans_ax, <- assoc, nat_trans_ax, assoc.
Qed.


Definition nat_trans_comp {C:precategory_data}{C' : precategory}
  (F G H: functor_data C C')
  (a : nat_trans F G)
  (b : nat_trans G H): nat_trans F H :=
    tpair _ _ (is_nat_trans_comp a b).

(** Natural transformations for reasoning about various compositions of functors *)
Section nat_trans_functor.

Context {A B C D : precategory}.

Definition nat_trans_functor_id_right (F : functor A B) :
  nat_trans (functor_composite F (functor_identity B)) F.
Proof.
exists (λ x, identity _).
abstract (now intros a b f; rewrite id_left, id_right).
Defined.

Definition nat_trans_functor_id_right_inv (F : functor A B) :
  nat_trans F (functor_composite F (functor_identity B)) :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_id_left (F : functor A B) :
  nat_trans (functor_composite (functor_identity A) F) F :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_id_left_inv (F : functor A B) :
  nat_trans F (functor_composite (functor_identity A) F) :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_assoc (F1 : functor A B) (F2 : functor B C) (F3 : functor C D) :
  nat_trans (functor_composite (functor_composite F1 F2) F3)
            (functor_composite F1 (functor_composite F2 F3)).
Proof.
exists (λ x, identity _).
abstract (now intros a b f; rewrite id_right, id_left).
Defined.

Definition nat_trans_functor_assoc_inv (F1 : functor A B) (F2 : functor B C) (F3 : functor C D) :
  nat_trans (functor_composite F1 (functor_composite F2 F3))
            (functor_composite (functor_composite F1 F2) F3) :=
    nat_trans_functor_assoc F1 F2 F3.

End nat_trans_functor.

(** ** Natural isomorphisms *)

Definition is_nat_iso {C D : precategory_data} {F G : functor_data C D} (μ : F ⟹ G) : UU :=
∏ (c : C), is_iso (μ c).

Definition isaprop_is_nat_iso
           {C D : category}
           {F G : C ⟶ D}
           (α : F ⟹ G)
  : isaprop (is_nat_iso α).
Proof.
  apply impred.
  intro.
  apply isaprop_is_iso.
Defined.

Definition is_nat_id {C D : precategory} {F : C ⟶ D} (μ : F ⟹ F) : UU :=
∏ (c : C), μ c = identity (F c).

Definition nat_iso {C D : precategory} (F G : C ⟶ D) : UU
:= ∑ (μ : F ⟹ G), is_nat_iso μ.

Definition make_nat_iso {C D : precategory} (F G : C ⟶ D) (μ : F ⟹ G) (is_iso : is_nat_iso μ) : nat_iso F G.
Proof.
  exists μ.
  exact is_iso.
Defined.

Definition iso_inv_after_iso' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : f · inv_from_iso f' = identity _.
Proof.
  rewrite <- deref.
  exact (iso_inv_after_iso f').
Defined.

Definition iso_after_iso_inv' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : inv_from_iso f' · f = identity _.
Proof.
  rewrite <- deref.
  exact (iso_after_iso_inv f').
Defined.

Definition nat_iso_inv {C D : precategory} {F G : C ⟶ D} (μ : nat_iso F G) : nat_iso G F.
Proof.
  pose (iso := (λ c, make_iso _ (pr2 μ c))).
  pose (inv := (λ c, inv_from_iso (iso c))).
  use tpair.
  - exists inv.
    intros c c' f.
    pose (coher := pr2 (pr1 μ) c c' f).
    pose (coher_inv := maponpaths (λ p, inv c · p · inv c') coher).
    simpl in coher_inv.
    repeat rewrite <- assoc in coher_inv.
    unfold inv in coher_inv.
    assert (coher_inv' : (inv_from_iso (iso c) · (# F f · ((pr1 μ) c' · inv_from_iso (iso c'))) = inv_from_iso (iso c) · (pr1 (pr1 μ) c · (# G f · inv_from_iso (iso c'))))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    assert (deref' : pr1 (iso c') = (pr1 μ) c') by reflexivity.
    rewrite (iso_inv_after_iso' ((pr1 μ) c') (iso c') deref') in coher_inv.
    rewrite id_right in coher_inv.
    repeat rewrite assoc in coher_inv.
    assert (deref : pr1 (iso c) = (pr1 μ) c) by reflexivity.
    assert (coher_inv' : (inv_from_iso (iso c) · # F f = inv_from_iso (iso c) · (pr1 μ) c · # G f · inv_from_iso (iso c'))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    rewrite (iso_after_iso_inv' ((pr1 μ) c) (iso c) deref) in coher_inv.
    rewrite id_left in coher_inv.
    unfold inv.
    symmetry.
    assumption.
  - intro c.
    exact (is_iso_inv_from_iso (iso c)).
Defined.

Definition nat_iso_to_trans {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : F ⟹ G :=
  pr1 ν.

Coercion nat_iso_to_trans : nat_iso >-> nat_trans.

(* ⁻¹ *)
Definition nat_iso_to_trans_inv {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : G ⟹ F :=
  pr1 (nat_iso_inv ν).

Definition nat_comp_to_endo {C D : precategory} {F G : C ⟶ D} (eq : F = G) {c : C} (f : F c --> G c) : F c --> F c.
Proof.
  rewrite <- eq in f.
  assumption.
Defined.

Definition is_nat_iso_id {C D : precategory} {F G : C ⟶ D} (eq : F = G) (ν : nat_iso F G) : UU :=
  ∏ (c : C), nat_comp_to_endo eq (nat_iso_to_trans ν c) = identity (F c).

Definition induced_precategory_incl {M : precategory} {X:Type} (j : X -> ob M) :
  induced_precategory M j ⟶ M.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact j.
    + intros a b f. exact f.
  - repeat split.
Defined.


(* ** analogous development for [z_iso] *)

Definition is_nat_z_iso {C D : precategory_data} {F G : functor_data C D} (μ : F ⟹ G) : UU :=
∏ (c : C), is_z_isomorphism (μ c).

Definition isaprop_is_nat_z_iso
           {C D : category}
           {F G : C ⟶ D}
           (α : F ⟹ G)
  : isaprop (is_nat_z_iso α).
Proof.
  apply impred.
  intro.
  apply isaprop_is_z_isomorphism.
Defined.

Definition nat_z_iso {C D : precategory_data} (F G : C ⟶ D) : UU
:= ∑ (μ : F ⟹ G), is_nat_z_iso μ.

Definition make_nat_z_iso {C D : precategory_data} (F G : C ⟶ D) (μ : F ⟹ G) (is_z_iso : is_nat_z_iso μ) : nat_z_iso F G.
Proof.
  exists μ.
  exact is_z_iso.
Defined.

Definition nat_z_iso_to_trans {C D : precategory_data} {F G : C ⟶ D} (μ : nat_z_iso F G) : F ⟹ G :=
  pr1 μ.

Coercion nat_z_iso_to_trans : nat_z_iso >-> nat_trans.

Definition nat_z_iso_pointwise_z_iso {C D : precategory_data} {F G : C ⟶ D} (μ : nat_z_iso F G) (c: C): z_iso (F c) (G c) := (pr1 μ c,,pr2 μ c).

(* ⁻¹ *)
Definition nat_z_iso_to_trans_inv {C : precategory_data} {D : precategory} {F G : C ⟶ D} (μ : nat_z_iso F G) : G ⟹ F.
Proof.
  apply (make_nat_trans G F (fun c => is_z_isomorphism_mor (pr2 μ c))).
  red.
  intros c c' f.
  set (h := μ c,,pr2 μ c : z_iso (F c) (G c)).
  set (h' := μ c',,pr2 μ c' : z_iso (F c') (G c')).
  change (# G f · inv_from_z_iso h' = inv_from_z_iso h · # F f).
  apply pathsinv0.
  apply z_iso_inv_on_right.
  rewrite assoc.
  apply z_iso_inv_on_left.
  apply pathsinv0.
  apply (nat_trans_ax μ).
Defined.

Definition nat_z_iso_inv {C : precategory_data} {D : precategory} {F G : C ⟶ D} (μ : nat_z_iso F G) : nat_z_iso G F.
Proof.
  exists (nat_z_iso_to_trans_inv μ).
  intro c.
  red.
  exists (μ c).
  red.
  split.
  - apply (pr2 (is_z_isomorphism_is_inverse_in_precat (pr2 μ c))).
  - apply (pr1 (is_z_isomorphism_is_inverse_in_precat (pr2 μ c))).
Defined.

Definition is_nat_z_iso_id {C D : precategory} {F G : C ⟶ D} (eq : F = G) (ν : nat_z_iso F G) : UU :=
  ∏ (c : C), nat_comp_to_endo eq (nat_z_iso_to_trans ν c) = identity (F c).

End nat_trans.

Notation "F ⟹ G" := (nat_trans F G) (at level 39) : cat.
(* to input: type "\==>" with Agda input method *)
