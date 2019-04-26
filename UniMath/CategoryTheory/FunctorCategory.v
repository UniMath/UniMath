(** * Functor (pre)categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)

(** ** Contents

  - Isomorphisms in functor category are pointwise isomorphisms

  - Isomorphic Functors are equal if target precategory is univalent_category
    [functor_eq_from_functor_iso]

  - Functor precategory is univalent_category if target precategory is
    [is_univalent_functor_category]
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Univalence.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

(** ** Functor category [[C, D]] *)

Definition functor_precategory_ob_mor (C C' : precategory_data):
  precategory_ob_mor := make_precategory_ob_mor
   (functor C C') (λ F F' : functor C C', nat_trans F F').


(** *** The data of the functor precategory *)

Definition functor_precategory_data (C : precategory_data)(C' : precategory): precategory_data.
Proof.
  apply (make_precategory_data (functor_precategory_ob_mor C C')).
  + intro a; simpl.
    apply (nat_trans_id (pr1 a)).
  + intros a b c f g.
    apply (nat_trans_comp _ _ _ f g).
Defined.

(** *** Above data forms a precategory *)

Lemma is_precategory_functor_precategory_data
  (C:precategory_data)(C' : precategory) (hs: has_homsets C'):
   is_precategory (functor_precategory_data C C').
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat split; simpl; intros.
  unfold identity.
  simpl.
  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply id_left.

  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply id_right.

  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply assoc.
Qed.

Definition functor_precategory (C : precategory_data) (C' : precategory)
  (hs: has_homsets C'): precategory :=
  tpair (λ C, is_precategory C)
        (functor_precategory_data C C')
        (is_precategory_functor_precategory_data C C' hs).

Notation "[ C , D , hs ]" := (functor_precategory C D hs) : cat.

Definition functor_identity_as_ob (C : precategory) (hsC : has_homsets C)
  : [C, C, hsC]
  := (functor_identity C).

Definition functor_composite_as_ob {C C' C'' : precategory}
  {hsC' : has_homsets C'} {hsC'' : has_homsets C''}
  (F : [C, C', hsC']) (F' : [C', C'', hsC'']) :
  [C, C'', hsC''] := tpair _ _ (is_functor_composite F F').

(** Characterizing isomorphisms in the functor category *)

Lemma is_nat_trans_inv_from_pointwise_inv_ext {C : precategory_data} {D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} {A : nat_trans F G}
  (H : forall a : ob C, is_iso (pr1 A a)) :
  is_nat_trans _ _
     (λ a : ob C, inv_from_iso (tpair _ _ (H a))).
Proof.
  red.
  intros x x' f.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite assoc.
  apply iso_inv_on_left.
  set (HA:= pr2 A).
  simpl in *.
  apply pathsinv0.
  unfold is_nat_trans in HA.
  apply HA.
Qed.

Lemma is_nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
  is_nat_trans _ _
     (λ a : ob C, inv_from_iso (tpair _ _ (H a))).
Proof.
  apply is_nat_trans_inv_from_pointwise_inv_ext.
  exact hs.
Qed.

Definition nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : ∏ a : ob C, is_iso (pr1 A a)) :
    G --> F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H).

Definition nat_trans_inv_from_pointwise_inv_ext {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
    nat_trans G F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv_ext hs H).

Lemma nat_trans_inv_is_iso {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
  forall a : ob C, is_iso ((nat_trans_inv_from_pointwise_inv_ext hs A H) a).
Proof.
  intros a.
  apply is_iso_inv_from_iso.
Defined.

Lemma is_inverse_nat_trans_inv_from_pointwise_inv (C : precategory_data)(C' : precategory) (hs: has_homsets C')
    (F G : [C, C', hs]) (A : F --> G)
   (H : ∏ a : C, is_iso (pr1 A a)) :
  is_inverse_in_precat A (nat_trans_inv_from_pointwise_inv C C' _ F G A H).
Proof.
  simpl; split; simpl.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T := iso_inv_after_iso (tpair _ (pr1 A x) (H x))).
    apply T.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T := iso_after_iso_inv (tpair _ (pr1 A x) (H x))).
    apply T.
Qed.


Lemma functor_iso_if_pointwise_iso (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) :
   (∏ a : ob C, is_iso (pr1 A a)) ->
           is_iso A .
Proof.
  intro H.
  apply (is_iso_qinv _ (nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H)).
  simpl; apply is_inverse_nat_trans_inv_from_pointwise_inv.
Defined.

Definition functor_iso_from_pointwise_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G)
   (H : ∏ a : ob C, is_iso (pr1 A a)) :
     iso F G :=
 tpair _ _ (functor_iso_if_pointwise_iso _ _ _ _ _ _ H).


Lemma is_functor_iso_pointwise_if_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) :
  is_iso A ->
       ∏ a : ob C, is_iso (pr1 A a).
Proof.
  intros H a.
  set (T := inv_from_iso (tpair _ A H)).
  set (TA := iso_inv_after_iso (tpair _ A H)).
  set (TA' := iso_after_iso_inv (tpair _ A H)).
  simpl in *.
  apply (is_iso_qinv _ (T a)).
  unfold is_inverse_in_precat in *; simpl; split.
  - unfold T.
    set (H1' := nat_trans_eq_pointwise TA). apply H1'.
  - apply (nat_trans_eq_pointwise TA').
Defined.

Lemma nat_trans_inv_pointwise_inv_before (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) :
       ∏ a : C, pr1 (inv_from_iso (make_iso A Aiso)) a · pr1 A a = identity _ .
Proof.
  intro a.
  set (T := inv_from_iso (make_iso A Aiso)).
  set (TA := iso_inv_after_iso (make_iso A Aiso)).
  set (TA' := iso_after_iso_inv (make_iso A Aiso)).
  apply (nat_trans_eq_pointwise TA').
Defined.

Lemma nat_trans_inv_pointwise_inv_after (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) :
       ∏ a : C, pr1 A a · pr1 (inv_from_iso (make_iso A Aiso)) a = identity _ .
Proof.
  intro a.
  set (T := inv_from_iso (make_iso A Aiso)).
  set (TA := iso_inv_after_iso (make_iso A Aiso)).
  set (TA' := iso_after_iso_inv (make_iso A Aiso)).
  apply (nat_trans_eq_pointwise TA).
Defined.


Definition functor_iso_pointwise_if_iso (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C',hs]) (A : F --> G)
  (H : is_iso A) :
     ∏ a : ob C,
       iso (pr1 F a) (pr1 G a) :=
  λ a, tpair _ _ (is_functor_iso_pointwise_if_iso C C' _ F G A H a).

Lemma nat_trans_inv_pointwise_inv_after_p (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) a :
  inv_from_iso (functor_iso_pointwise_if_iso C C' hs F G A Aiso a) =
        pr1 (inv_from_iso (make_iso A Aiso)) a.
Proof.
  apply pathsinv0.
  apply inv_iso_unique'.
  unfold precomp_with.
  simpl.
  set (TA := iso_inv_after_iso (make_iso A Aiso)).
  simpl in TA.
  apply (nat_trans_eq_pointwise TA).
Defined.

Definition pr1_pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs]) :
   iso F G -> pr1 (pr1 F) = pr1 (pr1 G).
Proof.
  intro A.
  apply funextsec.
  intro t.
  apply isotoid.
  assumption.
  apply (functor_iso_pointwise_if_iso _ _ _ _ _ A).
  apply (pr2 A).
Defined.

Lemma transport_of_functor_map_is_pointwise (C : precategory_data) (D : precategory)
      (F0 G0 : ob C -> ob D)
      (F1 : ∏ a b : ob C, a --> b -> F0 a --> F0 b)
      (gamma : F0  = G0 )
      (a b : ob C) (f : a --> b) :
  transportf (fun x : ob C -> ob D =>
                ∏ a0 b0 : ob  C, a0 --> b0 -> x a0 --> x b0)
             gamma F1 a b f =
  double_transport (toforallpaths (λ _ : ob C, D) F0 G0 gamma a)
                   (toforallpaths (λ _ : ob C, D) F0 G0 gamma b)
                   (F1 a b f).
Proof.
  induction gamma.
  apply idpath.
Defined.

Lemma nat_trans_comp_pointwise (C : precategory_data)(C' : precategory) (hs: has_homsets C')
  (F G H : ob [C, C', hs]) (A : F --> G) (A' : G --> H)
   (B : F --> H) : A · A' = B ->
        ∏ a, pr1 A a · pr1 A' a = pr1 B a.
Proof.
  intros H' a.
  intermediate_path (pr1 (A · A') a).
  apply idpath.
  destruct H'.
  apply idpath.
Defined.

Definition pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)(hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs]) :
   iso F G -> pr1 F = pr1 G.
Proof.
  intro A.
  apply (total2_paths_f (pr1_pr1_functor_eq_from_functor_iso C D _ H F G A)).
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply funextsec; intro a.
  apply funextsec; intro b.
  apply funextsec; intro f.
  rewrite transport_of_functor_map_is_pointwise.
  rewrite toforallpaths_funextsec.
  etrans.
  { apply double_transport_idtoiso. }
  rewrite idtoiso_isotoid.
  rewrite idtoiso_isotoid.
  etrans.
  { rewrite <- assoc.
    apply cancel_precomposition.
    apply (nat_trans_ax (pr1 A)).
  }
  etrans.
  { apply cancel_postcomposition.
    apply nat_trans_inv_pointwise_inv_after_p. }
  rewrite assoc.
  apply remove_id_left; try apply idpath.
  set (TA' := iso_after_iso_inv A).
  set (TA'' := nat_trans_comp_pointwise _ _ _ _ _ _ _ _  _ TA').
  apply TA''.
Defined.

Definition functor_eq_from_functor_iso {C : precategory_data} {D : precategory}
  (hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs])
    (H' : iso F G) : F = G.
Proof.
  apply (functor_eq _ _ hs F G).
  apply pr1_functor_eq_from_functor_iso;
  assumption.
Defined.


Lemma idtoiso_functorcat_compute_pointwise (C : precategory_data) (D : precategory)
  (hs: has_homsets D) (F G : ob [C, D, hs])
     (p : F = G) (a : ob C) :
  functor_iso_pointwise_if_iso C D _ F G (idtoiso p) (pr2 (idtoiso p)) a =
idtoiso
  (toforallpaths (λ _ : ob C, D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  apply eq_iso. apply idpath.
Qed.


Lemma functor_eq_from_functor_iso_idtoiso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D)
    (F G : ob [C, D, hs]) (p : F = G) :
  functor_eq_from_functor_iso _ H F G (idtoiso p) = p.
Proof.
  simpl; apply functor_eq_eq_from_functor_ob_eq. apply hs.
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total2_paths.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total2_paths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply (invmaponpathsweq (weqtoforallpaths _ _ _ )).
  simpl.
  rewrite toforallpaths_funextsec.
  apply funextsec; intro a.
  rewrite idtoiso_functorcat_compute_pointwise.
  apply isotoid_idtoiso.
Qed.

Lemma idtoiso_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D)
    (F G : ob [C, D, hs]) (gamma : iso F G) :
        idtoiso (functor_eq_from_functor_iso _ H F G gamma) = gamma.
Proof.
  apply eq_iso.
  simpl; apply nat_trans_eq; intro a. apply hs.
  assert (H' := idtoiso_functorcat_compute_pointwise C D _ F G (functor_eq_from_functor_iso _ H F G gamma) a).
  simpl in *.
  assert (H2 := maponpaths (@pr1 _ _ ) H'). simpl in H2.
  etrans.
  { apply H2. }
  clear H' H2.
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total2_paths.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total2_paths.
  intermediate_path (pr1 (idtoiso
     (isotoid D H (functor_iso_pointwise_if_iso C D hs F G gamma (pr2 gamma) a)))).
  2: { rewrite idtoiso_isotoid.
       apply idpath.
  }
  apply maponpaths.
  apply maponpaths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  rewrite toforallpaths_funextsec.
  apply idpath.
Qed.

Lemma isweq_idtoiso_functorcat (C : precategory_data) (D : precategory) (H : is_univalent D)
    (F G : ob [C, D, (pr2 H)]) :
   isweq (@idtoiso _ F G).
Proof.
  apply (isweq_iso _ (functor_eq_from_functor_iso _ H F G)).
  apply functor_eq_from_functor_iso_idtoiso.
  apply idtoiso_functor_eq_from_functor_iso.
Defined.

Lemma is_univalent_functor_category (C : precategory_data) (D : precategory) (H : is_univalent D) :
   is_univalent [C, D, (pr2 H)].
Proof.
  split.
  - intros F G.
    apply isweq_idtoiso_functorcat.
  - intros a b.
    apply isaset_nat_trans.
    apply (pr2 H).
Defined.


Lemma functor_category_has_homsets (C D : precategory) (hs: has_homsets D):
  has_homsets [C, D, hs].
Proof.
  intros F G.
  apply isaset_nat_trans.
  apply hs.
Qed.


Definition functor_category (C : precategory) (D : category) : category.
Proof.
  exists (functor_precategory C D (homset_property D)).
  apply functor_category_has_homsets.
Defined.

Definition iso_to_nat_iso
           {C D : category}
           (F G : C ⟶ D)
  : @iso (functor_category C D) F G → nat_iso F G.
Proof.
  intros α.
  use make_nat_iso.
  - exact (pr1 α).
  - use is_functor_iso_pointwise_if_iso.
    apply α.
Defined.

Definition nat_iso_to_iso
           {C D : category}
           (F G : C ⟶ D)
  : nat_iso F G → @iso (functor_category C D) F G.
Proof.
  intros α.
  use functor_iso_from_pointwise_iso ; apply α.
Defined.

Definition iso_is_nat_iso
           {C D : category}
           (F G : C ⟶ D)
  : @iso (functor_category C D) F G ≃ nat_iso F G.
Proof.
  refine (make_weq (iso_to_nat_iso F G) _).
  use isweq_iso.
  - exact (nat_iso_to_iso F G).
  - intros X.
    use subtypeEquality.
    + intro.
      apply isaprop_is_iso.
    + apply nat_trans_eq.
      { apply D. }
      reflexivity.
  - intros X.
    use subtypeEquality.
    + intro.
      apply isaprop_is_nat_iso.
    + reflexivity.
Defined.

Lemma functor_comp_pw {C C' D D' : precategory} hsD hsD'
           (F : [C,D,hsD] ⟶ [C',D',hsD']) {a b c}  (f : [C,D,hsD] ⟦ a, b ⟧)
           (g : [C,D,hsD] ⟦ b, c ⟧) (x :C') :
  (# F f:nat_trans _ _) x · (# F g:nat_trans _ _) x = ((# F (f · g)) :  nat_trans _ _ ) x .
Proof.
  now rewrite functor_comp.
Qed.

Lemma functor_cancel_pw {C C' D D' : precategory} hsD hsD'
           (F : [C,D,hsD] ⟶ [C',D',hsD']) {a b }  (f g : [C,D,hsD] ⟦ a, b ⟧)
           (x :C') : f = g ->
                     ((# F f ) :  nat_trans _ _ ) x = (# F g:nat_trans _ _) x .
Proof.
  intro e.
  now induction e.
Qed.

Notation "[ C , D , hs ]" := (functor_precategory C D hs) : cat.

Notation "[ C , D ]" := (functor_category C D) : cat.

(* Declare Scope Cat. *)
Notation "G □ F" := (functor_composite (F:[_,_]) (G:[_,_]) : [_,_]) (at level 35) : Cat.
(* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)