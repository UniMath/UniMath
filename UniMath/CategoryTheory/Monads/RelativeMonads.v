(** **********************************************************

Contents:

- Definition of relative monads [RelMonad]
- Functoriality for relative monads [r_lift]
- Kleisli category associated to a relative monad [Kleisli_precat] [Kleisli_cat], canonical relative adjunction [rKleisli_functors_are_relative_adjoints]
- Category of relative monads is univalent if the target category is [is_univalent_RelMonad]

Reference: % \cite{DBLP:journals/corr/AltenkirchCU14} \par %

Written by: Benedikt Ahrens (started May 2017)
Extended by: Ralph Matthes (starting August 2018), in particular all on univalence


************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** * Definition of relative monads *)
Section RMonad_def.

Context {C D : precategory_data} {J : functor_data C D}.

(* implicitness of arguments for RelMonad_data are set after this section *)
Definition RelMonad_data : UU
  := ∑ F : C -> D, (∏ c, D ⟦J c, F c⟧)
                 × (∏ c d, D ⟦J c, F d⟧ → D ⟦F c, F d⟧).

Definition RelMonad_ob (R : RelMonad_data) (c : C) : D := pr1 R c.
Coercion RelMonad_ob : RelMonad_data >-> Funclass.
Definition r_eta (R : RelMonad_data) c : D ⟦J c, R c⟧ := pr1 (pr2 R) c.
Definition r_bind (R : RelMonad_data) {c d} (f : D⟦J c, R d⟧) : D ⟦R c, R d⟧
  := pr2 (pr2 R) _ _ f.

Definition RelMonad_axioms (R : RelMonad_data) : UU
  := (∏ c, r_bind R (r_eta R c) = identity _ )
   × (∏ c d (f : D⟦J c, R d⟧), r_eta R _ · r_bind R f = f)
   × (∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
      r_bind R f · r_bind R g = r_bind R (f · r_bind R g)).

Lemma isaprop_RelMonad_axioms (R : RelMonad_data)(hs : has_homsets D) :
  isaprop (RelMonad_axioms R).
Proof.
  apply isapropdirprod.
  - apply impred_isaprop; intros. apply hs.
  - apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

Definition r_bind_r_eta {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c, r_bind R (r_eta R c) = identity _ := pr1 X.
Definition r_eta_r_bind {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c d (f : D⟦J c, R d⟧), r_eta R _ · r_bind R f = f := pr1 (pr2 X).
Definition r_bind_r_bind {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
         r_bind R f · r_bind R g = r_bind R (f · r_bind R g)
  := pr2 (pr2 X).

(* implicitness of arguments for RelMonad are set after this section *)
Definition RelMonad : UU := ∑ R : RelMonad_data, RelMonad_axioms R.
Coercion RelMonad_data_from_RelMonad (R : RelMonad) : RelMonad_data := pr1 R.
Coercion RelMonad_axioms_from_RelMonad (R : RelMonad) : RelMonad_axioms R := pr2 R.

Lemma RelMonad_eq (R R' : RelMonad)(hs : has_homsets D) :
  pr1 R = pr1 R' -> R = R'.
Proof.
  intro p.
  apply (total2_paths_f p).
  apply proofirrelevance.
  apply isaprop_RelMonad_axioms.
  exact hs.
Defined.

(**  previous proof *)
Lemma RelMonad_eq_obsolete (R R' : RelMonad)(hs : has_homsets D) :
  pr1 R = pr1 R' -> R = R'.
Proof.
  intro p.
  apply subtypeInjectivity.
  - intro R''.
    apply isaprop_RelMonad_axioms.
    exact hs.
  - assumption.
Defined.


(** generalize [UniMath.CategoryTheory.Monads.KTriples.map] *)
Definition r_lift (R : RelMonad_data) {c d : C} (f : c --> d) : R c --> R d
  := r_bind R (#J f · r_eta R _ ).

End RMonad_def.

(** generalize [UniMath.CategoryTheory.Monads.KTriples.map_id] and
               [UniMath.CategoryTheory.Monads.KTriples.map_map] *)
Definition is_functor_r_lift {C: precategory_data} {D: precategory} {J : functor C D} (R : RelMonad)
  : is_functor (RelMonad_ob R,, @r_lift _ _ J R).
Proof.
  split; [intro c | intros a b c f g]; cbn; unfold r_lift; cbn.
  - etrans. apply maponpaths.
      etrans. eapply (maponpaths (λ x, x · _  )). apply functor_id.
      apply id_left.
    apply (r_bind_r_eta R).
  - etrans. 2: { eapply pathsinv0; apply (r_bind_r_bind R). }
    apply maponpaths.
    etrans.
    apply map_on_two_paths. apply functor_comp. apply idpath.
    etrans.
    2: { etrans. 2: apply assoc.
         eapply pathsinv0. apply maponpaths. apply (r_eta_r_bind R).
    }
    apply pathsinv0, assoc.
Defined.

Definition R_functor {C: precategory_data} {D: precategory} {J : functor C D}
  (R : RelMonad): functor C D
  := _,, is_functor_r_lift(J:=J) R.


(** generalize [UniMath.CategoryTheory.Monads.KTriples.is_nat_trans_η] *)
Definition is_nat_trans_r_eta {C: precategory_data} {D: precategory} {J : functor C D}(R : RelMonad)
  : is_nat_trans J (R_functor R) (r_eta R).
Proof.
  red.
  intros c c' f.
  unfold R_functor; simpl.
  unfold r_lift; simpl.
  apply pathsinv0.
  apply (r_eta_r_bind R).
Defined.

Definition r_eta_nat_trans {C: precategory_data} {D: precategory} {J : functor C D}(R : RelMonad)
  : nat_trans J (R_functor R) := _ ,, is_nat_trans_r_eta R.


(** generalize [UniMath.CategoryTheory.Monads.KTriples.map_bind] *)
Definition r_lift_r_bind {C: precategory_data} {D: precategory} {J : functor C D}(R : RelMonad)(a b c : C) (f : b --> c) (g : J a --> R b)
  : r_bind R g · r_lift R f = r_bind R (g · r_lift R f).
Proof.
  unfold r_lift.
  rewrite <- (r_bind_r_bind R).
  apply idpath.
Defined.

(** generalize [UniMath.CategoryTheory.Monads.KTriples.bind_map] *)
Definition r_bind_r_lift {C: precategory_data} {D: precategory} {J : functor C D}(R : RelMonad)(a b c : C) (f : J b --> R c) (g : a --> b)
  : r_lift R g · r_bind R f = r_bind R (#J g · f).
Proof.
  unfold r_lift.
  rewrite (r_bind_r_bind R).
  apply maponpaths.
  rewrite <- assoc.
  apply cancel_precomposition.
  apply (r_eta_r_bind R).
Defined.


(* Underlying functor argument should be explicit for RelMonad_data and RelMonad *)
Arguments RelMonad_data {C} {D} J.
Arguments RelMonad {C} {D} J.


(** analogue of [UniMath.CategoryTheory.functor_categories.functor_eq_eq_from_functor_ob_eq *)
Definition relmonad_eq_eq_from_relmonad_ob_eq {C: precategory_data} {D: precategory} (hs: has_homsets D)
           {J : functor C D} (R R' : RelMonad J) (p q : R = R')
    (H : base_paths _ _ (base_paths _ _ p) =
         base_paths _ _ (base_paths _ _ q)) :
    p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
  assert (H' : base_paths _ _ p = base_paths _ _ q).
  { apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
    apply (two_arg_paths_f H), uip.
    apply isaset_dirprod.
    - apply impred_isaset; intro c. apply hs.
    - apply impred_isaset; intro c; apply impred_isaset; intro d; apply impred_isaset; intro f.
      apply hs.
  }
  apply (two_arg_paths_f H'), uip, isasetaprop, isaprop_RelMonad_axioms, hs.
Defined.


(** Kleisli precategory associated to a relative monad *)
Section Kleisli_precat.

Context {C: precategory_data} {D : precategory} {J : functor_data C D}.

Definition Kleisli_precat_ob_mor (R : RelMonad_data J) : precategory_ob_mor :=
  precategory_ob_mor_pair (ob C) (λ c d, J c --> R d).

Definition Kleisli_precat_data (R : RelMonad_data J) : precategory_data :=
  precategory_data_pair (Kleisli_precat_ob_mor R) (λ c, r_eta R c)
                                              (λ a b c f g, f · r_bind R g).

Lemma Kleisli_precat_is_precat (R : RelMonad J) : is_precategory (Kleisli_precat_data R).
Proof.
  apply is_precategory_one_assoc_to_two.
  do 2 try apply tpair;
    try unfold compose; simpl.
  - intros a b f.
    apply (r_eta_r_bind R).
  - intros a b f.
    now rewrite (r_bind_r_eta R), id_right.
  - intros a b c d f g h.
    now rewrite <- assoc, (r_bind_r_bind R).
Qed.

Definition Kleisli_precat (R : RelMonad J) : precategory := (_,, Kleisli_precat_is_precat R).

End Kleisli_precat.

(** Kleisli category associated to a relative monad *)
Section Kleisli_cat.

Lemma Kleisli_precat_has_homsets {C : precategory_data} {D : category} {J : functor_data C D} (R : RelMonad J)
      (hs : has_homsets D) : has_homsets (Kleisli_precat_data R).
Proof.
  intros a b.
  apply hs.
Defined.

Definition Kleisli_cat {C : precategory_data} {D : category} {J : functor_data C D} (R : RelMonad J)
  : category := (Kleisli_precat R,, Kleisli_precat_has_homsets R (homset_property D)).

End Kleisli_cat.

Section MorphismsOfRelativeMonads.

Definition RelMonadMor_data {C D : precategory_data}
           {J : functor_data C D} (R R' : RelMonad_data J): UU :=
  ∏ a : C, R a --> R' a.

Definition RelMonadMor_axioms {C D : precategory_data}
           {J : functor_data C D} {R R' : RelMonad_data J} (α : RelMonadMor_data R R') : UU
  := (∏ a : C, r_eta R a · α a = r_eta R' a) ×
     (∏ (a b : C) (f : D⟦J a,R b⟧), α a · r_bind R' (f · α b) = (r_bind R f)· α b).

Lemma isaprop_RelMonadMor_axioms {C D : precategory_data}
      {J : functor_data C D} {R R' : RelMonad_data J} (α : RelMonadMor_data R R')
      (hs : has_homsets D) :
  isaprop (RelMonadMor_axioms α).
Proof.
  apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

(** generalize [UniMath.CategoryTheory.Monads.KTriples.Kleisli_Mor_η] *)
Definition r_eta_α {C D : precategory_data} {J : functor_data C D}
           {R R' : RelMonad_data J} {α : RelMonadMor_data R R'}
           (X : RelMonadMor_axioms α)
  : ∏ a : C, r_eta R a · α a = r_eta R' a := pr1 X.

(** generalize [UniMath.CategoryTheory.Monads.KTriples.Kleisli_Mor_bind] *)
Definition α_r_bind {C D : precategory_data} {J : functor_data C D}
           {R R' : RelMonad_data J} {α : RelMonadMor_data R R'}
           (X : RelMonadMor_axioms α)
  : ∏ (a b : C) (f : D⟦J a,R b⟧), α a · r_bind R' (f · α b) = (r_bind R f) · α b  := pr2 X.

Definition RelMonadMor {C D : precategory_data} {J : functor_data C D}
           (R R' : RelMonad_data J) : UU
  := ∑ α : RelMonadMor_data R R', RelMonadMor_axioms α.
Coercion RelMonadMor_data_from_RelMonadMor  {C D : precategory_data} {J : functor_data C D}
           {R R' : RelMonad_data J} (α : RelMonadMor R R') : RelMonadMor_data R R' := pr1 α.

 Coercion RelMonadMor_axioms_from_RelMonadMor {C D : precategory_data} {J : functor_data C D}
         {R R' : RelMonad_data J} (α : RelMonadMor R R') :
  RelMonadMor_axioms α := pr2 α.

Definition RelMonadMor_map {C D : precategory_data} {J : functor_data C D}
           {R R' : RelMonad_data J} (f : RelMonadMor R R') (X : C)
  : R X --> R' X
  := (f : RelMonadMor_data _ _ ) X.

Definition RelMonadMor_equiv  {C D : precategory_data} (hs : has_homsets D)
           {J : functor_data C D} {R R' : RelMonad_data J} (α β : RelMonadMor R R') :
  α = β ≃ ((α: RelMonadMor_data R R') = β).
Proof.
  apply subtypeInjectivity.
  intro a.
  apply isaprop_RelMonadMor_axioms.
  exact hs.
Defined.

(** generalize [UniMath.CategoryTheory.Monads.KTriples.is_nat_trans_kleisli_mor] *)
Definition is_nat_trans_RelMonadMor {C : precategory_data} {D: precategory} {J : functor C D}
           {R R' : RelMonad J} (α : RelMonadMor R R'):
  is_nat_trans (R_functor R) (R_functor R') (α:RelMonadMor_data R R').
Proof.
  red.
  intros c c' f.
  unfold R_functor; simpl. unfold r_lift; simpl.
  rewrite <- (α_r_bind α).
  rewrite <- assoc.
  now rewrite (r_eta_α α).
Defined.

Definition nat_trans_RelMonadMor {C : precategory_data} {D: precategory} {J : functor C D}
           {R R' : RelMonad J} (α : RelMonadMor R R'):
  nat_trans (R_functor R) (R_functor R') := _ ,, is_nat_trans_RelMonadMor α.

End MorphismsOfRelativeMonads.

Section PrecategoryOfRelativeMonads.

(* ----- Identity Morphism ----- *)

Lemma RelMonad_identity_laws {C : precategory_data} {D : precategory}
      {J : functor_data C D} (R : RelMonad_data J):
  RelMonadMor_axioms (λ a : C, identity (R a)).
Proof.
  split; simpl; intros c.
  - apply id_right.
  - intros. do 2 rewrite id_right; apply id_left.
Defined.

Definition RelMonad_identity {C : precategory_data} {D : precategory}
  {J : functor_data C D} (R : RelMonad_data J): RelMonadMor R R
  := _ ,, RelMonad_identity_laws R.

(* ----- Composition of Morphisms ----- *)

(** generalize [UniMath.CategoryTheory.Monads.KTriples.Kleisli_composition_laws] *)
Lemma RelMonad_composition_laws {C : precategory_data} {D : precategory}
      {J : functor_data C D} {R R' R'' : RelMonad_data J}
      (α : RelMonadMor R R') (α' : RelMonadMor R' R''):
  RelMonadMor_axioms (λ a : C, (α : RelMonadMor_data R R') a · (α' : RelMonadMor_data R' R'') a).
Proof.
  split; intros; simpl.
  - rewrite assoc.
    rewrite (r_eta_α α).
    apply (r_eta_α α').
  - intermediate_path ((α:RelMonadMor_data R R') a ·
             ((α':RelMonadMor_data R' R'') a ·
              r_bind R'' ((f · (α:RelMonadMor_data R R') b) ·
                        (α':RelMonadMor_data R' R'') b))).
    * now repeat rewrite assoc.
    * rewrite (α_r_bind α').
      rewrite assoc. rewrite (α_r_bind α).
      apply pathsinv0. apply assoc.
Defined.

Definition RelMonad_composition {C : precategory_data} {D : precategory}
      {J : functor_data C D} {R R' R'' : RelMonad_data J}
      (α : RelMonadMor R R') (α' : RelMonadMor R' R''):
  RelMonadMor R R'' := _ ,, RelMonad_composition_laws α α'.

(* ----- Precategory of relative Monads (for a given functor [J]) ----- *)

Definition precategory_RelMonad_ob_mor  {C : precategory_data} {D : precategory}
      (J : functor_data C D) : precategory_ob_mor :=
  precategory_ob_mor_pair (RelMonad J) RelMonadMor.

Definition precategory_RelMonad_data {C : precategory_data} {D : precategory}
           (J : functor_data C D) : precategory_data.
Proof.
  apply (precategory_data_pair (precategory_RelMonad_ob_mor J)).
  - intro R.
    apply RelMonad_identity.
  - intros R R' R'' α α'.
    apply (RelMonad_composition α α').
Defined.

Lemma precategory_RelMonad_axioms {C : precategory_data} {D : precategory}
      (hs : has_homsets D) (J : functor_data C D) :
  is_precategory (precategory_RelMonad_data J).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (RelMonadMor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_left.
  - apply (invmap (RelMonadMor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_right.
  - apply (invmap (RelMonadMor_equiv hs _ _ )).
    apply funextsec. intros x. apply assoc.
  - apply (invmap (RelMonadMor_equiv hs _ _ )).
    apply funextsec. intros x. apply assoc'.
Defined.

Definition precategory_RelMonad {C : precategory_data} {D : precategory}
      (hs : has_homsets D) (J : functor_data C D): precategory :=
  _ ,, precategory_RelMonad_axioms hs J.

Lemma has_homsets_RelMonad {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor_data C D) :
  has_homsets (precategory_RelMonad hs J).
Proof.
  intros R R'. simpl. unfold RelMonadMor.
  apply isaset_total2 .
  - apply impred_isaset.
    intro. apply hs.
  - intro α.
    apply isasetaprop.
    apply isaprop_RelMonadMor_axioms.
    apply hs.
Defined.

(* ----- Category of relative Monads (for a given functor [J]) ----- *)

Definition category_RelMonad {C : precategory_data} (D : category)
      (J : functor_data C D) : category :=
  precategory_RelMonad (homset_property D) J,, has_homsets_RelMonad (homset_property D) J.


Definition forgetfunctor_RelMonad {C : precategory} (D : category)
      (J : functor C D) :
  functor (category_RelMonad D J) (functor_category C D).
Proof.
  use mk_functor.
  - simpl.
    use mk_functor_data.
    + simpl.
      exact (λ R : RelMonad J, R_functor R).
    + simpl. intros R R' α.
      exact (nat_trans_RelMonadMor α).
  - split.
    + red. intros. simpl. apply nat_trans_eq.
      * apply D.
      * intros; apply idpath.
    + unfold functor_compax. simpl. intros R R' R'' α α'. apply nat_trans_eq.
      * apply D.
      * intro c. apply idpath.
Defined.

Lemma forgetRelMonad_faithful {C : precategory} (D : category)
      (J : functor C D) : faithful (forgetfunctor_RelMonad D J).
Proof.
  intros R R'. simpl.
  apply isinclbetweensets.
  - apply isaset_total2.
    + apply impred_isaset.
      intros. apply D.
    + intros. apply isasetaprop. apply isaprop_RelMonadMor_axioms. apply D.
  - apply isaset_nat_trans. apply D.
  - intros α α' p.
    apply RelMonadMor_equiv.
    + apply D.
    + apply funextsec. intro c.
      change (nat_trans_RelMonadMor α c = nat_trans_RelMonadMor α' c).
      rewrite p.
      apply idpath.
Defined.


End PrecategoryOfRelativeMonads.

Section RelativeMonads_saturated.

Definition relmonadmor_weq_nat_trans_fails {C : precategory_data} {D : precategory} (hs: has_homsets D)
           (J : functor C D)(R R': RelMonad J) :
  (precategory_RelMonad hs J ⟦R, R'⟧) ≃ [C, D, hs] ⟦R_functor R, R_functor R'⟧.
Proof.
  apply (weqpair nat_trans_RelMonadMor).
  use isweq_iso.
  - intro α.
    exists (nat_trans_data_from_nat_trans α).
    split; intros.
    (* nothing like that! *)
Abort.


Definition relmonadmor_eq_type  {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor C D)(R R': RelMonad J) : UU
  := ∑ p : iso (C := [C, D, hs]) (R_functor R) (R_functor R'),
           RelMonadMor_axioms (nat_trans_data_from_nat_trans (morphism_from_iso _ _ _ p)).

Definition relmonadmor_ob_eq  {C : precategory_data} {D : precategory} (H: is_univalent D)
      (J : functor C D)(R R': RelMonad J) :
  (R = R') ≃ relmonadmor_eq_type (pr2 H) J R R'.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - set (H1 := weqpair _ (pr1 (is_univalent_functor_category C D H) (R_functor R) (R_functor R'))).
Abort.


(** better upstream *)
Definition functor_iso_pointwise_if_iso' (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C',hs]) (α: iso F G) :
     ∏ a : ob C,
       iso (pr1 F a) (pr1 G a) :=
  λ a, tpair _ _ (is_functor_iso_pointwise_if_iso C C' _ F G (pr1 α) (pr2 α) a).

Lemma idtoiso_functorcat_compute_pointwise' (C : precategory_data) (D : precategory)
  (hs: has_homsets D) (F G : ob [C, D, hs])
     (p : F = G) (a : ob C) :
  functor_iso_pointwise_if_iso' C D _ F G (idtoiso p) a =
idtoiso
  (toforallpaths (λ _ : ob C, D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  apply eq_iso. apply idpath.
Qed.
(** end of better upstream *)


(** a rather trivial observation *)
Definition is_iso_from_is_relmonadmor_iso  {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R')
  : is_iso(C := [C, D, hs]) (nat_trans_RelMonadMor (pr1 α)).
Proof.
  apply is_iso_from_is_z_iso.
  set (H' := iso_inv_after_iso α).
  set (H'':= iso_after_iso_inv α).
  set (α' := inv_from_iso α).
  exists (nat_trans_RelMonadMor α').
  split; simpl.
  - unfold α'. unfold R_functor.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (nat_trans_eq hs).
    set (aux := maponpaths pr1 H'). apply toforallpaths in aux.
    exact aux.
  - unfold α'. unfold R_functor.
    apply (nat_trans_eq hs).
    set (aux := maponpaths pr1 H''). apply toforallpaths in aux.
    exact aux.
Defined.

(** its immediate consequence *)
Definition iso_from_is_relmonadmor_iso  {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R')
  : iso(C := [C, D, hs]) (R_functor R) (R_functor R').
Proof.
  use (isopair(C := [C, D, hs]) (nat_trans_RelMonadMor (pr1 α))).
  exact (is_iso_from_is_relmonadmor_iso hs J α).
Defined.

Corollary iso_from_is_relmonadmor_iso_p  {C : precategory_data} {D : precategory} (hs: has_homsets D)
          (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R') (c : C) :
  pr1 (pr1 α) c =
        functor_iso_pointwise_if_iso' C D
          hs (R_functor R) (R_functor R') (iso_from_is_relmonadmor_iso
            hs J α) c.
Proof.
  apply idpath.
Defined.


Lemma iso_from_is_relmonadmor_iso_idtoiso {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor C D) {R R': RelMonad J} (p : @paths (precategory_RelMonad hs J) R R'):
  iso_from_is_relmonadmor_iso hs J (idtoiso p) =
  idtoiso(C := [C, D, hs]) (maponpaths (@R_functor C D J) p).
Proof.
  unfold iso_from_is_relmonadmor_iso.
  simpl.
  apply eq_iso.
  simpl.
  apply nat_trans_eq.
  - exact hs.
  - intro c.
    induction p.
    apply idpath.
Qed.


Definition alternative_inv_to_relmonadmor_iso {C : precategory_data} {D : precategory} (hs: has_homsets D)
           (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R')
  : precategory_RelMonad hs J ⟦R', R⟧.
Proof.
  use tpair.
  - intro c.
    exact (inv_from_iso (functor_iso_pointwise_if_iso' C D
          hs (R_functor R) (R_functor R') (iso_from_is_relmonadmor_iso
            hs J α) c)).
  - split.
    + intro c.
      apply pathsinv0.
      apply iso_inv_on_left.
      rewrite <- iso_from_is_relmonadmor_iso_p.
      apply pathsinv0.
      apply (r_eta_α (RelMonadMor_axioms_from_RelMonadMor (pr1 α))).
    + intros c d f.
      apply iso_inv_on_left.
      rewrite <- assoc.
      apply pathsinv0.
      apply iso_inv_on_right.
      do 2 rewrite <- iso_from_is_relmonadmor_iso_p.
      intermediate_path (pr1 (pr1 α) c · r_bind R' ((f · (inv_from_iso
           (functor_iso_pointwise_if_iso' C D hs (R_functor R)
              (R_functor R') (iso_from_is_relmonadmor_iso hs J α) d) )) ·
                  (functor_iso_pointwise_if_iso' C D hs (R_functor R)
                      (R_functor R') (iso_from_is_relmonadmor_iso hs J α) d ))).
      2: { apply cancel_precomposition.
           apply maponpaths.
           rewrite <- assoc.
           rewrite iso_after_iso_inv.
           apply id_right.
      }
      apply pathsinv0.
      rewrite <- iso_from_is_relmonadmor_iso_p.
      apply (α_r_bind (RelMonadMor_axioms_from_RelMonadMor (pr1 α))).
Defined.

Lemma alternative_inv_to_relmonadmor_iso_is_inv {C : precategory_data} {D : precategory} (hs: has_homsets D)
      (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R'):
  alternative_inv_to_relmonadmor_iso hs J α = inv_from_iso α.
Proof.
  apply inv_iso_unique'.
  unfold precomp_with.
  apply RelMonadMor_equiv.
  - exact hs.
  - apply funextsec.
    intro c.
    unfold alternative_inv_to_relmonadmor_iso.
    simpl.
    apply pathsinv0.
    apply iso_inv_on_left.
    rewrite id_left.
    intermediate_path (pr1 (pr1 α) c).
    { apply idpath. }
    rewrite iso_from_is_relmonadmor_iso_p.
    apply idpath.
Qed.

Corollary iso_from_is_relmonadmor_iso_inv_p  {C : precategory_data} {D : precategory} (hs: has_homsets D)
          (J : functor C D) {R R': RelMonad J} (α : iso(C := precategory_RelMonad hs J) R R') (c : C) :
  pr1 (inv_from_iso α) c =
        inv_from_iso (functor_iso_pointwise_if_iso' C D
          hs (R_functor R) (R_functor R') (iso_from_is_relmonadmor_iso
            hs J α) c).
Proof.
  rewrite <- alternative_inv_to_relmonadmor_iso_is_inv.
  apply idpath.
Qed.


(** the other direction, first the inverse monad morphism *)
Definition inv_relmonadmor_from_is_iso {C : precategory_data} {D : precategory}
           (hs: has_homsets D) (J : functor C D){R R': RelMonad J}
           (α : precategory_RelMonad hs J ⟦R, R'⟧)
  : is_iso(C := [C, D, hs]) (nat_trans_RelMonadMor α) → precategory_RelMonad hs J ⟦R', R⟧.
Proof.
  intro T.
  set (fiso := isopair(C := [C, D, hs]) (nat_trans_RelMonadMor α) T).
  set (finv := inv_from_iso fiso).
  exists (pr1 finv).
  unfold finv.
  split.
  - intros c.
    unfold fiso.
    rewrite <- nat_trans_inv_pointwise_inv_after_p.
    apply pathsinv0.
    apply iso_inv_on_left.
    simpl.
    apply pathsinv0.
    apply (r_eta_α (RelMonadMor_axioms_from_RelMonadMor α)).
  - intros a b f.
    unfold fiso.
    do 2 rewrite <- nat_trans_inv_pointwise_inv_after_p.
    apply iso_inv_on_left.
    rewrite <- assoc.
    apply pathsinv0.
    apply iso_inv_on_right.
    simpl.
    etrans.
    { apply pathsinv0.
      apply (α_r_bind (RelMonadMor_axioms_from_RelMonadMor α)). }
    apply cancel_precomposition.
    apply maponpaths.
    rewrite <- assoc.
    etrans.
    2: { apply id_right. }
    apply cancel_precomposition.
    apply iso_inv_on_right.
    apply pathsinv0.
    apply id_right.
Defined.

(** verification that the proposed inverse monad morphism is suitable *)
Definition is_relmonadmor_iso_from_is_iso {C : precategory_data} {D : precategory}
           (hs: has_homsets D) (J : functor C D) {R R': RelMonad J}
           (α : precategory_RelMonad hs J ⟦R, R'⟧)
  : is_iso(C := [C, D, hs]) (nat_trans_RelMonadMor α) → is_iso α.
Proof.
  intro T.
  apply is_iso_from_is_z_iso.
  exists (inv_relmonadmor_from_is_iso hs J α T).
  split; simpl.
  - (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply RelMonadMor_equiv.
    + exact hs.
    + simpl.
      set (aux := iso_inv_after_iso (isopair(C := [C, D, hs]) (nat_trans_RelMonadMor α) T)).
      apply (maponpaths pr1) in aux.
      exact aux.
  - apply RelMonadMor_equiv.
    + exact hs.
    + simpl.
      set (aux := iso_after_iso_inv (isopair(C := [C, D, hs]) (nat_trans_RelMonadMor α) T)).
      apply (maponpaths pr1) in aux.
      exact aux.
Defined.

(** its immediate consequence *)
Definition relmonadmor_iso_from_is_iso {C : precategory_data} {D : precategory}
           (hs: has_homsets D) (J : functor C D)(R R': RelMonad J)
           (α : precategory_RelMonad hs J ⟦R, R'⟧)
  : is_iso(C := [C, D, hs]) (nat_trans_RelMonadMor α) → iso(C := precategory_RelMonad hs J) R R'.
Proof.
  intro T.
  use (isopair α).
  exact (is_relmonadmor_iso_from_is_iso hs J α T).
Defined.


Definition relmonadmor_iso_first_iso {C : precategory_data} {D : precategory}
           (hs: has_homsets D) (J : functor C D)(R R': RelMonad J)
  : iso(C := precategory_RelMonad hs J) R R' ≃ ∑ α : R_functor R ⟹ R_functor R', is_iso(C := [C, D, hs]) α.
Proof.
  unfold iso.
Abort.

Definition pr1_pr1_relmonadmor_eq_from_relmonadmor_iso {C : precategory_data} {D : precategory}
   (H: is_univalent D) (J : functor C D) {R R': RelMonad J} :
  iso(C := precategory_RelMonad (pr2 H) J) R R' -> pr1 (pr1 R) = pr1 (pr1 R').
Proof.
  intro α.
  change (pr1 (pr1 (R_functor R)) = pr1 (pr1 (R_functor R'))).
  do 2 apply maponpaths.
  set (H1 := weqpair _ (pr1 (is_univalent_functor_category C D H) (R_functor R) (R_functor R'))).
  apply H1.
  apply (iso_from_is_relmonadmor_iso (pr2 H) J α).
Defined.


Lemma pr1_pr1_relmonadmor_eq_from_relmonadmor_iso_idtoiso_aux {C : precategory_data} {D : precategory}
      (hs: has_homsets D) (J : functor C D) {R R': RelMonad J}
      (p: @paths (precategory_RelMonad hs J) R R'):
  base_paths (pr1 (R_functor R)) (pr1 (R_functor R'))
             (base_paths (R_functor R) (R_functor R') (maponpaths R_functor p)) =
  base_paths (pr1 R) (pr1 R') (base_paths R R' p).
Proof.
  unfold base_paths.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  etrans.
  { apply maponpaths.
    apply (maponpathscomp (@R_functor C D J) (@functor_data_from_functor C D)).
  }
  etrans.
  { apply (maponpathscomp ((functor_data_from_functor C D ∘ R_functor)%functions) (@functor_on_objects C D)). }
  etrans.
  2: { apply pathsinv0.
       apply (maponpathscomp  (@RelMonad_data_from_RelMonad C D J) (@RelMonad_ob C D J)).
  }
  apply idpath.
Qed.

Lemma pr1_pr1_relmonadmor_eq_from_relmonadmor_iso_idtoiso {C : precategory_data} {D : precategory}
      (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
      (p: @paths (precategory_RelMonad (pr2 H) J) R R'):
  pr1_pr1_relmonadmor_eq_from_relmonadmor_iso H J (idtoiso p) =
  base_paths (pr1 R) (pr1 R') (base_paths R R' p).
Proof.
  unfold pr1_pr1_relmonadmor_eq_from_relmonadmor_iso.
  simpl.
  rewrite (iso_from_is_relmonadmor_iso_idtoiso (pr2 H) J).
  rewrite functor_eq_from_functor_iso_idtoiso.
  apply pr1_pr1_relmonadmor_eq_from_relmonadmor_iso_idtoiso_aux.
Qed.


Lemma transport_of_relmonad_η_is_pointwise {C : precategory_data} {D : precategory}
      (J : functor C D) (F0 G0 : ob C -> ob D)
      (F1 : ∏ a : ob C, J a --> F0 a)
      (gamma : F0 = G0 )
      (c: ob C) :
  transportf (fun x : ob C -> ob D => ∏ a, D ⟦J a, x a⟧) gamma F1 c =
  transportf (fun d: ob D => D ⟦J c, d⟧) (toforallpaths (λ _ : ob C, D) F0 G0 gamma c) (F1 c).
Proof.
  induction gamma.
  apply idpath.
Defined.

Lemma transport_of_relmonad_bind_is_pointwise {C : precategory_data} {D : precategory}
      (J : functor C D) (F0 G0 : ob C -> ob D)
      (F1 : ∏ a b : ob C , D ⟦J a, F0 b⟧ → D ⟦F0 a, F0 b⟧)
      (gamma : F0 = G0 )
      (c d : ob C) (f : J c --> G0 d) :
  transportf (fun x : ob C -> ob D => ∏ a b : ob C , D ⟦J a, x b⟧ → D ⟦x a, x b⟧) gamma F1 c d f =
  double_transport (toforallpaths (λ _ : ob C, D) F0 G0 gamma c)
                   (toforallpaths (λ _ : ob C, D) F0 G0 gamma d)
                   (F1 c d (transportb (fun x : ob D => D ⟦J c, x⟧)
                                       (toforallpaths (λ _ : ob C, D) F0 G0 gamma d) f)).
Proof.
  induction gamma.
  apply idpath.
Defined.

(** a preparation for the following lemma *)
Lemma isotoid_functorcat_pointwise_aux (C : precategory_data) (D : precategory)
      (H : is_univalent D) (F G : ob [C, D, (pr2 H)]) (p: F = G) (c: C) :
  let α := idtoiso p in
   toforallpaths (fun _ : ob C => ob D) (pr1 (pr1 F)) (pr1 (pr1 G))
    (maponpaths pr1
       (maponpaths pr1
          (isotoid [C, D, pr2 H]
                   (is_univalent_functor_category C D H) α))) c
   = isotoid D H
             (functor_iso_pointwise_if_iso C D (pr2 H) F G α (pr2 α) c).
Proof.
  induction p.
  cbn delta in *.
  unfold functor_iso_pointwise_if_iso.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  rewrite isotoid_idtoiso.
  unfold idtoiso.
  simpl.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  simpl.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply eq_iso.
  apply idpath.
Defined.


(** general lemma on univalence of functor category *)
Lemma isotoid_functorcat_pointwise (C : precategory_data) (D : precategory) (H : is_univalent D)
      (F G : ob [C, D, (pr2 H)]) (α: iso F G) (c: C) :
   toforallpaths (fun _ : ob C => ob D) (pr1 (pr1 F)) (pr1 (pr1 G))
    (maponpaths pr1
       (maponpaths pr1
          (isotoid [C, D, pr2 H]
                   (is_univalent_functor_category C D H) α))) c
   = isotoid D H
             (functor_iso_pointwise_if_iso' C D (pr2 H) F G α c).
Proof.
  assert (aux := isotoid_functorcat_pointwise_aux C D H F G
                      (isotoid [C, D, pr2 H] (is_univalent_functor_category C D H) α)).
  rewrite idtoiso_isotoid in aux.
  apply aux.
Qed.

Definition η_relmonadmor_eq_from_relmonadmor_iso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
           (α: iso(C := precategory_RelMonad (pr2 H) J) R R')
  : transportf (fun x : ob C -> ob D => ∏ c, D ⟦J c, x c⟧)
               (pr1_pr1_relmonadmor_eq_from_relmonadmor_iso H J α) (pr1 (pr2 (pr1 R))) =
    pr1 (pr2 (pr1 R')).
Proof.
  apply funextsec; intro c.
  rewrite transport_of_relmonad_η_is_pointwise.
  unfold pr1_pr1_relmonadmor_eq_from_relmonadmor_iso.
  simpl.
  rewrite <- idtoiso_postcompose.
  simpl.
  change (pr1 (pr2 (pr1 R')) c) with (r_eta R' c).
  change (pr1 (pr2 (pr1 R)) c) with (r_eta R c).
  intermediate_path (r_eta R c · (pr1 (pr1 α): RelMonadMor_data _ _) c).
  2: { set (X := RelMonadMor_axioms_from_RelMonadMor (pr1 α)).
       exact (pr1 X c).
       (* does not terminate: apply (r_eta_α X). *)
  }
  apply cancel_precomposition.
  set (isor := iso_from_is_relmonadmor_iso (pr2 H) J α).
  set (isor_p := functor_iso_pointwise_if_iso' C D (pr2 H) _ _ isor c).
  change (pr1 (pr1 α) c) with (pr1 isor_p).
  apply maponpaths.
  unfold precategory_data_from_precategory in isor.
  simpl in isor.
  unfold precategory_data_from_precategory; simpl.
  fold isor.
  intermediate_path (idtoiso (isotoid _ H isor_p)).
  2: { apply idtoiso_isotoid. }
  apply maponpaths.
  change (functor_eq_from_functor_iso
             (pr2 H) H (R_functor R)
             (R_functor R') isor) with (isotoid _ (is_univalent_functor_category C D H) isor).
  apply (isotoid_functorcat_pointwise C D H (R_functor R) (R_functor R')).
Defined.


(** the dual of [UniMath.MoreFoundations.PartA.transportf_transpose] *)
Lemma transportb_transpose {X : UU} {P : X → UU} {x x' : X}
      (e : x' = x) (y : P x) (y' : P x') :
      transportf P e y' = y -> y' = transportb P e y.
Proof.
intro H; induction e; exact H.
Defined.

(** the following lemma should also be put upstream *)
Lemma transportb_isotoid (C : precategory) (H : is_univalent C)
   (a b b' : ob C) (p : iso b b') (f : a --> b') :
 transportb (λ b0 : C, a --> b0) (isotoid C H p) f = f · inv_from_iso p.
Proof.
  apply pathsinv0.
  apply transportb_transpose.
  change (precategory_morphisms a) with (λ b0 : C, a --> b0).
  rewrite transportf_isotoid'.
  rewrite <- assoc.
  rewrite iso_after_iso_inv.
  apply id_right.
Qed.


Definition bind_relmonadmor_eq_from_relmonadmor_iso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
           (α: iso(C := precategory_RelMonad (pr2 H) J) R R')
  : transportf (fun x : ob C -> ob D => ∏ c d, D ⟦J c, x d⟧ → D ⟦x c, x d⟧)
               (pr1_pr1_relmonadmor_eq_from_relmonadmor_iso H J α) (pr2 (pr2 (pr1 R))) =
    pr2 (pr2 (pr1 R')).
Proof.
  apply funextsec; intro c. apply funextsec; intro d. apply funextsec; intro f.
  rewrite transport_of_relmonad_bind_is_pointwise.
  unfold pr1_pr1_relmonadmor_eq_from_relmonadmor_iso.
  simpl.
  rewrite double_transport_idtoiso.
  rewrite <- assoc.
  set (isor := iso_from_is_relmonadmor_iso (pr2 H) J α).
  unfold precategory_data_from_precategory in isor.
  simpl in isor.
  unfold precategory_data_from_precategory; simpl.
  fold isor.
  change (functor_eq_from_functor_iso
             (pr2 H) H (R_functor R)
             (R_functor R') isor) with (isotoid _ (is_univalent_functor_category C D H) isor).
  do 2 rewrite (isotoid_functorcat_pointwise C D H (R_functor R) (R_functor R')).
  do 2 rewrite idtoiso_isotoid.
  change (pr2 (pr2 (pr1 R')) c d f) with (r_bind R' f).
  change (pr2 (pr2 (pr1 R)) c d) with (r_bind(c:=c)(d:=d) R).
  rewrite (transportb_isotoid D H).
  do 2 rewrite <- (iso_from_is_relmonadmor_iso_inv_p (pr2 H) J α).
  rewrite <- (iso_from_is_relmonadmor_iso_p (pr2 H) J α).
  assert (aux := α_r_bind (RelMonadMor_axioms_from_RelMonadMor (inv_from_iso α)) c d f).
  etrans.
  { apply assoc. }
  etrans.
  { apply cancel_postcomposition.
    apply aux.
  }
  intermediate_path (r_bind R' f · identity _).
  2: { apply id_right. }
  etrans.
  { apply pathsinv0. apply assoc. }
  apply cancel_precomposition.
  assert (aux2 := iso_after_iso_inv α).
  apply (maponpaths pr1) in aux2.
  apply toforallpaths in aux2.
  apply aux2.
Defined.


Definition relmonad_eq_from_relmonad_iso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
           (α : iso(C := precategory_RelMonad (pr2 H) J) R R')
  : R = R'.
Proof.
  apply RelMonad_eq.
  - exact (pr2 H).
  - set (Hob := pr1_pr1_relmonadmor_eq_from_relmonadmor_iso H J α).
    apply (total2_paths_f Hob).
    apply dirprodeq.
    + intermediate_path (transportf (λ F : C → D, ∏ c : C, D ⟦ J c, F c ⟧) Hob
                                    (pr1 (pr2 (pr1 R)))).
      { apply pathsinv0. apply (transport_map (fun F => dirprod_pr1(X := ∏ c : C, D ⟦ J c, F c ⟧)(Y := ∏ c d : C, D ⟦ J c, F d ⟧ → D ⟦ F c, F d ⟧))). }
      apply (η_relmonadmor_eq_from_relmonadmor_iso H J α).
    + intermediate_path (transportf (λ F : C → D, ∏ c d : C, D ⟦ J c, F d ⟧ → D ⟦ F c, F d ⟧) Hob
                                    (pr2 (pr2 (pr1 R)))).
      { apply pathsinv0. apply (transport_map (fun F => dirprod_pr2(X := ∏ c : C, D ⟦ J c, F c ⟧)(Y := ∏ c d : C, D ⟦ J c, F d ⟧ → D ⟦ F c, F d ⟧))). }
      apply (bind_relmonadmor_eq_from_relmonadmor_iso H J α).
Defined.

(* former more destructive proof: *)
Definition relmonad_eq_from_relmonad_iso_obsolete {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
           (α : iso(C := precategory_RelMonad (pr2 H) J) R R')
  : R = R'.
Proof.
  set (Hob := pr1_pr1_relmonadmor_eq_from_relmonadmor_iso H J α).
  assert (η_eq := η_relmonadmor_eq_from_relmonadmor_iso H J α).
  assert (bind_eq := bind_relmonadmor_eq_from_relmonadmor_iso H J α).
  fold Hob in η_eq, bind_eq.
  induction R as [[F [e b]] a].
  induction R' as [[F' [e' b']] a'].
  simpl in Hob.
  induction Hob.
  cbn in η_eq, bind_eq.
  apply RelMonad_eq.
  + exact (pr2 H).
  + simpl.
    apply maponpaths.
    apply pathsdirprod; assumption.
Defined.

Lemma relmonad_eq_from_relmonad_iso_idtoiso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J} (p: R = R') :
  relmonad_eq_from_relmonad_iso H J (idtoiso(C := precategory_RelMonad (pr2 H) J) p) = p.
Proof.
  apply relmonad_eq_eq_from_relmonad_ob_eq.
  - apply (pr2 H).
  - unfold relmonad_eq_from_relmonad_iso.
    unfold RelMonad_eq.
    rewrite base_total2_paths.
    rewrite base_total2_paths.
    apply pr1_pr1_relmonadmor_eq_from_relmonadmor_iso_idtoiso.
Qed.



Lemma idtoiso_relmonad_eq_from_relmonad_iso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D) {R R': RelMonad J}
           (α : iso(C := precategory_RelMonad (pr2 H) J) R R') :
        idtoiso(C := precategory_RelMonad (pr2 H) J) (relmonad_eq_from_relmonad_iso H J α) = α.
Proof.
  apply eq_iso.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply RelMonadMor_equiv.
  - exact (pr2 H).
  - (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply funextsec; intro c.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    etrans.
    { apply iso_from_is_relmonadmor_iso_p. }
    rewrite (iso_from_is_relmonadmor_iso_idtoiso (pr2 H) J (relmonad_eq_from_relmonad_iso H J α)).
    rewrite idtoiso_functorcat_compute_pointwise'.
    unfold relmonad_eq_from_relmonad_iso.
    unfold RelMonad_eq.
    rewrite pr1_pr1_relmonadmor_eq_from_relmonadmor_iso_idtoiso_aux; try apply (pr2 H).
    rewrite base_total2_paths.
    rewrite base_total2_paths.
    intermediate_path (pr1 (idtoiso
     (isotoid D H (functor_iso_pointwise_if_iso' C D (pr2 H) _ _ (iso_from_is_relmonadmor_iso (pr2 H) J α) c)))).
    2: { rewrite idtoiso_isotoid.
         apply idpath.
    }
    apply maponpaths.
    apply maponpaths.
    apply isotoid_functorcat_pointwise.
Qed.


Definition relmonadmor_idtoiso {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D)(R R': RelMonad J) :
  (R = R') ≃ iso(C := precategory_RelMonad (pr2 H) J) R R'.
Proof.
  apply (weqpair (@idtoiso (precategory_RelMonad (pr2 H) J) R R')).
  use isweq_iso.
  - exact (relmonad_eq_from_relmonad_iso H J).
  - intro p. exact (relmonad_eq_from_relmonad_iso_idtoiso H J p).
  - intro α. exact (idtoiso_relmonad_eq_from_relmonad_iso H J α).
Defined.

Lemma isweq_idtoiso_RelMonad {C : precategory_data} {D : precategory}
           (H: is_univalent D) (J : functor C D)(R R': RelMonad J)
  : isweq (@idtoiso (precategory_RelMonad (pr2 H) J) R R').
Proof.
  apply (isweqhomot (relmonadmor_idtoiso H J R R')).
  - intro p. induction p.
    apply idpath.
  - apply (pr2 _ ).
Qed.

Lemma is_univalent_RelMonad {C : precategory_data} {D : precategory}
      (H: is_univalent D) (J : functor C D)(R R': RelMonad J)
  : is_univalent (precategory_RelMonad (pr2 H) J).
Proof.
  split.
  - apply isweq_idtoiso_RelMonad.
  - clear R R'. intros R R'.
    apply (has_homsets_RelMonad (pr2 H) J).
Defined.



End RelativeMonads_saturated.

Section RelAdjunctionWithKleisliCategory.
(** The canonical relative adjunction between J and the Kleisli category of a J-relative monad

    This is the obvious generalization of the material in [UniMath.CategoryTheory.Monads.KleisliCategory].

*)

Definition Left_rKleisli_functor_data {C: precategory_data} {D : precategory}
             {J : functor_data C D} (R: RelMonad J) :
  functor_data C (Kleisli_precat R).
Proof.
  use mk_functor_data.
  - apply idfun.
  - intros a b f; unfold idfun.
    exact (#J f · (r_eta R) b).
Defined.

Lemma Left_rKleisli_is_functor {C: precategory_data} {D : precategory}
      {J : functor C D} (R: RelMonad J) :
  is_functor (Left_rKleisli_functor_data R).
Proof.
  split.
  - intro a.
    unfold Left_rKleisli_functor_data; simpl.
    rewrite functor_id.
    apply id_left.
  - intros a b c f g.
    unfold Left_rKleisli_functor_data; simpl.
    unfold compose at 3; simpl.
    rewrite functor_comp.
    do 2 (rewrite <- assoc).
    apply cancel_precomposition.
    apply pathsinv0.
    apply (r_eta_r_bind R).
Defined.

Definition Left_rKleisli_functor {C: precategory_data} {D : precategory}
      {J : functor C D} (R: RelMonad J) :
  functor C (Kleisli_precat R)
  := (Left_rKleisli_functor_data R,,Left_rKleisli_is_functor R).

Definition Right_rKleisli_functor_data {C: precategory_data} {D : precategory}
      {J : functor_data C D} (R: RelMonad J):
  functor_data (Kleisli_precat R) D.
Proof.
  use mk_functor_data.
  - exact R.
  - intros a b.
    apply r_bind.
Defined.

Lemma Right_rKleisli_is_functor {C: precategory_data} {D : precategory}
      {J : functor C D} (R: RelMonad J) :
  is_functor (Right_rKleisli_functor_data R).
Proof.
  use tpair.
  - intro a.
    unfold Right_rKleisli_functor_data; unfold identity;
    unfold functor_on_morphisms; simpl.
    apply (r_bind_r_eta R).
  - intros a b c f g; simpl.
    apply pathsinv0.
    apply (r_bind_r_bind R).
Defined.

Definition Right_rKleisli_functor {C: precategory_data} {D : precategory}
      {J : functor C D} (R: RelMonad J) :
  functor (Kleisli_precat R) D
  := (Right_rKleisli_functor_data R,,Right_rKleisli_is_functor R).

(** Composition of the left and right Kleisli functors is equal to [R] as a functor **)

Definition rKleisli_functor_left_right_compose {C: precategory} {D : precategory}
  (hs : has_homsets D) {J : functor C D} (R: RelMonad J) :
  (Left_rKleisli_functor R) ∙ (Right_rKleisli_functor R) = R_functor R.
Proof.
  use functor_eq.
  - exact hs.
  - use functor_data_eq_from_nat_trans.
    + intro a; apply idpath.
    + intros a b f; simpl.
      rewrite id_right.
      rewrite id_left.
      apply idpath.
Defined.

(** Showing that these functors are relative adjoints *)

Definition rKleisli_functors_are_relative_adjoints {C: precategory_data} {D : precategory}
           (hs : has_homsets D) {J : functor C D} (R: RelMonad J) :
  are_relative_adjoints J (Left_rKleisli_functor R) (Right_rKleisli_functor R).
Proof.
  use tpair.
  - intros a b.
    use tpair.
    + simpl.
      apply idfun.
    + simpl.
      apply idisweq.
  - unfold idfun; split.
    + intros a b f c h.
      simpl.
      unfold compose at 1; simpl.
      rewrite <- assoc.
      apply cancel_precomposition.
      apply (r_eta_r_bind R).
    + intros a b f c k; simpl.
      reflexivity.
Defined.

End RelAdjunctionWithKleisliCategory.