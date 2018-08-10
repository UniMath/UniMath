(** **********************************************************

Contents:

- Definition of relative monads [RelMonad]
- Functoriality for relative monads [r_lift]
- Kleisli category associated to a relative monad [Kleisli_precat] [Kleisli_cat]

Reference: % \cite{DBLP:journals/corr/AltenkirchCU14} \par %

Written by: Benedikt Ahrens (started May 2017)
Extended by: Ralph Matthes (starting August 2018)


************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.

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

(** Kleisli precategory associated to a relative monad *)
Section Kleisli_precat.

Context {C: precategory_data} {D : precategory} {J : functor_data C D}.

Definition Kleisli_precat_ob_mor (R : RelMonad_data J) : precategory_ob_mor :=
  precategory_ob_mor_pair (ob C) (λ c d, J c --> R d).

Definition Kleisli_precat_data (R : RelMonad_data J) : precategory_data :=
  precategory_data_pair (Kleisli_precat_ob_mor R) (λ c, r_eta R c)
                                              (λ a b c f g, f · r_bind R g).

Lemma Kleisli_precat_is_precat (R : RelMonad J) : is_precategory (Kleisli_precat_data R).
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
Defined.

Definition precategory_RelMonad {C : precategory_data} {D : precategory}
      (hs : has_homsets D) (J : functor_data C D): precategory :=
  _ ,, precategory_RelMonad_axioms hs J.

Lemma has_homsets_RelMonad {C : precategory_data} (D : category)
      (J : functor_data C D) :
  has_homsets (precategory_RelMonad (homset_property D) J).
Proof.
  intros R R'. simpl. unfold RelMonadMor.
  apply isaset_total2 .
  - apply impred_isaset.
    intro. apply D.
  - intro α.
    apply isasetaprop.
    apply isaprop_RelMonadMor_axioms.
    apply D.
Defined.

(* ----- Category of relative Monads (for a given functor [J]) ----- *)

Definition category_RelMonad {C : precategory_data} (D : category)
      (J : functor_data C D) : category :=
  precategory_RelMonad (homset_property D) J,, has_homsets_RelMonad D J.


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
