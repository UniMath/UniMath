(** Definitions of various kinds of _fibrations_, using displayed categories. *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.
(*
Local Open Scope hide_transport_scope.
*)
(** Fibratons, opfibrations, and isofibrations are all displayed categories with extra lifting conditions.

Classically, these lifting conditions are usually taken by default as mere existence conditions; when they are given by operations, one speaks of a _cloven_ fibration, etc.

We make the cloven version the default, so [is_fibration] etc are the cloven notions, and call the mere-existence versions _un-cloven_.

(This conventional is provisional and and might change in future.) *)

(** * Isofibrations *)

(** The easiest to define are _isofibrations_, since they do not depend on a definition of (co-)cartesian-ness (because all displayed isomorphisms are cartesian). *)

Section Isofibrations.

(** Given an iso φ : c' =~ c in C, and an object d in D c,
there’s some object d' in D c', and an iso φbar : d' =~ d over φ.
*)

Definition iso_cleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (i : iso c' c) (d : D c),
          ∑ d' : D c', iso_disp i d' d.

Definition iso_fibration (C : category) : UU
  := ∑ D : disp_cat C, iso_cleaving D.

Definition is_uncloven_iso_cleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (i : iso c' c) (d : D c),
          ∃ d' : D c', iso_disp i d' d.

Definition weak_iso_fibration (C : category) : UU
  := ∑ D : disp_cat C, is_uncloven_iso_cleaving D.


(** As with fibrations, there is an evident dual version.  However, in the iso case, it is self-dual: having forward (i.e. cocartesian) liftings along isos is equivalent to having backward (cartesian) liftings. *)

Definition is_op_isofibration {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (i : iso c c') (d : D c),
          ∑ d' : D c', iso_disp i d d'.

Lemma is_isofibration_iff_is_op_isofibration
    {C : category} (D : disp_cat C)
  : iso_cleaving D <-> is_op_isofibration D.
Proof.
  (* TODO: give this! *)
Abort.

End Isofibrations.

(** * Fibrations *)
Section Fibrations.

Definition is_cartesian {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall c'' (g : c'' --> c') (d'' : D c'') (hh : d'' -->[g·f] d),
  ∃! (gg : d'' -->[g] d'), gg ;; ff = hh.

(** See also [cartesian_factorisation'] below, for when the map one wishes to factor is not judgementally over [g;;f], but over some equal map. *)
Definition cartesian_factorisation {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g·f] d)
  : d'' -->[g] d'
:= pr1 (pr1 (H _ g _ hh)).

Definition cartesian_factorisation_commutes
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g·f] d)
  : cartesian_factorisation H g hh ;; ff = hh
:= pr2 (pr1 (H _ g _ hh)).

(** This is essentially the third access function for [is_cartesian], but given in a more usable form than [pr2 (H …)] would be. *)
Definition cartesian_factorisation_unique
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} {g : c'' --> c'} {d'' : D c''} (gg gg' : d'' -->[g] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  revert gg gg'.
  assert (goal' : forall gg : d'' -->[g] d',
                    gg = cartesian_factorisation H g (gg ;; ff)).
  {
    intros gg.
    exact (maponpaths pr1
      (pr2 (H _ g _ (gg ;; ff)) (gg,,idpath _))).
  }
  intros gg gg' Hggff.
  eapply pathscomp0. apply goal'.
  eapply pathscomp0. apply maponpaths, Hggff.
  apply pathsinv0, goal'.
Qed.

Definition cartesian_factorisation' {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g · f = h))
  : d'' -->[g] d'.
Proof.
  use (cartesian_factorisation H g).
  exact (transportb _ e hh).
Defined.

Definition cartesian_factorisation_commutes'
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g · f = h))
  : (cartesian_factorisation' H g hh e) ;; ff
  = transportb _ e hh.
Proof.
  apply cartesian_factorisation_commutes.
Qed.

Definition cartesian_lift {C : category} {D : disp_cat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
  : UU
:= ∑ (d' : D c') (ff : d' -->[f] d), is_cartesian ff.

Definition object_of_cartesian_lift  {C : category} {D : disp_cat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : D c'
:= pr1 fd.
Coercion object_of_cartesian_lift : cartesian_lift >-> ob_disp.

Definition mor_disp_of_cartesian_lift  {C : category} {D : disp_cat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : (fd : D c') -->[f] d
:= pr1 (pr2 fd).
Coercion mor_disp_of_cartesian_lift : cartesian_lift >-> mor_disp.

Definition cartesian_lift_is_cartesian {C : category} {D : disp_cat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : is_cartesian fd
:= pr2 (pr2 fd).
Coercion cartesian_lift_is_cartesian : cartesian_lift >-> is_cartesian.

Definition is_cartesian_disp_functor
  {C C' : category} {F : functor C C'}
  {D : disp_cat C} {D' : disp_cat C'} (FF : disp_functor F D D') : UU
:= ∏  (c c' : C) (f : c' --> c)
      (d : D c) (d' : D c') (ff : d' -->[f] d),
   is_cartesian ff -> is_cartesian (#FF ff).

Definition disp_functor_identity_is_cartesian_disp_functor
           {C : category}
           (D : disp_cat C)
  : is_cartesian_disp_functor (disp_functor_identity D).
Proof.
  intros x y f xx yy ff Hff.
  exact Hff.
Defined.

Definition disp_functor_composite_is_cartesian_disp_functor
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           {GG : disp_functor G D₂ D₃}
           (HFF : is_cartesian_disp_functor FF)
           (HGG : is_cartesian_disp_functor GG)
  : is_cartesian_disp_functor (disp_functor_composite FF GG).
Proof.
  intros x y f xx yy ff Hff.
  apply HGG.
  apply HFF.
  exact Hff.
Defined.

Definition disp_functor_over_id_composite_is_cartesian
           {C : category}
           {D₁ D₂ D₃ : disp_cat C}
           {FF : disp_functor (functor_identity C) D₁ D₂}
           {GG : disp_functor (functor_identity C) D₂ D₃}
           (HFF : is_cartesian_disp_functor FF)
           (HGG : is_cartesian_disp_functor GG)
  : is_cartesian_disp_functor (disp_functor_over_id_composite FF GG).
Proof.
  intros x y f xx yy ff Hff.
  apply HGG.
  apply HFF.
  exact Hff.
Defined.

Definition cartesian_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D₁ : disp_cat C₁)
           (D₂ : disp_cat C₂)
  : UU
  := ∑ (FF : disp_functor F D₁ D₂), is_cartesian_disp_functor FF.

Coercion disp_functor_of_cartesian_disp_functor
         {C₁ C₂ : category}
         {F : C₁ ⟶ C₂}
         {D₁ : disp_cat C₁}
         {D₂ : disp_cat C₂}
         (FF : cartesian_disp_functor F D₁ D₂)
  : disp_functor F D₁ D₂
  := pr1 FF.

Definition cartesian_disp_functor_is_cartesian
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : cartesian_disp_functor F D₁ D₂)
  : is_cartesian_disp_functor FF
  := pr2 FF.

Lemma isaprop_is_cartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : isaprop (is_cartesian ff).
Proof.
  repeat (apply impred_isaprop; intro).
  apply isapropiscontr.
Defined.

(* TODO: should the arguments be re-ordered as in [cartesian_lift]? If so, reorder in [isofibration] etc as well, for consistency. *)
(* TODO: consider renaming to e.g. [cleaving] to follow convention that [is_] is reserved for hprops. *)
Definition cleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (f : c' --> c) (d : D c), cartesian_lift d f.

(** ** (Cloven) fibration *)

Definition fibration (C : category) : UU
:=
  ∑ D : disp_cat C, cleaving D.


(** ** Weak fibration *)

(* TODO: give access functions! *)

Definition is_cleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (f : c' --> c) (d : D c), ∥ cartesian_lift d f ∥.

Definition weak_fibration (C : category) : UU
:= ∑ D : disp_cat C, is_cleaving D.

(** ** Connection with isofibrations *)

Lemma is_iso_from_is_cartesian {C : category} {D : disp_cat C}
    {c c' : C} (i : iso c' c) {d : D c} {d'} (ff : d' -->[i] d)
  : is_cartesian ff -> is_iso_disp i ff.
Proof.
  intros Hff.
  use (_,,_); try split.
  - use
      (cartesian_factorisation' Hff (inv_from_iso i) (id_disp _)).
    apply iso_after_iso_inv.
  - apply cartesian_factorisation_commutes'.
  - apply (cartesian_factorisation_unique Hff).
    etrans. apply assoc_disp_var.
    rewrite cartesian_factorisation_commutes'.
    etrans. eapply transportf_bind.
      etrans. apply mor_disp_transportf_prewhisker.
      eapply transportf_bind, id_right_disp.
    apply pathsinv0.
    etrans. apply mor_disp_transportf_postwhisker.
    etrans. eapply transportf_bind, id_left_disp.
    apply maponpaths_2, homset_property.
Qed.

Lemma is_isofibration_from_is_fibration {C : category} {D : disp_cat C}
  : cleaving D -> iso_cleaving D.
Proof.
  intros D_fib c c' f d.
  assert (fd := D_fib _ _ f d).
  exists (fd : D _).
  exists (fd : _ -->[_] _).
  apply is_iso_from_is_cartesian; exact fd.
Defined.

(** ** Uniqueness of cartesian lifts *)

(* TODO: show that when [D] is _univalent_, cartesian lifts are literally unique, and so any uncloven fibration (isofibration, etc) is in fact cloven. *)
Definition cartesian_lifts_iso {C : category} {D : disp_cat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : iso_disp (identity_iso c') fd fd'.
Proof.
  use (_,,(_,,_)).
  - exact (cartesian_factorisation' fd' (identity _) fd (id_left _)).
  - exact (cartesian_factorisation' fd (identity _) fd' (id_left _)).
  - cbn; split.
    + apply (cartesian_factorisation_unique fd').
      etrans. apply assoc_disp_var.
      rewrite cartesian_factorisation_commutes'.
      etrans. eapply transportf_bind, mor_disp_transportf_prewhisker.
      rewrite cartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      rewrite id_left_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
    + apply (cartesian_factorisation_unique fd).
      etrans. apply assoc_disp_var.
      rewrite cartesian_factorisation_commutes'.
      etrans. eapply transportf_bind, mor_disp_transportf_prewhisker.
      rewrite cartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      rewrite id_left_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
Defined.

Definition cartesian_lifts_iso_commutes {C : category} {D : disp_cat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : (cartesian_lifts_iso fd fd') ;; fd'
  = transportb _ (id_left _) (fd : _ -->[_] _).
Proof.
  cbn. apply cartesian_factorisation_commutes'.
Qed.

(** In a displayed _category_ (i.e. _univalent_), cartesian lifts are literally unique, if they exist; that is, the type of cartesian lifts is always a proposition. *)
Definition isaprop_cartesian_lifts
    {C : category} {D : disp_cat C} (D_cat : is_univalent_disp D)
    {c} (d : D c) {c' : C} (f : c' --> c)
  : isaprop (cartesian_lift d f).
Proof.
  apply invproofirrelevance; intros fd fd'.
  use total2_paths_f.
  { apply (isotoid_disp D_cat (idpath _)); cbn.
    apply cartesian_lifts_iso. }
  apply subtypePath.
  { intros ff. repeat (apply impred; intro).
    apply isapropiscontr. }
  etrans.
  { exact (! transport_map (λ x:D c', pr1) _ _). }
  cbn. etrans. apply transportf_precompose_disp.
  rewrite idtoiso_isotoid_disp.
  use (pathscomp0 (maponpaths _ _) (transportfbinv _ _ _)).
  apply (precomp_with_iso_disp_is_inj (cartesian_lifts_iso fd fd')).
  etrans. apply assoc_disp.
  etrans. eapply transportf_bind, cancel_postcomposition_disp.
    use inv_mor_after_iso_disp.
  etrans. eapply transportf_bind, id_left_disp.
  apply pathsinv0.
  etrans. apply mor_disp_transportf_prewhisker.
  etrans. eapply transportf_bind, cartesian_lifts_iso_commutes.
  apply maponpaths_2, homset_property.
Defined.

Definition univalent_fibration_is_cloven
    {C : category} {D : disp_cat C} (D_cat : is_univalent_disp D)
  : is_cleaving D -> cleaving D.
Proof.
  intros D_fib c c' f d.
  apply (squash_to_prop (D_fib c c' f d)).
  apply isaprop_cartesian_lifts; assumption.
  auto.
Defined.

End Fibrations.

Definition isaprop_cleaving
           {C : univalent_category}
           (D : disp_cat C)
           (HD : is_univalent_disp D)
  : isaprop (cleaving D).
Proof.
  repeat (use impred ; intro).
  apply isaprop_cartesian_lifts.
  exact HD.
Defined.

Section Discrete_Fibrations.

Definition is_discrete_fibration {C : category} (D : disp_cat C) : UU
:=
  (forall (c c' : C) (f : c' --> c) (d : D c),
          ∃! d' : D c', d' -->[f] d)
  ×
  (forall c, isaset (D c)).

Definition discrete_fibration C : UU
  := ∑ D : disp_cat C, is_discrete_fibration D.

Coercion disp_cat_from_discrete_fibration C (D : discrete_fibration C)
  : disp_cat C := pr1 D.
Definition unique_lift {C} {D : discrete_fibration C} {c c'}
           (f : c' --> c) (d : D c)
  : ∃! d' : D c', d' -->[f] d
  := pr1 (pr2 D) c c' f d.
Definition isaset_fiber_discrete_fibration {C} (D : discrete_fibration C)
           (c : C) : isaset (D c) := pr2 (pr2 D) c.

(** TODO: move upstream *)
Lemma pair_inj {A : UU} {B : A -> UU} (is : isaset A) {a : A}
   {b b' : B a} : (a,,b) = (a,,b') -> b = b'.
Proof.
  intro H.
  use (invmaponpathsincl _ _ _ _ H).
  apply isofhlevelffib. intro. apply is.
Defined.

Lemma disp_mor_unique_disc_fib C (D : discrete_fibration C)
  : ∏ (c c' : C) (f : c --> c') (d : D c) (d' : D c')
      (ff ff' : d -->[f] d'), ff = ff'.
Proof.
  intros.
  assert (XR := unique_lift f d').
  assert (foo : ((d,,ff) : ∑ d0, d0 -->[f] d') = (d,,ff')).
  { apply proofirrelevancecontr. apply XR. }
  apply (pair_inj (isaset_fiber_discrete_fibration _ _ ) foo).
Defined.

Lemma isaprop_disc_fib_hom C (D : discrete_fibration C)
  : ∏ (c c' : C) (f : c --> c') (d : D c) (d' : D c'),
    isaprop (d -->[f] d').
Proof.
  intros.
  apply invproofirrelevance.
  intros x x'. apply disp_mor_unique_disc_fib.
Qed.

Definition fibration_from_discrete_fibration C (D : discrete_fibration C)
  : cleaving D.
Proof.
  intros c c' f d.
  use tpair.
  - exact (pr1 (iscontrpr1 (unique_lift f d))).
  - use tpair.
    + exact (pr2 (iscontrpr1 (unique_lift f d))).
    + intros c'' g db hh.
      set (ff := pr2 (iscontrpr1 (unique_lift f d))  ). cbn in ff.
      set (d' := pr1 (iscontrpr1 (unique_lift f d))) in *.
      set (ggff := pr2 (iscontrpr1 (unique_lift (g·f) d))  ). cbn in ggff.
      set (d'' := pr1 (iscontrpr1 (unique_lift (g·f) d))) in *.
      set (gg := pr2 (iscontrpr1 (unique_lift g d'))). cbn in gg.
      set (d3 := pr1 (iscontrpr1 (unique_lift g d'))) in *.
      assert (XR : ((d'',, ggff) : ∑ r, r -->[g·f] d) = (db,,hh)).
      { apply proofirrelevancecontr. apply (pr2 D). }
      assert (XR1 : ((d'',, ggff) : ∑ r, r -->[g·f] d) = (d3 ,,gg;;ff)).
      { apply proofirrelevancecontr. apply (pr2 D). }
      assert (XT := maponpaths pr1 XR). cbn in XT.
      assert (XT1 := maponpaths pr1 XR1). cbn in XT1.
      generalize XR.
      generalize XR1; clear XR1.
      destruct XT.
      generalize gg; clear gg.
      destruct XT1.
      intros gg XR1 XR0.
      apply iscontraprop1.
      * apply invproofirrelevance.
        intros x x'. apply subtypePath.
        { intro. apply homsets_disp. }
        apply disp_mor_unique_disc_fib.
      * exists gg.
        cbn.
        assert (XX := pair_inj (isaset_fiber_discrete_fibration _ _ ) XR1).
        assert (YY := pair_inj (isaset_fiber_discrete_fibration _ _ ) XR0).
        etrans. apply (!XX). apply YY.
Defined.



Section Equivalence_disc_fibs_presheaves.

(* GOAL: correspondence between discrete fibrations and presheaves.

Outline via categories:

- show that the fibers of a discrete fibration are (discrete categories on) sets, and that the disp morphism types are props;
- define the category of discrete fibrations over C, using [disp_functor_id] for morphisms, and with [homset_property] coming from the previous point;
- construct equivalence of cats; probably easiest by explicit functors and natural isos (not by “ess split” plus “full and faithful”);
- show [disc_fib_precat C] is univalent (possibly _using_ the above equivalence of cats, to get “isos of displayed cats are weq to isos btn associated presheaves”?);
- conclude equivalence of types.

More direct equivalence of types:

- ?

 *)


Variable C : category.

Definition precat_of_discrete_fibs_ob_mor : precategory_ob_mor.
Proof.
  exists (discrete_fibration C).
  intros a b. exact (disp_functor (functor_identity _ ) a b).
Defined.

Definition precat_of_discrete_fibs_data : precategory_data.
Proof.
  exists precat_of_discrete_fibs_ob_mor.
  split.
  - intro.
    exact (@disp_functor_identity _ _ ).
  - intros ? ? ? f g. exact (disp_functor_composite f g ).
Defined.

Lemma eq_discrete_fib_mor (F G : precat_of_discrete_fibs_ob_mor)
      (a b : F --> G)
      (H : ∏ x y, pr1 (pr1 a) x y = pr1 (pr1 b) x y)
  : a = b.
Proof.
  apply subtypePath.
  { intro. apply isaprop_disp_functor_axioms. }
  use total2_paths_f.
  - apply funextsec. intro x.
    apply funextsec. intro y.
    apply H.
  - repeat (apply funextsec; intro).
    apply disp_mor_unique_disc_fib.
Qed.

Definition precat_axioms_of_discrete_fibs : is_precategory precat_of_discrete_fibs_data.
Proof.
  repeat split; intros;
  apply eq_discrete_fib_mor; intros; apply idpath.
Qed.

Definition precat_of_discrete_fibs : precategory
  := (_ ,, precat_axioms_of_discrete_fibs).

Lemma has_homsets_precat_of_discrete_fibs : has_homsets precat_of_discrete_fibs.
Proof.
  intros f f'.
  apply (isofhleveltotal2 2).
  - apply (isofhleveltotal2 2).
    + do 2 (apply impred; intro).
      apply isaset_fiber_discrete_fibration.
    + intro. do 6 (apply impred; intro).
      apply homsets_disp.
  - intro. apply isasetaprop. apply isaprop_disp_functor_axioms.
Qed.

Definition Precat_of_discrete_fibs : category
  := ( precat_of_discrete_fibs ,, has_homsets_precat_of_discrete_fibs).

(** ** Functor from discrete fibrations to presheaves *)

(** *** Functor on objects *)

(* TODO: split into data and properties *)


Definition preshv_data_from_disc_fib_ob (D : discrete_fibration C)
  : functor_data C^op HSET_univalent_category.
Proof.
  use tpair.
  + intro c. exists (D c). apply  isaset_fiber_discrete_fibration.
  + intros c' c f x. cbn in *.
    exact (pr1 (iscontrpr1 (unique_lift f x))).
Defined.

Definition preshv_ax_from_disc_fib_ob (D : discrete_fibration C)
  : is_functor (preshv_data_from_disc_fib_ob D).
Proof.
  split.
  + intro c; cbn.
    apply funextsec; intro x. simpl.
    apply pathsinv0. apply path_to_ctr.
      apply id_disp.
  + intros c c' c'' f g. cbn in *.
    apply funextsec; intro x.
    apply pathsinv0.
    apply path_to_ctr.
    eapply comp_disp.
    * apply (pr2 (iscontrpr1 (unique_lift g _))).
    * apply (pr2 (iscontrpr1 (unique_lift f _ ))).
Qed.

Definition preshv_from_disc_fib_ob (D : discrete_fibration C)
  : PreShv C := (_ ,, preshv_ax_from_disc_fib_ob D).

(** *** Functor on morphisms *)

Definition foo : functor_data Precat_of_discrete_fibs (PreShv C).
Proof.
  exists preshv_from_disc_fib_ob.
  intros D D' a.
  use tpair.
  - intro c. simpl.
    exact (pr1 a c).
  - abstract (
        intros x y f; cbn in *;
        apply funextsec; intro d;
        apply path_to_ctr;
        apply #a;
        apply (pr2 (iscontrpr1 (unique_lift f _ )))
      ).
Defined.

(** *** Functor properties *)

Definition bar : is_functor foo.
Proof.
  split.
  - intro D. apply nat_trans_eq. { apply has_homsets_HSET. }
    intro c . apply idpath.
  - intros D E F a b. apply nat_trans_eq. { apply has_homsets_HSET. }
    intro c. apply idpath.
Qed.

Definition functor_Disc_Fibs_to_preShvs : functor _ _
  := ( _ ,, bar).

(** ** Functor from presheaves to discrete fibrations *)

(** *** Functor on objects *)

(* TODO: split into data and properties *)
Definition disp_cat_from_preshv (D : PreShv C) : disp_cat C.
Proof.
  use tpair.
  - use tpair.
    + exists (λ c, pr1hSet (pr1 D c)).
      intros x y c d f. exact (functor_on_morphisms (pr1 D) f d = c).
    + split.
      * intros; cbn in *; apply (toforallpaths _ _ _ (functor_id D x ) _ ).
      * intros ? ? ? ? ? ? ? ? X X0; cbn in *;
        etrans; [apply (toforallpaths _ _ _ (functor_comp D g f ) _ ) |];
        cbn; etrans; [ apply maponpaths; apply X0 |]; (* here maponpaths depends on cbn *)
        apply X.
  - abstract (
         repeat use tpair; cbn; intros; try apply setproperty;
         apply isasetaprop; apply setproperty
       ).
Defined.

Definition disc_fib_from_preshv (D : PreShv C) : discrete_fibration C.
Proof.
  use tpair.
  - apply (disp_cat_from_preshv D).
  - cbn.
    split.
    + intros c c' f d. simpl.
      use unique_exists.
      * apply (functor_on_morphisms (pr1 D) f d).
      * apply idpath.
      * intro. apply setproperty.
      * intros. apply pathsinv0. assumption.
    + intro. simpl. apply setproperty.
Defined.

(** *** Functor on morphisms *)

Definition functor_data_preShv_Disc_fibs
  : functor_data (PreShv C) Precat_of_discrete_fibs.
Proof.
  use tpair.
  - apply disc_fib_from_preshv.
  - intros F G a.
    use tpair.
    + use tpair.
      * intros c. apply (pr1 a c).
      * intros x y X Y f H;
        assert (XR := nat_trans_ax a);
        apply pathsinv0; etrans; [|apply (toforallpaths _ _ _ (XR _ _ f))];
        cbn; apply maponpaths, (!H).
    +  cbn. abstract (repeat use tpair; cbn; intros; apply setproperty).
Defined.

(** *** Functor properties *)

Definition is_functor_functor_data_preShv_Disc_fibs
  : is_functor functor_data_preShv_Disc_fibs .
Proof.
  split; unfold functor_idax, functor_compax; intros;
  apply eq_discrete_fib_mor; intros; apply idpath.
Qed.


Definition functor_preShvs_to_Disc_Fibs : functor _ _
  := ( _ ,,  is_functor_functor_data_preShv_Disc_fibs ).

Definition η_disc_fib : nat_trans (functor_identity _ )
                          (functor_preShvs_to_Disc_Fibs ∙ functor_Disc_Fibs_to_preShvs).
Proof.
  use tpair.
  - intro F.
    cbn. use tpair.
    + red. cbn. intro c; apply idfun.
    + intros c c' f. cbn in *. apply idpath.
  - abstract (
        intros F G a;
        apply nat_trans_eq; [ apply has_homsets_HSET |];
        intro c ; apply idpath
      ).
Defined.

Definition ε_disc_fib
  : nat_trans (functor_Disc_Fibs_to_preShvs ∙ functor_preShvs_to_Disc_Fibs)
              (functor_identity _ ).
Proof.
  use tpair.
  - intro D.
    use tpair.
    + use tpair.
      * cbn. intro c; apply idfun.
      * cbn. intros c c' x y f H.
        set (XR := pr2 (iscontrpr1 (unique_lift f y))). cbn in XR.
        apply (transportf (λ t, t -->[f] y) H XR).
    + abstract (split; cbn; intros; apply  disp_mor_unique_disc_fib).
  - abstract (intros c c' f; apply eq_discrete_fib_mor; intros; apply idpath).
Defined.

Definition ε_inv_disc_fib
  : nat_trans (functor_identity _ )
      (functor_Disc_Fibs_to_preShvs ∙ functor_preShvs_to_Disc_Fibs).
Proof.
  use tpair.
  - intro D.
    cbn.
    use tpair.
    + use tpair.
      * cbn. intro c; apply idfun.
      * abstract (
            intros c c' x y f H; cbn;
            apply pathsinv0; apply path_to_ctr; apply H
          ).
    + abstract (
          split;
          [ intros x y; apply isaset_fiber_discrete_fibration |];
          intros; apply isaset_fiber_discrete_fibration
        ).
  - abstract (intros c c' f; apply eq_discrete_fib_mor; intros; apply idpath).
Defined.


Definition adjunction_data_disc_fib
  : adjunction_data (PreShv C) Precat_of_discrete_fibs.
Proof.
  exists functor_preShvs_to_Disc_Fibs.
  exists functor_Disc_Fibs_to_preShvs.
  exists η_disc_fib.
  exact  ε_disc_fib.
Defined.

Lemma forms_equivalence_disc_fib
  : forms_equivalence adjunction_data_disc_fib.
Proof.
  split.
  - intro F.
    apply functor_iso_if_pointwise_iso.
    intro c. cbn.
    set (XR := hset_equiv_is_iso _ _ (idweq (pr1 F c : hSet) )).
    apply XR.
  - intro F.
    apply is_iso_from_is_z_iso.
    use (_ ,, (_,,_ )).
    + apply ε_inv_disc_fib.
    + apply eq_discrete_fib_mor.
      intros. apply idpath.
    + apply eq_discrete_fib_mor.
      intros. apply idpath.
Qed.

Definition adj_equivalence_disc_fib : adj_equivalence_of_cats _ :=
  adjointificiation (_ ,, forms_equivalence_disc_fib).

End Equivalence_disc_fibs_presheaves.

End Discrete_Fibrations.

(**
 The notion of an opcartesian morphism
 *)
Section Opcartesian.
  Context {C : category}
          {D : disp_cat C}.

  Definition is_opcartesian
             {c₁ c₂ : C}
             {f : c₁ --> c₂}
             {cc₁ : D c₁}
             {cc₂ : D c₂}
             (ff : cc₁ -->[ f ] cc₂)
    : UU
    := ∏ (c₃ : C)
         (cc₃ : D c₃)
         (g : c₂ --> c₃)
         (hh : cc₁ -->[ f · g ] cc₃),
       ∃! (gg : cc₂ -->[ g ] cc₃),
       ff ;; gg = hh.

  Section ProjectionsOpcartesian.
    Context {c₁ c₂ : C}
            {f : c₁ --> c₂}
            {cc₁ : D c₁}
            {cc₂ : D c₂}
            {ff : cc₁ -->[ f ] cc₂}
            (Hff : is_opcartesian ff)
            {c₃ : C}
            {cc₃ : D c₃}
            (g : c₂ --> c₃)
            (hh : cc₁ -->[ f · g ] cc₃).

    Definition opcartesian_factorisation
      : cc₂ -->[ g ] cc₃
      := pr11 (Hff c₃ cc₃ g hh).

    Definition opcartesian_factorisation_commutes
      : ff ;; opcartesian_factorisation = hh
      := pr21 (Hff c₃ cc₃ g hh).

    Definition opcartesian_factorisation_unique
               (gg₁ gg₂ : cc₂ -->[ g ] cc₃)
               (H : ff ;; gg₁ = ff ;; gg₂)
      : gg₁ = gg₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
               _
               (isapropifcontr
                  (Hff c₃ cc₃ g (ff ;; gg₁)))
               (gg₁ ,, idpath _)
               (gg₂ ,, !H))).
    Qed.
  End ProjectionsOpcartesian.
End Opcartesian.

(**
 Opcartesian morphism
 *)
Definition is_cartesian_weq_is_opcartesian
           {C : category}
           {D : disp_cat C}
           {c₁ c₂ : C}
           {f : c₁ --> c₂}
           {cc₁ : D c₁}
           {cc₂ : D c₂}
           (ff : cc₁ -->[ f ] cc₂)
  : is_cartesian ff ≃ @is_opcartesian _ (op_disp_cat D) _ _ _ _ _ ff.
Proof.
  use make_weq.
  - exact (λ Hff c₃ cc₃ g hh, Hff c₃ g cc₃ hh).
  - use gradth.
    + exact (λ Hff c₃ cc₃ g hh, Hff c₃ g cc₃ hh).
    + intro ; apply idpath.
    + intro ; apply idpath.
Defined.

Definition is_opcartesian_weq_is_cartesian
           {C : category}
           {D : disp_cat C}
           {c₁ c₂ : C}
           {f : c₁ --> c₂}
           {cc₁ : D c₁}
           {cc₂ : D c₂}
           (ff : cc₁ -->[ f ] cc₂)
  : is_opcartesian ff ≃ @is_cartesian _ (op_disp_cat D) _ _ _ _ _ ff.
Proof.
  use make_weq.
  - exact (λ Hff c₃ cc₃ g hh, Hff c₃ g cc₃ hh).
  - use gradth.
    + exact (λ Hff c₃ cc₃ g hh, Hff c₃ g cc₃ hh).
    + intro ; apply idpath.
    + intro ; apply idpath.
Defined.

Definition is_cartesian_to_is_opcartesian
           {C : category}
           {D : disp_cat C}
           {c₁ c₂ : C}
           {f : c₁ --> c₂}
           {cc₁ : D c₁}
           {cc₂ : D c₂}
           {ff : cc₁ -->[ f ] cc₂}
           (Hff : @is_cartesian _ (op_disp_cat D) _ _ _ _ _ ff)
  : is_opcartesian ff
  := invmap (is_opcartesian_weq_is_cartesian ff) Hff.

Definition isaprop_is_opcartesian
           {C : category}
           {D : disp_cat C}
           {c₁ c₂ : C}
           {f : c₁ --> c₂}
           {cc₁ : D c₁}
           {cc₂ : D c₂}
           (ff : cc₁ -->[ f ] cc₂)
  : isaprop (is_opcartesian ff).
Proof.
  apply (isofhlevelweqb 1 (is_opcartesian_weq_is_cartesian ff)).
  apply isaprop_is_cartesian.
Qed.

(** Opcleavings *)
Section Opcleaving.
  Context {C : category}
          (D : disp_cat C).

  Definition opcartesian_lift
             {c₁ c₂ : C}
             (cc₁ : D c₁)
             (f : c₁ --> c₂)
    : UU
    := ∑ (cc₂ : D c₂) (ff : cc₁ -->[ f ] cc₂), is_opcartesian ff.

  Definition ob_of_opcartesian_lift
             {c₁ c₂ : C}
             {cc₁ : D c₁}
             {f : c₁ --> c₂}
             (ℓ : opcartesian_lift cc₁ f)
    : D c₂
    := pr1 ℓ.

  Definition mor_of_opcartesian_lift
             {c₁ c₂ : C}
             {cc₁ : D c₁}
             {f : c₁ --> c₂}
             (ℓ : opcartesian_lift cc₁ f)
    : cc₁ -->[ f ] ob_of_opcartesian_lift ℓ
    := pr12 ℓ.

  Definition mor_of_opcartesian_lift_is_opcartesian
             {c₁ c₂ : C}
             {cc₁ : D c₁}
             {f : c₁ --> c₂}
             (ℓ : opcartesian_lift cc₁ f)
    : is_opcartesian (mor_of_opcartesian_lift ℓ)
    := pr22 ℓ.

  Definition opcleaving
    : UU
    := ∏ (c₁ c₂ : C)
         (cc₁ : D c₁)
         (f : c₁ --> c₂),
       opcartesian_lift cc₁ f.

  Definition is_opcleaving
    : UU
    := ∏ (c₁ c₂ : C)
         (cc₁ : D c₁)
         (f : c₁ --> c₂),
       ∥ opcartesian_lift cc₁ f ∥.
End Opcleaving.

Definition opcleaving_ob
           {C : category}
           {D : disp_cat C}
           (HD : opcleaving D)
           {c c' : C}
           (f : c --> c')
           (d : D c)
  : D c'
  := ob_of_opcartesian_lift _ (HD c c' d f).

Definition opcleaving_mor
           {C : category}
           {D : disp_cat C}
           (HD : opcleaving D)
           {c c' : C}
           (f : c --> c')
           (d : D c)
  : d -->[ f ] opcleaving_ob HD f d
  := mor_of_opcartesian_lift _ (HD c c' d f).

Definition cleaving_weq_opcleaving
           {C : category}
           (D : disp_cat C)
  : cleaving D ≃ @opcleaving _ (op_disp_cat D).
Proof.
  use make_weq.
  - exact (λ HD c₁ c₂ cc₁ f,
           let ℓ := HD c₁ c₂ f cc₁ in
           pr1 ℓ ,, pr12 ℓ ,, is_cartesian_weq_is_opcartesian _ ℓ).
  - use gradth.
    + refine (λ HD c₁ c₂ cc₁ f,
              let ℓ := HD c₁ c₂ f cc₁ in
              pr1 ℓ ,, pr12 ℓ ,, _).
      exact (invmap (is_cartesian_weq_is_opcartesian _) (pr22 ℓ)).
    + intro ; apply idpath.
    + intro ; apply idpath.
Defined.

Definition opcleaving_weq_cleaving
           {C : category}
           (D : disp_cat C)
  : opcleaving D ≃ @cleaving _ (op_disp_cat D).
Proof.
  use make_weq.
  - exact (λ HD c₁ c₂ cc₁ f,
           let ℓ := HD c₁ c₂ f cc₁ in
           pr1 ℓ ,, pr12 ℓ ,, is_opcartesian_weq_is_cartesian _ (pr22 ℓ)).
  - use gradth.
    + refine (λ HD c₁ c₂ cc₁ f,
              let ℓ := HD c₁ c₂ f cc₁ in
              pr1 ℓ ,, pr12 ℓ ,, _).
      exact (invmap (is_opcartesian_weq_is_cartesian _) (pr22 ℓ)).
    + intro ; apply idpath.
    + intro ; apply idpath.
Defined.

(** Cloven opfibration *)
Definition opfibration
           (C : category)
  : UU
  := ∑ (D : disp_cat C), opcleaving D.

(** Weak opfibration *)
Definition weak_opfibration
           (C : category)
  : UU
  := ∑ (D : disp_cat C), is_opcleaving D.

Definition is_opcartesian_disp_functor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₁}
           {D' : disp_cat C₂}
           (FF : disp_functor F D D')
  : UU
  := ∏  (c c' : C₁)
        (f : c' --> c)
        (d : D c)
        (d' : D c')
        (ff : d' -->[f] d),
     is_opcartesian ff -> is_opcartesian (#FF ff).

Definition disp_functor_identity_is_opcartesian_disp_functor
           {C : category}
           (D : disp_cat C)
  : is_opcartesian_disp_functor (disp_functor_identity D).
Proof.
  intros x y f xx yy ff Hff.
  exact Hff.
Defined.

Definition disp_functor_composite_is_opcartesian_disp_functor
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           {GG : disp_functor G D₂ D₃}
           (HFF : is_opcartesian_disp_functor FF)
           (HGG : is_opcartesian_disp_functor GG)
  : is_opcartesian_disp_functor (disp_functor_composite FF GG).
Proof.
  intros x y f xx yy ff Hff.
  apply HGG.
  apply HFF.
  exact Hff.
Defined.

Definition disp_functor_over_id_composite_is_opcartesian
           {C : category}
           {D₁ D₂ D₃ : disp_cat C}
           {FF : disp_functor (functor_identity C) D₁ D₂}
           {GG : disp_functor (functor_identity C) D₂ D₃}
           (HFF : is_opcartesian_disp_functor FF)
           (HGG : is_opcartesian_disp_functor GG)
  : is_opcartesian_disp_functor (disp_functor_over_id_composite FF GG).
Proof.
  intros x y f xx yy ff Hff.
  apply HGG.
  apply HFF.
  exact Hff.
Defined.

Definition opcartesian_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D₁ : disp_cat C₁)
           (D₂ : disp_cat C₂)
  : UU
  := ∑ (FF : disp_functor F D₁ D₂), is_opcartesian_disp_functor FF.

Coercion disp_functor_of_opcartesian_disp_functor
         {C₁ C₂ : category}
         {F : C₁ ⟶ C₂}
         {D₁ : disp_cat C₁}
         {D₂ : disp_cat C₂}
         (FF : opcartesian_disp_functor F D₁ D₂)
  : disp_functor F D₁ D₂
  := pr1 FF.

Definition opcartesian_disp_functor_is_opcartesian
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : opcartesian_disp_functor F D₁ D₂)
  : is_opcartesian_disp_functor FF
  := pr2 FF.

(** Opfibrations are isofibrations *)
Section IsoCleavingFromOpcleaving.
  Context {C : category}
          (D : disp_cat C)
          (HD : opcleaving D).

  Section Lift.
    Context {x y : C}
            (f : iso x y)
            (d : D y).

    Definition iso_cleaving_from_opcleaving_ob
      : D x
      := opcleaving_ob HD (inv_from_iso f) d.

    Let ℓ : d -->[ inv_from_iso f ] iso_cleaving_from_opcleaving_ob
      := opcleaving_mor HD (inv_from_iso f) d.
    Let ℓ_opcart : is_opcartesian (pr12 (HD y x d (inv_from_iso f)))
      := pr22 (HD _ _ d (inv_from_iso f)).

    Definition iso_cleaving_from_opcleaving_ob_disp_iso_map
      : iso_cleaving_from_opcleaving_ob -->[ f ] d.
    Proof.
      use (opcartesian_factorisation ℓ_opcart).
      refine (transportb
                (λ z, _ -->[ z ] _)
                _
                (id_disp d)).
      apply iso_after_iso_inv.
    Defined.

    Definition iso_cleaving_from_opcleaving_ob_disp_iso
      : iso_disp f iso_cleaving_from_opcleaving_ob d.
    Proof.
      use make_iso_disp.
      - exact iso_cleaving_from_opcleaving_ob_disp_iso_map.
      - simple refine (_ ,, _ ,, _).
        + exact ℓ.
        + abstract
            (apply opcartesian_factorisation_commutes).
        + abstract
            (apply (opcartesian_factorisation_unique ℓ_opcart) ;
             unfold transportb ;
             rewrite mor_disp_transportf_prewhisker ;
             rewrite assoc_disp ;
             unfold transportb ;
             etrans ;
               [ apply maponpaths ;
                 apply maponpaths_2 ;
                 apply (opcartesian_factorisation_commutes ℓ_opcart)
               | ] ;
             unfold transportb ;
             rewrite mor_disp_transportf_postwhisker ;
             rewrite id_left_disp, id_right_disp ;
             unfold transportb ;
             rewrite !transport_f_f ;
             apply maponpaths_2 ;
             apply homset_property).
    Defined.
  End Lift.

  Definition iso_cleaving_from_opcleaving
    : iso_cleaving D
    := λ x y f d,
       iso_cleaving_from_opcleaving_ob f d
       ,,
       iso_cleaving_from_opcleaving_ob_disp_iso f d.
End IsoCleavingFromOpcleaving.

Section isofibration_from_disp_over_univalent.

Context (C : category)
        (Ccat : is_univalent C)
        (D : disp_cat C).

Definition iso_cleaving_category : iso_cleaving D.
Proof.
  intros c c' i d.
  use tpair.
  - exact (transportb D (isotoid _ Ccat i) d).
  - generalize i. clear i.
    apply forall_isotoid.
    { apply Ccat. }
    intro e. induction e.
    cbn.
    rewrite isotoid_identity_iso.
    cbn.
    apply identity_iso_disp.
Defined.

End isofibration_from_disp_over_univalent.

(** * Split fibrations *)

Definition cleaving_ob {C : category} {D : disp_cat C}
           (X : cleaving D) {c c' : C} (f : c' --> c) (d : D c)
  : D c' := X _ _ f d.

Definition cleaving_mor {C : category} {D : disp_cat C}
           (X : cleaving D) {c c' : C} (f : c' --> c) (d : D c)
  : cleaving_ob X f d -->[f] d := X _ _ f d.

Definition is_split_id {C : category} {D : disp_cat C}
           (X : cleaving D) : UU
  := ∏ c (d : D c),
      ∑ e : cleaving_ob X (identity _) d = d,
            cleaving_mor X (identity _) d =
            transportb (λ x, x -->[ _ ] _ ) e (id_disp d).

Definition is_split_comp {C : category} {D : disp_cat C}
           (X : cleaving D) : UU
  :=
    ∏ (c c' c'' : C) (f : c' --> c) (g : c'' --> c') (d : D c),
      ∑ e : cleaving_ob X (g · f) d =
                cleaving_ob X g (cleaving_ob X f d),
            cleaving_mor X (g · f) d =
            transportb (λ x, x -->[ _ ] _ ) e
                       (cleaving_mor X g (cleaving_ob X f d) ;;
                                     cleaving_mor X f d).

Definition is_split {C : category} {D : disp_cat C}
           (X : cleaving D) : UU
  := is_split_id X × is_split_comp X × (∏ c, isaset (D c)).


Lemma is_split_fibration_from_discrete_fibration
      {C : category} {D : disp_cat C}
      (X : is_discrete_fibration D)
: is_split (fibration_from_discrete_fibration _ (D,,X)).
Proof.
  repeat split.
  - intros c d.
    cbn.
    use tpair.
    + apply pathsinv0.
      apply path_to_ctr.
      apply id_disp.
    + cbn.
      apply  (disp_mor_unique_disc_fib _ (D,,X)).
  - intros c c' c'' f g d.
    cbn.
    use tpair.
    + set (XR := unique_lift f d).
      set (d' := pr1 (iscontrpr1 XR)).
      set (f' := pr2 (iscontrpr1 XR)). cbn in f'.
      set (g' := pr2 (iscontrpr1 (unique_lift g d'))).
      cbn in g'.
      set (gf' := g' ;; f').
      match goal with |[ |- ?a = ?b ] =>
                       assert (X0 : (a,,pr2 (iscontrpr1 (unique_lift (g · f) d))) =
                                    (b,,gf')) end.

      { apply proofirrelevancecontr. apply X. }
      apply (maponpaths pr1 X0).
    + apply  (disp_mor_unique_disc_fib _ (D,,X)).
  - apply isaset_fiber_discrete_fibration.
Defined.

(** Some standard cartesian cells *)
Definition is_cartesian_id_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           (xx : D x)
  : is_cartesian (id_disp xx).
Proof.
  intros z g zz hh.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros f₁ f₂ ;
       use subtypePath ; [ intro ; intros ; apply D | ] ;
       refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)) ;
       rewrite (pr2 f₁), (pr2 f₂) ;
       apply idpath).
  - use tpair.
    + exact (transportf _ (id_right _) hh).
    + abstract
        (simpl ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite pathsinv0r ;
         apply idpath).
Defined.

Definition is_cartesian_comp_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {z : C}
           {zz : D z}
           {f : x --> y} {g : y --> z}
           {ff : xx -->[ f ] yy} {gg : yy -->[ g ] zz}
           (Hff : is_cartesian ff) (Hgg : is_cartesian gg)
  : is_cartesian (ff ;; gg)%mor_disp.
Proof.
  intros w h ww hh'.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros f₁ f₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (cartesian_factorisation_unique Hff) ;
       use (cartesian_factorisation_unique Hgg) ;
       rewrite !assoc_disp_var ;
       rewrite (pr2 f₁), (pr2 f₂) ;
       apply idpath).
  - simple refine (_ ,, _).
    + exact (cartesian_factorisation
               Hff
               h
               (cartesian_factorisation
                  Hgg
                  (h · f)
                  (transportf
                     (λ z, _ -->[ z ] _)
                     (assoc _ _ _)
                     hh'))).
    + abstract
        (simpl ;
         rewrite assoc_disp ;
         rewrite !cartesian_factorisation_commutes ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Definition is_cartesian_iso_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {f : x --> y}
           {Hf : is_iso f}
           {ff : xx -->[ f ] yy}
           (Hff : is_iso_disp (make_iso f Hf) ff)
  : is_cartesian ff.
Proof.
  intros z g zz gf.
  use iscontraprop1.
  - abstract
      (apply invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       pose (pr2 φ₁ @ !(pr2 φ₂)) as r ;
       refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)) ;
       pose (transportf_transpose_left (inv_mor_after_iso_disp Hff)) as r' ;
       rewrite <- !r' ; clear r' ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !assoc_disp ;
       unfold transportb ;
       rewrite !transport_f_f ;
       apply maponpaths ;
       apply maponpaths_2 ;
       exact r).
  - simple refine (_ ,, _).
    + refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (gf ;; inv_mor_disp_from_iso Hff)%mor_disp).
      abstract
        (rewrite assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (iso_inv_after_iso (make_iso f Hf))).
    + abstract
        (simpl ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite assoc_disp_var ;
         rewrite transport_f_f ;
         etrans ;
           [ do 2 apply maponpaths ;
             apply (iso_disp_after_inv_mor Hff)
           | ] ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property ;
         rewrite disp_id_right).
Defined.

Definition is_cartesian_transportf
           {C : category}
           {D : disp_cat C}
           {x y : C}
           {f f' : x --> y}
           (p : f = f')
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           (Hff : is_cartesian ff)
  : is_cartesian (transportf (λ z, _ -->[ z ] _) p ff).
Proof.
  intros c g cc gg.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (cartesian_factorisation_unique Hff) ;
       pose (p₁ := pr2 φ₁) ;
       pose (p₂ := pr2 φ₂) ;
       cbn in p₁, p₂ ;
       rewrite mor_disp_transportf_prewhisker in p₁ ;
       rewrite mor_disp_transportf_prewhisker in p₂ ;
       pose (transportb_transpose_right p₁) as r₁ ;
       pose (transportb_transpose_right p₂) as r₂ ;
       exact (r₁ @ !r₂)).
  - simple refine (_ ,, _).
    + exact (cartesian_factorisation
               Hff
               g
               (transportb
                  (λ z, _ -->[ z ] _)
                  (maponpaths (λ z, g · z) p)
                  gg)).
    + abstract
        (cbn ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite cartesian_factorisation_commutes ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Definition is_cartesian_precomp
           {C : category}
           {D : disp_cat C}
           {x y z : C}
           {f : x --> y}
           {g : y --> z}
           {h : x --> z}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff : xx -->[ f ] yy}
           {gg : yy -->[ g ] zz}
           {hh : xx -->[ h ] zz}
           (p : h = f · g)
           (pp : (ff ;; gg = transportf (λ z, _ -->[ z ] _) p hh)%mor_disp)
           (Hgg : is_cartesian gg)
           (Hhh : is_cartesian hh)
  : is_cartesian ff.
Proof.
  intros w φ ww φφ.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros ψ₁ ψ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (cartesian_factorisation_unique Hhh) ;
       rewrite <- (transportb_transpose_left pp) ;
       unfold transportb ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !assoc_disp ;
       rewrite (pr2 ψ₁), (pr2 ψ₂) ;
       apply idpath).
  - simple refine (_ ,, _).
    + refine (cartesian_factorisation
                Hhh
                φ
                (transportf (λ z, _ -->[ z ] _) _ (φφ ;; gg)%mor_disp)).
      abstract
        (rewrite p ;
         rewrite assoc ;
         apply idpath).
    + abstract
        (simpl ;
         use (cartesian_factorisation_unique Hgg) ;
         rewrite assoc_disp_var ;
         rewrite pp ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite cartesian_factorisation_commutes ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Definition iso_disp_to_is_cartesian
           {C : category}
           {D : disp_cat C}
           {x y z : C}
           {f : x --> z}
           {g : y --> z}
           {h : y --> x}
           (Hh : is_iso h)
           {p : h · f = g}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff : xx -->[ f ] zz}
           {gg : yy -->[ g ] zz}
           {hh : yy -->[ h ] xx}
           (Hff : is_cartesian ff)
           (Hhh : is_iso_disp (make_iso h Hh) hh)
           (pp : (hh ;; ff = transportb _ p gg)%mor_disp)
  : is_cartesian gg.
Proof.
  intros q k qq kg.
  assert (f = inv_from_iso (make_iso h Hh) · g) as r.
  {
    abstract
      (refine (!_) ;
       use iso_inv_on_right ;
       exact (!p)).
  }
  assert (transportf (λ z, _ -->[ z ] _) r ff
          =
          inv_mor_disp_from_iso Hhh ;; gg)%mor_disp as rr.
  {
    abstract
      (rewrite <- (transportb_transpose_left pp) ;
       unfold transportb ;
       rewrite mor_disp_transportf_prewhisker ;
       rewrite assoc_disp ;
       refine (!_) ;
       etrans ;
       [ do 2 apply maponpaths ;
         apply maponpaths_2 ;
         exact (iso_disp_after_inv_mor Hhh)
       | ] ;
       unfold transportb ;
       rewrite mor_disp_transportf_postwhisker ;
       rewrite id_left_disp ;
       unfold transportb ;
       rewrite !transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
  }
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (postcomp_with_iso_disp_is_inj Hh (idpath _) Hhh) ; cbn ;
       use (cartesian_factorisation_unique Hff) ;
       rewrite !assoc_disp_var ;
       rewrite pp ;
       unfold transportb ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !transport_f_f ;
       apply maponpaths ;
       exact (pr2 φ₁ @ !(pr2 φ₂))).
  - simple refine (_ ,, _).
    + refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (cartesian_factorisation
                   Hff
                   (k · h)
                   (transportf
                      (λ z, _ -->[ z ] _)
                      _
                      kg)
                 ;; inv_mor_disp_from_iso Hhh)%mor_disp).
      * abstract
          (rewrite assoc' ;
           etrans ; [ apply maponpaths ; apply (iso_inv_after_iso (make_iso h Hh)) | ] ;
           apply id_right).
      * abstract
          (rewrite assoc' ;
           rewrite p ;
           apply idpath).
    + abstract
        (simpl ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite assoc_disp_var ;
         etrans ; [ do 3 apply maponpaths ; exact (!rr) | ] ;
         rewrite transport_f_f ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite cartesian_factorisation_commutes ;
         rewrite !transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Definition is_opcartesian_id_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           (xx : D x)
  : is_opcartesian (id_disp xx).
Proof.
  apply is_cartesian_to_is_opcartesian.
  exact (@is_cartesian_id_disp _ (op_disp_cat D) _ xx).
Defined.

Definition is_opcartesian_comp_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {z : C}
           {zz : D z}
           {f : x --> y} {g : y --> z}
           {ff : xx -->[ f ] yy} {gg : yy -->[ g ] zz}
           (Hff : is_opcartesian ff) (Hgg : is_opcartesian gg)
  : is_opcartesian (ff ;; gg)%mor_disp.
Proof.
  apply is_cartesian_to_is_opcartesian.
  use (@is_cartesian_comp_disp _ (op_disp_cat D)).
  - apply is_opcartesian_weq_is_cartesian.
    exact Hgg.
  - apply is_opcartesian_weq_is_cartesian.
    exact Hff.
Defined.

Definition is_opcartesian_postcomp
           {C : category}
           {D : disp_cat C}
           {x y z : C}
           {f : x --> y}
           {g : y --> z}
           {h : x --> z}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff : xx -->[ f ] yy}
           {gg : yy -->[ g ] zz}
           {hh : xx -->[ h ] zz}
           (p : h = f · g)
           (pp : (ff ;; gg = transportf (λ z, _ -->[ z ] _) p hh)%mor_disp)
           (Hff : is_opcartesian ff)
           (Hhh : is_opcartesian hh)
  : is_opcartesian gg.
Proof.
  apply is_cartesian_to_is_opcartesian.
  use (@is_cartesian_precomp _ (op_disp_cat D) _ _ _ g f h zz yy xx gg ff hh p pp).
  - apply is_opcartesian_weq_is_cartesian.
    exact Hff.
  - apply is_opcartesian_weq_is_cartesian.
    exact Hhh.
Defined.

Definition is_opcartesian_iso_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {f : x --> y}
           {Hf : is_iso f}
           {ff : xx -->[ f ] yy}
           (Hff : is_iso_disp (make_iso f Hf) ff)
  : is_opcartesian ff.
Proof.
  apply is_cartesian_to_is_opcartesian.
  use (@is_cartesian_iso_disp _ (op_disp_cat D) _ _ _ _ _ _ ff).
  - exact (pr2 (@opp_iso C _ _ (make_iso f Hf))).
  - use (@to_iso_disp_op_disp_cat C D y x (make_iso f Hf) yy xx ff).
    exact Hff.
Defined.

Definition is_opcartesian_transportf
           {C : category}
           {D : disp_cat C}
           {x y : C}
           {f f' : x --> y}
           (p : f = f')
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           (Hff : is_opcartesian ff)
  : is_opcartesian (transportf (λ z, _ -->[ z ] _) p ff).
Proof.
  apply is_cartesian_to_is_opcartesian.
  apply (@is_cartesian_transportf _ (op_disp_cat D)).
  apply is_opcartesian_weq_is_cartesian.
  exact Hff.
Defined.

(**
Cartesian factorisation of disp nat trans and functor
 *)
Section CartesianFactorisationDispNatTrans.
  Context {C₁ C₂ : category}
          {F₁ F₂ F₃ : C₁ ⟶ C₂}
          {α : F₂ ⟹ F₃}
          {β : F₁ ⟹ F₂}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          {FF₁ : disp_functor F₁ D₁ D₂}
          {FF₂ : disp_functor F₂ D₁ D₂}
          {FF₃ : disp_functor F₃ D₁ D₂}
          (αα : disp_nat_trans α FF₂ FF₃)
          (ββ : disp_nat_trans (nat_trans_comp _ _ _ β α) FF₁ FF₃)
          (Hαα : ∏ (x : C₁) (xx : D₁ x), is_cartesian (αα x xx)).

  Definition cartesian_factorisation_disp_nat_trans_data
    : disp_nat_trans_data β FF₁ FF₂
    := λ x xx, cartesian_factorisation (Hαα x xx) (β x) (ββ x xx).

  Definition cartesian_factorisation_disp_nat_trans_axioms
    : disp_nat_trans_axioms cartesian_factorisation_disp_nat_trans_data.
  Proof.
    intros x y f xx yy ff ; cbn in *.
    unfold cartesian_factorisation_disp_nat_trans_data.
    use (cartesian_factorisation_unique (Hαα y yy)).
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    refine (maponpaths _ (disp_nat_trans_ax ββ ff) @ _).
    unfold transportb.
    rewrite !transport_f_f.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (disp_nat_trans_ax αα ff).
    }
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition cartesian_factorisation_disp_nat_trans
    : disp_nat_trans β FF₁ FF₂.
  Proof.
    simple refine (_ ,, _).
    - exact cartesian_factorisation_disp_nat_trans_data.
    - exact cartesian_factorisation_disp_nat_trans_axioms.
  Defined.
End CartesianFactorisationDispNatTrans.

Section CartesianFactorisationDispFunctor.
  Context {C₁ C₂ : category}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (HD₁ : cleaving D₂)
          {F G : C₁ ⟶ C₂}
          (GG : disp_functor G D₁ D₂)
          (α : F ⟹ G).

  Definition cartesian_factorisation_disp_functor_data
    : disp_functor_data F D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, pr1 (HD₁ (G x) (F x) (α x) (GG x xx))).
    - exact (λ x y xx yy f ff,
             cartesian_factorisation
               (pr22 (HD₁ (G y) (F y) (α y) (GG y yy)))
               _
               (transportb
                  (λ z, _ -->[ z ] _)
                  (nat_trans_ax α _ _ f)
                  (pr12 (HD₁ (G x) (F x) (α x) (GG x xx)) ;; #GG ff)%mor_disp)).
  Defined.

  Definition cartesian_factorisation_disp_functor_axioms
    : disp_functor_axioms cartesian_factorisation_disp_functor_data.
  Proof.
    repeat split.
    - intros x xx ; cbn.
      use (cartesian_factorisation_unique
             (pr22 (HD₁ (G x) (F x) (α x) (GG x xx)))).
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z xx yy zz f g ff hh ; cbn.
      use (cartesian_factorisation_unique
             (pr22 (HD₁ (G z) (F z) (α z) (GG z zz)))).
      unfold transportb.
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition cartesian_factorisation_disp_functor
    : disp_functor F D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact cartesian_factorisation_disp_functor_data.
    - exact cartesian_factorisation_disp_functor_axioms.
  Defined.

  Definition cartesian_factorisation_disp_functor_is_cartesian
             (HGG : is_cartesian_disp_functor GG)
    : is_cartesian_disp_functor cartesian_factorisation_disp_functor.
  Proof.
    intros x y f xx yy ff Hff ; cbn.
    pose (HGff := HGG _ _ _ _ _ _ Hff).
    refine (is_cartesian_precomp
              (idpath _)
              _
              (pr22 (HD₁ (G x) (F x) (α x) (GG x xx)))
              (is_cartesian_transportf
                 (!(nat_trans_ax α _ _ f))
                 (is_cartesian_comp_disp
                    (pr22 (HD₁ (G y) (F y) (α y) (GG y yy)))
                    HGff))).
    rewrite cartesian_factorisation_commutes.
    apply idpath.
  Qed.

  Definition cartesian_factorisation_disp_functor_cell_data
    : disp_nat_trans_data α cartesian_factorisation_disp_functor_data GG
    := λ x xx, pr12 (HD₁ (G x) (F x) (α x) (GG x xx)).

  Definition cartesian_factorisation_disp_functor_cell_axioms
    : disp_nat_trans_axioms cartesian_factorisation_disp_functor_cell_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold cartesian_factorisation_disp_functor_cell_data.
    unfold transportb.
    rewrite cartesian_factorisation_commutes.
    apply idpath.
  Qed.

  Definition cartesian_factorisation_disp_functor_cell
    : disp_nat_trans
        α
        cartesian_factorisation_disp_functor_data
        GG.
  Proof.
    simple refine (_ ,, _).
    - exact cartesian_factorisation_disp_functor_cell_data.
    - exact cartesian_factorisation_disp_functor_cell_axioms.
  Defined.

  Definition cartesian_factorisation_disp_functor_cell_is_cartesian
             {x : C₁}
             (xx : D₁ x)
    : is_cartesian (cartesian_factorisation_disp_functor_cell x xx).
  Proof.
    exact (pr22 (HD₁ (G x) (F x) (α x) (GG x xx))).
  Defined.
End CartesianFactorisationDispFunctor.

(**
Cartesian factorisation of disp nat trans and functor
 *)
Section OpCartesianFactorisationDispNatTrans.
  Context {C₁ C₂ : category}
          {F₁ F₂ F₃ : C₁ ⟶ C₂}
          {α : F₁ ⟹ F₂}
          {β : F₂ ⟹ F₃}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          {FF₁ : disp_functor F₁ D₁ D₂}
          {FF₂ : disp_functor F₂ D₁ D₂}
          {FF₃ : disp_functor F₃ D₁ D₂}
          (αα : disp_nat_trans α FF₁ FF₂)
          (ββ : disp_nat_trans (nat_trans_comp _ _ _ α β) FF₁ FF₃)
          (Hαα : ∏ (x : C₁) (xx : D₁ x), is_opcartesian (αα x xx)).

  Definition opcartesian_factorisation_disp_nat_trans_data
    : disp_nat_trans_data β FF₂ FF₃
    := λ x xx, opcartesian_factorisation (Hαα x xx) (β x) (ββ x xx).

  Definition opcartesian_factorisation_disp_nat_trans_axioms
    : disp_nat_trans_axioms opcartesian_factorisation_disp_nat_trans_data.
  Proof.
    intros x y f xx yy ff ; cbn in *.
    unfold opcartesian_factorisation_disp_nat_trans_data.
    use (opcartesian_factorisation_unique (Hαα x xx)).
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite opcartesian_factorisation_commutes.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (disp_nat_trans_ax_var αα ff).
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    rewrite opcartesian_factorisation_commutes.
    etrans.
    {
      apply maponpaths.
      exact (disp_nat_trans_ax ββ ff).
    }
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition opcartesian_factorisation_disp_nat_trans
    : disp_nat_trans β FF₂ FF₃.
  Proof.
    simple refine (_ ,, _).
    - exact opcartesian_factorisation_disp_nat_trans_data.
    - exact opcartesian_factorisation_disp_nat_trans_axioms.
  Defined.
End OpCartesianFactorisationDispNatTrans.

Section OpCartesianFactorisationDispFunctor.
  Context {C₁ C₂ : category}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (HD₁ : opcleaving D₂)
          {F G : C₁ ⟶ C₂}
          (FF : disp_functor F D₁ D₂)
          (α : F ⟹ G).

  Definition opcartesian_factorisation_disp_functor_data
    : disp_functor_data G D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, ob_of_opcartesian_lift _ (HD₁ (F x) (G x) (FF x xx) (α x))).
    - exact (λ x y xx yy f ff,
             opcartesian_factorisation
               (mor_of_opcartesian_lift_is_opcartesian
                  _
                  (HD₁ (F x) (G x) (FF x xx) (α x)))
               _
               (transportf
                  (λ z, _ -->[ z ] _)
                  (nat_trans_ax α _ _ f)
                  (#FF ff
                   ;;
                   mor_of_opcartesian_lift
                     _
                     (HD₁ (F y) (G y) (FF y yy) (α y))))).
  Defined.

  Definition opcartesian_factorisation_disp_functor_axioms
    : disp_functor_axioms opcartesian_factorisation_disp_functor_data.
  Proof.
    repeat split.
    - intros x xx ; cbn.
      use (opcartesian_factorisation_unique
             (pr22 (HD₁ (F x) (G x) (FF x xx) (α x)))).
      rewrite opcartesian_factorisation_commutes.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z xx yy zz f g ff hh ; cbn.
      use (opcartesian_factorisation_unique
             (pr22 (HD₁ (F x) (G x) (FF x xx) (α x)))).
      unfold transportb.
      rewrite opcartesian_factorisation_commutes.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite !assoc_disp_var.
      unfold transportb.
      rewrite transport_f_f.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition opcartesian_factorisation_disp_functor
    : disp_functor G D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact opcartesian_factorisation_disp_functor_data.
    - exact opcartesian_factorisation_disp_functor_axioms.
  Defined.

  Definition opcartesian_factorisation_disp_functor_is_opcartesian
             (HFF : is_opcartesian_disp_functor FF)
    : is_opcartesian_disp_functor opcartesian_factorisation_disp_functor.
  Proof.
    intros x y f xx yy ff Hff ; cbn.
    pose (HFff := HFF _ _ _ _ _ _ Hff).
    use (is_opcartesian_postcomp
           (idpath _)
           _
           (pr22 (HD₁ (F y) (G y) (FF y yy) (α y)))
           (is_opcartesian_transportf
              (nat_trans_ax α _ _ f)
              (is_opcartesian_comp_disp
                 HFff
                 (pr22 (HD₁ (F x) (G x) (FF x xx) (α x)))))).
    rewrite opcartesian_factorisation_commutes.
    apply idpath.
  Qed.

  Definition opcartesian_factorisation_disp_functor_cell_data
    : disp_nat_trans_data α FF opcartesian_factorisation_disp_functor_data
    := λ x xx, pr12 (HD₁ (F x) (G x) (FF x xx) (α x)).

  Definition opcartesian_factorisation_disp_functor_cell_axioms
    : disp_nat_trans_axioms opcartesian_factorisation_disp_functor_cell_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold opcartesian_factorisation_disp_functor_cell_data.
    unfold transportb.
    rewrite opcartesian_factorisation_commutes.
    rewrite transport_f_f.
    refine (!_).
    apply transportf_set.
    apply homset_property.
  Qed.

  Definition opcartesian_factorisation_disp_functor_cell
    : disp_nat_trans
        α
        FF
        opcartesian_factorisation_disp_functor_data.
  Proof.
    simple refine (_ ,, _).
    - exact opcartesian_factorisation_disp_functor_cell_data.
    - exact opcartesian_factorisation_disp_functor_cell_axioms.
  Defined.

  Definition opcartesian_factorisation_disp_functor_cell_is_opcartesian
             {x : C₁}
             (xx : D₁ x)
    : is_opcartesian (opcartesian_factorisation_disp_functor_cell x xx).
  Proof.
    exact (pr22 (HD₁ (F x) (G x) (FF x xx) (α x))).
  Defined.
End OpCartesianFactorisationDispFunctor.

Section fiber_functor_from_cleaving.

  Context {C : category} (D : disp_cat C) (F : cleaving D).
  Context {c c' : C} (f : C⟦c', c⟧).

  Let lift_f :  ∏ d : D c, cartesian_lift d f := F _ _ f.

  Definition fiber_functor_from_cleaving_data : functor_data (D [{c}]) (D [{c'}]).
  Proof.
    use tpair.
    + intro d. exact (object_of_cartesian_lift _ _ (lift_f d)).
    + intros d' d ff. cbn.

      set (XR' := @cartesian_factorisation C D _ _ f).
      specialize (XR' _ _ _ (lift_f d)).
      use XR'.
      * use (transportf (mor_disp _ _ )
                        _
                        (mor_disp_of_cartesian_lift _ _ (lift_f d') ;; ff)).
        etrans; [ apply id_right |]; apply pathsinv0; apply id_left.
  Defined.

  Lemma is_functor_from_cleaving_data : is_functor fiber_functor_from_cleaving_data.
  Proof.
    split.
    - intro d; cbn.
      apply pathsinv0.
      apply path_to_ctr.
      etrans; [apply id_left_disp |].
      apply pathsinv0.
      etrans. { apply maponpaths. apply id_right_disp. }
      etrans; [ apply transport_f_f |].
      unfold transportb.
      apply maponpaths_2.
      apply homset_property.
    - intros d'' d' d ff' ff; cbn.
      apply pathsinv0.
      apply path_to_ctr.
      etrans; [apply mor_disp_transportf_postwhisker |].
      apply pathsinv0.
      etrans. { apply maponpaths; apply mor_disp_transportf_prewhisker. }
      etrans; [apply transport_f_f |].
      apply transportf_comp_lemma.
      apply pathsinv0.
      etrans; [apply assoc_disp_var |].
      apply pathsinv0.
      apply transportf_comp_lemma.
      apply pathsinv0.
      etrans ; [ apply maponpaths, cartesian_factorisation_commutes |].
      etrans ; [ apply mor_disp_transportf_prewhisker |].
      apply pathsinv0.
      apply transportf_comp_lemma.
      apply pathsinv0.
      etrans; [ apply assoc_disp |].
      apply pathsinv0.
      apply transportf_comp_lemma.
      apply pathsinv0.
      etrans; [ apply maponpaths_2, cartesian_factorisation_commutes |].
      etrans; [ apply mor_disp_transportf_postwhisker |].
      etrans. { apply maponpaths. apply assoc_disp_var. }
      etrans. { apply transport_f_f. }
      apply maponpaths_2, homset_property.
  Qed.

  Definition fiber_functor_from_cleaving : D [{c}] ⟶ D [{c'}]
    := make_functor _  is_functor_from_cleaving_data.

End fiber_functor_from_cleaving.

Section Essential_Surjectivity.

  Definition fiber_functor_ess_split_surj
             {C C' : category} {D} {D'}
             {F : functor C C'} (FF : disp_functor F D D')
             (H : disp_functor_ff FF)
             {X : disp_functor_ess_split_surj FF}
             {Y : is_op_isofibration D}
             (* TODO: change to [is_isofibration], once [is_isofibration_iff_is_op_isofibration] is provided *)
             (x : C)
    : ∏ yy : D'[{F x}], ∑ xx : D[{x}],
          iso (fiber_functor FF _ xx) yy.
  Proof.
    intro yy.
    set (XR := X _ yy).
    destruct XR as [c'' [i [xx' ii]]].
    set (YY := Y _ _ i xx').
    destruct YY as [ dd pe ].
    use tpair.
    - apply dd.
    - (* now need disp_functor_on_iso_disp *)
      set (XR := disp_functor_on_iso_disp FF pe).
      set (XR' := iso_inv_from_iso_disp XR).
      (* now need composition of iso_disps *)
      apply  (invweq (iso_disp_iso_fiber _ _ _ _)).
      set (XRt := iso_disp_comp XR' ii).
      transparent assert (XH :
                           (iso_comp (iso_inv_from_iso (functor_on_iso F i))
                                     (functor_on_iso F i) = identity_iso _ )).
      { apply eq_iso. cbn. simpl. unfold precomp_with.
        etrans. apply maponpaths_2. apply id_right.
        etrans. eapply pathsinv0. apply functor_comp.
        etrans. 2: apply functor_id.
        apply maponpaths. apply iso_after_iso_inv.
      }
      set (XRT := transportf (λ r, iso_disp r (FF x dd) yy )
                             XH).
      apply XRT.
      assumption.
  Defined.

End Essential_Surjectivity.
