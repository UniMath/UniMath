(** Definitions of various kinds of _fibraitions_, using displayed categories. *)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.

Set Automatic Introduction.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.
Local Open Scope hide_transport_scope.

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

Definition is_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c' c) (d : D c),
          Σ d' : D c', iso_disp i d' d.

Definition is_uncloven_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c' c) (d : D c),
          ∃ d' : D c', iso_disp i d' d.

(** As with fibrations, there is an evident dual version.  However, in the iso case, it is self-dual: having forward (i.e. cocartesian) liftings along isos is equivalent to having backward (cartesian) liftings. *)

Definition is_op_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c c') (d : D c),
          Σ d' : D c', iso_disp i d d'.

Lemma is_isofibration_iff_is_op_isofibration 
    {C : Precategory} (D : disp_precat C)
  : is_isofibration D <-> is_op_isofibration D.
Proof.
  (* TODO: give this! *)
Abort.

End Isofibrations.

(** * Fibrations *)
Section Fibrations.

Definition is_cartesian {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall c'' (g : c'' --> c') (d'' : D c'') (hh : d'' -->[g;;f] d),
  ∃! (gg : d'' -->[g] d'), gg ;; ff = hh.

(** See also [cartesian_factorisation'] below, for when the map one wishes to factor is not judgementally over [g;;f], but over some equal map. *)
Definition cartesian_factorisation {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g;;f] d)
  : d'' -->[g] d'
:= pr1 (pr1 (H _ g _ hh)).

Definition cartesian_factorisation_commutes
    {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g;;f] d)
  : cartesian_factorisation H g hh ;; ff = hh
:= pr2 (pr1 (H _ g _ hh)).

(** This is essentially the third access function for [is_cartesian], but given in a more usable form than [pr2 (H …)] would be. *)
Definition cartesian_factorisation_unique
    {C : Precategory} {D : disp_precat C}
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

Definition cartesian_factorisation' {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g ;; f = h)%mor)
  : d'' -->[g] d'.
Proof.
  simple refine (cartesian_factorisation H g _).
  exact (transportb _ e hh).
Defined.

Definition cartesian_factorisation_commutes'
    {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g ;; f = h)%mor)
  : (cartesian_factorisation' H g hh e) ;; ff
  = transportb _ e hh.
Proof.
  apply cartesian_factorisation_commutes.
Qed.

Definition cartesian_lift {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
  : UU
:= Σ (d' : D c') (ff : d' -->[f] d), is_cartesian ff.

Definition object_of_cartesian_lift  {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : D c'
:= pr1 fd.
Coercion object_of_cartesian_lift : cartesian_lift >-> ob_disp.

Definition mor_disp_of_cartesian_lift  {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : (fd : D c') -->[f] d
:= pr1 (pr2 fd).
Coercion mor_disp_of_cartesian_lift : cartesian_lift >-> mor_disp.

Definition cartesian_lift_is_cartesian {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : is_cartesian fd
:= pr2 (pr2 fd).
Coercion cartesian_lift_is_cartesian : cartesian_lift >-> is_cartesian.

(* TODO: should the arguments be re-ordered as in [cartesian_lift]? If so, reorder in [isofibration] etc as well, for consistency. *)
Definition is_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (f : c' --> c) (d : D c), cartesian_lift d f.

(* TODO: give access functions! *)

Definition is_uncloven_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (f : c' --> c) (d : D c), ∥ cartesian_lift d f ∥.

(** ** Connection with isofibrations *)

Lemma is_iso_from_is_cartesian {C : Precategory} {D : disp_precat C}
    {c c' : C} (i : iso c' c) {d : D c} {d'} (ff : d' -->[i] d)
  : is_cartesian ff -> is_iso_disp i ff.
Proof.
  intros Hff.
  simple refine (_,,_); try split.
  - simple refine
      (cartesian_factorisation' Hff (inv_from_iso i) (id_disp _) _).
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

Lemma is_isofibration_from_is_fibration {C : Precategory} {D : disp_precat C}
  : is_fibration D -> is_isofibration D.
Proof.
  intros D_fib c c' f d.
  assert (fd := D_fib _ _ f d).
  exists (fd : D _).
  exists (fd : _ -->[_] _).
  apply is_iso_from_is_cartesian; exact fd.
Defined.

(** ** Uniqueness of cartesian lifts *)

(* TODO: show that when [D] is _univalent_, cartesian lifts are literally unique, and so any uncloven fibration (isofibration, etc) is in fact cloven. *)
Definition cartesian_lifts_iso {C : Precategory} {D : disp_precat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : iso_disp (identity_iso c') fd fd'.
Proof.
  simple refine (_,,(_,,_)).
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

Definition cartesian_lifts_iso_commutes {C : Precategory} {D : disp_precat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : (cartesian_lifts_iso fd fd') ;; fd'
  = transportb _ (id_left _) (fd : _ -->[_] _).
Proof.
  cbn. apply cartesian_factorisation_commutes'.
Qed.

(** In a displayed _category_ (i.e. _univalent_), cartesian lifts are literally unique, if they exist; that is, the type of cartesian lifts is always a proposition. *) 
Definition isaprop_cartesian_lifts
    {C : Precategory} {D : disp_precat C} (D_cat : is_category_disp D)
    {c} (d : D c) {c' : C} (f : c' --> c)
  : isaprop (cartesian_lift d f).
Proof.
  apply invproofirrelevance; intros fd fd'.
  use total2_paths.
  { apply (isotoid_disp D_cat (idpath _)); cbn.
    apply cartesian_lifts_iso. }
  apply subtypeEquality.
  { intros ff. repeat (apply impred; intro).
    apply isapropiscontr. }
  etrans.
    refine (@functtransportf_2 (D c') _ _ (fun x => pr1) _ _ _ _). 
  cbn. etrans. apply transportf_precompose_disp.
  rewrite idtoiso_isotoid_disp.
  refine (pathscomp0 (maponpaths _ _) (Utilities.transportfbinv _ _ _)). 
  apply (precomp_with_iso_disp_is_inj (cartesian_lifts_iso fd fd')).
  etrans. apply assoc_disp.
  etrans. eapply transportf_bind, cancel_postcomposition_disp.
    refine (inv_mor_after_iso_disp _).
  etrans. eapply transportf_bind, id_left_disp.
  apply pathsinv0.
  etrans. apply mor_disp_transportf_prewhisker.
  etrans. eapply transportf_bind, cartesian_lifts_iso_commutes.
  apply maponpaths_2, homset_property.  
Defined.

Definition univalent_fibration_is_cloven
    {C : Precategory} {D : disp_precat C} (D_cat : is_category_disp D)
  : is_uncloven_fibration D -> is_fibration D.
Proof.
  intros D_fib c c' f d.
  apply (squash_to_prop (D_fib c c' f d)).
  apply isaprop_cartesian_lifts; assumption.
  auto.
Defined.
 
End Fibrations.

Section Discrete_Fibrations.

Definition is_discrete_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (f : c' --> c) (d : D c),
          ∃! d' : D c', d' -->[f] d.

Definition discrete_fibration C : UU
  := Σ D : disp_precat C, is_discrete_fibration D.

(* GOAL: correspondence between discrete fibrations and presheaves.

Outline via categories:

- show that the fibers of a discrete fibration are (discrete categories on) sets, and that the disp morphism types are props;
- define the category of discrete fibrations over C, using [functor_over_id] for morphisms, and with [homset_property] coming from the previous point;
- construct equivalence of cats; probably easiest by explicit functors and natural isos (not by “ess split” plus “full and faithful”); 
- show [disc_fib_precat C] is univalent (possibly _using_ the above equivalence of cats, to get “isos of displayed cats are weq to isos btn associated presheaves”?);
- conclude equivalence of types.

More direct equivalence of types:

- ?

 *)
 
End Discrete_Fibrations.

Section Opfibrations.

(* TODO: add definitions analogous to in [Fibrations].  For constructions/theorems: think about whether it’s possible to recover them by duality, instead of repeating all proofs?? *)

End Opfibrations.