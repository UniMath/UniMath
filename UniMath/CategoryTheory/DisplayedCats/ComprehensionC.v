
(** * Displayed Category from a category with display maps

Definition of the displayed category of display maps over a category [C]

Given a category with display maps [C], we define a displayed
category over [C]. Objects over [c:C] are display maps into [c].

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Codomain.
Require Import TypeTheory.Displayed_Cats.Fibrations.
Require Import TypeTheory.Displayed_Cats.DisplayedCatFromCwDM.
Require Import TypeTheory.OtherDefs.DM.


(** * Definition of a cartesian displayed functor *)

(* TODO: upstream to with definition of fibrations/cartesianness *)
Definition is_cartesian_disp_functor
  {C C' : category} {F : functor C C'}
  {D : disp_cat C} {D' : disp_cat C'} (FF : disp_functor F D D') : UU
:= ∏  {c c' : C} {f : c' --> c}
      {d : D c} {d' : D c'} (ff : d' -->[f] d),
  is_cartesian ff -> is_cartesian (#FF ff).


(* TODO: upstream *)
Lemma isaprop_is_cartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : isaprop (is_cartesian ff).
Proof.
  repeat (apply impred_isaprop; intro).
  apply isapropiscontr.
Qed.

(* TODO: upstream *)
Lemma is_cartesian_from_iso_to_cartesian
    {C : category} {D : disp_cat C}
    {c} {d : D c} {c' : C} {f : c' --> c}
    {d0'} {ff : d0' -->[f] d} (ff_cart : is_cartesian ff)
    {d1'} {ff' : d1' -->[f] d}
    (i : iso_disp (identity_iso _) d0' d1')
    (e : (i ;; ff')%mor_disp
         = transportb _ (id_left _) ff)
  : is_cartesian ff'.
Proof.
  intros c'' g d'' h.
  refine (iscontrweqf _ (ff_cart c'' g d'' h)).
  use weq_subtypes'.
  - eapply weqcomp.
    + exists (fun gg => (gg ;; i))%mor_disp.
      apply iso_disp_postcomp.
    + exists (transportf _ (id_right _)).
      apply isweqtransportf.
  - intros ?; apply homsets_disp.
  - intros ?; apply homsets_disp.
  - simpl. intros gg.
    (* Better, if [weq_pathscomp0] existed:
      apply weq_to_iff, weq_pathscomp0. *)
    assert (forall X (x y z : X),
      x = y -> (x = z <-> y = z)) as H.
    { intros X x y z p; split.
      + intros q; exact (!p @ q).
      + intros q; exact (p @ q).
    }
    apply H.
    apply pathsinv0.
    etrans. apply mor_disp_transportf_postwhisker.
    etrans. eapply transportf_bind.
      apply assoc_disp_var.
    etrans. eapply transportf_bind.
      etrans. apply maponpaths, e.
      apply mor_disp_transportf_prewhisker.
    refine (_ @ idpath_transportf _ _).
    apply maponpaths_2, homset_property.
Defined.

(* TODO: upstream *)

(* TODO: upstream also *)
(** For a functor to be cartesian, it’s enough to show that it preserves _some_ cartesian lift of each lifting problem.

  Of course, this can only happen when the domain is a fibration; and in practice, it is useful exactly in the case where one has shown it is a fibration by exhibiting some particular construction of (mere existence of) cartesian lifts. *)
Lemma cartesian_functor_from_fibration
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
    (H : forall (c c' : C) (f : c' --> c) (d : D c),
      ∥ { ff : cartesian_lift d f & is_cartesian (#FF ff) } ∥)
  : is_cartesian_disp_functor FF.
Proof.
  intros c c' f d d' ff ff_cart.
  use (squash_to_prop (H _ _ f d)).
  - apply isaprop_is_cartesian.
  - intros [ff' ff'_cart].
    use (is_cartesian_from_iso_to_cartesian ff'_cart).
    + refine (transportf (fun i => iso_disp i _ _)
                       _
                       (@disp_functor_on_iso_disp
                          _ _ _ _ _ FF
                          _ _ _ _ (identity_iso _) _)).
      apply (eq_iso _ _), functor_id.
      refine (cartesian_lifts_iso ff' (_,,_)).
      exact (_,,ff_cart).
    + etrans. {
        apply maponpaths_2.
        refine (pr1_transportf _ _ (fun i ff => is_iso_disp i ff) _ _ _ _). }
      etrans. {
        apply maponpaths_2.
        apply functtransportf. }
      etrans. {
        apply mor_disp_transportf_postwhisker. }
      etrans. {
        eapply maponpaths. simpl.
        etrans. {
          eapply pathsinv0, disp_functor_comp_var. }
        eapply transportf_bind.
        etrans. {
          apply maponpaths, cartesian_factorisation_commutes'. }
        apply disp_functor_transportf. }
      etrans. apply transport_f_f.
      unfold transportb. apply maponpaths_2, homset_property.
Qed.

Lemma cartesian_functor_from_cleaving
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
    (clD : cleaving D)
    (H : forall c c' f d, is_cartesian (# FF (clD c c' f d)))
  : is_cartesian_disp_functor FF.
Proof.
  apply cartesian_functor_from_fibration.
  intros c c' f d. apply hinhpr.
  exists (clD c c' f d).
  apply H.
Qed.

Definition comprehension_cat_structure (C : category) : UU
  := ∑ (D : disp_cat C) (H : cleaving D)
     (F : disp_functor (functor_identity _ ) D (disp_codomain C)),
     is_cartesian_disp_functor F.

Arguments comprehension_cat_structure _ : clear implicits.

Section Comp_Cat_of_DM_Structure.

Context {C : category}.

(* TODO: change name [dm_sub_pb] to something more comprehensible, e.g. [dm_struct]. *)
Variable (H : dm_sub_pb C).

Definition comprehension_of_dm_structure_data
  : disp_functor_data (functor_identity C) (DM_disp H) (disp_codomain C).
Proof.
  use tpair.
  + intros x d. cbn in *.
    exact (pr1 d).
  + cbn. intros x y xx yy f ff.
    exact ff.
Defined.

Definition comprehension_of_dm_structure_axioms
  : disp_functor_axioms comprehension_of_dm_structure_data.
Proof.
  cbn; repeat split; cbn.
  + intros.
    apply subtypeEquality.
    { intro. apply homset_property. }
    apply idpath.
  + intros.
    apply subtypeEquality.
    { intro. apply homset_property. }
    apply idpath.
Qed.

Definition comprehension_of_dm_structure
  : disp_functor _ _ _ := _ ,, comprehension_of_dm_structure_axioms.

Lemma is_cartesian_comprehension_of_dm_structure
  : is_cartesian_disp_functor comprehension_of_dm_structure.
Proof.
  use cartesian_functor_from_cleaving.
  - apply is_fibration_DM_disp.
  - intros c c' f d.
    apply isPullback_cartesian_in_cod_disp.
    apply isPullback_of_dm_sub_pb, homset_property.
Qed.

Definition total_comprehension_of_dm_structure
  : functor _ _ := total_functor comprehension_of_dm_structure.


(** This commutativity is an instance of a general lemma about comprehension categories
    once we have produced [comp_cat_of_dm] below
*)
Lemma comprehension_of_dm_structure_triangle_commutes
: functor_composite total_comprehension_of_dm_structure (pr1_category _)
  = pr1_category _ .
Proof.
  apply functor_eq.
  - apply homset_property.
  - apply idpath.
Qed.

Definition comp_cat_of_dm :  comprehension_cat_structure C.
Proof.
  mkpair.
  - apply DM_disp. apply H.
  - mkpair.
    + apply is_fibration_DM_disp.
    + mkpair.
      * apply comprehension_of_dm_structure.
      * apply is_cartesian_comprehension_of_dm_structure.
Defined.

End Comp_Cat_of_DM_Structure.
