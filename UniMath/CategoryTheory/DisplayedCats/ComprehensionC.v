
(** * Displayed Category from a category with display maps

Definition of the displayed category of display maps over a category [C]

Given a category with display maps [C], we define a displayed
category over [C]. Objects over [c:C] are display maps into [c].

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope cat.

(** * Definition of a cartesian displayed functor *)

(* TODO: upstream *)
Lemma is_cartesian_from_z_iso_to_cartesian
    {C : category} {D : disp_cat C}
    {c} {d : D c} {c' : C} {f : c' --> c}
    {d0'} {ff : d0' -->[f] d} (ff_cart : is_cartesian ff)
    {d1'} {ff' : d1' -->[f] d}
    (i : z_iso_disp (identity_z_iso _) d0' d1')
    (e : (i ;; ff')%mor_disp
         = transportb _ (id_left _) ff)
  : is_cartesian ff'.
Proof.
  intros c'' g d'' h.
  refine (iscontrweqf _ (ff_cart c'' g d'' h)).
  use weq_subtypes'.
  - eapply weqcomp.
    + exists (fun gg => (gg ;; i))%mor_disp.
      apply z_iso_disp_postcomp.
    + exists (transportf _ (id_right _)).
      apply isweqtransportf.
  - intro; apply homsets_disp.
  - intro; apply homsets_disp.
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

(** For a functor to be cartesian, it’s enough to show that it preserves _some_ cartesian lift of each lifting problem.

  Of course, this can only happen when the domain is a fibration; and in practice, it is useful exactly in the case where one has shown it is a fibration by exhibiting some particular construction of (mere existence of) cartesian lifts. *)
Lemma cartesian_functor_from_fibration
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
    (H : forall (c c' : C) (f : c' --> c) (d : D c),
      ∥ total2 (fun ff : cartesian_lift d f => is_cartesian (♯ FF ff)) ∥)
  : is_cartesian_disp_functor FF.
Proof.
  intros c c' f d d' ff ff_cart.
  use (squash_to_prop (H _ _ f d)).
  - apply isaprop_is_cartesian.
  - intros [ff' ff'_cart].
    use (is_cartesian_from_z_iso_to_cartesian ff'_cart).
    + refine (transportf (fun i => z_iso_disp i _ _)
                       _
                       (@disp_functor_on_z_iso_disp
                          _ _ _ _ _ FF
                          _ _ _ _ (identity_z_iso _) _)).
      apply (z_iso_eq _ _), functor_id.
      refine (cartesian_lifts_iso ff' (_,,_)).
      exact (_,,ff_cart).
    + etrans. {
        apply maponpaths_2.
        refine (@pr1_transportf _ _  (fun i ff => is_z_iso_disp i ff) _ _ _ _). }
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
    (H : forall c c' f d, is_cartesian (♯ FF (clD c c' f d)))
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

Definition make_comprehension_cat_structure
  {C : category}
  (D : disp_cat C)
  {clD : cleaving D}
  (χ : disp_functor (functor_identity C) D (disp_codomain C))
  (H : forall c c' f d, is_cartesian (♯ χ (clD c c' f d)))
  (* (Hχ : is_cartesian_disp_functor χ) *)
  : comprehension_cat_structure C :=
  (D ,, clD ,, χ ,, cartesian_functor_from_cleaving clD H).

Definition comprehension {C : category} (CC : comprehension_cat_structure C)
  : disp_functor (functor_identity C) (pr1 CC) (disp_codomain C) :=
  pr122 CC.
Declare Scope comp_cat_struct.
Local Open Scope comp_cat_struct.
Notation "'π_χ'" := comprehension : comp_cat_struct.

(** Pseudo Map between Comprehension Categories *)
Definition pseudo_map_structure {C C' : category} (CC : comprehension_cat_structure C) (CC' : comprehension_cat_structure C') :=
  ∑ (F : C ⟶ C') (F_bar : disp_functor F (pr1 CC) (pr1 CC')),
    disp_nat_z_iso (disp_functor_composite F_bar (π_χ CC')) (disp_functor_composite (π_χ CC) (disp_codomain_functor F)) (nat_z_iso_id F).

Definition make_pseudo_map_structure
  {C C' : category} {CC : comprehension_cat_structure C} {CC' : comprehension_cat_structure C'}
  {F : C ⟶ C'}
  (F_bar : disp_functor F (pr1 CC) (pr1 CC'))
  (ϕ : disp_nat_z_iso (disp_functor_composite F_bar (π_χ CC')) (disp_functor_composite (π_χ CC) (disp_codomain_functor F)) (nat_z_iso_id F))
  : pseudo_map_structure CC CC'
  := (F ,, F_bar ,, ϕ).

(** Transformation between Pseudo Maps *)
Lemma base_nat_trans_equality
  {C C' : category} {F G: C ⟶ C'} (α : nat_trans F G)
  : nat_trans_comp (functor_composite F (functor_identity C'))
     (functor_composite G (functor_identity C')) (functor_identity C ∙ G)
     (post_whisker α (functor_identity C')) (nat_z_iso_id G) =
   nat_trans_comp (F ∙ functor_identity C') (functor_identity C ∙ F)
     (functor_composite (functor_identity C) G) (nat_z_iso_id F)
     (pre_whisker (functor_identity C) α).
Proof.
  simpl.
  rewrite identity_pre_whisker.
  rewrite identity_post_whisker.
  rewrite (nat_trans_comp_id_left (pr2 C') F G _).
  rewrite (nat_trans_comp_id_right (pr2 C') F G _).
  apply idpath.
Qed.

Definition transformation_structure_axiom
  {C C' : category}
  {CC : comprehension_cat_structure C} {CC' : comprehension_cat_structure C'}
  {F F': pseudo_map_structure CC CC'}
  {α : nat_trans (pr1 F) (pr1 F')}
  (α_bar : disp_nat_trans α (pr12 F) (pr12 F'))
  := disp_nat_trans_comp (post_whisker_disp_nat_trans α_bar (π_χ CC')) (pr22 F')
    =
      transportb
        (λ n, disp_nat_trans n _ _)
        (base_nat_trans_equality α)
      (disp_nat_trans_comp (pr22 F) (pre_whisker_disp_nat_trans (π_χ CC) (disp_codomain_nat_trans α))).

Definition transformation_structure
  {C C' : category}
  {CC : comprehension_cat_structure C} {CC' : comprehension_cat_structure C'}
  (F F': pseudo_map_structure CC CC')
  :=
  ∑ (α : nat_trans (pr1 F) (pr1 F')) (α_bar : disp_nat_trans α (pr12 F) (pr12 F')),
    transformation_structure_axiom α_bar
.
