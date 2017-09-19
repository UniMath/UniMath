
(** * Displayed category from a category with display maps

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
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import TypeTheory.OtherDefs.DM.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** ** Displayed category induced by a display map category

The total category associated to this displayed category is going to be isomorphic to
the subcategory of the arrow category where objects are display maps 
(instead of all morphisms) 

*)

(* TODO: we could define the concept of a full displayed subcategory 
   The predicate on objects here would be induced by the predicate [H : DM]
   on arrows of [C].
*)

Section DM_Disp.

Context {CC:category}.

Section Displayed_Cat_of_Class_of_Maps.
(* We separate this out from the fibrational part since it has a weaker hypothesis: it just needs a class of maps, no closure under pullback required. *)

Context  (D : dm_sub_struct CC).

Definition DM_disp_ob_mor : disp_cat_ob_mor CC.
Proof.
  exists (fun Γ => DM_over D Γ).
  simpl; intros Γ Δ p q f. 
  exact (∑ ff : ob_from_DM_over p --> ob_from_DM_over q,
           ff ;; q = p ;; f).
Defined.

(* TODO: consider implicit args of [disp_cat_id_comp]. *)
Definition DM_disp_id_comp : disp_cat_id_comp _ DM_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    exists (identity _ ).
    abstract (
        etrans; [apply id_left |];
        apply pathsinv0, id_right ).
  - simpl; intros Γ Γ' Γ'' f g p p' p'' ff gg.
    exists (pr1 ff ;; pr1 gg).
    abstract (
        etrans; [eapply pathsinv0, assoc |];
        etrans; [apply maponpaths, (pr2 gg) |];
        etrans; [eapply assoc |];
        etrans; [apply maponpaths_2, (pr2 ff)|];
        eapply pathsinv0, assoc).
Defined.

Definition DM_disp_data : disp_cat_data CC
  := (DM_disp_ob_mor ,, DM_disp_id_comp).

Lemma DM_disp_axioms : disp_cat_axioms CC DM_disp_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  - (* id_left_disp *) 
    apply subtypeEquality.
    { intro. apply homset_property. }
    etrans. apply id_left.
    apply pathsinv0.
    etrans. refine (pr1_transportf (CC⟦_,_⟧) _ _ _ _ _ _ ).
    use transportf_const.
  - (* id_right_disp *) 
    apply subtypeEquality.
    { intro. apply homset_property. }
    etrans. apply id_right.
    apply pathsinv0.
    etrans. refine (pr1_transportf (CC⟦_,_⟧) _ _ _ _ _ _ ).
    use transportf_const.
  - (* assoc_disp *) 
    apply subtypeEquality.
    { intro. apply homset_property. }
    etrans. apply assoc.
    apply pathsinv0.
    etrans. unfold mor_disp.
    refine (pr1_transportf (CC⟦_,_⟧) _ _ _ _ _ _ ).
    use transportf_const.
  - (* homsets_disp *)
    apply (isofhleveltotal2 2).
    + apply homset_property.
    + intro. apply isasetaprop. apply homset_property.
Qed.

Definition DM_disp : disp_cat CC
  := (DM_disp_data ,, DM_disp_axioms).

(* TODO: check what naming conventions suggest for this. *)
(* TODO: once [DM_disp] is defined as a full subcat of [cod_disp], this should be from [pullback_is_cartesian_in_cod_disp] together with lemma about cartesianness in full subcats. *)
Definition pullback_is_cartesian
    { Γ Γ' : CC } {f : Γ' --> Γ}
    {p : DM_disp Γ} {p' : DM_disp Γ'} (ff : p' -->[f] p)
  : (isPullback _ _ _ _ (pr2 ff)) -> is_cartesian ff.
Proof.
  intros Hpb Δ g q hh.
  eapply iscontrweqf.
  Focus 2. { 
    use Hpb.
    + exact (ob_from_DM_over q).
    + exact (pr1 hh).
    + simpl in q. refine (q ;; g).
    + etrans. apply (pr2 hh). apply assoc.
  } Unfocus.
  eapply weqcomp.
  Focus 2. apply weqtotal2asstol.
  apply weq_subtypes_iff.
  - intro. apply isapropdirprod; apply homset_property.
  - intro. apply (isofhleveltotal2 1). 
    + apply homset_property.
    + intros. apply homsets_disp.
  - intros gg; split; intros H.
    + exists (pr2 H).
      apply subtypeEquality.
        intro; apply homset_property.
      exact (pr1 H).
    + split.
      * exact (maponpaths pr1 (pr2 H)).
      * exact (pr1 H).
Qed.

End Displayed_Cat_of_Class_of_Maps.

(* Even for a fibration, we don’t need a full displayed cat structure: just that we have pullbacks, not the closure under iso or the fact that the [DM] predicate is a prop. 

TODO: maybe factor out this dependency — name the separate conditions on classes of maps, and state just the hypotheses as needed. *)

Context (D : dm_sub_pb CC).

Lemma is_fibration_DM_disp : cleaving (DM_disp D).
Proof.
  intros Γ Γ' f p.
  exists (pb_DM_over_of_DM_over p f).
  use tpair.
  + use tpair.
    * use (@pb_mor_of_mor _ D).
    * apply sqr_comm_of_dm_sub_pb.
  + apply pullback_is_cartesian.
    apply isPullback_of_dm_sub_pb.
    apply homset_property.
Defined.

End DM_Disp.

