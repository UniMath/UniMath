
(** * Displayed category from a category with display maps

Definition of the displayed category of display maps over a category [C]

Given a category with display maps [C], we define a displayed 
category over [C]. Objects over [c:C] are display maps into [c].

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
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

Context {CC:Precategory}.

Section Displayed_Cat_of_Class_of_Maps.
(* We separate this out from the fibrational part since it has a weaker hypothesis: it just needs a class of maps, no closure under pullback required. *)

Context  (D : dm_sub_struct CC).

Definition DM_disp_ob_mor : disp_precat_ob_mor CC.
Proof.
  exists (fun Γ => DM_over D Γ).
  simpl; intros Γ Δ p q f. 
  exact (Σ ff : ob_from_DM_over p --> ob_from_DM_over q,
           p ;; f = ff ;; q).
  (* TODO: maybe direction of this equality? *)
Defined.

(* TODO: consider implicit args of [disp_precat_id_comp]. *)
Definition DM_disp_id_comp : disp_precat_id_comp _ DM_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    exists (identity _ ).
    abstract (
        etrans; [apply id_right |];
        apply pathsinv0, id_left ).
  - simpl; intros Γ Γ' Γ'' f g p p' p'' ff gg.
    exists (pr1 ff ;; pr1 gg).
    abstract (
        etrans; [apply assoc |];
        etrans; [apply maponpaths_2, (pr2 ff) |];
        etrans; [eapply pathsinv0, assoc |];
        etrans; [apply maponpaths, (pr2 gg)|];
        apply assoc).
Defined.

Definition DM_disp_data : disp_precat_data CC
  := (DM_disp_ob_mor ,, DM_disp_id_comp).

Lemma DM_disp_axioms : disp_precat_axioms CC DM_disp_data.
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

Definition DM_disp : disp_precat CC
  := (DM_disp_data ,, DM_disp_axioms).

End Displayed_Cat_of_Class_of_Maps.

(* Even for a fibration, we don’t need a full displayed cat structure: just that we have pullbacks, not the closure under iso or the fact that the [DM] predicate is a prop. *)

Context (D : dm_sub_pb CC).

Lemma is_fibration_DM_disp : is_fibration (DM_disp D).
Proof.
  intros Γ Γ' f p.
  exists (pb_DM_over_of_DM_over p f).
  use tpair.
  + use tpair. 
    * use (@pb_mor_of_mor _ D).
    * abstract (cbn; apply pathsinv0; use (@sqr_comm_of_dm_sub_pb _ D) ).
  + (* TODO: abstract as pair of lemmas:
      (a) a cartesian [mor_disp] is still cartesian in a full displayed subcat;
      (b) a pullback square is cartesian in the codomain fibration. *)
    cbn. 
    intros c'' g0 d'' hh.
    destruct d'' as [[e k] H2]. cbn in *.
    destruct hh as [h H3]. cbn in *.
    { use unique_exists.
      - use tpair.
        use PullbackArrow.
        + exact h.
        + exact (k ;; g0).
        + abstract (etrans; [apply (!H3) |]; apply assoc ) .
        + abstract (
              cbn;
              match goal with [|- _ = PullbackArrow ?PP _ _ _ _ ;; _    ] => 
                              set (P := PP) end;
              apply pathsinv0;
              apply (PullbackArrow_PullbackPr2 P)
            ).
      - cbn.
        apply subtypeEquality.
        { intro.  apply homset_property. }
        cbn.
        match goal with [|- PullbackArrow ?PP _ _ _ _  ;; _ = _ ] =>
                              set (P := PP) end.
        apply (PullbackArrow_PullbackPr1 P).
      - intro y0.
        simpl.
        admit.
      - cbn.
        intros y0 H5.
        apply subtypeEquality.
        { intro. apply homset_property. }
        destruct y0 as [p' H6]. cbn in *.
        use PullbackArrowUnique.
        assert (H7 := maponpaths pr1 H5); cbn in H7.
        apply H7.
        apply (!H6).
Abort.

End DM_Disp.

