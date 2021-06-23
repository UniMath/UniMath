(**
  Definition of tensorial strengths between actions over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.

  To distinguish this from less general approaches, we will speak of action-based strength.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.

Local Open Scope cat.

Section A.

Context (Mon_V : monoidal_precat).

Local Definition V := monoidal_precat_precat Mon_V.
Local Definition I := monoidal_precat_unit Mon_V.
Local Definition tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Section ActionBasedStrengths_Definition.

Context (actn actn' : action Mon_V).

Local Definition A := pr1 actn.
Local Definition odot := pr1 (pr2 actn).
Local Definition ϱ := pr1 (pr2 (pr2 actn)).
Local Definition χ := pr1 (pr2 (pr2 (pr2 actn))).
Local Definition A' := pr1 actn'.
Local Definition odot' := pr1 (pr2 actn').
Local Definition ϱ' := pr1 (pr2 (pr2 actn')).

Local Definition χ' := pr1 (pr2 (pr2 (pr2 actn'))).

Section ActionBasedStrengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition strength_dom : A ⊠ V ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) odot'.

Lemma strength_dom_ok: functor_on_objects strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_codom : A ⊠ V ⟶ A' :=
  functor_composite odot F.

Lemma strength_codom_ok: functor_on_objects strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_nat : UU := nat_trans strength_dom strength_codom.

Definition strength_triangle_eq (ϛ : strength_nat) :=
  ∏ (a : A), (pr1 ϛ (a, I)) · (#F (pr1 ϱ a)) = pr1 ϱ' (F a).

Definition strength_pentagon_eq (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y) =
  (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

(** the original notion in Fiore's LICS'08 paper *)
Definition strength_pentagon_eq_variant1 (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  pr1 ϛ (a, x ⊗ y) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

(** the notion that fits with the definition of relative strength in the TYPES'15 post-proceedings paper by Ahrens and Matthes *)
Definition strength_pentagon_eq_variant2 (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  pr1 ϛ (a, x ⊗ y) · (#F (nat_z_iso_to_trans_inv χ ((a, x), y))) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)).

Lemma strength_pentagon_eq_tovariant1 (ϛ : strength_nat): strength_pentagon_eq ϛ -> strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq ? ? ?.
  red in Heq.
  apply pathsinv0.
  unfold nat_z_iso_to_trans_inv; cbn.
  unfold is_z_isomorphism_mor.
  do 2 rewrite <- assoc.
  apply (z_iso_inv_on_right _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, x), y)))).
  apply pathsinv0.
  rewrite assoc.
  cbn.
  apply Heq.
Qed.

Lemma strength_pentagon_eq_fromvariant1 (ϛ : strength_nat): strength_pentagon_eq_variant1 ϛ -> strength_pentagon_eq ϛ.
Proof.
  intros Heq ? ? ?.
  red in Heq.
  unfold nat_z_iso_to_trans_inv in Heq; cbn in Heq.
  unfold is_z_isomorphism_mor in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, x), y)))).
  cbn.
  apply pathsinv0.
  do 2 rewrite assoc.
  apply Heq.
Qed.

Lemma strength_pentagon_eq_variant1variant2 (ϛ : strength_nat): strength_pentagon_eq_variant1 ϛ -> strength_pentagon_eq_variant2 ϛ.
Proof.
  intros Heq ? ? ?.
  red in Heq.
  etrans.
  { unfold nat_z_iso_to_trans_inv.  cbn.
    apply maponpaths.
    apply pathsinv0.
    apply functor_on_inv_from_z_iso'.
  }
  apply pathsinv0.
  apply (z_iso_inv_on_left _ _ _ _ (make_z_iso (# F (pr1 χ ((a, x), y)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))).
  apply Heq.
Qed.

Lemma strength_pentagon_eq_variant2variant1 (ϛ : strength_nat): strength_pentagon_eq_variant2 ϛ -> strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq ? ? ?.
  red in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_right _ _ _ _ (make_z_iso (# F (pr1 χ ((a, x), y)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))).
  etrans.
  { apply pathsinv0.
    apply Heq. }
  clear Heq.
  apply maponpaths.
  apply pathsinv0.
  apply (functor_on_inv_from_z_iso' _ (pr2 χ ((a, x), y))).
Qed.

End ActionBasedStrengths_Natural_Transformation.

Definition strength (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

(*
Definition strength_variant1 (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq_variant1 F ϛ).

Definition strength_variant2 (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq_variant2 F ϛ).
*)

End ActionBasedStrengths_Definition.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength := strength (tensorial_action Mon_V) (tensorial_action Mon_V).

End A.

Section B.
(** following the TYPES'15 post-proceedings paper by Ahrens and Matthes - will be identified as an instance of the previous *)

  Context (Mon_W Mon_V : monoidal_precat).

  Local Definition VV := monoidal_precat_precat Mon_V.
  Local Definition timesV := monoidal_precat_tensor Mon_V.
  Local Definition II := monoidal_precat_unit Mon_V.
  Local Definition lambda := monoidal_precat_left_unitor Mon_V.
  Local Definition alpha := monoidal_precat_associator Mon_V.

  Local Definition W := monoidal_precat_precat Mon_W.
  Local Definition timesW := monoidal_precat_tensor Mon_W.
  Local Definition E := monoidal_precat_unit Mon_W.

  Context (U:strong_monoidal_functor Mon_W Mon_V).
  Local Definition phiI := pr1 (pr2 (pr1 U)).
  Local Definition phiIinv := inv_from_z_iso (make_z_iso phiI _ (pr1 (pr2 U))).
  Local Definition phi := pr1 (pr2 (pr2 (pr1 U))).
  Local Definition phiinv := nat_z_iso_to_trans_inv (make_nat_z_iso _ _ phi (pr2 (pr2 U))).

Section RelativeStrengths_Natural_Transformation.
  Context (F: functor VV VV).

  Notation "X ⊗V Y" := (timesV (X , Y)) (at level 31).
  Notation "X •W Y" := (timesW (X , Y)) (at level 31).

  Notation "f #⊗V g" := (#timesV (f #, g)) (at level 31).
  Notation "f #•W g" := (#timesW (f #, g)) (at level 31).

  Definition rel_strength_dom : W ⊠ VV ⟶ VV :=
    functor_composite (pair_functor U F) timesV.

  Lemma rel_strength_dom_ok: functor_on_objects rel_strength_dom = λ ax, U (ob1 ax) ⊗V  F (ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_codom : W ⊠ VV ⟶ VV :=
  functor_composite (functor_composite (pair_functor U (functor_identity _)) timesV) F.

  Lemma rel_strength_codom_ok: functor_on_objects rel_strength_codom = λ ax, F (U (ob1 ax) ⊗V ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_nat : UU := nat_trans rel_strength_dom rel_strength_codom.

  (** the following looks like a pentagon but is of the nature of a triangle equation *)
  Definition rel_strength_pentagon_eq (ϛ : rel_strength_nat) :=
    ∏ (v : VV), (pr1 ϛ (E, v)) · (#F (phiIinv #⊗V (identity v))) · (#F (pr1 lambda v))  =
               (phiIinv #⊗V (identity (F v))) · (pr1 lambda (F v)).

  (** the following looks like a rectangle in the paper but is of the nature of a pentagon equation *)
  Definition rel_strength_rectangle_eq (ϛ : rel_strength_nat): UU := ∏ (w w' : W), ∏ (v : VV),
  ( pr1 ϛ (w •W w', v) ) · (#F (phiinv (w, w') #⊗V (identity v))) · (#F (pr1 alpha ((U w, U w'), v))) =
  (phiinv (w, w') #⊗V (identity (F v))) · (pr1 alpha ((U w, U w'), F v)) ·
                                        ((identity (U w)) #⊗V pr1 ϛ (w', v)) · ( pr1 ϛ (w, U w' ⊗V v)).

(* the following was part of a desperate try to avoid z_iso
  Definition rel_strength_rectangle_eq_with_given_inverse
  (gphiinv: monoidal_functor_map_codom Mon_W Mon_V (pr1 (pr1 U))
                                       ⟹ monoidal_functor_map_dom Mon_W Mon_V (pr1 (pr1 U)))
  (ϛ : rel_strength_nat): UU := ∏ (w w' : W), ∏ (v : VV),
  ( pr1 ϛ (w •W w', v) ) · (#F (gphiinv (w, w') #⊗V (identity v))) · (#F (pr1 alpha ((U w, U w'), v))) =
  (gphiinv (w, w') #⊗V (identity (F v))) · (pr1 alpha ((U w, U w'), F v)) ·
                                        ((identity (U w)) #⊗V pr1 ϛ (w', v)) · ( pr1 ϛ (w, U w' ⊗V v)).
*)

End RelativeStrengths_Natural_Transformation.

Definition rel_strength (F : VV ⟶ VV): UU :=
  ∑ (ϛ : rel_strength_nat F), (rel_strength_pentagon_eq F ϛ) × (rel_strength_rectangle_eq F ϛ).

(* the following was part of a desperate try to avoid z_iso
Definition rel_strength_with_chosen_inverse (F : VV ⟶ VV): UU :=
  ∑ (ϛ : rel_strength_nat F), (rel_strength_pentagon_eq F ϛ) ×
      ∑ (gphiinv: monoidal_functor_map_codom Mon_W Mon_V (pr1 (pr1 U))
                                             ⟹ monoidal_functor_map_dom Mon_W Mon_V (pr1 (pr1 U))),
  (rel_strength_rectangle_eq_with_given_inverse F gphiinv ϛ).
*)


Section RelativeStrength_Is_An_ActionBasedStrength.

  Context (F: functor VV VV).
  Context (str: rel_strength F).

  Local Definition ϛ := pr1 str.
  Local Definition pentagon := pr1 (pr2 str).
  Local Definition rectangle := pr2 (pr2 str).

  Local Definition Mon_W' := swapping_of_monoidal_precat Mon_W.
  Local Definition timesW' := monoidal_precat_tensor Mon_W'.
  Local Definition Mon_V' := swapping_of_monoidal_precat Mon_V.
  Local Definition timesV' := monoidal_precat_tensor Mon_V'.

  Local Definition U' := swapping_of_strong_monoidal_functor U: strong_monoidal_functor Mon_W' Mon_V'.
  Local Definition phiinv' := pre_whisker binswap_pair_functor phiinv.

  Local Definition UAct := U_action Mon_W' Mon_V' U': action Mon_W'.

  Local Definition ϛ' := pre_whisker binswap_pair_functor ϛ.

Definition strength_from_relative_strength: strength Mon_W' UAct UAct F.
Proof.
  exists ϛ'.
  use tpair.
  - red.
    cbn.
    intro v.
    change (pr1 ϛ (E, v) · # F (# timesV (phiIinv #, id v) · pr1 lambda v) =
            # timesV (phiIinv #, id F v) · pr1 lambda (F v)).
    rewrite <- pentagon.
    rewrite assoc'. rewrite functor_comp.
    fold ϛ.
    apply idpath.
  - cbn.
    (* apply strength_pentagon_eq_fromvariant1.
    apply strength_pentagon_eq_variant2variant1. *)
    red.
    intros v w' w.
    (* massage the goal a bit - easier roads to it seem blocked - in particular, with the change command that does not terminate! *)
    (* change (U_action_χ_nat_trans Mon_W' Mon_V' U' ((F v, w'), w)
  · pr1 ϛ' (v, monoidal_precat_tensor Mon_W' (w', w)) =
  # (pr1 (pr2 UAct)) (pr1 ϛ' (v, w') #, id w) · pr1 ϛ' (pr1 (pr2 UAct) (v, w'), w)
  · # F (U_action_χ_nat_trans Mon_W' Mon_V' U' ((v, w'), w))). *)
    assert (eqaux : (pr1 (χ' Mon_W' UAct) ((F v, w'), w) = pr1 (U_action_χ Mon_W' Mon_V' U') ((F v, w'), w))) by apply idpath.
    assert (eqaux' : pr1 (U_action_χ Mon_W' Mon_V' U') ((F v, w'), w) = U_action_χ_nat_trans Mon_W' Mon_V' U' ((F v, w'), w)) by apply idpath.
    etrans. apply cancel_postcomposition.
    apply eqaux.
    etrans. apply cancel_postcomposition.
    apply eqaux'.
    assert (eqaux1 : (pr1 (χ Mon_W' UAct) ((v, w'), w) = pr1 (U_action_χ Mon_W' Mon_V' U') ((v, w'), w))) by apply idpath.
    assert (eqaux1' : pr1 (U_action_χ Mon_W' Mon_V' U') ((v, w'), w) = U_action_χ_nat_trans Mon_W' Mon_V' U' ((v, w'), w)) by apply idpath.
    apply pathsinv0.
    etrans. apply maponpaths. apply maponpaths.
    apply eqaux1.
    etrans. apply maponpaths. apply maponpaths.
    apply eqaux1'.
    apply pathsinv0.
    (* the goal is now a bit better readable *)
    unfold ϛ', Mon_W', Mon_V', U', odot'.
    simpl.
    unfold is_z_isomorphism_mor.
    unfold nat_trans_data_post_whisker_fst_param.
    simpl.
    set (Hyp := rectangle w w' v).
    fold ϛ in Hyp.
    (* the following fails
    rewrite (swapping_of_strong_monoidal_functor_on_objects U w).
    Therefore brute force: *)
    change (pr1
    (pr2 (monoidal_precat_associator Mon_V)
       ((U w, U w'), F v))
  · # (monoidal_precat_tensor Mon_V) (pr1 (pr1 (pr2 (pr2 (pr1 U)))) (w, w') #, id F v)
  · pr1 ϛ (monoidal_precat_tensor Mon_W (w, w'), v) =
  # (monoidal_precat_tensor Mon_V) (# U' (id w) #, pr1 ϛ (w', v))
  · pr1 ϛ (w, monoidal_precat_tensor Mon_V (U' w', v))
  · # F
      (pr1
         (pr2 (monoidal_precat_associator Mon_V)
            ((U w, U w'), v))
       · # (monoidal_precat_tensor Mon_V) (pr1 (pr1 (pr2 (pr2 (pr1 U)))) (w, w') #, id v))).
    fold phi.
    rewrite functor_id.
    fold alpha.
    fold timesV.
    (* one can now finally start with the mathematics *)

    (* further tinkering *)
    assert (aux1: U_action_χ_nat_trans Mon_W' Mon_V' U' ((v, w'), w) = U_action_χ_nat_trans Mon_W' Mon_V' U' ((v, w'), w)).
    { etrans. unfold U_action_χ_nat_trans. unfold nat_trans_comp. cbn beta iota delta.
      etrans. apply cancel_postcomposition. cbn.
(* inv_from_iso
    (make_iso (pr1 (monoidal_precat_associator Mon_V) ((pr1 (pr1 U) w, pr1 (pr1 U) w'), v))
       (pr2 (monoidal_precat_associator Mon_V) ((pr1 (pr1 U) w, pr1 (pr1 U) w'), v))) =

      apply idpath.

      unfold U_action_χ_nat_trans.
    unfold nat_trans_comp.

*)
(*
other approach:
    unfold ϛ'.
    unfold Mon_W'.
    unfold swapping_of_monoidal_precat.
    cbn.
    unfold U'.
*)
(* we now have to abstract away from knowledge of being iso
   U_action_χ_is_nat_iso is opaque!
    unfold swapping_of_strong_monoidal_functor. unfold swapping_of_lax_monoidal_functor.
    simpl.
 *)
Abort.

(* TO BE CONTINUED *)


End RelativeStrength_Is_An_ActionBasedStrength.

End B.
