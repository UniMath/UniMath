(**
  Definition of tensorial strengths between actions over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.

  To distinguish this from less general approaches, we will speak of action-based strength.

  Added by Ralph Matthes in 2021: relative strength of Ahrens and Matthes defined and shown to be an instance of action-based strength
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
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

Context {A A': precategory}.
Context (actn : action Mon_V A)(actn' : action Mon_V A').

Local Definition odot := pr1 actn.
Local Definition ϱ := pr12 actn.
Local Definition χ := pr122 actn.
Local Definition odot' := pr1 actn'.
Local Definition ϱ' := pr12 actn'.

Local Definition χ' := pr122 actn'.

Section ActionBasedStrengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition actionbased_strength_dom : A ⊠ V ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) odot'.

Lemma actionbased_strength_dom_ok: functor_on_objects actionbased_strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition actionbased_strength_codom : A ⊠ V ⟶ A' :=
  functor_composite odot F.

Lemma actionbased_strength_codom_ok: functor_on_objects actionbased_strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.

Definition actionbased_strength_nat : UU := nat_trans actionbased_strength_dom actionbased_strength_codom.

Definition actionbased_strength_nat_funclass (ϛ : actionbased_strength_nat):
  ∏ x : ob (A ⊠ V), actionbased_strength_dom x --> actionbased_strength_codom x
  := pr1 ϛ.
Coercion actionbased_strength_nat_funclass : actionbased_strength_nat >-> Funclass.

Definition actionbased_strength_triangle_eq (ϛ : actionbased_strength_nat) :=
  ∏ (a : A), (ϛ (a, I)) · (#F (ϱ a)) = ϱ' (F a).

Definition actionbased_strength_pentagon_eq (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  (χ' ((F a, x), y)) · ϛ (a, x ⊗ y) =
  (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)) · (#F (χ ((a, x), y))).

(** the original notion in Fiore's LICS'08 paper *)
Definition actionbased_strength_pentagon_eq_variant1 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  ϛ (a, x ⊗ y) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)) · (#F (χ ((a, x), y))).

(** the notion that fits with the definition of relative strength in the TYPES'15 post-proceedings paper by Ahrens and Matthes *)
Definition actionbased_strength_pentagon_eq_variant2 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  ϛ (a, x ⊗ y) · (#F (nat_z_iso_to_trans_inv χ ((a, x), y))) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)).

(** as expected, the notions are logically equivalent *)
Lemma actionbased_strength_pentagon_eq_tovariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a x y.
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

Lemma actionbased_strength_pentagon_eq_fromvariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq ϛ.
Proof.
  intros Heq a x y.
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

Lemma actionbased_strength_pentagon_eq_variant1variant2 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq_variant2 ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  etrans.
  { unfold nat_z_iso_to_trans_inv.  cbn.
    apply maponpaths.
    apply pathsinv0.
    apply functor_on_inv_from_z_iso'.
  }
  apply pathsinv0.
  apply (z_iso_inv_on_left _ _ _ _ (make_z_iso (# F (χ ((a, x), y)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))).
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_variant2variant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant2 ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_right _ _ _ _ (make_z_iso (# F (χ ((a, x), y)))
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

Lemma isaprop_actionbased_strength_triangle_eq (ϛ : actionbased_strength_nat) (hsA' : has_homsets A') : isaprop (actionbased_strength_triangle_eq ϛ).
Proof.
  apply impred; intros a.
  apply hsA'.
Qed.

Lemma isaprop_actionbased_strength_pentagon_eq (ϛ : actionbased_strength_nat) (hsA' : has_homsets A') : isaprop (actionbased_strength_pentagon_eq ϛ).
Proof.
  apply impred; intros a.
  apply impred; intros v.
  apply impred; intros w.
  apply hsA'.
Qed.

End ActionBasedStrengths_Natural_Transformation.

Definition actionbased_strength (F : A ⟶ A'): UU := ∑ (ϛ : actionbased_strength_nat F),
   (actionbased_strength_triangle_eq F ϛ) × (actionbased_strength_pentagon_eq F ϛ).

Lemma actionbased_strength_eq (hsA' : has_homsets A') {F : A ⟶ A'} (sη sη': actionbased_strength F) :
  pr1 sη = pr1 sη' -> sη = sη'.
Proof.
  intro Heq.
  apply subtypePath; trivial.
  intro ϛ. apply isapropdirprod.
  + apply isaprop_actionbased_strength_triangle_eq, hsA'.
  + apply isaprop_actionbased_strength_pentagon_eq, hsA'.
Qed.

End ActionBasedStrengths_Definition.

Definition actionbased_strong_functor {A A' : precategory} (actn : action Mon_V A)(actn' : action Mon_V A') : UU
  := ∑ (F : A ⟶ A'), actionbased_strength actn actn' F.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength : functor V V → UU:= actionbased_strength (tensorial_action Mon_V) (tensorial_action Mon_V).

End A.

Section B.
(** following the TYPES'15 post-proceedings paper by Ahrens and Matthes - will be identified as an instance of the previous *)

  Context {Mon_W Mon_V : monoidal_precat}.

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

  Definition rel_strength_nat_funclass (ϛ : rel_strength_nat):
  ∏ x : ob (W ⊠ VV), rel_strength_dom x --> rel_strength_codom x
  := pr1 ϛ.
  Coercion rel_strength_nat_funclass : rel_strength_nat >-> Funclass.

  (** the following looks like a pentagon but is of the nature of a triangle equation *)
  Definition rel_strength_pentagon_eq (ϛ : rel_strength_nat) :=
    ∏ (v : VV), (ϛ (E, v)) · (#F (phiIinv #⊗V (identity v))) · (#F (lambda v))  =
               (phiIinv #⊗V (identity (F v))) · (lambda (F v)).

  (** the following looks like a rectangle in the paper but is of the nature of a pentagon equation *)
  Definition rel_strength_rectangle_eq (ϛ : rel_strength_nat): UU := ∏ (w w' : W), ∏ (v : VV),
  (ϛ (w •W w', v) ) · (#F (phiinv (w, w') #⊗V (identity v))) · (#F (alpha ((U w, U w'), v))) =
  (phiinv (w, w') #⊗V (identity (F v))) · (alpha ((U w, U w'), F v)) ·
                                        ((identity (U w)) #⊗V ϛ (w', v)) · (ϛ (w, U w' ⊗V v)).

End RelativeStrengths_Natural_Transformation.

Definition rel_strength (F : VV ⟶ VV): UU :=
  ∑ (ϛ : rel_strength_nat F), (rel_strength_pentagon_eq F ϛ) × (rel_strength_rectangle_eq F ϛ).

Section RelativeStrength_Is_An_ActionBasedStrength.

  Context (F: functor VV VV) (str: rel_strength F).

  Local Definition ϛ := pr1 str.
  Local Definition pentagon := pr1 (pr2 str).
  Local Definition rectangle := pr2 (pr2 str).

  Local Definition Mon_W' := swapping_of_monoidal_precat Mon_W.
  Local Definition timesW' := monoidal_precat_tensor Mon_W'.
  Local Definition Mon_V' := swapping_of_monoidal_precat Mon_V.
  Local Definition timesV' := monoidal_precat_tensor Mon_V'.

  Local Definition U' := swapping_of_strong_monoidal_functor U: strong_monoidal_functor Mon_W' Mon_V'.
  Local Definition phiinv' := pre_whisker binswap_pair_functor phiinv.

  Local Definition UAct := U_action Mon_W' U': action Mon_W' ( monoidal_precat_precat Mon_V').

  Local Definition ϛ' := pre_whisker binswap_pair_functor ϛ.

Definition actionbased_strength_from_relative_strength: actionbased_strength Mon_W' UAct UAct F.
Proof.
  exists ϛ'.
  split.
  - red.
    cbn.
    intro v.
    change (ϛ (E, v) · # F (# timesV (phiIinv #, id v) · lambda v) =
            # timesV (phiIinv #, id F v) · lambda (F v)).
    rewrite <- pentagon.
    rewrite assoc'. rewrite functor_comp.
    fold ϛ.
    apply idpath.
  - cbn.
    apply actionbased_strength_pentagon_eq_fromvariant1.
    apply actionbased_strength_pentagon_eq_variant2variant1.
    red.
    intros v w' w.
    unfold ϛ', Mon_W', Mon_V', U', odot'.
    cbn.
    unfold is_z_isomorphism_mor, pre_whisker_on_nat_z_iso.
    cbn.
    assert (Hyp := rectangle w w' v).
    fold ϛ in Hyp.
    fold timesV.
    fold timesW.
    fold alpha.
    change (ϛ (timesW (w, w'), v)
  · # F (# timesV (pr1 (pr2 (pr2 U) (w, w')) #, id v) · alpha ((U w, U w'), v)) =
  # timesV (pr1 (pr2 (pr2 U) (w, w')) #, id F v) · alpha ((U w, U w'), F v)
  · # timesV (# (pr1 (pr1 U)) (id w) #, ϛ (w', v)) · ϛ (w, timesV (U w', v))).
    rewrite functor_id.
    rewrite functor_comp.
    rewrite assoc.
    exact Hyp.
Defined.

End RelativeStrength_Is_An_ActionBasedStrength.

Section ActionBasedStrength_Instantiates_To_RelativeStrength.

  Context (F: functor VV VV) (ab_str: actionbased_strength Mon_W' UAct UAct F).

  Local Definition θ := pr1 ab_str.
  Local Definition θ' : rel_strength_nat F := pre_whisker binswap_pair_functor θ.
  Local Definition triangle_eq := pr1 (pr2 ab_str).
  Local Definition pentagon_eq := pr2 (pr2 ab_str).

  Definition relative_strength_from_actionbased_strength: rel_strength F.
  Proof.
    exists θ'.
    split.
    - red.
      cbn.
      intro v.
      assert (Hyp := triangle_eq v).
      cbn in Hyp. fold θ E timesV in Hyp.
      etrans.
      2: exact Hyp.
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      apply functor_comp.
    - red. cbn. intros w w' v.
      assert (Hyp := actionbased_strength_pentagon_eq_variant1variant2 _ _ _ _ θ
                      (actionbased_strength_pentagon_eq_tovariant1 _ _ _ _ θ pentagon_eq) v w' w).
      cbn in Hyp.
      unfold is_z_isomorphism_mor, pre_whisker_on_nat_z_iso in Hyp.
      cbn in Hyp.
      unfold is_z_isomorphism_mor.
      rewrite functor_id in Hyp.
      rewrite functor_comp in Hyp.
      rewrite assoc in Hyp.
      exact Hyp.
  Defined.

End ActionBasedStrength_Instantiates_To_RelativeStrength.

End B.
