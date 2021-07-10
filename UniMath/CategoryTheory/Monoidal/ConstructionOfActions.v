(**
  Construction of actions, over monoidal categories:
  - the monoidal category acting on itself
  - lifting an action from the target of a strong monoidal functor to its source

  These modularize the construction of the action induced by a strong monoidal functor U, see [U_action].

  Author: Ralph Matthes 2021. However, the code is to a good extent copied from the construction of [U_action].
**)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
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
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Local Definition α' := monoidal_precat_associator Mon_V.
Local Definition λ' := monoidal_precat_left_unitor Mon_V.
Local Definition ρ' := monoidal_precat_right_unitor Mon_V.

Definition action_on_itself: action Mon_V.
Proof.
  exists V.
  exists tensor.
  exists ρ'.
  exists α'.
  apply monoidal_precat_eq.
Defined.

Section Action_Lifting_Through_Strong_Monoidal_Functor.

Context {Mon_A : monoidal_precat}.

Local Definition A := monoidal_precat_precat Mon_A.
Local Definition I_A := monoidal_precat_unit Mon_A.
Local Definition tensor_A := monoidal_precat_tensor Mon_A.
Notation "X ⊗_A Y" := (tensor_A (X , Y)) (at level 31).
Notation "f #⊗_A g" := (#tensor_A (f #, g)) (at level 31).
Local Definition α_A := monoidal_precat_associator Mon_A.
Local Definition λ_A := monoidal_precat_left_unitor Mon_A.
Local Definition ρ_A := monoidal_precat_right_unitor Mon_A.
Local Definition triangle_eq_A := pr1 (monoidal_precat_eq Mon_A).
Local Definition pentagon_eq_A := pr2 (monoidal_precat_eq Mon_A).


Context (U : strong_monoidal_functor Mon_V Mon_A).
Local Definition ϵ := pr1 (pr2 (pr1 U)).
Local Definition ϵ_U_is_z_iso := pr1 (pr2 U).
Local Definition ϵ_inv := inv_from_z_iso (make_z_iso _ _ ϵ_U_is_z_iso).
Local Definition μ := pr1 (pr2 (pr2 (pr1 U))).
Local Definition unitality_U := pr2 (pr2 (pr2 (pr2 (pr1 U)))).
Local Definition assoc_U := pr1 (pr2 (pr2 (pr2 (pr1 U)))).

Context (actA : action Mon_A).

Local Definition C : precategory := pr1 actA.
Local Definition odotA := pr12 actA.
Local Definition ρA : action_right_unitor Mon_A odotA := pr122 actA.
Local Definition αA : action_convertor Mon_A odotA := pr1(pr222 actA).

Definition lifted_odot : C ⊠ V ⟶ C :=
  functor_composite (pair_functor (functor_identity _) (pr11 U)) odotA.

Definition lifted_action_right_unitor_nat_trans:
  odot_I_functor Mon_V lifted_odot ⟹ functor_identity C.
Proof.
  cbn.
  refine (nat_trans_comp _ _ _ _  (pr1 ρA)).
  set (aux := nat_trans_from_functor_fix_snd_morphism_arg _ _ _ odotA _ _ ϵ_inv).
  use tpair.
  - intro a.
    apply (pr1 aux a).
  - abstract
      (cbn; red ;
       intros a a' f ;
       cbn ;
       rewrite functor_id ;
       exact (pr2 aux a a' f)).
Defined.

Definition lifted_action_right_unitor: action_right_unitor Mon_V lifted_odot.
Proof.
  exists lifted_action_right_unitor_nat_trans.
  intro.
  cbn.
  use is_z_iso_comp_of_is_z_isos.
  2: { exact (pr2 ρA c). }
  - use is_z_iso_odot_z_iso.
    + exact (identity_is_z_iso _ ).
    + apply (is_z_iso_inv_from_z_iso _ _ (make_z_iso _ _ ϵ_U_is_z_iso)).
Defined.
Definition lifted_action_convertor_nat_trans:
  odot_x_odot_y_functor _ lifted_odot ⟹ odot_x_otimes_y_functor _ lifted_odot.
Proof.
  apply (nat_trans_comp _ _ _ (pre_whisker (pair_functor (pair_functor (functor_identity _) U) U) (pr1 αA))).
  exact (pre_whisker (precategory_binproduct_unassoc _ _ _) (post_whisker_fst_param μ odotA)).
Defined.

Definition lifted_action_convertor: action_convertor Mon_V lifted_odot.
Proof.
  exists lifted_action_convertor_nat_trans.
  intro x.
  pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
  use is_z_iso_comp_of_is_z_isos.
  - exact (pr2 αA ((k, U k'), U k'')).
  - use is_z_iso_odot_z_iso.
    + use identity_is_z_iso.
    + exact (pr2 (pr2 U) (k', k'')).
Defined.

Lemma lifted_action_tlaw : action_triangle_eq (A := C) Mon_V
        lifted_odot lifted_action_right_unitor lifted_action_convertor.
Proof.
  red.
  intros.
  cbn.
  unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
  unfold nat_trans_data_post_whisker_fst_param.
  simpl.
  unfold make_dirprod.
  rewrite functor_id.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply pathsinv0.
  etrans.
  { rewrite assoc'. apply maponpaths. apply pathsinv0. apply functor_comp. }
  unfold compose at 2. simpl. unfold make_dirprod. rewrite id_left.
  rewrite <- (id_left (id (pr11 U) x)).
  apply pathsinv0.
  intermediate_path (# odotA ((# odotA (id a #, ϵ_inv)) #, id U x) · # odotA (ρA a #, id U x)).
  { rewrite <- functor_comp.
    apply idpath. }
  pose (f := # odotA (# odotA (id a #, ϵ) #, id U x)).
  apply (pre_comp_with_z_iso_is_inj'(f:=f)).
  { use is_z_iso_odot_z_iso.
    - use is_z_iso_odot_z_iso.
      + exact (identity_is_z_iso _).
      + exact ϵ_U_is_z_iso.
    - exact (identity_is_z_iso _ ).
  }
  rewrite assoc.
  intermediate_path (# odotA (ρA a #, id U x)).
  { apply pathsinv0. etrans.
    - apply (!(id_left _)).
    - apply cancel_postcomposition.
      unfold f.
      rewrite <- functor_comp.
      apply pathsinv0. apply functor_id_id.
      apply pathsdirprod; simpl.
      + etrans.
        * apply pathsinv0. apply functor_comp.
        * apply functor_id_id.
          apply pathsdirprod; simpl.
          -- apply id_left.
          -- apply pathsinv0. apply z_iso_inv_on_left.
             rewrite id_left. apply idpath.
      + apply id_left.
  }
  (* UniMath.MoreFoundations.Tactics.show_id_type.
     unfold functor_fix_snd_arg_ob in TYPE. *)
  rewrite assoc.
  apply pathsinv0. etrans.
  { apply cancel_postcomposition.
    apply (nat_trans_ax (pr1 αA) ((a, I_A), U x) ((a, U I), U x) (make_dirprod (make_dirprod (id a) ϵ) (id U x))). }
  simpl.
  etrans.
  { rewrite assoc'. apply maponpaths. apply pathsinv0.
    apply functor_comp. }
  unfold compose at 2. simpl. unfold make_dirprod. rewrite id_left.
  (* UniMath.MoreFoundations.Tactics.show_id_type.
     unfold functor_fix_snd_arg_ob in TYPE. *)
  rewrite assoc.
  etrans.
  - apply maponpaths.
    eapply (maponpaths (fun u: pr1 Mon_A ⟦I_A ⊗_A (U x), U x⟧ => # odotA (id a #, u))).
    apply pathsinv0.
    apply (pr1 (unitality_U x)).
  - fold λ_A.
    (* UniMath.MoreFoundations.Tactics.show_id_type.
       unfold functor_fix_snd_arg_ob in TYPE. *)
    apply pathsinv0.
    apply (pr12(pr222 actA)).
Defined.

Lemma lifted_action_plaw : action_pentagon_eq (A := C) Mon_V
                             lifted_odot lifted_action_convertor.
Proof.
  red.
  intros.
  cbn.
  unfold nat_trans_data_post_whisker_fst_param.
  unfold ob1, ob2.
  cbn.
  rewrite functor_id.
  apply pathsinv0. etrans.
  { repeat rewrite assoc'.
    apply maponpaths.
    apply maponpaths.
    apply pathsinv0.
    apply functor_comp.
  }
  unfold compose at 4. cbn. unfold make_dirprod.
  rewrite id_left.
  etrans.
  { rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite <- (id_left (id (pr11 U) z)).
    intermediate_path (# odotA ((αA ((a, U x), U y) #, id U z) · (# odotA (id a #, μ (x, y)) #, id U z))).
    - apply idpath.
    - apply functor_comp.
  }
  etrans.
  { apply cancel_postcomposition.
    rewrite assoc'.
    apply maponpaths.
    apply (nat_trans_ax (pr1 αA) ((a, U x ⊗_A U y), U z) ((a, U (x ⊗ y)), U z) (make_dirprod (make_dirprod (id a) (μ (x, y))) (id U z))).
  }
  etrans.
  { unfold assoc_right. cbn.
    rewrite assoc'.
    apply maponpaths.
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0.
    apply functor_comp.
  }
  unfold compose at 3. cbn. unfold make_dirprod.
  rewrite id_left.
  etrans.
  { do 2 apply maponpaths.
    rewrite assoc.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    eapply (maponpaths (fun u: A ⟦(U x ⊗_A U y) ⊗_A U z, U (x ⊗ (y ⊗ z))⟧ => # odotA (id a #, u))).
    apply assoc_U.
  }
  fold αA. fold μ.
  etrans.
  { rewrite assoc. apply maponpaths.
    rewrite assoc'.
    rewrite <- (id_left (id a)).
    intermediate_path (# odotA ((id a #, α_A ((U x, U y), U z)) · (id a #, # tensor_A (id U x #, μ (y, z)) · μ (x, y ⊗ z)))).
    2: { apply functor_comp. }
    apply idpath.
  }
  etrans.
  { do 2 apply maponpaths.
    rewrite <- (id_left (id a)).
    intermediate_path (# odotA ((id a #, # tensor_A (id pr1 (pr1 U) x #, μ (y, z))) · (id a #, μ (x, y ⊗ z)))).
    2: { apply functor_comp. }
    apply idpath.
  }
  repeat rewrite assoc.
  apply cancel_postcomposition.
  etrans.
  { apply cancel_postcomposition.
    apply pathsinv0.
    apply (pr22(pr222 actA)).
  }
  fold odotA.
  change (αA ((odotA (a, U x), U y), U z) · αA ((a, U x), tensor_A (U y, U z))
  · # odotA (id a #, # tensor_A (id U x #, μ (y, z))) =
  αA ((odotA (a , U x), U y), U z) · # odotA (id (odotA (a , U x)) #, μ (y, z))
      · αA ((a, U x), U (y ⊗ z))).
  repeat rewrite assoc'.
  apply maponpaths.
  etrans.
  { apply pathsinv0.
    apply (nat_trans_ax (pr1 αA) ((a, U x), U y ⊗_A U z) ((a, U x), U (y ⊗ z)) (make_dirprod (make_dirprod (id a) (id U x)) (μ (y, z)))).
  }
  cbn. unfold make_dirprod.
  apply cancel_postcomposition.
  (* present the identity in the binary product of categories *)
  change (# odotA (# odotA (id (a, U x)) #, μ (y, z)) = # odotA (id (odotA (a, U x)) #, μ (y, z))).
  rewrite functor_id.
  apply idpath.
Defined.

Definition lifted_action: action Mon_V.
Proof.
  exists C.
  exists lifted_odot.
  exists lifted_action_right_unitor.
  exists lifted_action_convertor.
  split.
  - exact lifted_action_tlaw.
  - exact lifted_action_plaw.
Defined.

End Action_Lifting_Through_Strong_Monoidal_Functor.

End A.
(*
Section Strong_Monoidal_Functor_Action_Reloaded.

  Context {Mon_V Mon_A : monoidal_precat}.
  Context (U : strong_monoidal_functor Mon_V Mon_A).

  Definition U_action_alt : action Mon_V := lifted_action Mon_V U (action_on_itself Mon_A).

(* the two actions are even convertible - thanks to definedness of the proofs of the equations *)
  (*
  Lemma U_action_alt_ok: U_action_alt = U_action _ U.
  Proof.
    do 2 (use total2_paths_f ; [ apply idpath | ] ; cbn).
  Qed.
   *)

(* the following lemmas work even when the equational proofs are opaque *)
  Lemma U_action_alt_ok1: pr1 U_action_alt = pr1(U_action _ U).
  Proof.
    apply idpath.
  Qed.

  Lemma U_action_alt_ok2: pr1(pr2 U_action_alt) = pr1(pr2(U_action _ U)).
  Proof.
    apply idpath.
  Qed.

  Lemma U_action_alt_ok3: pr1(pr22 U_action_alt) = pr1(pr22(U_action _ U)).
  Proof.
    apply idpath.
  Qed.

  Lemma U_action_alt_ok4: pr1(pr222 U_action_alt) = pr1(pr222(U_action _ U)).
  Proof.
    apply idpath.
  Qed.

End Strong_Monoidal_Functor_Action_Reloaded.
 *)
