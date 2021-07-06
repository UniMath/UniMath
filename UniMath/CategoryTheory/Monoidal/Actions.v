(**
  Generalisation of the concept of actions, over monoidal categories.

  This notion is found in G. Janelidze and G.M. Kelly: A Note on Actions of a Monoidal Category, Theory and Applications of Categories, Vol. 9, 2001, No. 4, pp 61-91.

  The presentation is based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore. It seems that the order of the arguments of the action functor has been chosen differently there.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.

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

Section Actions_Definition.

(* A ⊙ I --> A *)

Section Actions_Natural_Transformations.

Context {A : precategory} (odot : functor (precategory_binproduct A V) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition is_z_iso_odot_z_iso {X Y : A} { X' Y' : V} {f : X --> Y} {g : X' --> Y'}
           (f_is_z_iso : is_z_isomorphism f) (g_is_z_iso : is_z_isomorphism g) : is_z_isomorphism (f #⊙ g).
Proof.
  exact (functor_on_is_z_isomorphism _ (is_z_iso_binprod_z_iso f_is_z_iso g_is_z_iso)).
Defined.

Definition odot_I_functor : functor A A := functor_fix_snd_arg _ _ _ odot I.

Lemma odot_I_functor_ok: functor_on_objects odot_I_functor =
  λ a, a ⊙ I.
Proof.
  apply idpath.
Qed.

Definition action_right_unitor : UU := nat_z_iso odot_I_functor (functor_identity A).

Definition action_right_unitor_funclass (μ : action_right_unitor):
  ∏ x : ob A, odot_I_functor x -->  x
  := pr1 (nat_z_iso_to_trans μ).
Coercion action_right_unitor_funclass : action_right_unitor >-> Funclass.

Definition odot_x_odot_y_functor : (A ⊠ V) ⊠ V ⟶ A :=
  functor_composite (pair_functor odot (functor_identity _)) odot.

Lemma odot_x_odot_y_functor_ok: functor_on_objects odot_x_odot_y_functor =
  λ a, (ob1 (ob1 a) ⊙ ob2 (ob1 a)) ⊙ ob2 a.
Proof.
  apply idpath.
Qed.

Definition odot_x_otimes_y_functor : (A ⊠ V) ⊠ V ⟶ A :=
  functor_composite (precategory_binproduct_unassoc _ _ _)
                    (functor_composite (pair_functor (functor_identity _) tensor) odot).

Lemma odot_x_otimes_y_functor_ok: functor_on_objects odot_x_otimes_y_functor =
  λ a, ob1 (ob1 a) ⊙ (ob2 (ob1 a) ⊗ ob2 a).
Proof.
  apply idpath.
Qed.

Definition action_convertor : UU := nat_z_iso odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_convertor_funclass (χ : action_convertor):
  ∏ x : ob ((A ⊠ V) ⊠ V), odot_x_odot_y_functor x --> odot_x_otimes_y_functor x
  := pr1 (nat_z_iso_to_trans χ).
Coercion action_convertor_funclass : action_convertor >-> Funclass.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (ϱ a) #⊙ (id x) = (χ ((a, I), x)) · (id a) #⊙ (λ' x).

Definition action_pentagon_eq (χ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
  (χ ((a ⊙ x, y), z)) · (χ ((a, x), y ⊗ z)) =
  (χ ((a, x), y)) #⊙ (id z) · (χ ((a, x ⊗ y), z)) · (id a) #⊙ (α' ((x, y), z)).

End Actions_Natural_Transformations.

(* Action over a monoidal category. *)
Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), (action_triangle_eq odot ϱ χ) × (action_pentagon_eq odot χ).

(* Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), unit. *)

End Actions_Definition.

(* The canonical tensorial action on a monoidal category. *)
Definition tensorial_action : action.
Proof.
  exists V.
  exists tensor.
  exists ρ'.
  exists α'.
  exact (monoidal_precat_eq Mon_V).
Defined.

(* The action induced by a strong monoidal functor U. *)
Section Strong_Monoidal_Functor_Action.

Context (Mon_A : monoidal_precat).

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

Definition otimes_U_functor : A ⊠ V ⟶ A := functor_composite (pair_functor (functor_identity _) U) tensor_A.

Lemma otimes_U_functor_ok: functor_on_objects otimes_U_functor =
  λ av, ob1 av ⊗_A U (ob2 av).
Proof.
  apply idpath.
Qed.

Definition U_action_ρ_nat_trans : odot_I_functor otimes_U_functor ⟹ functor_identity A.
  refine (nat_trans_comp _ _ _ _  (pr1 ρ_A)).
  unfold odot_I_functor.
  set (aux := nat_trans_from_functor_fix_snd_morphism_arg _ _ _ tensor_A _ _ ϵ_inv).
  (* aux is "morally" the result, but types do not fully agree, hence we argue more extensionally *)
  use tpair.
  - intro a.
    apply (pr1 aux a).
  - cbn; red.
    intros a a' f.
    cbn.
    rewrite functor_id.
    exact (pr2 aux a a' f).
Defined.

Lemma U_action_ρ_nat_trans_ok: nat_trans_data_from_nat_trans U_action_ρ_nat_trans = λ x, id x #⊗_A ϵ_inv · ρ_A x.
Proof.
  apply idpath.
Qed.

Definition U_action_ρ_is_nat_z_iso : is_nat_z_iso U_action_ρ_nat_trans.
Proof.
  intro.
  cbn.
  use is_z_iso_comp_of_is_z_isos.
  - use is_z_iso_tensor_z_iso.
    + exact (identity_is_z_iso _ ).
    + apply (is_z_iso_inv_from_z_iso _ _ (make_z_iso _ _ ϵ_U_is_z_iso)).
  - exact (pr2 ρ_A c).
Defined.

Definition U_action_ρ : action_right_unitor otimes_U_functor := make_nat_z_iso _ _ U_action_ρ_nat_trans U_action_ρ_is_nat_z_iso.

Definition U_action_χ_nat_trans : odot_x_odot_y_functor otimes_U_functor ⟹ odot_x_otimes_y_functor otimes_U_functor.
Proof.
  apply (nat_trans_comp _ _ _ (pre_whisker (pair_functor (pair_functor (functor_identity _) U) U) (pr1 α_A))).
  exact (pre_whisker (precategory_binproduct_unassoc _ _ _) (post_whisker_fst_param μ tensor_A)).
Defined.

Lemma U_action_χ_nat_trans_ok: nat_trans_data_from_nat_trans U_action_χ_nat_trans =
  let μ := pr1 (pr2 (pr2 (pr1 U))) in
  λ x, let k   := ob1 (ob1 x) in
       let k'  := ob2 (ob1 x) in
       let k'' := ob2 x in
       α_A ((k, U k'), U k'') · id k #⊗_A (μ (k', k'')).
Proof.
  apply idpath.
Qed.

Lemma U_action_χ_is_nat_z_iso : is_nat_z_iso U_action_χ_nat_trans.
Proof.
  intro x.
  pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
  use is_z_iso_comp_of_is_z_isos.
  - exact (pr2 α_A ((k, U k'), U k'')).
  - use is_z_iso_tensor_z_iso.
    + use identity_is_z_iso.
    + exact (pr2 (pr2 U) (k', k'')).
Defined.

Definition U_action_χ : action_convertor otimes_U_functor :=
  make_nat_z_iso _ _ U_action_χ_nat_trans U_action_χ_is_nat_z_iso.

(*
Definition U_action_struct : action_struct.
Proof.
  exists A.
  exists otimes_U_functor.
  (* K ⊗ U I_C -- (1_K ⊗ ϵ^{-1} · λ_D K) --> K *)
  exists U_action_ρ.
  exists U_action_χ.
  exact tt.
Defined.
*)

Lemma U_action_tlaw : action_triangle_eq (A := A) otimes_U_functor U_action_ρ U_action_χ.
Proof.
  red.
  intros.
  cbn.
  unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
  unfold nat_trans_data_post_whisker_fst_param.
  cbn.
  unfold make_dirprod.
  rewrite functor_id.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply pathsinv0.
  etrans.
  { rewrite assoc'. apply maponpaths. apply pathsinv0. apply functor_comp. }
  unfold compose at 2. simpl. unfold make_dirprod. rewrite id_left.
  rewrite <- (id_left (id U x)).
  apply pathsinv0.
  intermediate_path (# tensor_A ((# tensor_A (id a #, ϵ_inv)) #, id U x) · # tensor_A (ρ_A a #, id U x)).
  { rewrite <- functor_comp.
    apply idpath. }
  pose (f := # tensor_A (# tensor_A (id a #, ϵ) #, id U x)).
  apply (pre_comp_with_z_iso_is_inj'(f:=f)).
  { use is_z_iso_tensor_z_iso.
    - use is_z_iso_tensor_z_iso.
      + exact (identity_is_z_iso _).
      + exact ϵ_U_is_z_iso.
    - exact (identity_is_z_iso _ ).
  }
  rewrite assoc.
  intermediate_path (# tensor_A (ρ_A a #, id U x)).
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
    apply (nat_trans_ax (pr1 α_A) ((a, I_A), U x) ((a, U I), U x) (make_dirprod (make_dirprod (id a) ϵ) (id U x))). }
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
    eapply (maponpaths (fun u: pr1 Mon_A ⟦I_A ⊗_A (U x), U x⟧ => # tensor_A (id a #, u))).
    apply pathsinv0.
    apply (pr1 (unitality_U x)).
  - fold λ_A.
    (* UniMath.MoreFoundations.Tactics.show_id_type.
       unfold functor_fix_snd_arg_ob in TYPE. *)
    apply pathsinv0.
    apply triangle_eq_A.
Defined.

Lemma U_action_plaw : action_pentagon_eq (A := A) otimes_U_functor U_action_χ.
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
    rewrite <- (id_left (id U z)).
    intermediate_path (# tensor_A ((α_A ((a, U x), U y) #, id U z) · (# tensor_A (id a #, μ (x, y)) #, id U z))).
    - apply idpath.
    - apply functor_comp.
  }
  etrans.
  { apply cancel_postcomposition.
    rewrite assoc'.
    apply maponpaths.
    apply (nat_trans_ax (pr1 α_A) ((a, U x ⊗_A U y), U z) ((a, U (x ⊗ y)), U z) (make_dirprod (make_dirprod (id a) (μ (x, y))) (id U z))).
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
    eapply (maponpaths (fun u: A ⟦(U x ⊗_A U y) ⊗_A U z, U (x ⊗ (y ⊗ z))⟧ => id a  #⊗_A u)).
    apply assoc_U.
  }
  fold α_A. fold tensor_A. fold tensor. fold μ.
  etrans.
  { rewrite assoc. apply maponpaths.
    rewrite assoc'.
    rewrite <- (id_left (id a)).
    intermediate_path (# tensor_A ((id a #, α_A ((U x, U y), U z)) · (id a #, # tensor_A (id U x #, μ (y, z)) · μ (x, y ⊗ z)))).
    2: { apply functor_comp. }
    apply idpath.
  }
  etrans.
  { do 2 apply maponpaths.
    rewrite <- (id_left (id a)).
    intermediate_path (# tensor_A ((id a #, # tensor_A (id pr1 (pr1 U) x #, μ (y, z))) · (id a #, μ (x, y ⊗ z)))).
    2: { apply functor_comp. }
    apply idpath.
  }
  repeat rewrite assoc.
  apply cancel_postcomposition.
  etrans.
  { apply cancel_postcomposition.
    apply pathsinv0.
    apply pentagon_eq_A.
  }
  (* the goal has chains up to seven projections *)
  change (α_A ((tensor_A (a, U x), U y), U z) · α_A ((a, U x), tensor_A (U y, U z))
  · # tensor_A (id a #, # tensor_A (id U x #, μ (y, z))) =
  α_A ((a ⊗_A U x, U y), U z) · # tensor_A (id (a ⊗_A U x) #, μ (y, z))
      · α_A ((a, U x), U (y ⊗ z))).
  repeat rewrite assoc'.
  apply maponpaths.
  etrans.
  { apply pathsinv0.
    apply (nat_trans_ax (pr1 α_A) ((a, U x), U y ⊗_A U z) ((a, U x), U (y ⊗ z)) (make_dirprod (make_dirprod (id a) (id U x)) (μ (y, z)))).
  }
  cbn. unfold make_dirprod.
  apply cancel_postcomposition.
  (* present the identity in the binary product of categories *)
  change (# tensor_A (# tensor_A (id (a, U x)) #, μ (y, z)) = # tensor_A (id (a ⊗_A U x) #, μ (y, z))).
  rewrite functor_id.
  apply idpath.
Defined.

Definition U_action : action.
  exists A.
  exists otimes_U_functor.
  exists U_action_ρ.
  exists U_action_χ.
  split.
  - exact U_action_tlaw.
  - exact U_action_plaw.
Defined.

End Strong_Monoidal_Functor_Action.

End A.
