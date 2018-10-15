(**
  Generalisation of the concept of actions, over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.

Local Open Scope cat.

Context (Mon_V : monoidal_precat).

Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := monoidal_precat_associator Mon_V.
Let λ' := monoidal_precat_left_unitor Mon_V.
Let ρ' := monoidal_precat_right_unitor Mon_V.

Section Actions_Definition.

(* A ⊙ I --> A *)

Section Actions_Natural_Transformations.

Context (A : precategory) (odot : functor (precategory_binproduct A V) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition odot_I_functor_data : functor_data A A.
Proof.
  exists (λ a, a ⊙ I).
  intros ? ? f.
  exact (f #⊙ (id I)).
Defined.

Definition odot_I_is_functor : is_functor odot_I_functor_data.
Proof.
  split.
  - intro.
    simpl.
    rewrite binprod_id.
    rewrite (functor_id odot).
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    replace (id I) with (id I · id I).
    rewrite binprod_comp.
    rewrite id_left.
    rewrite (functor_comp odot).
    reflexivity.
    rewrite id_left.
    reflexivity.
Qed.

Definition odot_I_functor : functor A A := mk_functor odot_I_functor_data odot_I_is_functor.

Definition action_right_unitor : UU := nat_iso odot_I_functor (functor_identity A).

Definition odot_x_odot_y_functor_data : functor_data ((A ⊠ V) ⊠ V) A.
Proof.
  exists (λ a, (ob1 (ob1 a) ⊙ ob2 (ob1 a)) ⊙ ob2 a).
  intros ? ? f.
  exact ((mor1 (mor1 f) #⊙ mor2 (mor1 f)) #⊙ mor2 f).
Defined.

Definition odot_x_odot_y_is_functor : is_functor odot_x_odot_y_functor_data.
Proof.
  split.
  - intro.
    simpl.
    repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
    do 2 (rewrite binprod_id; rewrite (functor_id odot)).
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
    do 2 (rewrite binprod_comp; rewrite (functor_comp odot)).
    reflexivity.
Qed.

Definition odot_x_odot_y_functor : (A ⊠ V) ⊠ V ⟶ A := mk_functor odot_x_odot_y_functor_data odot_x_odot_y_is_functor.

Definition odot_x_otimes_y_functor_data : functor_data ((A ⊠ V) ⊠ V) A.
Proof.
  exists (λ a, ob1 (ob1 a) ⊙ (ob2 (ob1 a) ⊗ ob2 a)).
  intros ? ? f.
  exact (mor1 (mor1 f) #⊙ (mor2 (mor1 f) #⊗ mor2 f)).
Defined.

Definition odot_x_otimes_y_is_functor : is_functor odot_x_otimes_y_functor_data.
  split.
  - intro.
    simpl.
    repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
    rewrite binprod_id.
    rewrite (functor_id tensor).
    rewrite binprod_id.
    rewrite (functor_id odot).
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    rewrite <- (functor_comp odot).
    rewrite <- binprod_comp.
    repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
    rewrite binprod_comp.
    rewrite (functor_comp tensor).
    reflexivity.
Qed.

Definition odot_x_otimes_y_functor : (A ⊠ V) ⊠ V ⟶ A := mk_functor odot_x_otimes_y_functor_data odot_x_otimes_y_is_functor.

Definition action_convertor : UU := nat_iso odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (pr1 ϱ a) #⊙ (id x) = (pr1 χ ((a, I), x)) · (id a) #⊙ (pr1 λ' x).

Definition action_pentagon_eq (χ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
(pr1 χ ((a ⊙ x, y), z)) · (pr1 χ ((a, x), y ⊗ z)) = (pr1 χ ((a, x), y)) #⊙ (id z) · (pr1 χ ((a, x ⊗ y), z)) · (id a) #⊙ (pr1 α' ((x, y), z)).

End Actions_Natural_Transformations.

(* Action over a monoidal category. *)
Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), (action_triangle_eq A odot ϱ χ) × (action_pentagon_eq A odot χ).

Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), unit.

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

Let A := monoidal_precat_precat Mon_A.
Let I_A := monoidal_precat_unit Mon_A.
Let tensor_A := monoidal_precat_tensor Mon_A.
Notation "X ⊗_A Y" := (tensor_A (X , Y)) (at level 31).
Notation "f #⊗_A g" := (#tensor_A (f #, g)) (at level 31).
Let α_A := monoidal_precat_associator Mon_A.
Let λ_A := monoidal_precat_left_unitor Mon_A.
Let ρ_A := monoidal_precat_right_unitor Mon_A.

Context (U : strong_monoidal_functor Mon_V Mon_A).

Definition otimes_U_functor_data : functor_data (A ⊠ V) A.
Proof.
  exists (λ av, ob1 av ⊗_A U (ob2 av)).
  intros ? ? f.
  exact (mor1 f #⊗_A #U (mor2 f)).
Defined.

Definition otimes_U_is_functor : is_functor otimes_U_functor_data.
Proof.
  split.
  - intro.
    simpl.
    rewrite (functor_id U).
    rewrite binprod_id.
    rewrite (functor_id tensor_A).
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    rewrite (functor_comp U).
    rewrite binprod_comp.
    rewrite (functor_comp tensor_A).
    reflexivity.
Qed.

Definition otimes_U_functor : A ⊠ V ⟶ A := mk_functor otimes_U_functor_data otimes_U_is_functor.

Definition U_action_ρ : action_right_unitor A otimes_U_functor.
Proof.
  unfold action_right_unitor.
  unfold nat_iso.
  use tpair.
  + (* natural transformation *)
    unfold nat_trans.
    pose (ϵ_inv := inv_from_iso (mk_iso (pr1 (pr2 U)))).
    exists (λ x, id x #⊗_A ϵ_inv · pr1 ρ_A x). (* ϱ *)
    intros x x' f.
    pose (ρ_nat_law := pr2 (pr1 ρ_A) x x' f).
    simpl; simpl in ρ_nat_law.
    assert (ϵ_coher : id x #⊗_A ϵ_inv · f #⊗_A id I_A = f #⊗_A (#U (id I)) · id x' #⊗_A ϵ_inv).
    * do 2 rewrite <- functor_comp.
      do 2 rewrite <- binprod_comp.
      rewrite functor_id.
      do 2 (rewrite id_left; rewrite id_right).
      reflexivity.
    * rewrite assoc.
      assert (ϵ_coher' : (# tensor_A (id x #, ϵ_inv) · # tensor_A (f #, id I_A) = # tensor_A (f #, # U (id I)) · # tensor_A (id x' #, ϵ_inv))) by (exact ϵ_coher); clear ϵ_coher; rename ϵ_coher' into ϵ_coher.
      assert (goal' : (# tensor_A (f #, # U (id I)) · # tensor_A (id x' #, ϵ_inv) · (pr1 ρ_A) x' = # tensor_A (id x #, ϵ_inv) · (pr1 ρ_A) x · f)); [| exact goal'].
      rewrite <- ϵ_coher.
      repeat rewrite <- assoc.
      assert (goal' : (# tensor_A (id x #, ϵ_inv) · (# tensor_A (f #, id I_A) · (pr1 ρ_A) x') = # tensor_A (id x #, ϵ_inv) · (pr1 (pr1 ρ_A) x · f))); [| exact goal'].
      assert (ρ_nat_law' : (# (pr1 (pr2 Mon_A)) (f #, id pr1 (pr2 (pr2 Mon_A))) · pr1 (pr1 ρ_A) x' = pr1 (pr1 ρ_A) x · f)) by (exact ρ_nat_law); clear ρ_nat_law; rename ρ_nat_law' into ρ_nat_law.
      rewrite <- ρ_nat_law.
      reflexivity.
  + (* is_nat_iso ϱ *)
    intro.
    simpl.
    use is_iso_comp_of_is_isos.
    use is_iso_tensor_iso.
    exact (identity_is_iso _ _).
    use is_iso_inv_from_iso.
    exact (pr2 ρ_A c).
Defined.

Definition U_action_χ : action_convertor A otimes_U_functor.
Proof.
  use tpair.
  + (* natural transformation *)
    unfold nat_trans.
    pose (μ := pr1 (pr2 (pr2 (pr1 U)))).
    use tpair.
    intro x.
    pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
    exact (pr1 α_A ((k, U k'), U k'') · id k #⊗_A pr1 μ (k', k'')). (* χ *)
    intros x x' g.
    simpl.
    pose (k_1 := ob1 (ob1 x)); pose (k'_1 := ob2 (ob1 x)); pose (k''_1 := ob2 x).
    pose (k_2 := ob1 (ob1 x')); pose (k'_2 := ob2 (ob1 x')); pose (k''_2 := ob2 x').
    pose (f := mor1 (mor1 g)); pose (f' := mor2 (mor1 g)); pose (f'' := mor2 g).
    fold monoidal_precat_precat.
    pose (α_nat_law := pr2 (pr1 α_A) ((k_1, U k'_1), U k''_1) ((k_2, U k'_2), U k''_2) ((f #, #U f') #, #U f'')).
    assert (μ_coher : id k_1 #⊗_A (pr1 μ (k'_1, k''_1)) · (f #⊗_A #U (f' #⊗ f'')) = f #⊗_A (#U f' #⊗_A #U f'') · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))).
    do 2 rewrite <- tensor_comp.
    rewrite id_left; rewrite id_right.
    assert (snd_eq : pr1 μ (k'_1, k''_1) · # U (f' #⊗ f'') = # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2)).
    symmetry.
    exact (pr2 μ (k'_1, k''_1) (k'_2, k''_2) (f' #, f'')).
    assert (goal' : (# tensor_A (f #, pr1 μ (k'_1, k''_1) · # U (# tensor (f' #, f''))) = # tensor_A (f #, # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2)))); [| exact goal'].
    rewrite <- snd_eq.
    reflexivity.
    assert (α_nat_law' : (# tensor_A (# tensor_A (f #, # U f') #, # U f'') · pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) = pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) · # tensor_A (f #, # tensor_A (# U f' #, # U f'')))) by (exact α_nat_law); clear α_nat_law; rename α_nat_law' into α_nat_law.
    pose (α_nat_law' := maponpaths (λ p, p · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))) α_nat_law).
    simpl in α_nat_law'.
    repeat rewrite <- assoc in α_nat_law'.
    assert (α_nat_law'' : (# tensor_A (# tensor_A (f #, # U f') #, # U f'') · (pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))) = pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) · (# tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))))) by (exact α_nat_law'); clear α_nat_law'; rename α_nat_law'' into α_nat_law'.
    assert (μ_coher' : (# tensor_A (id k_1 #, pr1 μ (k'_1, k''_1)) · # tensor_A (f #, # U (# tensor (f' #, f''))) = # tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2)))) by (exact μ_coher); clear μ_coher; rename μ_coher' into μ_coher.
    pose (common := (# tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2)))).
    fold common in μ_coher.
    fold common in α_nat_law'.
    rewrite <- μ_coher in α_nat_law'.
    repeat rewrite assoc in α_nat_law'.
    repeat rewrite assoc.
    exact α_nat_law'.
  + (* is_nat_iso χ *)
    intro x.
    pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
    use is_iso_comp_of_is_isos.
    exact (pr2 α_A ((k, U k'), U k'')).
    use is_iso_tensor_iso.
    use identity_is_iso.
    exact (pr2 (pr2 U) (k', k'')).
Defined.

Definition U_action_struct : action_struct.
Proof.
  exists A.
  exists otimes_U_functor.
  (* K ⊗ U I_C -- (1_K ⊗ ϵ^{-1} · λ_D K) --> K *)
  exists U_action_ρ.
  exists U_action_χ.
  exact tt.
Defined.

Context
  {U_action_tlaw : action_triangle_eq (pr1 U_action_struct) (pr1 (pr2 U_action_struct)) (pr1 (pr2 (pr2 U_action_struct))) (pr1 (pr2 (pr2 (pr2 U_action_struct))))}
  {U_action_plaw : action_pentagon_eq (pr1 U_action_struct) (pr1 (pr2 U_action_struct)) (pr1 (pr2 (pr2 (pr2 U_action_struct))))}.

Definition U_action : action.
  exists (pr1 U_action_struct).
  exists (pr1 (pr2 U_action_struct)).
  exists (pr1 (pr2 (pr2 U_action_struct))).
  exists (pr1 (pr2 (pr2 (pr2 U_action_struct)))).
  exists U_action_tlaw.
  exact U_action_plaw.
Defined.

End Strong_Monoidal_Functor_Action.
