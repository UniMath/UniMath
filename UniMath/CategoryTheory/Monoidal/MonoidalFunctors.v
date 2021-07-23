(** Monoidal functors *)

(** behaviour w.r.t. to swapped tensor products added by Ralph Matthes in 2019, then iso changed to z_iso in 2021 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Monoidal_Functor.

Context (Mon_C Mon_D : monoidal_precat).

Local Definition tensor_C := monoidal_precat_tensor Mon_C.
Notation "X ⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Local Definition I_C := monoidal_precat_unit Mon_C.
Local Definition α_C := monoidal_precat_associator Mon_C.
Local Definition λ_C := monoidal_precat_left_unitor Mon_C.
Local Definition ρ_C := monoidal_precat_right_unitor Mon_C.

Local Definition tensor_D := monoidal_precat_tensor Mon_D.
Notation "X ⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Local Definition I_D := monoidal_precat_unit Mon_D.
Local Definition α_D := monoidal_precat_associator Mon_D.
Local Definition λ_D := monoidal_precat_left_unitor Mon_D.
Local Definition ρ_D := monoidal_precat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : Mon_C ⟶ Mon_D).

Definition monoidal_functor_map_dom : precategory_binproduct Mon_C Mon_C ⟶ Mon_D :=
  functor_composite (pair_functor F F) tensor_D.

Lemma monoidal_functor_map_dom_ok: functor_on_objects monoidal_functor_map_dom =
  λ c, F (ob1 c) ⊗_D F (ob2 c).
Proof.
  apply idpath.
Qed.

Definition monoidal_functor_map_codom : precategory_binproduct Mon_C Mon_C ⟶ Mon_D :=
  functor_composite tensor_C F.

Lemma monoidal_functor_map_codom_ok: functor_on_objects monoidal_functor_map_codom =
  λ c, F (ob1 c ⊗_C ob2 c).
Proof.
  apply idpath.
Qed.

Definition monoidal_functor_map :=
  monoidal_functor_map_dom ⟹ monoidal_functor_map_codom.

Definition monoidal_functor_map_funclass (μ : monoidal_functor_map) :
  ∏ x : ob (Mon_C ⊠ Mon_C), monoidal_functor_map_dom x -->  monoidal_functor_map_codom x
  := pr1 μ.
Coercion monoidal_functor_map_funclass : monoidal_functor_map >-> Funclass.

Definition monoidal_functor_associativity (μ : monoidal_functor_map) :=
  ∏ (x y z : Mon_C),
  μ (x, y) #⊗_D id F(z) · μ (x ⊗_C y, z) · #F (α_C ((x, y), z))
  =
  α_D ((F x, F y), F z) · id (F x) #⊗_D μ (y, z) · μ (x, y ⊗_C z).

Definition monoidal_functor_unitality (ϵ : I_D --> F I_C) (μ : monoidal_functor_map) :=
  ∏ (x : Mon_C),
  (λ_D (F x) = ϵ #⊗_D (id (F x)) · μ (I_C, x) · #F (λ_C x))
  ×
  (ρ_D (F x) = (id (F x)) #⊗_D ϵ · μ (x, I_C) · #F (ρ_C x)).

End Monoidal_Functor_Conditions.

Definition lax_monoidal_functor : UU :=
  ∑ F : Mon_C ⟶ Mon_D, ∑ ϵ : I_D --> F I_C, ∑ μ : monoidal_functor_map F,
  (monoidal_functor_associativity F μ) × (monoidal_functor_unitality F ϵ μ).

Definition mk_lax_monoidal_functor (F : Mon_C ⟶ Mon_D) (ϵ : I_D --> F I_C)
  (μ : monoidal_functor_map F) (Hass: monoidal_functor_associativity F μ)
  (Hunit: monoidal_functor_unitality F ϵ μ): lax_monoidal_functor :=
  (F,, (ϵ,, (μ,, (Hass,, Hunit)))).

Definition lax_monoidal_functor_functor (lmF : lax_monoidal_functor) : Mon_C ⟶ Mon_D := pr1 lmF.
Coercion lax_monoidal_functor_functor : lax_monoidal_functor >-> functor.

Definition lax_monoidal_functor_ϵ (lmF : lax_monoidal_functor) :
  I_D -->  lax_monoidal_functor_functor lmF I_C
  := pr1 (pr2 lmF).

Definition lax_monoidal_functor_μ (lmF : lax_monoidal_functor) :
  monoidal_functor_map (lax_monoidal_functor_functor lmF)
  := pr1 (pr2 (pr2 lmF)).

Definition lax_monoidal_functor_assoc (lmF : lax_monoidal_functor) :
  monoidal_functor_associativity (lax_monoidal_functor_functor lmF) (lax_monoidal_functor_μ lmF)
  := pr1 (pr2 (pr2 (pr2 lmF))).

Definition lax_monoidal_functor_unital (lmF : lax_monoidal_functor) :
  monoidal_functor_unitality (lax_monoidal_functor_functor lmF) (lax_monoidal_functor_ϵ lmF) (lax_monoidal_functor_μ lmF)
  := pr2 (pr2 (pr2 (pr2 lmF))).


Definition strong_monoidal_functor : UU :=
  ∑ lmF : lax_monoidal_functor,
  (is_z_isomorphism (lax_monoidal_functor_ϵ lmF)) (* ϵ is an iso *)
  ×
  (is_nat_z_iso (lax_monoidal_functor_μ lmF)). (* μ is an iso *)

Definition strong_monoidal_functor_lax_monoidal_functor (smF : strong_monoidal_functor) : lax_monoidal_functor
  := pr1 smF.
Coercion strong_monoidal_functor_lax_monoidal_functor : strong_monoidal_functor >-> lax_monoidal_functor.

Definition strong_monoidal_functor_ϵ_is_z_iso (smF : strong_monoidal_functor) :
  is_z_isomorphism (lax_monoidal_functor_ϵ smF)
  := pr1 (pr2 smF).

Definition strong_monoidal_functor_μ_is_nat_z_iso (smF : strong_monoidal_functor) :
  is_nat_z_iso (lax_monoidal_functor_μ smF)
  := pr2 (pr2 smF).

Definition strong_monoidal_functor_ϵ (smF : strong_monoidal_functor) :
  z_iso I_D (lax_monoidal_functor_functor smF I_C)
  := make_z_iso _ _ (strong_monoidal_functor_ϵ_is_z_iso smF).

Definition strong_monoidal_functor_ϵ_inv (smF : strong_monoidal_functor) :
  lax_monoidal_functor_functor smF I_C  --> I_D
  := inv_from_z_iso (strong_monoidal_functor_ϵ smF).

Definition strong_monoidal_functor_μ (smF : strong_monoidal_functor) :
  nat_z_iso (monoidal_functor_map_dom smF) (monoidal_functor_map_codom smF)
  := make_nat_z_iso _ _
                    (lax_monoidal_functor_μ smF)
                    (strong_monoidal_functor_μ_is_nat_z_iso smF).

Definition strong_monoidal_functor_μ_inv (smF : strong_monoidal_functor)
  : monoidal_functor_map_codom smF ⟹ monoidal_functor_map_dom smF
  := nat_z_iso_to_trans_inv (strong_monoidal_functor_μ smF).

End Monoidal_Functor.

Arguments lax_monoidal_functor_ϵ {_ _} _ .
Arguments lax_monoidal_functor_μ {_ _} _ .
Arguments lax_monoidal_functor_assoc {_ _} _ .
Arguments lax_monoidal_functor_unital {_ _} _ .
Arguments strong_monoidal_functor_ϵ_is_z_iso {_ _} _ .
Arguments strong_monoidal_functor_μ_is_nat_z_iso {_ _} _ .
Arguments strong_monoidal_functor_ϵ {_ _} _ .
Arguments strong_monoidal_functor_ϵ_inv {_ _} _ .
Arguments strong_monoidal_functor_μ {_ _} _ .
Arguments strong_monoidal_functor_μ_inv {_ _} _ .

Section swapped_tensor.

  Context {Mon Mon' : monoidal_precat}.

  Local Definition tensor := monoidal_precat_tensor Mon.
  Local Definition tensor' := monoidal_precat_tensor Mon'.

Lemma swapping_of_lax_monoidal_functor_assoc (lmF: lax_monoidal_functor Mon Mon'):
  monoidal_functor_associativity (swapping_of_monoidal_precat Mon) (swapping_of_monoidal_precat Mon') lmF
                                 (pre_whisker binswap_pair_functor (lax_monoidal_functor_μ lmF)).
Proof.
  induction lmF as [F [ϵ [μ [Hass Hunit]]]].
  red. intros x y z.
  set (Hass_inst := Hass z y x).
  apply pathsinv0. rewrite <- assoc.
  cbn.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_precat_associator Mon') ((F z, F y), F x)).
  apply (z_iso_inv_on_right _ _ _ f).
  transparent assert (is : (is_z_isomorphism (# F (monoidal_precat_associator Mon ((z, y), x))))).
  { apply functor_on_is_z_isomorphism.
    apply monoidal_precat_associator.
  }
  set (Hass_inst' := z_iso_inv_on_left _ _ _ _ (_,, is) _ (! Hass_inst)).
  etrans.
  { exact Hass_inst'. }
  clear Hass_inst Hass_inst'.
  do 2 rewrite assoc.
  apply cancel_precomposition.
  apply idpath.
Qed.

Definition swapping_of_lax_monoidal_functor: lax_monoidal_functor Mon Mon' ->
  lax_monoidal_functor (swapping_of_monoidal_precat Mon)
                       (swapping_of_monoidal_precat Mon').
Proof.
  intro lmF.
  induction lmF as [F [ϵ [μ [Hass Hunit]]]].
  use mk_lax_monoidal_functor.
  - exact F.
  - exact ϵ.
  - exact (pre_whisker binswap_pair_functor μ).
  - apply (swapping_of_lax_monoidal_functor_assoc (F,, (ϵ,, (μ,, (Hass,, Hunit))))).
  - abstract ( red; intro x; induction (Hunit x) as [Hunit1 Hunit2]; split; assumption ).
Defined.

Definition swapping_of_strong_monoidal_functor: strong_monoidal_functor Mon Mon' ->
  strong_monoidal_functor (swapping_of_monoidal_precat Mon)
                          (swapping_of_monoidal_precat Mon').
Proof.
  intro smF.
  induction smF as [lmF [Hϵ Hμ]].
  apply (tpair _ (swapping_of_lax_monoidal_functor lmF)).
  split.
  - exact Hϵ.
  - exact (pre_whisker_on_nat_z_iso binswap_pair_functor (lax_monoidal_functor_μ lmF) Hμ).
Defined.

Lemma swapping_of_strong_monoidal_functor_on_objects (smF: strong_monoidal_functor Mon Mon')(a: Mon): swapping_of_strong_monoidal_functor smF a = smF a.
Proof.
  apply idpath.
Qed.

End swapped_tensor.
