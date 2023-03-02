(** Monoidal functors *)

(** behaviour w.r.t. to swapped tensor products added by Ralph Matthes in 2019, then iso changed to z_iso in 2021 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Monoidal_Functor.

Context (Mon_C Mon_D : monoidal_cat).

Local Definition tensor_C := monoidal_cat_tensor Mon_C.
Notation "X ⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Local Definition I_C := monoidal_cat_unit Mon_C.
Local Definition α_C := monoidal_cat_associator Mon_C.
Local Definition λ_C := monoidal_cat_left_unitor Mon_C.
Local Definition ρ_C := monoidal_cat_right_unitor Mon_C.

Local Definition tensor_D := monoidal_cat_tensor Mon_D.
Notation "X ⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Local Definition I_D := monoidal_cat_unit Mon_D.
Local Definition α_D := monoidal_cat_associator Mon_D.
Local Definition λ_D := monoidal_cat_left_unitor Mon_D.
Local Definition ρ_D := monoidal_cat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : Mon_C ⟶ Mon_D).

Definition monoidal_functor_map_dom : category_binproduct Mon_C Mon_C ⟶ Mon_D :=
  functor_composite (pair_functor F F) tensor_D.

Lemma monoidal_functor_map_dom_ok: functor_on_objects monoidal_functor_map_dom =
  λ c, F (ob1 c) ⊗_D F (ob2 c).
Proof.
  apply idpath.
Qed.

Definition monoidal_functor_map_codom : category_binproduct Mon_C Mon_C ⟶ Mon_D :=
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

Definition make_lax_monoidal_functor (F : Mon_C ⟶ Mon_D) (ϵ : I_D --> F I_C)
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

  Context {Mon Mon' : monoidal_cat}.

  Local Definition tensor := monoidal_cat_tensor Mon.
  Local Definition tensor' := monoidal_cat_tensor Mon'.

Lemma swapping_of_lax_monoidal_functor_assoc (lmF: lax_monoidal_functor Mon Mon'):
  monoidal_functor_associativity (swapping_of_monoidal_cat Mon) (swapping_of_monoidal_cat Mon') lmF
                                 (pre_whisker binswap_pair_functor (lax_monoidal_functor_μ lmF)).
Proof.
  induction lmF as [F [ϵ [μ [Hass Hunit]]]].
  red. intros x y z.
  set (Hass_inst := Hass z y x).
  apply pathsinv0. rewrite <- assoc.
  cbn.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_cat_associator Mon') ((F z, F y), F x)).
  apply (z_iso_inv_on_right _ _ _ f).
  transparent assert (is : (is_z_isomorphism (# F (monoidal_cat_associator Mon ((z, y), x))))).
  { apply functor_on_is_z_isomorphism.
    apply monoidal_cat_associator.
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
  lax_monoidal_functor (swapping_of_monoidal_cat Mon)
                       (swapping_of_monoidal_cat Mon').
Proof.
  intro lmF.
  induction lmF as [F [ϵ [μ [Hass Hunit]]]].
  use make_lax_monoidal_functor.
  - exact F.
  - exact ϵ.
  - exact (pre_whisker binswap_pair_functor μ).
  - apply (swapping_of_lax_monoidal_functor_assoc (F,, (ϵ,, (μ,, (Hass,, Hunit))))).
  - abstract ( red; intro x; induction (Hunit x) as [Hunit1 Hunit2]; split; assumption ).
Defined.

Definition swapping_of_strong_monoidal_functor: strong_monoidal_functor Mon Mon' ->
  strong_monoidal_functor (swapping_of_monoidal_cat Mon)
                          (swapping_of_monoidal_cat Mon').
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

Local Open Scope moncat.

Definition mon_functor_unit
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
  : 𝟙 --> F 𝟙
  := pr12 F.

Definition mon_functor_tensor
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
           (x y : V₁)
  : F x ⊗ F y --> F(x ⊗ y)
  := pr122 F (x ,, y).

Section MonoidalFunctorAccessors.
  Context {V₁ V₂ : monoidal_cat}
          (F : lax_monoidal_functor V₁ V₂).

  Definition tensor_mon_functor_tensor
             {x₁ x₂ y₁ y₂ : V₁}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : #F f #⊗ #F g · mon_functor_tensor F x₂ y₂
      =
      mon_functor_tensor F x₁ y₁ · #F (f #⊗ g).
  Proof.
    exact (nat_trans_ax (pr122 F) (x₁ ,, y₁) (x₂ ,, y₂) (f ,, g)).
  Qed.

  Definition mon_functor_lassociator
             (x y z : V₁)
    : mon_functor_tensor F x y #⊗ id (F z)
      · mon_functor_tensor F (x ⊗ y) z
      · #F (mon_lassociator x y z)
      =
      mon_lassociator (F x) (F y) (F z)
      · id (F x) #⊗ mon_functor_tensor F y z
      · mon_functor_tensor F x (y ⊗ z)
    := pr1 (pr222 F) x y z.

  Definition mon_functor_rassociator
             (x y z : V₁)
    : mon_rassociator (F x) (F y) (F z)
      · mon_functor_tensor F x y #⊗ id (F z)
      · mon_functor_tensor F (x ⊗ y) z
      =
      id (F x) #⊗ mon_functor_tensor F y z
      · mon_functor_tensor F x (y ⊗ z)
      · #F (mon_rassociator x y z).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!(id_left _) @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply mon_rassociator_lassociator.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      refine (!_).
      apply mon_functor_lassociator.
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_lassociator_rassociator.
  Qed.

  Definition mon_functor_lunitor
             (x : V₁)
    : mon_lunitor (F x)
      =
      mon_functor_unit F #⊗ id (F x)
      · mon_functor_tensor F 𝟙 x
      · #F (mon_lunitor x)
    := pr1 (pr2 (pr222 F) x).

  Definition mon_functor_linvunitor
             (x : V₁)
    : #F (mon_linvunitor x)
      =
      mon_linvunitor (F x)
      · mon_functor_unit F #⊗ id (F x)
      · mon_functor_tensor F 𝟙 x.
  Proof.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply mon_linvunitor_lunitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply mon_functor_lunitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_lunitor_linvunitor.
  Qed.

  Definition mon_functor_runitor
             (x : V₁)
    : mon_runitor (F x)
      =
      id (F x) #⊗ mon_functor_unit F
      · mon_functor_tensor F x 𝟙
      · #F (mon_runitor x)
    := pr2 (pr2 (pr222 F) x).

  Definition mon_functor_rinvunitor
             (x : V₁)
    : #F (mon_rinvunitor x)
      =
      mon_rinvunitor (F x)
      · id (F x) #⊗ mon_functor_unit F
      · mon_functor_tensor F x 𝟙.
  Proof.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply mon_rinvunitor_runitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply mon_functor_runitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_runitor_rinvunitor.
  Qed.
End MonoidalFunctorAccessors.

Section StrongMonoidalFunctorAccessors.
  Context {V₁ V₂ : monoidal_cat}
          (F : strong_monoidal_functor V₁ V₂).

  Definition strong_functor_unit_inv
    : F 𝟙 --> 𝟙
    := inv_from_z_iso (_ ,, pr12 F).

  Definition strong_functor_unit_inv_unit
    : strong_functor_unit_inv · mon_functor_unit F = identity _.
  Proof.
    apply z_iso_after_z_iso_inv.
  Qed.

  Definition strong_functor_unit_unit_inv
    : mon_functor_unit F · strong_functor_unit_inv = identity _.
  Proof.
    apply (z_iso_inv_after_z_iso (_ ,, pr12 F)).
  Qed.

  Definition strong_functor_tensor_inv
             (x y : V₁)
    : F(x ⊗ y) --> F x ⊗ F y
    := nat_z_iso_inv (make_nat_z_iso _ _ _ (pr22 F)) (x ,, y).

  Definition strong_functor_tensor_inv_tensor
             (x y : V₁)
    : strong_functor_tensor_inv x y · mon_functor_tensor F x y = identity _.
  Proof.
    apply (z_iso_after_z_iso_inv (_ ,, (pr22 F) (x ,, y))).
  Qed.

  Definition strong_functor_tensor_tensor_inv
             (x y : V₁)
    : mon_functor_tensor F x y · strong_functor_tensor_inv x y = identity _.
  Proof.
    apply (z_iso_inv_after_z_iso (_ ,, (pr22 F) (x ,, y))).
  Qed.

  Definition tensor_strong_functor_tensor_inv
             {x₁ x₂ y₁ y₂ : V₁}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : strong_functor_tensor_inv x₁ y₁ · #F f #⊗ #F g
      =
      #F (f #⊗ g) · strong_functor_tensor_inv x₂ y₂.
  Proof.
    apply (!(nat_trans_ax
               (nat_z_iso_inv (make_nat_z_iso _ _ _ (pr22 F)))
               (x₁ ,, y₁)
               (x₂ ,, y₂)
               (f ,, g))).
  Qed.
End StrongMonoidalFunctorAccessors.
