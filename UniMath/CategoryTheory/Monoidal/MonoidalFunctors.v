(** Monoidal functors **)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Section Monoidal_Functor.

Context (Mon_C Mon_D : monoidal_precat).

Let C := monoidal_precat_precat Mon_C.
Let tensor_C := monoidal_precat_tensor Mon_C.
Notation "X ⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Let I_C := monoidal_precat_unit Mon_C.
Let α_C := monoidal_precat_associator Mon_C.
Let λ_C := monoidal_precat_left_unitor Mon_C.
Let ρ_C := monoidal_precat_right_unitor Mon_C.

Let D := monoidal_precat_precat Mon_D.
Let tensor_D := monoidal_precat_tensor Mon_D.
Notation "X ⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Let I_D := monoidal_precat_unit Mon_D.
Let α_D := monoidal_precat_associator Mon_D.
Let λ_D := monoidal_precat_left_unitor Mon_D.
Let ρ_D := monoidal_precat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : C ⟶ D).

Definition monoidal_functor_map_dom : precategory_binproduct C C ⟶ D.
use tpair; [| split].
- use tpair.
  exact (λ c, F (ob1 c) ⊗_D F (ob2 c)).
  intros ? ? f.
  exact (#F (mor1 f) #⊗_D #F (mor2 f)).
- intro.
  simpl.
  repeat rewrite functor_id.
  apply tensor_id.
- unfold functor_compax.
  simpl.
  intros.
  repeat rewrite functor_comp.
  apply tensor_comp.
Defined.

Definition monoidal_functor_map_codom : precategory_binproduct C C ⟶ D.
use tpair; [| split].
- use tpair.
  exact (λ c, F (ob1 c ⊗_C ob2 c)).
  intros ? ? f.
  exact (#F (mor1 f #⊗_C mor2 f)).
- intro.
  simpl.
  rewrite binprod_id.
  rewrite (functor_id tensor_C).
  rewrite functor_id.
  reflexivity.
- unfold functor_compax.
  simpl.
  intros.
  rewrite binprod_comp.
  rewrite (functor_comp tensor_C).
  rewrite functor_comp.
  reflexivity.
Defined.

Definition monoidal_functor_map :=
  monoidal_functor_map_dom ⟹ monoidal_functor_map_codom.

Definition monoidal_functor_associativity (μ : monoidal_functor_map) :=
  ∏ (x y z : C),
  pr1 μ (x, y) #⊗_D id F(z) · pr1 μ (x ⊗_C y, z) · #F (pr1 α_C ((x, y), z))
  =
  pr1 α_D ((F x, F y), F z) · id (F x) #⊗_D pr1 μ (y, z) · pr1 μ (x, y ⊗_C z).

Definition monoidal_functor_unitality (ϵ : I_D --> F I_C) (μ : monoidal_functor_map) :=
  ∏ (x : C),
  (pr1 λ_D (F x) = ϵ #⊗_D (id (F x)) · pr1 μ (I_C, x) · #F (pr1 λ_C x))
  ×
  (pr1 ρ_D (F x) = (id (F x)) #⊗_D ϵ · pr1 μ (x, I_C) · #F (pr1 ρ_C x)).

End Monoidal_Functor_Conditions.

Definition lax_monoidal_functor : UU :=
  ∑ F : C ⟶ D, ∑ ϵ : I_D --> F I_C, ∑ μ : monoidal_functor_map F, (monoidal_functor_associativity F μ) × (monoidal_functor_unitality F ϵ μ).

Definition strong_monoidal_functor : UU :=
  ∑ L : lax_monoidal_functor,
  (is_iso (pr1 (pr2 L))) (* ϵ is an iso *)
  ×
  (is_nat_iso (pr1 (pr2 (pr2 L)))). (* μ is an iso *)

End Monoidal_Functor.

Definition strong_monoidal_functor_functor {Mon Mon' : monoidal_precat} (U : strong_monoidal_functor Mon Mon') := pr1 (pr1 U).
Coercion strong_monoidal_functor_functor : strong_monoidal_functor >-> functor.