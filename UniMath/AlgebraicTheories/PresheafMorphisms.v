From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(**************************************************************************************************

  Presheaf morphisms

  Defines what a morphism between two algebraic theory presheaves is and gives constructors and
  accessors.

  Contents
  1. The definition of a presheaf morphism [presheaf_morphism]
  2. An alternate constructor [make_presheaf_morphism']
  3. An equality lemma [presheaf_morphism_eq]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategoryCore.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.

Local Open Scope cat.

(** * 1. The definition of a presheaf morphism *)

Definition presheaf_morphism
  {T : algebraic_theory}
  (P P' : presheaf T)
  : UU
  := presheaf_cat T ⟦P, P'⟧.

Definition make_presheaf_morphism
  {T : algebraic_theory}
  {P P' : presheaf T}
  (F: indexed_set_cat nat⟦P, P'⟧)
  (HF: ∏ m n a f, mor_op_ax (identity T) F (@op T P) (@op T P') m n a f)
  : presheaf_morphism P P'
  := F ,, HF ,, tt.

Definition presheaf_morphism_to_function
  {T : algebraic_theory}
  {P P' : presheaf T}
  (f : presheaf_morphism P P')
  (n : nat)
  : P n → P' n
  := pr1 f n.

Coercion presheaf_morphism_to_function : presheaf_morphism >-> Funclass.

Definition mor_op
  {T : algebraic_theory}
  {P P' : presheaf T}
  (F : presheaf_morphism P P')
  {m n : nat}
  (t : (P m : hSet))
  (f : stn m → (T n : hSet))
  : mor_op_ax (identity T) F (@op T P) (@op T P') m n t f
  := pr12 F m n t f.

(** * 3. An equality lemma *)

Lemma presheaf_morphism_eq
  {T : algebraic_theory}
  {P P' : presheaf T}
  (F F' : presheaf_morphism P P')
  (H : ∏ n, F n = F' n)
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    use isapropdirprod.
    + do 4 (apply impred_isaprop; intro).
      apply setproperty.
    + exact isapropunit.
  }
  apply funextsec.
  exact H.
Qed.

Lemma presheaf_mor_comp
  {T : algebraic_theory}
  {P P' P'' : presheaf T}
  (F : presheaf_morphism P P')
  (F' : presheaf_morphism P' P'')
  (n : nat)
  : (F · F' : presheaf_morphism _ _) n = funcomp (F n) (F' n).
Proof.
  refine (maponpaths (λ z, z _) (pr1_transportf (B := λ _, ∏ n, P n → P'' n) _ _) @ _).
  exact (maponpaths (λ z, (z _) _) (transportf_const _ _)).
Qed.
