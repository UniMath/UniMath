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

Local Open Scope cat.

(** * 1. The definition of a presheaf morphism *)

Definition presheaf_morphism {T : algebraic_theory_data} (P P' : presheaf_data T) : UU
  := ∑ (F: P ⟹ P') (HF: ∏ m n a f, F n (action a f) = action (F m a) f), unit.

Definition make_presheaf_morphism
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (F: P ⟹ P')
  (HF: ∏ m n a f, F n (action a f) = action (F m a) f)
  : presheaf_morphism P P'
  := F ,, HF ,, tt.

Coercion presheaf_morphism_to_nat_trans
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (f : presheaf_morphism P P')
  : nat_trans P P'
  := pr1 f.

Definition presheaf_morphism_commutes_with_action
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (F : presheaf_morphism P P')
  {m n : nat}
  (t : (P m : hSet))
  (f : stn m → (T n : hSet))
  : F n (action t f) = action (F m t) f
  := pr12 F m n t f.

(** * 2. An alternate constructor *)

Definition make_presheaf_morphism'
  {T : algebraic_theory_data}
  {P P' : presheaf T}
  (F: ∏ n, (P n : hSet) → (P' n : hSet))
  (HF: ∏ m n a f, F n (action a f) = action (F m a) f)
  : presheaf_morphism P P'.
Proof.
  use make_presheaf_morphism.
  - use make_nat_trans.
    + exact F.
    + abstract (
        intros n n' a;
        use funextfun;
        intro x;
        refine (maponpaths _ (presheaf_functor_uses_projections P _ _) @ !_);
        refine (presheaf_functor_uses_projections P' _ _ @ !_);
        apply HF
      ).
  - exact HF.
Defined.

(** * 3. An equality lemma *)

Lemma presheaf_morphism_eq
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
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
  apply nat_trans_eq.
  - apply homset_property.
  - exact H.
Qed.
