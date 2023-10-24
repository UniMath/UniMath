(**************************************************************************************************

  Algebraic theory morphisms

  Defines morphisms of algebraic theories, together with constructors, accessors and some
  properties.

  Contents
  1. The definition of algebraic theory morphisms [algebraic_theory_morphism]
  2. An alternate constructor [make_algebraic_theory_morphism']
  3. An equality lemma

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebraic theory morphisms *)

Definition base_nat_trans
  (T T' : base_functor)
  : UU
  := T ⟹ T'.

Coercion base_nat_trans_to_nat_trans
  (T T' : base_functor)
  (F : base_nat_trans T T')
  : T ⟹ T'
  := F.

Definition preserves_id_pr {T T' : pointed_functor} (F : base_nat_trans T T')
  : UU
  := (F _ id_pr) = id_pr.

Definition pointed_functor_morphism
  (T T' : pointed_functor)
  : UU
  := ∑ (F : base_nat_trans T T'), preserves_id_pr F.

Coercion pointed_functor_morphism_to_nat_trans {T T'} (F : pointed_functor_morphism T T')
  : nat_trans T T'
  := pr1 F.

Definition preserves_composition {T T' : algebraic_theory_data} (F : base_nat_trans T T') : UU := ∏
  (m n : nat)
  (f_m : (T m : hSet))
  (f_n : stn m → (T n : hSet)),
  (F _ (f_m • f_n)) = ((F m f_m) • (λ i, F _ (f_n i))).

Definition algebraic_theory_data_morphism
  (T T' : algebraic_theory_data)
  : UU
  := ∑ (F : pointed_functor_morphism T T'), preserves_composition F.

Coercion algebraic_theory_data_morphism_to_pointed_functor_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_data_morphism T T')
  : pointed_functor_morphism T T'
  := pr1 F.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := ∑ X : algebraic_theory_data_morphism T T', unit.

Coercion algebraic_theory_morphism_to_algebraic_theory_data_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  : algebraic_theory_data_morphism T T'
  := pr1 F.

Definition is_algebraic_theory_morphism
  {T T' : algebraic_theory_data}
  (F : base_nat_trans T T')
  : UU :=
    preserves_id_pr F ×
    preserves_composition F.

Definition make_is_algebraic_theory_morphism {T T' : algebraic_theory}
  (F : base_nat_trans T T')
  (H1 : preserves_id_pr F)
  (H2 : preserves_composition F) := (H1 ,, H2).

Lemma isaprop_is_algebraic_theory_morphism
  {T T' : algebraic_theory}
  (F : base_nat_trans T T')
  : isaprop (is_algebraic_theory_morphism F).
Proof.
  intro.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Definition make_algebraic_theory_morphism
  {T T' : algebraic_theory}
  (F : base_nat_trans T T')
  (H : is_algebraic_theory_morphism F)
  : algebraic_theory_morphism T T'
  := (((F ,, pr1 H) ,, pr2 H) ,, tt).

Definition algebraic_theory_morphism_preserves_id_pr
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  : preserves_id_pr F
  := pr211 F.

Definition algebraic_theory_morphism_preserves_composition
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  : preserves_composition F
  := pr21 F.

Lemma algebraic_theory_morphism_preserves_projections
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  {n : nat}
  (i : stn n)
  : F _ (pr i) = pr i.
Proof.
  unfold pr.
  rewrite <- (algebraic_theory_morphism_preserves_id_pr F).
  apply (maponpaths (λ x, x id_pr) : ((λ x, F _ (# T _ x)) = (λ x, # T' _ (F _ x))) → _).
  apply (nat_trans_ax F).
Qed.

(** * 2. An alternate constructor *)

Section MakeAlgebraicTheoryMorphisms2.
  Lemma algebraic_theory_morphism'_to_is_nat_trans
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism' T T')
    : is_nat_trans T T' F.
  Proof.
    do 3 intro.
    apply funextfun.
    intro.
    unfold compose.
    simpl.
    do 2 rewrite (algebraic_theory_functor_uses_projections).
    etrans.
    - apply algebraic_theory_morphism'_preserves_composition.
    - apply maponpaths, funextfun.
      intro.
      apply algebraic_theory_morphism'_preserves_projections.
  Qed.

  Definition algebraic_theory_morphism'_to_base_nat_trans
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism' T T')
    : base_nat_trans T T'
    := make_nat_trans _ _ _ (algebraic_theory_morphism'_to_is_nat_trans F).

  Lemma algebraic_theory_morphism'_to_is_algebraic_theory_morphism
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism' T T')
    : is_algebraic_theory_morphism (algebraic_theory_morphism'_to_base_nat_trans F).
  Proof.
    use make_is_algebraic_theory_morphism.
    - unfold preserves_id_pr.
      simpl.
      do 2 rewrite algebraic_theory_id_pr_is_pr.
      apply algebraic_theory_morphism'_preserves_projections.
    - exact (algebraic_theory_morphism'_preserves_composition F).
  Qed.

  Definition make_algebraic_theory_morphism'
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism'_data T T')
    (H : is_algebraic_theory_morphism' F)
    : algebraic_theory_morphism T T'
    := make_algebraic_theory_morphism
      _
      (algebraic_theory_morphism'_to_is_algebraic_theory_morphism (F ,, H)).
End MakeAlgebraicTheoryMorphisms2.

(** * 3. An equality lemma *)

Lemma algebraic_theory_morphism_eq
  {T T' : algebraic_theory}
  (F F' : algebraic_theory_morphism T T')
  (H1 : ∏ n f, F n f = F' n f)
  : F = F'.
Proof.
  use subtypePath.
  {
    intro.
    exact isapropunit.
  }
  use subtypePath.
  {
    intro.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  }
  use subtypePath.
  {
    intro.
    apply setproperty.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_is_nat_trans.
    apply homset_property.
  }
  do 2 (apply funextsec; intro).
  apply H1.
Qed.
