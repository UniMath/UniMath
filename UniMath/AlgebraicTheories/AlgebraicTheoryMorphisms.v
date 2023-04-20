Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition base_nat_trans
  (T T' : base_functor)
  : UU
  := T ⟹ T'.

Coercion base_nat_trans_to_nat_trans
  (T T' : base_functor)
  (F : base_nat_trans T T')
  : T ⟹ T'
  := F.

Definition preserves_id_pr {T T' : pointed_functor} (F : base_nat_trans T T') : UU := (F _ id_pr) = id_pr.

Definition pointed_functor_morphism
  (T T' : pointed_functor)
  : UU
  := ∑ (F : base_nat_trans T T'), preserves_id_pr F.

Coercion pointed_functor_morphism_to_nat_trans {T T' : pointed_functor} (F : pointed_functor_morphism T T') : nat_trans T T' := pr1 F.

Definition preserves_composition {T T' : algebraic_theory_data} (F : base_nat_trans T T') : UU := ∏
  (m n : nat)
  (f_m : (T m : hSet))
  (f_n : stn m → (T n : hSet)),
  (F _ (f_m • f_n)) = ((F m f_m) • (λ i, F _ (f_n i))).

Definition algebraic_theory_data_morphism
  (T T' : algebraic_theory_data)
  : UU
  := ∑ (F : pointed_functor_morphism T T'), preserves_composition F.

Coercion algebraic_theory_data_morphism_to_pointed_functor_morphism {T T' : algebraic_theory_data} (F : algebraic_theory_data_morphism T T') : pointed_functor_morphism T T' := pr1 F.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := algebraic_theory_data_morphism T T'.

Coercion algebraic_theory_morphism_to_algebraic_theory_data_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism T T') : algebraic_theory_data_morphism T T' := pr1 F.

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
  := ((F ,, pr1 H) ,, pr2 H).

Definition algebraic_theory_morphism_preserves_id_pr {T T'} (F : algebraic_theory_morphism T T') : preserves_id_pr F := pr21 F.

Definition algebraic_theory_morphism_preserves_composition {T T'} (F : algebraic_theory_morphism T T') : preserves_composition F := pr2 F.

Lemma algebraic_theory_morphism_eq
  {T T'}
  (F F' : algebraic_theory_morphism T T')
  (H1 : ∏ n f, F n f = F' n f)
  : F = F'.
Proof.
  repeat use subtypePairEquality'.
  - do 2 (apply funextsec; intro).
    apply H1.
  - apply isaprop_is_nat_trans, homset_property.
  - apply setproperty.
  - repeat (apply impred_isaprop; intro).
    apply setproperty.
Qed.
