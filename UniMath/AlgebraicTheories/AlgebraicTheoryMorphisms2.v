Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope algebraic_theories.

Definition algebraic_theory_morphism'_data (T T' : algebraic_theory_data) := ∏ n, (T n : hSet) → (T' n : hSet).

Definition algebraic_theory_morphism'_data_to_function {T T'} (F : algebraic_theory_morphism'_data T T')
  : ∏ n, (T n : hSet) → (T' n : hSet)
  := F.
Coercion algebraic_theory_morphism'_data_to_function : algebraic_theory_morphism'_data >-> Funclass.

Definition preserves_composition {T T'} (F : algebraic_theory_morphism'_data T T') := ∏
    (m n : nat)
    (f : (T m : hSet))
    (g : stn m → (T n : hSet)),
    F _ (f • g) = (F _ f) • (λ i, F _ (g i)).

Definition preserves_projections {T T'} (F : algebraic_theory_morphism'_data T T') := ∏
    (n : nat)
    (i : stn n),
    F _ (pr i) = pr i.

Definition is_algebraic_theory_morphism' {T T'} (F : algebraic_theory_morphism'_data T T') :=
    preserves_composition F ×
    preserves_projections F.

Definition make_is_algebraic_theory_morphism' {T T'}
  (F : algebraic_theory_morphism'_data T T')
  (H1 : preserves_composition F)
  (H2 : preserves_projections F) : is_algebraic_theory_morphism' F := (H1 ,, H2).

Lemma isaprop_is_algebraic_theory_morphism'
  {T T'}
  (F : algebraic_theory_morphism'_data T T')
  : isaprop (is_algebraic_theory_morphism' F).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intros);
    apply setproperty.
Qed.

Definition algebraic_theory_morphism'
  (T T' : algebraic_theory_data)
  := ∑ F : algebraic_theory_morphism'_data T T', is_algebraic_theory_morphism' F.

Coercion algebraic_theory_morphism'_to_function
  {T T'}
  (F : algebraic_theory_morphism' T T')
  : algebraic_theory_morphism'_data T T'
  := pr1 F.

(* Without pr1 F, the implicit coercion will cause errors in, for example, AbstractCloneTategory. It is not clear why. *)
Definition algebraic_theory_morphism'_preserves_composition {T T'} (F : algebraic_theory_morphism' T T') : preserves_composition F := pr12 F.

Definition algebraic_theory_morphism'_preserves_projections {T T'} (F : algebraic_theory_morphism' T T') : preserves_projections F := pr22 F.
