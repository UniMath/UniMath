(**************************************************************************************************

  Algebraic theory morphisms

  Defines morphisms of algebraic theories, together with constructors, accessors and some
  properties.

  Contents
  1. The definition of algebraic theory morphisms [algebraic_theory_morphism]
  2. An equality lemma [algebraic_theory_morphism_eq]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebraic theory morphisms *)

Definition algebraic_theory_morphism_data
  (T T' : algebraic_theory_data)
  : UU
  := indexed_set_cat _ ⟦T, T'⟧.

Definition algebraic_theory_morphism_data_to_function
  {T T' : algebraic_theory_data}
  (F : algebraic_theory_morphism_data T T')
  (n : nat)
  : T n → T' n
  := F n.

Coercion algebraic_theory_morphism_data_to_function : algebraic_theory_morphism_data >-> Funclass.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := algebraic_theory_cat⟦T, T'⟧.

Coercion algebraic_theory_morphism_to_algebraic_theory_morphism_data
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  : algebraic_theory_morphism_data T T'
  := pr11 F.

Definition make_is_algebraic_theory_morphism {T T' : algebraic_theory}
  {F : algebraic_theory_morphism_data T T'}
  (H1 : mor_pr_ax F)
  (H2 : mor_comp_ax F)
  : is_algebraic_theory_morphism F
  := H1 ,, H2.

Lemma isaprop_is_algebraic_theory_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism_data T T')
  : isaprop (is_algebraic_theory_morphism F).
Proof.
  intro.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Definition make_algebraic_theory_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism_data T T')
  (H : is_algebraic_theory_morphism F)
  : algebraic_theory_morphism T T'
  := (F ,, pr1 H ,, pr2 H) ,, tt.

Definition mor_pr
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  {n : nat}
  (i : stn n)
  : F n (pr i) = pr i
  := pr121 F n i.

Definition mor_comp
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T T')
  {m n : nat}
  (f : T m)
  (g : stn m → T n)
  : F n (f • g) = (F m f) • (λ i, F n (g i))
  := pr221 F m n f g.

(** * 2. An equality lemma *)

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
    apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
    apply setproperty.
  }
  do 2 (apply funextsec; intro).
  apply H1.
Qed.
