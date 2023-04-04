Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.AlgebraicTheories.

Local Open Scope cat.

Definition algebraic_theory_morphism_data (T T' : algebraic_theory_data) := ∏ n, T n → T' n.

Definition algebraic_theory_morphism_data_to_function {T T'} (F : algebraic_theory_morphism_data T T')
  : ∏ n, T n → T' n
  := F.

Coercion algebraic_theory_morphism_data_to_function : algebraic_theory_morphism_data >-> Funclass.

Definition algebraic_theory_morphism_data_to_nat_trans_data
  {T T'}
  (F : algebraic_theory_morphism_data T T')
  : nat_trans_data
    (algebraic_theory_data_to_functor_data T)
    (algebraic_theory_data_to_functor_data T')
  := F.

Definition preserves_projections {T T'} (F : algebraic_theory_morphism_data T T') : UU := ∏
  (n : finite_set_skeleton_category)
  (i : stn n),
    (F n (theory_pr i)) = (theory_pr i).

Definition preserves_composition {T T'} (F : algebraic_theory_morphism_data T T') : UU := ∏
  (m n : finite_set_skeleton_category)
  (f_m : T m)
  (f_n : stn m → T n),
  (F n (comp f_m f_n)) = (comp (F m f_m) (λ i, F n (f_n i))).

Definition is_algebraic_theory_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism_data T T')
  : UU :=
    is_nat_trans _ _ (algebraic_theory_morphism_data_to_nat_trans_data F) ×
    preserves_projections F ×
    preserves_composition F.

Definition make_is_algebraic_theory_morphism {T T' : algebraic_theory} 
  (F : algebraic_theory_morphism_data T T')
  (H1 : is_nat_trans _ _ (algebraic_theory_morphism_data_to_nat_trans_data F))
  (H2 : preserves_projections F)
  (H3 : preserves_composition F) := (H1 ,, H2 ,, H3).

Lemma isaprop_is_algebraic_theory_morphism 
  {T T' : algebraic_theory} 
  (F : algebraic_theory_morphism_data T T')
  : isaprop (is_algebraic_theory_morphism F).
Proof.
  intro.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    try apply funspace_isaset;
    apply setproperty.
Qed.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := ∑ F : algebraic_theory_morphism_data T T', is_algebraic_theory_morphism F.

Definition make_algebraic_theory_morphism 
  {T T' : algebraic_theory} 
  (F : algebraic_theory_morphism_data T T') 
  (H : is_algebraic_theory_morphism F)
  : algebraic_theory_morphism T T'
  := (F ,, H).

Coercion algebraic_theory_morphism_to_algebraic_theory_morphism_data 
  {T T'} 
  (F : algebraic_theory_morphism T T')
  : algebraic_theory_morphism_data T T'
  := pr1 F.

Definition algebraic_theory_morphism_is_nat_trans {T T'} (F : algebraic_theory_morphism T T') : is_nat_trans _ _ (algebraic_theory_morphism_data_to_nat_trans_data F) := pr12 F.

Definition algebraic_theory_morphism_preserves_projections {T T'} (F : algebraic_theory_morphism T T') : preserves_projections F := pr122 F.

Definition algebraic_theory_morphism_preserves_composition {T T'} (F : algebraic_theory_morphism T T') : preserves_composition F := pr222 F.

Definition algebraic_theory_morphism_to_nat_trans 
  {T T'} 
  (F : algebraic_theory_morphism T T')
  : (algebraic_theory_to_functor T) ⟹ (algebraic_theory_to_functor T')
  := make_nat_trans _ _ _ (algebraic_theory_morphism_is_nat_trans F).

Lemma algebraic_theory_morphism_eq 
  {T T'} 
  (F F' : algebraic_theory_morphism T T') 
  (H1 : ∏ n f, F n f = F' n f)
  : F = F'.
Proof.
  use (subtypePairEquality' _ (isaprop_is_algebraic_theory_morphism _)).
  do 2 (apply funextsec; intro).
  apply H1.
Qed.
