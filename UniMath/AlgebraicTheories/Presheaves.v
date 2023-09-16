Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(* The presheaf data type *)
Definition presheaf_data (T : algebraic_theory_data) : UU
  := ∑ A: (finite_set_skeleton_category ⟶ HSET),
    ∏ m n, (A m : hSet) → (stn m → (T n : hSet)) → (A n : hSet).

Coercion presheaf_data_to_functor {T : algebraic_theory_data} (A : presheaf_data T)
  : finite_set_skeleton_category ⟶ HSET
  := pr1 A.

Definition action {T} {A : presheaf_data T} {m n} : (A m : hSet) → (stn m → (T n : hSet)) → (A n : hSet) := pr2 A m n.

Definition make_presheaf_data {T : algebraic_theory_data}
  (A : finite_set_skeleton_category ⟶ HSET)
  (action : ∏ m n, (A m : hSet) → (stn m → (T n : hSet)) → (A n : hSet))
  : presheaf_data T
  := (A ,, action).

(* The presheaf type *)
Definition is_assoc {T : algebraic_theory_data} (A : presheaf_data T) : UU
  := ∏ l m n (a : (A l : hSet)) f (g : stn m → (T n : hSet)), action (action a f) g = action a (λ i, (f i) • g).

Definition identity_projections {T : algebraic_theory_data} (A : presheaf_data T) : UU
  := ∏ n (a : (A n : hSet)), action a (λ i, pr i) = a.

Definition action_is_natural {T : algebraic_theory_data} (A : presheaf_data T) : UU
  := ∏ m m' n (x : finite_set_skeleton_category⟦m, m'⟧) a (f : stn m' → T n : hSet),
  action (# A x a) f = action a (λ i, f (x i)).

Definition is_presheaf {T : algebraic_theory_data} (A : presheaf_data T) : UU :=
  is_assoc A ×
  identity_projections A ×
  action_is_natural A.

Definition make_is_presheaf
  {T : algebraic_theory_data}
  (A : presheaf_data T)
  (H1 : is_assoc A)
  (H2 : identity_projections A)
  (H3 : action_is_natural A)
  : is_presheaf A
  := H1 ,, H2 ,, H3.

Definition presheaf (T : algebraic_theory_data) : UU := ∑ (P : presheaf_data T), is_presheaf P.

Coercion presheaf_to_presheaf_data {T : algebraic_theory_data} (P : presheaf T) : presheaf_data T := pr1 P.

Definition make_presheaf
  {T : algebraic_theory_data}
  (P : presheaf_data T)
  (H : is_presheaf P)
  : presheaf T
  := P ,, H.

Lemma isaprop_is_presheaf {T : algebraic_theory_data} (A : presheaf_data T) : isaprop (is_presheaf A).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Definition presheaf_data_morphism {T : algebraic_theory_data} (P P' : presheaf_data T) : UU
  := ∑ F: P ⟹ P', (∏ m n a f, F n (action a f) = action (F m a) f).

Definition presheaf_morphism {T : algebraic_theory_data} (P P' : presheaf_data T) : UU
  := ∑ (F : presheaf_data_morphism P P'), unit.

Definition theory_presheaf (T : algebraic_theory)
  : presheaf T.
Proof.
  use make_presheaf.
  - use make_presheaf_data.
    + exact T.
    + intros ? ?.
      exact comp.
  - use make_is_presheaf.
    + exact (algebraic_theory_comp_is_assoc T).
    + exact (algebraic_theory_comp_identity_projections T).
    + exact (algebraic_theory_comp_is_natural_l T).
Defined.

(* Definition yoneda_lemma
  (T : algebraic_theory)
  (X : presheaf T)
  : (presheaf_cat T)⟦⟧ *)
