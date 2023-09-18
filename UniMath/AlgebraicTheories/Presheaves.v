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
  := ∑ P: (finite_set_skeleton_category ⟶ HSET),
    ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet).

Coercion presheaf_data_to_functor {T : algebraic_theory_data} (P : presheaf_data T)
  : finite_set_skeleton_category ⟶ HSET
  := pr1 P.

Definition action {T} {P : presheaf_data T} {m n} : (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet) := pr2 P m n.

Definition make_presheaf_data {T : algebraic_theory_data}
  (P : finite_set_skeleton_category ⟶ HSET)
  (action : ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet))
  : presheaf_data T
  := (P ,, action).

(* The presheaf type *)
Definition is_assoc {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ l m n (a : (P l : hSet)) f (g : stn m → (T n : hSet)), action (action a f) g = action a (λ i, (f i) • g).

Definition identity_projections {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ n (a : (P n : hSet)), action a (λ i, pr i) = a.

Definition action_is_natural {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ m m' n (x : finite_set_skeleton_category⟦m, m'⟧) a (f : stn m' → T n : hSet),
  action (# P x a) f = action a (λ i, f (x i)).

Definition is_presheaf {T : algebraic_theory_data} (P : presheaf_data T) : UU :=
  is_assoc P ×
  identity_projections P ×
  action_is_natural P.

Definition make_is_presheaf
  {T : algebraic_theory_data}
  (P : presheaf_data T)
  (H1 : is_assoc P)
  (H2 : identity_projections P)
  (H3 : action_is_natural P)
  : is_presheaf P
  := H1 ,, H2 ,, H3.

Definition presheaf (T : algebraic_theory_data) : UU := ∑
  (P : finite_set_skeleton_category ⟶ HSET)
  (action : ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet)),
    is_presheaf (make_presheaf_data P action).

Coercion presheaf_to_presheaf_data {T : algebraic_theory_data} (P : presheaf T) : presheaf_data T := make_presheaf_data (pr1 P) (pr12 P).

Definition make_presheaf
  {T : algebraic_theory_data}
  (P : presheaf_data T)
  (H : is_presheaf P)
  : presheaf T
  := (pr1 P) ,, (pr2 P) ,, H.

Definition presheaf_is_assoc
  {T : algebraic_theory}
  (P : presheaf T)
  : is_assoc P
  := pr122 P.

Definition presheaf_identity_projections
  {T : algebraic_theory}
  (P : presheaf T)
  : identity_projections P
  := pr1 (pr222 P).

Definition presheaf_action_is_natural
  {T : algebraic_theory}
  (P : presheaf T)
  : action_is_natural P
  := pr2 (pr222 P).

Lemma isaprop_is_presheaf {T : algebraic_theory_data} (P : presheaf_data T) : isaprop (is_presheaf P).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Definition presheaf_morphism {T : algebraic_theory_data} (P P' : presheaf_data T) : UU
  := ∑ (F: P ⟹ P') (HF: ∏ m n a f, F n (action a f) = action (F m a) f), unit.

Definition presheaf_morphism_to_nat_trans
  {T : algebraic_theory}
  {P P' : presheaf T}
  (f : presheaf_morphism P P')
  : nat_trans P P'
  := pr1 f.

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
