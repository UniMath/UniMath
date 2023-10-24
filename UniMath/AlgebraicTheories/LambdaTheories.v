(**************************************************************************************************

  λ-theories

  A λ-theory is a model for the untyped λ-calculus. It is a structure with variables, substitution,
  abstraction and application. Here it is formalized as an algebraic theory L, with functions
  between the L n and L (S n) that are compatible with the substitution in some way.
  This file defines what a λ-theory is and gives accessors, constructors and defines what it means
  for a λ-theory to have β- and η-equality.

  Contents
  1. The definition of λ-theories [lambda_theory]
  2. An alternate constructor for the properties of a λ-theory [make_is_lambda_theory']
  3. The definition of β-equality [has_beta]
  4. The definiiton of η-equality [has_eta]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of λ-theories *)

Definition lambda_theory_data : UU
  := ∑ (T : algebraic_theory),
    (∏ n, (T n : hSet) → (T (S n) : hSet)) ×
    (∏ n, (T (S n) : hSet) → (T n : hSet)).

Definition make_lambda_theory_data
  (T : algebraic_theory)
  (abs : ∏ n, (T n : hSet) → (T (S n) : hSet))
  (app : ∏ n, (T (S n) : hSet) → (T n : hSet))
  : lambda_theory_data
  := T ,, abs ,, app.

Coercion lambda_theory_data_to_algebraic_theory (L : lambda_theory_data)
  : algebraic_theory
  := pr1 L.

Definition app {L : lambda_theory_data} {n : nat} : (L n : hSet) → (L (S n) : hSet) := pr12 L n.

Definition abs {L : lambda_theory_data} {n : nat} : (L (S n) : hSet) → (L n : hSet) := pr22 L n.

Definition extend_finite_morphism_with_identity
  {m n : finite_set_skeleton_category}
  (f : finite_set_skeleton_category⟦m, n⟧)
  : finite_set_skeleton_category⟦S m, S n⟧
  := extend_tuple (T := stn (S n)) (λ i, dni lastelement (f i)) lastelement.

Definition extended_composition
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T (S m) : hSet)
  (g : stn m → (T n : hSet))
  : (T (S n) : hSet)
  := f • (extend_tuple (λ i, #T (dni lastelement (n := n)) (g i)) (pr lastelement)).

Definition is_lambda_theory (L : lambda_theory_data) : UU :=
    (∏ m n (a : _⟦m, n⟧) l, app (#L a l) = #L (extend_finite_morphism_with_identity a) (app l)) ×
    (∏ m n (a : _⟦m, n⟧) l, abs (#L (extend_finite_morphism_with_identity a) l) = #L a (abs l)) ×
    (∏ m n f (g : stn m → (L n : hSet)), app (f • g) = extended_composition (app f) g) ×
    (∏ m n f (g : stn m → (L n : hSet)), abs (extended_composition f g) = (abs f) • g).

Definition make_is_lambda_theory
  {L : lambda_theory_data}
  (app_natural: ∏ m n (a : finite_set_skeleton_category⟦m, n⟧) l,
    app (#L a l) = #L (extend_finite_morphism_with_identity a) (app l))
  (abs_natural : ∏ m n (a : finite_set_skeleton_category⟦m, n⟧) l,
    abs (#L (extend_finite_morphism_with_identity a) l) = #L a (abs l))
  (app_comp : ∏ m n f (g : stn m → (L n : hSet)), app (f • g) = extended_composition (app f) g)
  (abs_comp : ∏ m n f (g : stn m → (L n : hSet)), abs (extended_composition f g) = (abs f) • g)
  : is_lambda_theory L
  := app_natural ,, abs_natural ,, app_comp ,, abs_comp.

Definition lambda_theory : UU := ∑ L, is_lambda_theory L.

Definition make_lambda_theory
  (L : lambda_theory_data)
  (H : is_lambda_theory L)
  : lambda_theory
  := L ,, H.

Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data := pr1 L.

Definition lambda_theory_app_is_natural
  {L : lambda_theory}
  {m n : nat}
  (a : finite_set_skeleton_category⟦m, n⟧)
  (l : (L m : hSet))
  : app (#L a l) = #L (extend_finite_morphism_with_identity a) (app l)
  := pr12 L m n a l.

Definition lambda_theory_abs_is_natural
  {L : lambda_theory}
  {m n : nat}
  (a : finite_set_skeleton_category⟦m, n⟧)
  (l : (L (S m) : hSet))
  : abs (#L (extend_finite_morphism_with_identity a) l) = #L a (abs l)
  := pr122 L m n a l.

Definition lambda_theory_app_compatible_with_comp
  {L : lambda_theory}
  {m n : nat}
  (f : (L m : hSet))
  (g : stn m → (L n : hSet))
  : app (f • g) = extended_composition (app f) g
  := pr1 (pr222 L) m n f g.

Definition lambda_theory_abs_compatible_with_comp
  {L : lambda_theory}
  {m n : nat}
  (f : (L (S m) : hSet))
  (g : stn m → (L n : hSet))
  : abs (extended_composition f g) = (abs f) • g
  := pr2 (pr222 L) m n f g.

Lemma isaprop_is_lambda_theory
  (L : lambda_theory_data)
  : isaprop (is_lambda_theory L).
Proof.
  repeat apply isapropdirprod;
  do 4 (apply impred; intro);
  apply setproperty.
Qed.

(** * 2. An alternate constructor for the properties of a λ-theory *)

Lemma make_is_lambda_theory'
  {L : lambda_theory_data}
  (app_comp : ∏ m n f (g : stn m → (L n : hSet)), app (f • g) = extended_composition (app f) g)
  (abs_comp : ∏ m n f (g : stn m → (L n : hSet)), abs (extended_composition f g) = (abs f) • g)
  : is_lambda_theory L.
Proof.
  use (make_is_lambda_theory _ _ app_comp abs_comp);
    intros m n a l;
    do 2 rewrite algebraic_theory_functor_uses_projections;
    [ rewrite app_comp;
      apply (maponpaths (λ x, (app l) • x))
    | rewrite <- abs_comp;
      apply (maponpaths (λ x, abs (l • x)));
      symmetry];
    (apply extend_tuple_eq;
    [ intro i;
      refine (algebraic_theory_functor_uses_projections _ _ _ _ _ @ _);
      refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _);
      apply maponpaths;
      symmetry;
      exact (extend_tuple_inl _ _ _)
    | apply maponpaths;
      symmetry;
      apply extend_tuple_inr ] ).
Qed.

(** * 3. The definition of β-equality *)

Definition has_beta (L : lambda_theory) : UU
  := ∏ n (l : (L (S n) : hSet)), app (abs l) = l.

(** * 4. The definiiton of η-equality *)

Definition has_eta (L : lambda_theory) : UU
  := ∏ n (l : (L n : hSet)), abs (app l) = l.
