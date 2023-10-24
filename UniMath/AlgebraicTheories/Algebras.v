(**************************************************************************************************

  Algebras

  Defines what an algebra for an algebraic theory is, and gives constructors, accessors and
  some properties.

  Contents
  1. The definition of algebras [algebra]
  2. An alternate constructor for its properties [make_is_algebra']
  3. An equality lemma [algebra_eq]
  4. Some properties of algebras

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebras *)

Definition algebra_data
  (T : algebraic_theory_data)
  : UU
  := ∑ (A : hSet), ∏ (n : nat), (T n : hSet) → (stn n → A) → A.

Definition make_algebra_data
  {T : algebraic_theory_data}
  (A : hSet)
  (action : ∏ (n : nat), (T n : hSet) → (stn n → A) → A)
  : algebra_data T
  := (A ,, action).

Coercion algebra_data_to_hset
  {T : algebraic_theory_data}
  (A : algebra_data T)
  : hSet
  := pr1 A.

Definition action
  {T : algebraic_theory_data}
  {A : algebra_data T}
  {n : nat}
  : (T n : hSet) → (stn n → A) → A
  := pr2 A n.

Definition is_assoc
  {T : algebraic_theory_data}
  (A : algebra_data T)
  : UU
  := ∏ m n (f : (T m : hSet)) g (a : stn n → A), action (f • g) a = action f (λ i, action (g i) a).

Definition is_unital
  {T : algebraic_theory_data}
  (A : algebra_data T)
  : UU
  := ∏ (a : stn 1 → A), action id_pr a = a firstelement.

Definition is_natural
  {T : algebraic_theory_data}
  (A : algebra_data T)
  : UU
  := ∏ n n' t (f : (T n : hSet)) (a : stn n' → A),
  action (#T t f) a = action f (λ i, a (t i)).

Definition is_algebra
  {T : algebraic_theory_data}
  (A : algebra_data T) : UU :=
    is_assoc A ×
    is_unital A ×
    is_natural A.

Definition make_is_algebra
  {T : algebraic_theory_data}
  (A : algebra_data T)
  (H1 : is_assoc A)
  (H2 : is_unital A)
  (H3 : is_natural A)
  : is_algebra A
  := (H1 ,, H2 ,, H3).

Definition algebra
  (T : algebraic_theory_data)
  := ∑ (A : hSet) (action : ∏ (n : nat), (T n : hSet) → (stn n → A) → A),
    is_algebra (make_algebra_data A action).

Definition make_algebra
  {T : algebraic_theory_data}
  (A : algebra_data T)
  (H : is_algebra A)
  : algebra T
  := (pr1 A ,, pr2 A ,, H).

Coercion algebra_to_algebra_data
  {T : algebraic_theory_data}
  (A : algebra T)
  : algebra_data T
  := make_algebra_data (pr1 A) (pr12 A).

Definition algebra_is_assoc
  {T : algebraic_theory_data}
  (A : algebra T)
  : is_assoc A
  := pr122 A.

Definition algebra_is_unital
  {T : algebraic_theory_data}
  (A : algebra T)
  : is_unital A
  := pr1 (pr222 A).

Definition algebra_is_natural
  {T : algebraic_theory_data}
  (A : algebra T)
  : is_natural A
  := pr2 (pr222 A).

Lemma isaprop_is_algebra
  {T : algebraic_theory_data}
  (A : algebra_data T)
  : isaprop (is_algebra A).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

(** * 2. An alternate constructor for its properties *)

Lemma make_is_algebra'
  {T : algebraic_theory}
  {A : algebra_data T}
  (is_assoc : is_assoc A)
  (projects_component : ∏ n i (a : stn n → A), action (pr i) a = a i)
  : is_algebra A.
Proof.
  use make_is_algebra.
  - exact is_assoc.
  - intro.
    rewrite algebraic_theory_id_pr_is_pr.
    apply projects_component.
  - do 5 intro.
    rewrite algebraic_theory_functor_uses_projections, is_assoc.
    apply maponpaths, funextfun.
    intro.
    apply projects_component.
Qed.

(** * 3. An equality lemma *)

Lemma algebra_eq
  {T : algebraic_theory_data}
  (A B : algebra T)
  (H1 : (A : hSet) = (B : hSet))
  (H2 : ∏ n f, transportf (λ (X : hSet), (stn n → X) → X) H1 (action f) = action f)
  : A = B.
Proof.
  use total2_paths_f.
  - exact H1.
  - rewrite transportf_total2.
    use subtypePairEquality.
    {
      intro.
      apply isaprop_is_algebra.
    }
    rewrite transportf_sec_constant.
    apply funextsec.
    intro.
    rewrite transportf_sec_constant.
    apply funextsec.
    intro.
    apply H2.
Qed.

(** * 4. Some properties of algebras *)

Lemma lift_constant_action
  {T : algebraic_theory_data}
  {A : algebra T}
  (n : nat)
  (f : (T 0 : hSet))
  (a : stn n → A)
  : action (lift_constant n f) a = action f (weqvecfun _ vnil).
Proof.
  unfold lift_constant.
  rewrite algebra_is_assoc.
  apply maponpaths, funextfun.
  intro i.
  exact (fromempty (negnatlthn0 _ (stnlt i))).
Qed.

Lemma algebra_projects_component
  {T : algebraic_theory}
  (A : algebra T)
  : ∏ n i (a : stn n → A), action (pr i) a = a i.
Proof.
  intros.
  unfold pr.
  rewrite algebra_is_natural.
  apply algebra_is_unital.
Qed.
