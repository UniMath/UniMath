(**************************************************************************************************

  Constructing a λ-theory from an algebra for the pure λ-calculus

  Given a Λ-algebra A (an algebra for the pure λ-calculus), one can construct a λ-theory. This file
  formalizes this construction. For the construction, we first take the set A1 of 1-functional
  elements: the elements f that are equal to λ x, f x, so the elements that have η-equality at least
  once. Function composition gives this set a monoid structure. We then consider the category of
  sets with a right action from this monoid. Of course, the monoid A1 itself can be considered as an
  object in this category. We obtain the λ-theory as the endomorphism theory of this object A1.
  To construct the endomorphism theory, we need A1 to be a reflexive object: we need A1^A1 to be a
  retract of A1 itself. We obtain this by noticing that the exponential object A1^A1 is isomorphic
  to A2 (the set of 2-functional elements), and that A2 is a retract of A1 (with the retraction
  given by precomposing elements with λ x y, x y).

  Contents
  1. The construction of the monoid [lambda_algebra_monoid]
  2. The construction of the λ-theory with β-equality
    [lambda_algebra_theory] [lambda_algebra_theory_has_beta]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.Combinators.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidActions.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.

Local Open Scope cat.
Local Open Scope vec.
Local Open Scope algebraic_theories.
Local Open Scope lambda_calculus.
Local Open Scope stn.

(** * 1. The construction of the monoid *)

Section AlgebraToTheory.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).
  Context (A : algebra L).

  Let maction {M : monoid} {X : monoid_action M}
    : (∏ x m, MonoidActions.action_ax M X x m)
    := MonoidActions.action.
  Let aaction {n : nat}
    : (∏ f a, AlgebraCategoryCore.action_ax L A n f a)
    := Algebras.action (n := n).

  Definition compose
    (a b : A)
    : A
    := aaction (compose (var (● 0 : stn 2)) (var (● 1 : stn 2))) (weqvecfun _ [(a ; b)]).

  Lemma compose_assoc
    (a b c : A)
    : compose a (compose b c) = compose (compose a b) c.
  Proof.
    unfold compose, aaction.
    pose (v := weqvecfun _ [(a ; b ; c)]).
    pose (Hv := λ i, !(var_action _ (i : stn 3) v)).
    rewrite (Hv (● 0) : a = _).
    rewrite (Hv (● 1) : b = _).
    rewrite (Hv (● 2) : c = _).
    do 4 (rewrite (move_action_through_vector_2 A _ _ _), <- subst_action).
    apply (maponpaths (λ x, aaction x v)).
    do 4 rewrite subst_compose.
    do 8 rewrite (var_subst L).
    apply compose_assoc.
    exact Lβ.
  Qed.

  Definition I1
    : A
    := aaction (U_term L) (weqvecfun _ vnil).

  Lemma I1_idempotent
    : compose I1 I1 = I1.
  Proof.
    unfold compose, I1, aaction.
    rewrite (move_action_through_vector_2 A _ _ _).
    rewrite <- subst_action.
    apply (maponpaths (λ x, aaction x _)).
    rewrite subst_compose.
    do 2 rewrite (var_subst L).
    apply (U_compose _ Lβ).
  Qed.

  Definition make_functional_1 (a : A)
    : A
    := compose I1 a.

  Definition is_functional_1 (a: A)
    : UU
    := a = make_functional_1 a.

  Lemma isaprop_is_functional_1 (a : A) : isaprop (is_functional_1 a).
  Proof.
    apply setproperty.
  Qed.

  Lemma is_functional_1_action_abs
    {n : nat}
    (f : (L (S n) : hSet))
    (v : stn n → A)
    : is_functional_1 (aaction (abs f : ((L n) : hSet)) v).
  Proof.
    unfold is_functional_1, make_functional_1, compose, I1, aaction.
    rewrite <- (lift_constant_action _ _ v).
    rewrite (move_action_through_vector_2 A _ _ v).
    rewrite <- subst_action.
    apply (maponpaths (λ x, aaction x _)).
    rewrite subst_compose.
    do 2 rewrite (var_subst L).
    refine (_ @ !maponpaths (λ x, x ∘ _) (subst_U_term _ _)).
    apply (!U_compose L Lβ _).
  Qed.

  Definition functional_1_set
    : hSet.
  Proof.
    use (total2_hSet (X := A)).
    intro a.
    exists (is_functional_1 a).
    abstract exact (isasetaprop (isaprop_is_functional_1 _)).
  Defined.

  Definition functional_1_eq
    (a a' : functional_1_set)
    (H : pr1 a = pr1 a')
    : a = a'.
  Proof.
    apply subtypePairEquality.
    {
      intro.
      apply isaprop_is_functional_1.
    }
    exact H.
  Qed.

  Section Monoid.

    Lemma is_functional_1_compose
      (a b : A)
      : is_functional_1 (compose a b).
    Proof.
      unfold is_functional_1.
      unfold make_functional_1.
      unfold I1.
      unfold compose.
      set (v := weqvecfun _ [(a ; b)]).
      rewrite <- (lift_constant_action _ _ v).
      rewrite (move_action_through_vector_2 A _ _ v).
      rewrite <- (subst_action A).
      apply (maponpaths (λ x, aaction x _)).
      rewrite subst_compose.
      do 2 rewrite (var_subst L).
      refine (_ @ !maponpaths (λ x, x ∘ _) (subst_U_term _ _)).
      exact (!U_compose _ Lβ _).
    Qed.

    Definition is_functional_1_I1
      : is_functional_1 I1
      := !I1_idempotent.

    Lemma is_runit_I1
      (a : A)
      : compose a (I1) = make_functional_1 a.
    Proof.
      pose (Ha := (var_action _ (● 0 : stn 1) (weqvecfun 1 [(a)]))).
      refine (!_ @ maponpaths _ Ha).
      refine (!_ @ maponpaths (λ x, _ x _) Ha).
      unfold make_functional_1, compose, I1, aaction.
      rewrite <- (lift_constant_action 1 _ (weqvecfun 1 [(a)])).
      rewrite (move_action_through_vector_2 A (var _) _ _).
      rewrite (move_action_through_vector_2 A _ (var _) _).
      do 2 rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x _)).
      refine (subst_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, x ∘ _) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ x) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ x) (subst_U_term _ _) @ _).
      refine (_ @ !subst_compose _ _ _ (weqvecfun _ [(_ ; var _)])).
      refine (_ @ !maponpaths (λ x, x ∘ _) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, _ ∘ x) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, x ∘ _) (subst_U_term _ _)).
      cbn.
      unfold U_term.
      rewrite (compose_abs _ Lβ).
      rewrite (abs_compose _ Lβ).
      rewrite (var_subst L).
      now rewrite extend_tuple_inr.
    Qed.

    Lemma is_unit_I1
      : isunit
        (λ a b, compose (pr1 a) (pr1 b) ,, is_functional_1_compose (pr1 a) (pr1 b))
        (I1 ,, is_functional_1_I1).
    Proof.
      split;
        intro a;
        apply functional_1_eq;
        refine (_ @ !pr2 a).
      - apply idpath.
      - apply is_runit_I1.
    Qed.

    Definition lambda_algebra_monoid : monoid.
    Proof.
      use tpair.
      - use tpair.
        + exact functional_1_set.
        + intros a b.
          exact (compose (pr1 a) (pr1 b) ,, is_functional_1_compose (pr1 a) (pr1 b)).
      - split.
        + abstract (
            intros a b c;
            apply functional_1_eq;
            apply (!compose_assoc _ _ _)
          ).
        + exact (_ ,, is_unit_I1).
    Defined.

  End Monoid.

(** * 2. The construction of the λ-theory with β-equality *)

  Section Theory.

    Definition UU_term
      : L 0
      := exponential_term L (U_term L) (U_term L).

    Definition I2
      : A
      :=
      aaction UU_term (weqvecfun _ vnil).

    Lemma I2_idempotent
      : compose I2 I2 = I2.
    Proof.
      unfold compose, I2, aaction.
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x _)).
      rewrite subst_compose.
      do 2 rewrite (var_subst L).
      exact (exponential_idempotent L Lβ (U L Lβ) (U L Lβ)).
    Qed.

    Definition make_functional_2 (a : A)
      : A
      := compose I2 a.

    Definition is_functional_2 (a: A)
      : UU
      := a = make_functional_2 a.

    Lemma is_functional_2_action_abs
      {n : nat}
      (f : (L (S (S n)) : hSet))
      (p : stn n → A)
      : is_functional_2 (aaction (abs (abs f) : ((L n) : hSet)) p).
    Proof.
      unfold is_functional_2, make_functional_2, compose, I2, aaction.
      rewrite <- (lift_constant_action _ _ p).
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x _)).
      refine (_ @ !subst_compose _ _ _ _).
      refine (_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, x ∘ _) (subst_exponential_term _ _ _ _)).
      refine (_ @ !maponpaths (λ x, (exponential_term _ x x ∘ _)) (subst_U_term _ _)).
      refine (_ @ !maponpaths (λ x, x ∘ _) (exponential_term_is_compose L Lβ _ _)).
      refine (_ @ !compose_abs L Lβ _ _ ).
      refine (_ @ !maponpaths (λ x, (abs (app x _))) (inflate_abs _ _)).
      refine (_ @ !maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _)).
      refine (_ @ !maponpaths (λ x, (abs x)) (subst_subst _ _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs x)) (subst_compose _ _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs (x ∘ _))) (subst_compose _ _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs (_ ∘ x))) (subst_inflate _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs ((x ∘ _) ∘ _))) (subst_inflate _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs ((_ ∘ x) ∘ _))) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs ((_ ∘ (x • _)) ∘ _))) (extend_tuple_inr _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs ((_ ∘ x) ∘ _))) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs ((_ ∘ x) ∘ _))) (extend_tuple_inr _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs (x ∘ _ ∘ x))) (subst_U_term _ _)).
      refine (_ @ !maponpaths (λ x, (abs (x ∘ _))) (U_compose L Lβ _)).
      exact (!maponpaths (λ x, (abs x)) (compose_U L Lβ _)).
    Qed.

    Lemma isaprop_is_functional_2 (a : A) : isaprop (is_functional_2 a).
    Proof.
      apply setproperty.
    Qed.

    Definition functional_2_set
      : hSet.
    Proof.
      refine (∑ (a : A), make_hSet (is_functional_2 a) _)%set.
      abstract exact (isasetaprop (isaprop_is_functional_2 _)).
    Defined.

    Definition functional_2_eq
      (a a' : functional_2_set)
      (H : pr1 a = pr1 a')
      : a = a'.
    Proof.
      apply subtypePairEquality.
      {
        intro.
        apply isaprop_is_functional_2.
      }
      exact H.
    Qed.

    Definition compose_I1_I2
      : compose I1 I2 = I2
      := !is_functional_1_action_abs _ _.

    Lemma is_functional_2_to_is_functional_1
      (a : A)
      (H : is_functional_2 a)
      : is_functional_1 a.
    Proof.
      rewrite H.
      unfold is_functional_1, make_functional_1, make_functional_2.
      rewrite compose_assoc.
      now rewrite compose_I1_I2.
    Qed.

    Lemma is_functional_2_compose
      (a : functional_2_set)
      (m : A)
      : is_functional_2 (compose (pr1 a) m).
    Proof.
      unfold is_functional_2, make_functional_2.
      rewrite compose_assoc.
      exact (maponpaths (λ x, _ x _) (pr2 a)).
    Qed.

    Definition functional_2_monoid_action_data
      : monoid_action_data lambda_algebra_monoid.
    Proof.
      use make_monoid_action_data.
      - exact functional_2_set.
      - intros a m.
        exists (compose (pr1 a) (pr1 m)).
        apply is_functional_2_compose.
    Defined.

    Lemma functional_2_is_monoid_action
      : is_monoid_action functional_2_monoid_action_data.
    Proof.
      split.
      - intro x.
        apply functional_2_eq.
        simpl.
        apply (maponpaths pr1
          (runax lambda_algebra_monoid (_ ,, is_functional_2_to_is_functional_1 _ (pr2 x)))
        ).
      - intros.
        apply functional_2_eq.
        exact (compose_assoc _ _ _).
    Qed.

    Definition functional_2_monoid_action
      : monoid_action lambda_algebra_monoid
      := make_monoid_action _ functional_2_is_monoid_action.

    Definition functional_2_to_monoid_action_morphism_data_term
      (d : functional_2_monoid_action)
      (a b : A)
      : A.
    Proof.
      pose (p := (weqvecfun _ [(pr1 d ; a ; b)])).
      refine (aaction _ p).
      refine (uncurry (var (● 0 : stn 3)) ∘ pair_arrow (var (● 1 : stn 3)) (var (● 2 : stn 3))).
    Defined.

    Definition functional_2_to_monoid_action_morphism_data
      (d : functional_2_monoid_action)
      : (BinProductObject _ (binproducts_monoid_action_cat lambda_algebra_monoid
          (monoid_monoid_action _)
          (monoid_monoid_action _)
        ) : monoid_action _)
        →
        (monoid_monoid_action lambda_algebra_monoid)
      := λ x, (
        functional_2_to_monoid_action_morphism_data_term d (pr11 x) (pr12 x) ,,
        is_functional_1_action_abs _ _
      ).

    Lemma functional_2_to_monoid_action_is_morphism
      (d : functional_2_monoid_action)
      : ∏ x m, mor_action_ax (functional_2_to_monoid_action_morphism_data d) x m.
    Proof.
      intros x m.
      apply functional_1_eq.
      unfold functional_2_to_monoid_action_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data_term.
      cbn -[weqvecfun aaction].
      pose (p := weqvecfun _ [(pr1 m ; pr1 d ; pr11 x ; pr12 x)]).
      unfold compose, aaction.
      rewrite <- (var_action _ (● 0 : stn 4) p : _ = pr1 m).
      rewrite <- (var_action _ (● 1 : stn 4) p : _ = pr1 d).
      rewrite <- (var_action _ (● 2 : stn 4) p : _ = pr11 x).
      rewrite <- (var_action _ (● 3 : stn 4) p : _ = pr12 x).
      do 2 (rewrite (move_action_through_vector_2 A _ _ _)).
      do 2 (rewrite <- subst_action).
      do 2 (rewrite (move_action_through_vector_3 A _ _ _ _)).
      do 2 (rewrite <- subst_action).
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x p)).
      refine (subst_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, (x ∘ _)) (subst_uncurry _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ x)) (subst_pair_arrow _ _ _ _) @ _).
      refine (maponpaths (λ x, uncurry x ∘ _) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow x _) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow x _) (subst_compose _ _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow (x ∘ _) _) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow (_ ∘ x) _) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow _ x) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow _ x) (subst_compose _ _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow _ (x ∘ _)) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, _ ∘ pair_arrow _ (_ ∘ x)) (var_subst _ _ _) @ _).
      refine (_ @ !subst_compose _ (var _) _ _).
      refine (_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (x ∘ _)) (subst_compose _ _ _ _)).
      refine (_ @ !maponpaths (λ x, ((x ∘ _) ∘ _)) (subst_uncurry _ _ _)).
      refine (_ @ !maponpaths (λ x, ((_ ∘ x) ∘ _)) (subst_pair_arrow _ _ _ _)).
      refine (_ @ !maponpaths (λ x, uncurry x ∘ _ ∘ _) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, _ ∘ pair_arrow x _ ∘ _) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, _ ∘ pair_arrow _ x ∘ _) (var_subst _ _ _)).
      refine (_ @ Combinators.compose_assoc _ Lβ _ _ _).
      exact (!maponpaths (λ x, _ ∘ x) (pair_arrow_compose _ Lβ _ _ _)).
    Qed.

    Definition functional_2_to_exponential_object_morphism_data
      : functional_2_monoid_action →
        (exponential_object (monoid_monoid_action _) (monoid_monoid_action _))
      := λ d, make_monoid_action_morphism _ (functional_2_to_monoid_action_is_morphism d).

    Definition exponential_object_to_functional_2_term
      (f : (
        exponential_object
          (monoid_monoid_action lambda_algebra_monoid)
          (monoid_monoid_action lambda_algebra_monoid)
      ))
      : A.
    Proof.
      refine (aaction (curry (var (stnweq (inr tt)))) (weqvecfun _ [(_)])).
      apply (f : monoid_action_morphism _ _).
      split.
      - exact (aaction π1 (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
      - exact (aaction π2 (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
    Defined.

    Definition exponential_object_to_functional_2_morphism_data
      : (exponential_object (monoid_monoid_action _) (monoid_monoid_action _))
        →
        functional_2_monoid_action
      := λ x, (exponential_object_to_functional_2_term x ,, is_functional_2_action_abs _ _).

    Lemma functional_2_to_exponential_object_is_morphism
      : ∏ x m, mor_action_ax functional_2_to_exponential_object_morphism_data x m.
    Proof.
      intros a m.
      apply monoid_action_morphism_eq.
      intro x.
      apply functional_1_eq.
      unfold functional_2_to_exponential_object_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data.
      unfold functional_2_to_monoid_action_morphism_data_term.
      cbn -[weqvecfun aaction].
      set (p := weqvecfun _ [(pr1 a ; pr1 m ; pr11 x ; pr12 x)]).
      rewrite <- (var_action _ (● 0 : stn 4) p : _ = pr1 a).
      rewrite <- (var_action _ (● 1 : stn 4) p : _ = pr1 m).
      rewrite <- (var_action _ (● 2 : stn 4) p : _ = pr11 x).
      rewrite <- (var_action _ (● 3 : stn 4) p : _ = pr12 x).
      unfold compose, aaction.
      do 2 (rewrite (move_action_through_vector_2 A _ _ _)).
      do 2 (rewrite <- subst_action).
      do 2 (rewrite (move_action_through_vector_3 A _ _ _ _)).
      do 2 (rewrite <- subst_action).
      apply (maponpaths (λ x, aaction x p)).
      refine (subst_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, (x ∘ _)) (subst_uncurry _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ x)) (subst_pair_arrow _ _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry x) ∘ _)) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ (pair_arrow x _))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ (pair_arrow _ x))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry x) ∘ _)) (subst_compose _ _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry (x ∘ _)) ∘ _)) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry (_ ∘ x)) ∘ _)) (var_subst _ _ _) @ _).
      refine (uncurry_compose_pair_arrow _ Lβ _ _ _ @ _).
      refine (maponpaths (λ x, (abs (app (app x _) _))) (inflate_compose _ _ _) @ _).
      refine (maponpaths (λ x, (abs (app x _))) (app_compose _ Lβ _ _ _) @ _).
      refine (_ @ !subst_compose L _ _ (weqvecfun 3 [( _ ; (_ ∘ _) • _ ; _)])).
      refine (_ @ !maponpaths (λ x, (x ∘ _)) (subst_uncurry _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ x)) (subst_pair_arrow _ _ _ _)).
      refine (_ @ !maponpaths (λ x, ((uncurry x) ∘ _)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ (pair_arrow x _))) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ (pair_arrow _ x))) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ (pair_arrow x _))) (subst_compose _ _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ (pair_arrow (x ∘ _) _))) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (_ ∘ (pair_arrow (_ ∘ x) _))) (var_subst _ _ _)).
      refine (_ @ !uncurry_compose_pair_arrow _ Lβ _ _ _).
      refine (_ @ !maponpaths (λ x, (abs (app (app _ (app x _)) _))) (inflate_compose _ _ _)).
      exact (!maponpaths (λ x, (abs (app (app _ x) _))) (app_compose _ Lβ _ _ _)).
    Qed.

    Definition term_2
      (a a' : A)
      := (aaction (pair_arrow (var (● 0 : stn 2)) (var (● 1 : stn 2))) (weqvecfun _ [(a ; a')]) ,, is_functional_1_action_abs _ _).

    Lemma compose_2_term_1
      (b : monoid_monoid_action lambda_algebra_monoid)
      (a a' : A)
      : functional_2_to_monoid_action_morphism_data_term
        (aaction (curry (var (● 0 : stn 1))) (weqvecfun 1 [(pr1 b)]) ,, is_functional_2_action_abs _ _)
        a
        a'
      = pr1 (maction b (term_2 a a')).
    Proof.
      unfold functional_2_to_monoid_action_morphism_data_term.
      cbn -[weqvecfun aaction].
      set (p := weqvecfun _ [(pr1 b; a; a')]).
      unfold functional_2_to_monoid_action_morphism_data_term, compose, aaction.
      rewrite <- (var_action _ (● 0 : stn 3) p : _ = pr1 b).
      rewrite <- (var_action _ (● 1 : stn 3) p : _ = a).
      rewrite <- (var_action _ (● 2 : stn 3) p : _ = a').
      rewrite (move_action_through_vector_1 A _ _).
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      rewrite <- subst_action.
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite (move_action_through_vector_3 A _ _ _ _).
      rewrite <- subst_action.
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x p)).
      refine (subst_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, (x ∘ _)) (subst_uncurry _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ x)) (subst_pair_arrow _ _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry x) ∘ _)) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ (pair_arrow x _))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (_ ∘ (pair_arrow _ x))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry x) ∘ _)) (subst_curry _ _ _) @ _).
      refine (maponpaths (λ x, ((uncurry (curry x)) ∘ _)) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (x ∘ _)) (uncurry_curry _ Lβ _) @ _).
      refine (!Combinators.compose_assoc _ Lβ _ _ _ @ _).
      refine (maponpaths (λ x, (_ ∘ x)) (pair_arrow_compose _ Lβ _ _ _) @ _).
      refine (_ @ !subst_compose _ (var _) _ _).
      refine (_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _)).
      apply maponpaths.
      refine (maponpaths (λ x, (pair_arrow x _)) (π1_pair_arrow' _ Lβ _ _) @ _).
      refine (maponpaths (λ x, (pair_arrow _ x)) (π2_pair_arrow' _ Lβ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app x _), _⟩))) (inflate_abs _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (inflate_abs _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨x, _⟩))) (beta_equality _ Lβ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, x⟩))) (beta_equality _ Lβ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨x, _⟩))) (subst_subst _ _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, x⟩))) (subst_subst _ _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨x, _⟩))) (subst_app _ _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, x⟩))) (subst_app _ _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app x _), _⟩))) (subst_inflate _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (subst_inflate _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app x _), _⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app _ (x • _)), _⟩))) (extend_tuple_inr _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app _ (x • _))⟩))) (extend_tuple_inr _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app (x • _) _), _⟩))) (extend_tuple_inl _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app (x • _) _)⟩))) (extend_tuple_inl _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app x _), _⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (extend_tuple_inr _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (var_subst _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (extend_tuple_inr _ _ _) @ _).
      refine (maponpaths (λ x, (abs (⟨(app x _), _⟩))) (extend_tuple_inl _ _ _) @ _).
      refine (_ @ !var_subst _ _ _).
      refine (_ @ !subst_pair_arrow _ _ _ _).
      refine (_ @ !maponpaths (λ x, (pair_arrow x _)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (pair_arrow _ x)) (var_subst _ _ _)).
      refine (_ @ !maponpaths (λ x, (abs (⟨(app x _), _⟩))) (inflate_var _ _)).
      refine (_ @ !maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (inflate_var _ _)).
      exact (maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (extend_tuple_inl _ _ _)).
    Qed.

    Lemma is_z_iso_functional_2_exponential_object
      : is_inverse_in_precat
        (C := HSET)
        functional_2_to_exponential_object_morphism_data
        exponential_object_to_functional_2_morphism_data.
    Proof.
      split.
      - apply funextfun.
        intro a.
        apply functional_2_eq.
        set (p := weqvecfun _ [(pr1 a)]).
        unfold exponential_object_to_functional_2_morphism_data.
        unfold functional_2_to_exponential_object_morphism_data.
        unfold functional_2_to_monoid_action_morphism_data.
        unfold exponential_object_to_functional_2_term.
        unfold functional_2_to_monoid_action_morphism_data_term.
        cbn -[weqvecfun aaction].
        rewrite (pr2 a).
        rewrite <- (var_action _ (make_stn 1 0 (idpath true)) p : _ = pr1 a).
        unfold make_functional_2, compose, I2, aaction.
        do 3 (rewrite <- (lift_constant_action _ _ p)).
        rewrite (move_action_through_vector_2 A _ _ _).
        rewrite <- subst_action.
        rewrite (move_action_through_vector_3 A _ _ _ _).
        rewrite <- subst_action.
        rewrite (move_action_through_vector_1 A _ _).
        rewrite <- subst_action.
        apply (maponpaths (λ x, aaction x p)).
        refine (subst_curry _ _ _ @ _).
        refine (maponpaths (λ x, (curry x)) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry x)) (subst_compose _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry (x ∘ _))) (subst_uncurry _ _ _) @ _).
        refine (maponpaths (λ x, (curry (_ ∘ x))) (subst_pair_arrow _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry ((uncurry x) ∘ _))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry ((uncurry x) ∘ _))) (subst_compose _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry ((uncurry (x ∘ _)) ∘ _))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry ((uncurry (_ ∘ x)) ∘ _))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry (_ ∘ (pair_arrow x _)))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry (_ ∘ (pair_arrow x _)))) (subst_π1 _ _) @ _).
        refine (maponpaths (λ x, (curry (_ ∘ (pair_arrow _ x)))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry (_ ∘ (pair_arrow _ x)))) (subst_π2 _ _) @ _).
        refine (!maponpaths (λ x, (curry x)) (uncurry_curry _ Lβ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (x ∘ _)))))) (subst_exponential_term _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry ((exponential_term _ x x) ∘ _)))))) (subst_U_term _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (x ∘ _)))))) (exponential_term_is_compose _ Lβ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry ((abs (x ∘ _ ∘ x)) ∘ _)))))) (subst_U_term _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry x))))) (abs_compose _ Lβ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs x)))))) (subst_compose _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs (x ∘ _))))))) (subst_compose _ _ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs ((_ ∘ x) ∘ _))))))) (var_subst _ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs ((_ ∘ x) ∘ _))))))) (extend_tuple_inr _ _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs ((_ ∘ (app x _)) ∘ _))))))) (inflate_var _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry (curry (uncurry (abs (x ∘ _ ∘ x))))))) (subst_U_term _ _) @ _).
        refine (maponpaths (λ x, (curry (uncurry x))) (curry_uncurry _ Lβ _) @ _).
        refine (_ @ !subst_compose _ _ _ _).
        refine (_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _)).
        refine (_ @ !maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _)).
        refine (_ @ !maponpaths (λ x, (x ∘ _)) (subst_exponential_term _ _ _ _)).
        refine (_ @ !maponpaths (λ x, ((exponential_term _ x x) ∘ _)) (subst_U_term _ _)).
        refine (_ @ !maponpaths (λ x, (x ∘ _)) (exponential_term_is_compose _ Lβ _ _)).
        refine (_ @ !maponpaths (λ x, ((abs (x ∘ _ ∘ x)) ∘ _)) (subst_U_term _ _)).
        refine (_ @ !abs_compose _ Lβ _ _).
        refine (_ @ !maponpaths (λ x, (abs x)) (subst_compose _ _ _ _)).
        refine (_ @ !maponpaths (λ x, (abs (x ∘ _))) (subst_compose _ _ _ _)).
        refine (_ @ !maponpaths (λ x, (abs ((_ ∘ x) ∘ _))) (var_subst _ _ _)).
        refine (_ @ !maponpaths (λ x, (abs ((_ ∘ x) ∘ _))) (extend_tuple_inr _ _ _)).
        refine (_ @ !maponpaths (λ x, (abs ((_ ∘ (app x _)) ∘ _))) (inflate_var _ _)).
        refine (_ @ !maponpaths (λ x, (abs (x ∘ _ ∘ x))) (subst_U_term _ _)).
        apply (curry_uncurry _ Lβ).
      - apply funextfun.
        intro f.
        apply monoid_action_morphism_eq.
        intro a.
        apply functional_1_eq.
        refine (compose_2_term_1 _ _ _ @ _).
        refine (!base_paths _ _ (mor_action f _ _) @ _).
        do 2 (apply maponpaths).
        set (p := weqvecfun _ [(pr11 a ; pr12 a)]).
        apply pathsdirprod;
          apply functional_1_eq;
          [ refine (_ @ !pr21 a)
          | refine (_ @ !pr22 a) ];
          cbn -[weqvecfun aaction];
          unfold make_functional_1, compose, I1, aaction;
          rewrite <- (var_action _ (● 0 : stn 2) p : _ = pr11 a);
          rewrite <- (var_action _ (● 1 : stn 2) p : _ = pr12 a);
          do 2 (rewrite <- (lift_constant_action _ _ p));
          do 2 (rewrite (move_action_through_vector_2 A _ _ _));
          do 2 (rewrite <- subst_action);
          rewrite (move_action_through_vector_2 A _ _ _);
          rewrite <- subst_action;
          apply (maponpaths (λ x, aaction x p));
          refine (subst_compose _ _ _ _ @ _);
          refine (maponpaths (λ x, (x ∘ _)) (var_subst _ _ _) @ _);
          refine (maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _) @ _);
          refine (maponpaths (λ x, (_ ∘ x)) (subst_pair_arrow _ _ _ _) @ _);
          refine (maponpaths (λ x, (_ ∘ (pair_arrow x _))) (var_subst _ _ _) @ _);
          refine (maponpaths (λ x, (_ ∘ (pair_arrow _ x))) (var_subst _ _ _) @ _);
          refine (_ @ !subst_compose _ _ _ (weqvecfun _ [(_ ; var _)]));
          refine (_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _));
          refine (_ @ !maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _));
          refine (_ @ !maponpaths (λ x, (x ∘ _)) (subst_U_term _ _));
          refine (_ @ !abs_compose _ Lβ _ _);
          refine (_ @ !maponpaths (λ x, (abs x)) (var_subst _ _ _));
          refine (_ @ !maponpaths (λ x, (abs x)) (extend_tuple_inr _ _ _)).
        + refine (maponpaths (λ x, (x ∘ _)) (subst_π1 _ _) @ _).
          apply (π1_pair_arrow' _ Lβ).
        + refine (maponpaths (λ x, (x ∘ _)) (subst_π2 _ _) @ _).
          apply (π2_pair_arrow' _ Lβ).
    Qed.

    Definition universal_monoid_exponential_iso
      : z_iso (C := monoid_action_cat lambda_algebra_monoid)
        functional_2_monoid_action
        (exponential_object (monoid_monoid_action _) (monoid_monoid_action _)).
    Proof.
      use make_monoid_action_z_iso.
      - use make_z_iso.
        + exact functional_2_to_exponential_object_morphism_data.
        + exact exponential_object_to_functional_2_morphism_data.
        + exact is_z_iso_functional_2_exponential_object.
      - exact functional_2_to_exponential_object_is_morphism.
    Defined.

    Definition functional_app
      : monoid_action_morphism (monoid_monoid_action _) functional_2_monoid_action.
    Proof.
      use make_monoid_action_morphism.
      - intro a.
        exists (compose I2 (pr1 a)).
        abstract exact (
          !maponpaths (λ x, compose x _) (I2_idempotent) @
          !compose_assoc _ _ _
        ).
      - abstract (
          intros a m;
          apply functional_2_eq;
          exact (compose_assoc _ _ _)
        ).
    Defined.

    Definition functional_abs
      : monoid_action_morphism functional_2_monoid_action (monoid_monoid_action _).
    Proof.
      use make_monoid_action_morphism.
      - intro a.
        exists (pr1 a).
        exact (is_functional_2_to_is_functional_1 _ (pr2 a)).
      - intros a m.
        now apply functional_1_eq.
    Defined.

    Definition lambda_algebra_theory
      : lambda_theory.
    Proof.
      use endomorphism_lambda_theory.
      - exact (monoid_action_cat lambda_algebra_monoid).
      - apply terminal_monoid_action.
      - apply binproducts_monoid_action_cat.
      - apply monoid_monoid_action.
      - apply is_exponentiable_monoid_action.
      - exact (inv_from_z_iso universal_monoid_exponential_iso · functional_abs).
      - exact (
          (functional_app : monoid_action_cat _ ⟦_, _⟧) ·
          morphism_from_z_iso _ _ universal_monoid_exponential_iso
        ).
    Defined.

    Lemma lambda_algebra_theory_has_beta
      : has_β lambda_algebra_theory.
    Proof.
      apply endomorphism_theory_has_β.
      assert ((functional_abs : monoid_action_cat _⟦_, _⟧) · functional_app = identity _).
      {
        apply monoid_action_morphism_eq.
        intro a.
        apply functional_2_eq.
        exact (!pr2 a).
      }
      refine (assoc' _ _ _ @ _).
      refine (maponpaths (λ x, _ · x) (assoc _ _ _ ) @ _).
      rewrite X.
      rewrite id_left.
      apply z_iso_after_z_iso_inv.
    Qed.

  End Theory.

End AlgebraToTheory.
