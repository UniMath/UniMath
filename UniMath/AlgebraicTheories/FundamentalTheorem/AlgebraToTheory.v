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
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
(* Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SpecificUtilities.LambdaTerms. *)
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidActions.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Require Import UniMath.AlgebraicTheories.OriginalRepresentationTheorem.

Local Open Scope cat.
Local Open Scope vec.
Local Open Scope algebraic_theories.
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
    := aaction (compose L (var (● 0 : stn 2)) (var (● 1 : stn 2))) (weqvecfun _ [(a ; b)]).

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
(*
  Lemma compose_compose_eq
    {a b c d : A}
    (H : a = compose c d)
    : compose a b = compose c (compose d b).
  Proof.
    refine (_ @ compose_assoc _ _ _).
    apply (maponpaths (λ x, compose x _)).
    exact H.
  Qed. *)

  Lemma lift_constant_U
    {n : nat}
    : lift_constant n (U_term L) = (U_term L).
  Proof.
    unfold lift_constant, U_term.
    rewrite subst_abs.
    rewrite (var_subst L).
    now rewrite extend_tuple_inr.
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
    rewrite lift_constant_U.
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
      rewrite lift_constant_U.
      exact (!U_compose _ Lβ _).
    Qed.

    Lemma is_functional_1_I1
      : is_functional_1 I1.
    Proof.
      exact (!I1_idempotent).
    Qed.

    Lemma inflate_is_lift_constant
      (x : L 0)
      : inflate x = lift_constant 1 x.
    Proof.
      apply (maponpaths (subst _)).
      apply (iscontr_uniqueness (iscontr_empty_tuple _)).
    Qed.

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
      rewrite lift_constant_U.
      do 2 rewrite subst_compose.
      do 4 rewrite (var_subst L).
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
      := exponential_term L (U L Lβ) (U L Lβ).

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
      apply (exponential_idempotent L Lβ).
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
      (v : stn n → A)
      : is_functional_2 (aaction (abs (abs f) : ((L n) : hSet)) v).
    Proof.
      unfold is_functional_2, make_functional_2, compose, I2, aaction.
      rewrite <- (lift_constant_action _ _ v).
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x _)).
      rewrite subst_compose.
      do 2 rewrite (var_subst L).
      cbn.
      rewrite (compose_abs L Lβ).
      unfold lift_constant, UU_term, exponential_term.
      rewrite inflate_subst.
      rewrite subst_abs.
      rewrite (beta_equality L Lβ).
      rewrite (subst_subst L).
      do 2 rewrite (subst_compose L).
      rewrite (subst_inflate).
      rewrite (pr2 (iscontr_empty_tuple (L (S n))) (λ i, _ • _)).
      cbn -[weqvecfun stnweq].
      rewrite (lift_constant_U : U_term _ • _ = _).
      rewrite (var_subst L).
      rewrite extend_tuple_inr.
      rewrite (var_subst L).
      rewrite extend_tuple_inr.
      rewrite (U_compose _ Lβ).
      now rewrite (compose_U _ Lβ).
    Qed.

    Lemma isaprop_is_functional_2 (a : A) : isaprop (is_functional_2 a).
    Proof.
      apply setproperty.
    Qed.

    Definition functional_2_set
      : hSet.
    Proof.
      use (∑ (a : A), make_hSet (is_functional_2 a) _)%set.
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

    Lemma compose_I1_I2
      : compose I1 I2 = I2.
    Proof.
      unfold compose, I1, I2, aaction.
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x _)).
      rewrite subst_compose.
      do 2 rewrite (var_subst L).
      apply (U_compose L Lβ).
    Qed.

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

    Let R : category := R L Lβ.
    Let U : R := U L Lβ.

    Definition functional_2_to_monoid_action_morphism_data_term
      (d : functional_2_monoid_action)
      (a b : A)
      : A.
    Proof.
      pose (v := (weqvecfun _ [(pr1 d ; a ; b)])).
      refine (aaction _ v).
      pose (R_exponentials L Lβ U).

      Require Import UniMath.CategoryTheory.Adjunctions.Core.
      Require Import UniMath.CategoryTheory.exponentials.

      pose (abs (app (var (T := L) (● 0 : stn 2)) (var (● 1 : stn 2)))).
      assert (R ⟦U, U⟧).

      epose (BinProductArrow R (R_binproducts L Lβ U U)).
      epose (binproduct_arrow ).
      epose (φ_adj_inv (pr2 i) ∘ ).
      cbn in p.
      exact (aaction compose_2_λ v).
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
      pose (v := weqvecfun _ [(pr1 m ; pr1 d ; pr11 x ; pr12 x)]).
      unfold compose, aaction.
      rewrite <- (var_action _ (make_stn 4 0 (idpath true)) v : _ = pr1 m).
      rewrite <- (var_action _ (make_stn 4 1 (idpath true)) v : _ = pr1 d).
      rewrite <- (var_action _ (make_stn 4 2 (idpath true)) v : _ = pr11 x).
      rewrite <- (var_action _ (make_stn 4 3 (idpath true)) v : _ = pr12 x).
      do 2 rewrite (move_action_through_vector_2 A _ _ _).
      do 2 rewrite <- subst_action.
      do 2 rewrite (move_action_through_vector_3 A _ _ _ _).
      do 2 rewrite <- subst_action.
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x v)).
      exact (!compose_compose_2_λ _ _ _ _).
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
      refine (aaction term_1_λ
        (weqvecfun _ [(_)])).
      apply (f : monoid_action_morphism _ _).
      split.
      - exact (aaction T_λ (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
      - exact (aaction F_λ (weqvecfun _ [()]) ,, is_functional_1_action_abs _ _).
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
      set (v := weqvecfun _ [(pr1 a ; pr1 m ; pr11 x ; pr12 x)]).
      rewrite <- (var_action _ (make_stn 4 0 (idpath true)) v : _ = pr1 a).
      rewrite <- (var_action _ (make_stn 4 1 (idpath true)) v : _ = pr1 m).
      rewrite <- (var_action _ (make_stn 4 2 (idpath true)) v : _ = pr11 x).
      rewrite <- (var_action _ (make_stn 4 3 (idpath true)) v : _ = pr12 x).
      unfold compose, aaction.
      do 2 rewrite (move_action_through_vector_2 A _ _ _).
      do 2 rewrite <- subst_action.
      do 2 rewrite (move_action_through_vector_3 A _ _ _ _).
      do 2 rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x v)).
      cbn -[weqvecfun].
      apply compose_2_compose_λ.
    Qed.

    Definition term_2
      (a a' : A)
      := (aaction term_2_λ (weqvecfun _ [(a ; a')]) ,, is_functional_1_action_abs _ _).

    Lemma compose_2_term_1
      (b : monoid_monoid_action lambda_algebra_monoid)
      (a a' : A)
      : aaction compose_2_λ
        (weqvecfun 3 [(
          aaction term_1_λ (weqvecfun 1 [(pr1 b)]);
          a;
          a'
        )])
      = pr1 (maction b (term_2 a a')).
    Proof.
      cbn -[weqvecfun aaction].
      set (v := weqvecfun _ [(pr1 b; a; a')]).
      unfold compose, aaction.
      rewrite <- (var_action _ (make_stn 3 0 (idpath true)) v : _ = pr1 b).
      rewrite <- (var_action _ (make_stn 3 1 (idpath true)) v : _ = a).
      rewrite <- (var_action _ (make_stn 3 2 (idpath true)) v : _ = a').
      rewrite (move_action_through_vector_1 A _ _).
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite <- subst_action.
      rewrite <- subst_action.
      rewrite (move_action_through_vector_2 A _ _ _).
      rewrite (move_action_through_vector_3 A _ _ _ _).
      rewrite <- subst_action.
      rewrite <- subst_action.
      apply (maponpaths (λ x, aaction x v)).
      cbn -[weqvecfun].
      apply compose_2_term_1_λ.
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
        set (v := weqvecfun _ [(pr1 a)]).
        unfold exponential_object_to_functional_2_morphism_data.
        unfold functional_2_to_exponential_object_morphism_data.
        unfold functional_2_to_monoid_action_morphism_data.
        unfold exponential_object_to_functional_2_term.
        unfold functional_2_to_monoid_action_morphism_data_term.
        cbn -[weqvecfun aaction].
        rewrite (pr2 a).
        rewrite <- (var_action _ (make_stn 1 0 (idpath true)) v : _ = pr1 a).
        unfold make_functional_2, compose, I2, aaction.
        do 3 rewrite <- (lift_constant_action _ _ v).
        rewrite (move_action_through_vector_2 A _ _ _).
        rewrite <- subst_action.
        rewrite (move_action_through_vector_3 A _ _ _ _).
        rewrite <- subst_action.
        rewrite (move_action_through_vector_1 A _ _).
        rewrite <- subst_action.
        apply (maponpaths (λ x, aaction x v)).
        apply term_1_compose_2_λ.
      - apply funextfun.
        intro f.
        apply monoid_action_morphism_eq.
        intro a.
        apply functional_1_eq.
        refine (compose_2_term_1 _ _ _ @ _).
        refine (!base_paths _ _ (mor_action f _ _) @ _).
        apply maponpaths.
        apply maponpaths.
        set (v := weqvecfun _ [(pr11 a ; pr12 a)]).
        apply pathsdirprod;
          apply functional_1_eq;
          [ refine (_ @ !pr21 a)
          | refine (_ @ !pr22 a) ];
          cbn -[weqvecfun aaction];
          unfold make_functional_1, compose, I1, aaction;
          rewrite <- (var_action _ (make_stn 2 0 (idpath true)) v : _ = pr11 a);
          rewrite <- (var_action _ (make_stn 2 1 (idpath true)) v : _ = pr12 a);
          rewrite <- (lift_constant_action _ _ v);
          rewrite <- (lift_constant_action _ _ v);
          rewrite (move_action_through_vector_2 A _ _ _);
          rewrite (move_action_through_vector_2 A _ _ _);
          rewrite <- subst_action;
          rewrite <- subst_action;
          rewrite (move_action_through_vector_2 A _ _ _);
          rewrite <- subst_action;
          apply (maponpaths (λ x, aaction x v)).
        + apply compose_T_λ.
        + apply compose_F_λ.
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
        exact (compose_compose_eq (!I2_idempotent)).
      - intros a m.
        apply functional_2_eq.
        exact (!compose_assoc _ _ _).
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
