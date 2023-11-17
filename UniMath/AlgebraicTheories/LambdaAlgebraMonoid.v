(**************************************************************************************************

  The lambda algebra monoid

  For any algebra for a λ-theory, its functional elements form a monoid. This file defines this
  monoid. The functional elements are the elements f that are equal to λ x, f x.

  Contents
  1. The definition of the functional monoid [algebra_monoid]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Local Open Scope cat.
Local Open Scope vec.

(** * 1. The definition of the functional monoid [algebra_monoid] *)

Section Monoid.
  Variable lambda : lambda_calculus.
  Context (L := (lambda_calculus_lambda_theory lambda)).
  Variable A : algebra L.

  Lemma move_action_through_vector {n m : nat} (f : vec (L m : hSet) n) (a : stn m → A):
    weqvecfun _ (vec_map (λ fi, action fi a) f)
     = (λ i, action (weqvecfun _ f i) a).
  Proof.
    apply funextfun.
    intro.
    simpl.
    now rewrite el_vec_map.
  Qed.

  Lemma move_action_through_vector_1 {n : nat} (f : (L n : hSet)) (a : stn n → A) :
        weqvecfun 1 [(action f a)]
      = (λ i, action (weqvecfun 1 [(f)] i) a).
  Proof.
    exact (move_action_through_vector [(f)] _).
  Qed.

  Lemma move_action_through_vector_2 {n : nat} (f g : (L n : hSet)) (a : stn n → A) :
        weqvecfun _ [(action f a ; action g a )]
      = (λ i, action (weqvecfun _ [(f ; g)] i) a).
  Proof.
    exact (move_action_through_vector [(f ; g)] _).
  Qed.

  Definition make_functional (a : A) (n: nat) : A.
  Proof.
    induction n as [| n' a'].
    - exact a.
    - pose (f := (abs (app
      (var (make_stn 2 0 (idpath true)))
      (var (make_stn 2 1 (idpath true))))) : (L 1 : hSet)).
      exact (action f (weqvecfun _ [(a')])).
  Defined.

  Definition is_functional (a: A) (n: nat) : UU
    := a = make_functional a n.

  Lemma isaprop_is_functional (a : A) (n : nat) : isaprop (is_functional a n).
  Proof.
    apply setproperty.
  Qed.

  Ltac extend_tuple_2 := (
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 2 0 (idpath true) < 1)) +
    rewrite (extend_tuple_last _ _ _ (idpath 1 : stntonat _ (make_stn 2 1 (idpath true)) = 1))
  ).

  Ltac extend_tuple_3 := (
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 0 (idpath true) < 2)) +
    rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 1 (idpath true) < 2)) +
    rewrite (extend_tuple_last _ _ _ (idpath 2 : stntonat _ (make_stn 3 2 (idpath true)) = 2))
  ).

  Section Monoid.

    Lemma algebra_isaset_functionals
      (n : nat)
      : isaset (∑ (a: A), is_functional a n).
    Proof.
      apply isaset_total2.
      - apply setproperty.
      - intro a.
        apply isasetaprop.
        apply setproperty.
    Qed.

    Definition algebra_functionals_set
      (n : nat)
      : hSet
      := make_hSet _ (algebra_isaset_functionals n).

    Definition compose
      (a b : A)
      : A.
    Proof.
      pose (f := abs
        (app
          (var (make_stn 3 0 (idpath true)))
          (app
            (var (make_stn 3 1 (idpath true)))
            (var (make_stn 3 2 (idpath true)))
          )) : (L 2 : hSet)).
      exact (action (A := A) f (weqvecfun _ [( a ; b)])).
    Defined.

    Lemma is_functional_compose
      (a b : algebra_functionals_set 1)
      : is_functional (compose (pr1 a) (pr1 b)) 1.
    Proof.
      set (v := weqvecfun 2 [(pr1 a ; pr1 b)]).
      unfold compose, is_functional, make_functional.
      cbn -[weqvecfun action].
      rewrite move_action_through_vector_1.
      rewrite <- algebra_is_assoc.
      cbn -[weqvecfun].
      do 4 reduce_lambda.
      do 2 extend_tuple_2.
      cbn -[v].
      do 9 reduce_lambda.
      do 3 extend_tuple_3.
      now do 7 reduce_lambda.
    Qed.

    Lemma is_assoc_compose
      (a b c : A)
      : compose (compose a b) c = compose a (compose b c).
    Proof.
      unfold compose.
      pose (v := weqvecfun _ [(a ; b ; c)]).
      pose (Hv := λ i Hi,
        !(algebra_projects_component _ _ (make_stn 3 i Hi) v)).
      rewrite (Hv 0 (idpath true) : a = _),
        (Hv 1 (idpath true) : b = _),
        (Hv 2 (idpath true) : c = _).
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      cbn -[weqvecfun action].
      do 15 reduce_lambda.
      do 6 extend_tuple_3.
      do 2 rewrite move_action_through_vector_2.
      do 2 rewrite <- algebra_is_assoc.
      cbn -[weqvecfun v].
      do 12 reduce_lambda.
      do 6 extend_tuple_3.
      cbn -[v].
      now do 42 reduce_lambda.
    Qed.

    Definition unit_element
      : A.
    Proof.
      exact (action (T := L) (abs (var (make_stn 1 0 (idpath true)))) (weqvecfun _ [()])).
    Defined.

    Lemma is_functional_unit_element
      : is_functional unit_element 1.
    Proof.
      unfold unit_element, is_functional, make_functional.
      cbn -[weqvecfun action].
      rewrite move_action_through_vector_1.
      rewrite <- algebra_is_assoc.
      cbn -[weqvecfun action].
      do 4 reduce_lambda.
      do 2 extend_tuple_2.
      cbn.
      do 3 reduce_lambda.
      cbn.
      now reduce_lambda.
    Qed.

    (* Will make this more readable in future PR *)
    Lemma is_unit_unit_element
      : isunit
        (λ a b, compose (pr1 a) (pr1 b) ,, is_functional_compose a b)
        (unit_element ,, is_functional_unit_element).
    Proof.
      unfold unit_element, compose.
      split; (
      intro a;
      pose (v := weqvecfun 1 [(pr1 a)]);
      use subtypePairEquality; [intro; apply isaprop_is_functional | ];
      cbn -[weqvecfun action];
      etrans;
      [now rewrite <- (algebra_projects_component _ _
        (make_stn 1 0 (idpath true))
        v
      : _ = pr1 a) | ];

      pose (H1 := algebra_is_natural
        A
        0
        1
        (weqvecfun 0 [()])
        (abs (var (make_stn 1 0 (idpath true))))
        v
      );
      assert (H2 : (λ i, v (weqvecfun _ [()] i)) = (weqvecfun _ [()]));
      [ now apply (invmaponpathsweq (invweq (weqvecfun _))) | ];
      cbn -[weqvecfun action] in H1, H2;
      rewrite <- (H1 @ maponpaths _ H2);
      clear H1 H2;

      rewrite move_action_through_vector_2;
      rewrite <- algebra_is_assoc;
      cbn -[weqvecfun action];
      do 9 reduce_lambda;
      do 3 extend_tuple_3;
      cbn -[action v];
      do 7 reduce_lambda;
      exact (!pr2 a)).
    Qed.

    Definition algebra_monoid : monoid.
    Proof.
      use tpair.
      - use tpair.
        + exact (algebra_functionals_set 1).
        + intros a b.
          exact (compose (pr1 a) (pr1 b) ,, is_functional_compose a b).
      - split.
        + abstract (
            intros a b c;
            apply subtypePairEquality; [intro; apply isaprop_is_functional | ];
            apply is_assoc_compose
          ).
        + exact (_ ,, is_unit_unit_element).
    Defined.

  End Monoid.

  Definition monoid_category (m : monoid) : category.
  Proof.
    use make_category.
    - use make_precategory.
      + exact (make_precategory_data
          (make_precategory_ob_mor (unit)
          (λ _ _, m))
          (λ _, unel m)
          (λ _ _ _ f g, op g f)
        ).
      + abstract exact (
        ((λ _ _ _, runax _ _) ,,
        (λ _ _ _, lunax _ _)) ,,
        ((λ _ _ _ _ _ _ _, assocax _ _ _ _) ,,
        (λ _ _ _ _ _ _ _, !assocax _ _ _ _))
      ).
    - abstract (
        do 2 intro;
        apply setproperty
      ).
  Defined.

  Definition monoid_presheaf_cat (m : monoid) := PreShv (monoid_category m).

  Definition monoid_presheaf (m : monoid) : monoid_presheaf_cat m.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro.
        exact (m : hSet).
      + intros a b f.
        intro g.
        exact (op g f).
    - split.
      + intro.
        use funextfun.
        intro.
        apply runax.
      + intros a b c f g.
        use funextfun.
        intro h.
        symmetry.
        apply assocax.
  Defined.

  Definition PA : category := monoid_presheaf_cat algebra_monoid.

  Definition U : PA := monoid_presheaf algebra_monoid.

End Monoid.
