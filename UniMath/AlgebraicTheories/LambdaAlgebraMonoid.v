(*
  Gives the monoid of functional elements of a λ-theory [algebra_monoid].
  The functional elements are the elements f that are equal to λ x, f x.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.Examples.LambdaCalculus.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.AlgebraicTheories.Tuples.
Require Import UniMath.CategoryTheory.Presheaf.

Local Open Scope cat.
Local Open Scope vec.

Section Monoid.
  Variable lambda : lambda_calculus.
  Context (L := (lambda_calculus_lambda_theory lambda)).
  Variable A : algebraic_theory_algebra L.

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

  Definition algebra_monoid : monoid.
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (∑ a: A, is_functional a 1).
        * apply isaset_total2.
          -- apply setproperty.
          -- intro a.
            apply isasetaprop.
            apply setproperty.
      + intros a b.
        use tpair.
        * pose (f := abs
            (app
              (var (make_stn 3 0 (idpath true)))
              (app
                (var (make_stn 3 1 (idpath true)))
                (var (make_stn 3 2 (idpath true)))
              )) : (L 2 : hSet)).
          exact (action (A := A) f (weqvecfun _ [( pr1 a ; pr1 b)])).
        * abstract now (
            set (v := weqvecfun 2 [(pr1 a ; pr1 b)]);
            unfold is_functional, make_functional;
            cbn -[weqvecfun action];
            rewrite move_action_through_vector_1;
            rewrite <- algebraic_theory_algebra_is_assoc;
            cbn -[weqvecfun];
            do 4 reduce_lambda;
            do 2 extend_tuple_2;
            cbn -[v];
            do 9 reduce_lambda;
            do 3 extend_tuple_3;
            do 7 reduce_lambda
          ).
    - split.
      + abstract now (
          intros a b c;
          apply subtypePairEquality; [intro; apply isaprop_is_functional | ];
          cbn -[weqvecfun action];
          pose (v := weqvecfun _ [(pr1 a ; pr1 b ; pr1 c)]);
          pose (Hv := λ i Hi,
            !(algebraic_theory_algebra_projects_component _ _ (make_stn 3 i Hi) v));
          rewrite (Hv 0 (idpath true) : pr1 a = _),
            (Hv 1 (idpath true) : pr1 b = _),
            (Hv 2 (idpath true) : pr1 c = _);
          do 2 rewrite move_action_through_vector_2;
          do 2 rewrite <- algebraic_theory_algebra_is_assoc;
          cbn -[weqvecfun action];
          do 15 reduce_lambda;
          do 6 extend_tuple_3;
          do 2 rewrite move_action_through_vector_2;
          do 2 rewrite <- algebraic_theory_algebra_is_assoc;
          cbn -[weqvecfun v];
          do 12 reduce_lambda;
          do 6 extend_tuple_3;
          cbn -[v];
          do 42 reduce_lambda
        ).
      + use tpair.
        * use tpair.
          -- exact (action (T := L) (abs (var (make_stn 1 0 (idpath true)))) (weqvecfun _ [()])).
          -- abstract now (
              unfold is_functional, make_functional;
              cbn -[weqvecfun action];
              rewrite move_action_through_vector_1;
              rewrite <- algebraic_theory_algebra_is_assoc;
              cbn -[weqvecfun action];
              do 4 reduce_lambda;
              do 2 extend_tuple_2;
              cbn;
              do 3 reduce_lambda;
              cbn;
              reduce_lambda
            ).
        * abstract (split; (
            intro a;
            pose (v := weqvecfun 1 [(pr1 a)]);
            use subtypePairEquality; [intro; apply isaprop_is_functional | ];
            cbn -[weqvecfun action];
            etrans; [now rewrite <- (algebraic_theory_algebra_projects_component _ _ (make_stn 1 0 (idpath true)) v : _ = pr1 a) | ];

            pose (H1 := algebraic_theory_algebra_is_natural A 0 1 (weqvecfun 0 [()]) (abs (var (make_stn 1 0 (idpath true)))) v);
            assert (H2 : (λ i, v (weqvecfun _ [()] i)) = (weqvecfun _ [()]));
            [ now apply (invmaponpathsweq (invweq (weqvecfun _))) | ];
            cbn -[weqvecfun action] in H1, H2;
            rewrite <- (H1 @ maponpaths _ H2);
            clear H1 H2;

            rewrite move_action_through_vector_2;
            rewrite <- algebraic_theory_algebra_is_assoc;
            cbn -[weqvecfun action];
            do 9 reduce_lambda;
            do 3 extend_tuple_3;
            cbn -[action v];
            do 7 reduce_lambda;
            exact (!pr2 a)
          ) ).
  Defined.

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
