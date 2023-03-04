Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.ArnoudsThesis.AlgebraicTheory.
Require Import UniMath.ArnoudsThesis.AbstractClone.
Require Import UniMath.ArnoudsThesis.FiniteSetSkeleton.

Local Open Scope cat.

Section AbstractCloneAlgebraicTheory.

  Definition abstract_clone_from_algebraic_theory : algebraic_theory → abstract_clone.
  Proof.
    intros T.
    use make_abstract_clone.
    - use make_abstract_clone_data.
      + exact T. 
      + intros.
        apply AlgebraicTheory.pr.
        assumption.
      + intros m n f g.
        exact (pr221 T m n f g).
    - use make_is_abstract_clone. 
      + intros m n.
        apply AlgebraicTheory.comp_project_component.
      + apply (pr1 (pr222 T)).
      + apply (pr12 T).
  Defined.

  Definition abstract_clone_to_functor : abstract_clone → (finite_set_skeleton_category ⟶ HSET).
  Proof.
    intros C.
    use make_functor.
    - use make_functor_data.
      + intros.
        apply C.
        assumption.
      + intros m n a f.
        exact (AbstractClone.reindex a f).
    - destruct (pr2 C) as [H1 [H2 H3]].
      split.
      + intro.
        apply funextsec2.
        intro.
        apply H2.
      + intro.
        intros.
        apply funextsec2.
        intro.
        unfold reindex, compose.
        simpl.
        rewrite H3.
        apply maponpaths, funextsec2.
        intro.
        symmetry.
        apply H1.
  Defined.

  Definition algebraic_theory_from_abstract_clone : abstract_clone → algebraic_theory.
  Proof.
    intros C.
    use make_algebraic_theory.
    - use make_algebraic_theory_data.
      + exact (abstract_clone_to_functor C).
      + exact (pr121 C 1 (firstelement)).
      + apply (pr221 C).
    - destruct (pr2 C) as [H1 [H2 H3]].
      use make_is_algebraic_theory.
      + apply H3.
      + intro.
        intros.
        apply H1.
      + intro.
        intros.
        rewrite <- H2.
        apply maponpaths, funextsec2.
        intro.
        apply H1.
      + intro.
        intros.
        unfold AlgebraicTheory.comp, AlgebraicTheory.pr.
        simpl.
        unfold reindex, comp.
        rewrite H3.
        apply maponpaths, funextsec2.
        intro.
        apply H1.
  Defined.

  Lemma algebraic_theory_weq_abstract_clone : abstract_clone ≃ algebraic_theory.
  Proof.
    use (algebraic_theory_from_abstract_clone ,, _).
    apply isEquivalence_to_isweq.
    repeat use tpair.
    - exact abstract_clone_from_algebraic_theory.
    - intros.
      apply (subtypePairEquality ispredicate_is_algebraic_theory).
      use total2_paths2_b.
      + destruct (pr2 y) as [HTassoc [HTunit [HTproj HTnat]]].
        use (subtypePairEquality' _ (isaprop_is_functor _ _ (pr2 SET) _)).
        use (total2_paths2_b (idpath _)). 
        repeat (apply funextsec2; intro).
        rewrite <- (HTproj _ (transportb _ _ (pr211 (pr1 y)) _ _ _ _)).
        symmetry.
        apply y.
      + use total2_paths2_b.
        * 
          
          simpl.
          unfold abstract_clone_from_algebraic_theory.
          unfold AlgebraicTheory.pr.
          simpl.
        simpl.
        use subtypePairEquality'.
        use (subtypePairEquality' _ (isaprop_is_functor _ _ (pr2 SET) _)).
      simpl.
  Qed.

End AbstractCloneAlgebraicTheory.