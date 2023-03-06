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

  (* The function from algebraic theories to abstract clones *)
  Definition abstract_clone_data_from_algebraic_theory : algebraic_theory → abstract_clone_data.
  Proof.
    intros T.
    use make_abstract_clone_data.
    - exact T. 
    - intros.
      apply AlgebraicTheory.pr.
      assumption.
    - intros m n f g.
      exact (pr221 T m n f g).
  Defined.

  Lemma is_abstract_clone_from_algebraic_theory (T : algebraic_theory) : is_abstract_clone (abstract_clone_data_from_algebraic_theory T).
  Proof.
    use make_is_abstract_clone. 
    - intros m n.
      apply AlgebraicTheory.comp_project_component.
    - apply (pr1 (pr222 T)).
    - apply (pr12 T).
  Qed.

  Definition abstract_clone_from_algebraic_theory : algebraic_theory → abstract_clone := (λ T, (make_abstract_clone (abstract_clone_data_from_algebraic_theory T) (is_abstract_clone_from_algebraic_theory T))).

  (* The function from abstract clones to functors *)
  Definition functor_data_from_abstract_clone : abstract_clone → (functor_data finite_set_skeleton_category HSET).
  Proof.
    intros C.
    use make_functor_data.
    - intros.
      apply C.
      assumption.
    - intros m n a f.
      exact (AbstractClone.reindex a f).
  Defined.

  Lemma is_functor_from_abstract_clone (C : abstract_clone) : (is_functor (functor_data_from_abstract_clone C)).
  Proof.
    destruct (pr2 C) as [H1 [H2 H3]].
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
      unfold reindex.
      simpl.
      rewrite H3.
      apply maponpaths, funextsec2.
      intro.
      symmetry.
      apply H1.
  Qed.

  Definition functor_from_abstract_clone : abstract_clone → (finite_set_skeleton_category ⟶ HSET) := (λ C, make_functor (functor_data_from_abstract_clone C) (is_functor_from_abstract_clone C)).

  (* The function from abstract clones to algebraic theories *)
  Definition algebraic_theory_data_from_abstract_clone : abstract_clone → algebraic_theory_data.
  Proof.
    intros C.
    use make_algebraic_theory_data.
    - exact (functor_from_abstract_clone C).
    - exact (pr121 C 1 (firstelement)).
    - apply (pr221 C).
  Defined.

  Lemma is_algebraic_theory_from_abstract_clone (C : abstract_clone) : is_algebraic_theory (algebraic_theory_data_from_abstract_clone C).
  Proof.
    destruct (pr2 C) as [H1 [H2 H3]].
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
  Qed.
  
  Definition algebraic_theory_from_abstract_clone : abstract_clone → algebraic_theory := (λ C, make_algebraic_theory (algebraic_theory_data_from_abstract_clone C) (is_algebraic_theory_from_abstract_clone C)).

  (* Prove the weak equality *)
  Lemma algebraic_theory_eq (X Y : algebraic_theory) : ∏
    (p : pr11 X = pr11 Y),
    (transportf (λ T, (T 1 : hSet)) (maponpaths pr1 (maponpaths pr1 p)) (pr121 X) = (pr121 Y)) →
    (transportf (λ T, ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)) (maponpaths pr1 (maponpaths pr1 p)) (pr221 X) = (pr221 Y)) →
    X = Y.
  Proof.
    destruct X as [[X [Xe Xcomp]] XH].
    destruct Y as [[Y [Ye Ycomp]] YH].
    intros.
    apply (subtypePairEquality ispredicate_is_algebraic_theory).
    simpl in p.
    apply (total2_paths2_f p).
    induction p.
    rewrite idpath_transportf.
    apply pathsdirprod; assumption.
  Qed.

  Lemma L1 y : pr11 (algebraic_theory_from_abstract_clone (abstract_clone_from_algebraic_theory y)) = pr11 y.
  Proof.
    destruct (pr2 y) as [HTassoc [HTunit [HTproj HTnat]]].
    use (subtypePairEquality' _ (isaprop_is_functor _ _ (pr2 SET) _)).
    use (total2_paths2_b (idpath _)). 
    repeat (apply funextsec2; intro).
    rewrite <- (HTproj _ (transportb _ _ (pr211 (pr1 y)) _ _ _ _)).
    symmetry.
    apply y.
  Qed.

  Lemma L2 y p : transportf (λ T : nat → hSet, T 1 : hSet) (maponpaths pr1 (maponpaths pr1 p)) (pr121 (algebraic_theory_from_abstract_clone (abstract_clone_from_algebraic_theory y))) = pr121 y.
  Proof.
    simpl.
    unfold AlgebraicTheory.pr, e.
    destruct (pr2 y) as [H1 [H2 [H3 H4]]].
    assert ((λ (_ : stn 1), firstelement) = identity (1 : finite_set_skeleton_category)).
    {
      apply funextsec2.
      intro i.
      apply (subtypePairEquality (λ _, (isasetbool _ _))).
      exact (!(natlth1tois0 _ (pr2 i))).
    }
    rewrite X.
    rewrite (functor_id_id _ _ _ _ _ (idpath _)).
    unfold identity.
    simpl.
  Qed.

  Lemma algebraic_theory_weq_abstract_clone : abstract_clone ≃ algebraic_theory.
  Proof.
    use (algebraic_theory_from_abstract_clone ,, _).
    apply isEquivalence_to_isweq.
    repeat use tpair.
    - exact abstract_clone_from_algebraic_theory.
    - intros.
      use algebraic_theory_eq.
      + apply L1.
      + simpl.
  Qed.

End AbstractCloneAlgebraicTheory.