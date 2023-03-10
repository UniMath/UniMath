Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
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
    - apply T. 
    - intros.
      apply AlgebraicTheory.pr.
      assumption.
  Defined.

  Lemma is_abstract_clone_from_algebraic_theory (T : algebraic_theory) : is_abstract_clone (abstract_clone_data_from_algebraic_theory T).
  Proof.
    use make_is_abstract_clone. 
    - intros m n.
      apply AlgebraicTheory.comp_project_component.
    - apply (pr12 (pr222 T)).
    - apply (pr122 T).
  Qed.

  Definition abstract_clone_from_algebraic_theory : algebraic_theory → abstract_clone := (λ T, (make_abstract_clone (abstract_clone_data_from_algebraic_theory T) (is_abstract_clone_from_algebraic_theory T))).

  (* The function from abstract clones to functors *)
  (* Definition functor_data_from_abstract_clone : abstract_clone → (functor_data finite_set_skeleton_category HSET).
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
  Qed. *)

  (* Definition functor_from_abstract_clone : abstract_clone → (finite_set_skeleton_category ⟶ HSET) := (λ C, make_functor (functor_data_from_abstract_clone C) (is_functor_from_abstract_clone C)). *)

  (* The function from abstract clones to algebraic theories *)
  Definition algebraic_theory_data_from_abstract_clone : abstract_clone → algebraic_theory_data.
  Proof.
    intros C.
    use make_algebraic_theory_data.
    - apply C.
    - exact (AbstractClone.pr firstelement).
    - exact (λ _ _ a f, reindex a f).
  Defined.

  Lemma is_algebraic_theory_from_abstract_clone (C : abstract_clone) : is_algebraic_theory (algebraic_theory_data_from_abstract_clone C).
  Proof.
    destruct (pr2 C) as [H1 [H2 H3]].
    use make_is_algebraic_theory.
    - split.
      + intro.
        apply funextsec2.
        intro.
        apply H2.
      + intro.
        intros.
        apply funextsec2.
        intro.
        unfold Tmor, compose.
        simpl.
        unfold reindex, funcomp.
        rewrite H3.
        apply maponpaths, funextsec2.
        symmetry.
        apply H1.
    - apply H3.
    - intro.
      intros.
      apply H1.
    - intro.
      intros.
      rewrite <- H2.
      apply maponpaths, funextsec2.
      intro.
      apply H1.
    - intro.
      intros.
      unfold Tmor, algebraic_theory_data_from_abstract_clone, reindex, AlgebraicBase.comp.
      simpl.
      rewrite H3.
      apply maponpaths, funextsec2.
      intro.
      apply H1.
  Qed.
  
  Definition algebraic_theory_from_abstract_clone : abstract_clone → algebraic_theory := (λ C, make_algebraic_theory (algebraic_theory_data_from_abstract_clone C) (is_algebraic_theory_from_abstract_clone C)).

  (* Prove the weak equality *)
  Local Lemma algebraic_theory_id (T : algebraic_theory) : (algebraic_theory_from_abstract_clone (abstract_clone_from_algebraic_theory T)) = T.
  Proof.
    use algebraic_theory_eq.
    - apply idpath.
    - apply idpath.
    - rewrite idpath_transportf.
      simpl.
      unfold AlgebraicTheory.pr, e.
      simpl.
      assert (H1 : (λ (_ : stn 1), firstelement) = identity (1 : finite_set_skeleton_category)).
      {
        apply funextsec2.
        intro i.
        apply (subtypePairEquality (λ _, (isasetbool _ _))).
        exact (!(natlth1tois0 _ (pr2 i))).
      }
      rewrite H1.
      pose (H2 := pr112 T).
      unfold functor_idax in H2.
      simpl in H2.
      rewrite H2.
      apply idpath.
    - rewrite idpath_transportf.
      repeat (apply funextsec2; intro).
      symmetry.
      apply functor_uses_projections.
  Qed.

  Local Lemma abstract_clone_id (C : abstract_clone) : (abstract_clone_from_algebraic_theory (algebraic_theory_from_abstract_clone C)) = C.
  Proof.
    use abstract_clone_eq.
    - apply idpath.
    - rewrite idpath_transportf.
      repeat (apply funextsec2; intro).
      apply idpath.
    - rewrite idpath_transportf.
      repeat (apply funextsec2; intro).
      apply (pr12 C).
  Qed.

  Lemma algebraic_theory_weq_abstract_clone : abstract_clone ≃ algebraic_theory.
  Proof.
    use (algebraic_theory_from_abstract_clone ,, _).
    use isweq_iso.
    - exact abstract_clone_from_algebraic_theory.
    - exact abstract_clone_id.
    - exact algebraic_theory_id.
  Qed.

End AbstractCloneAlgebraicTheory.