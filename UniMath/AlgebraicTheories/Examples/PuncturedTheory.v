(**************************************************************************************************

  The "Punctured" Theory

  For any algebraic theory T, we can create its "punctured" theory T*, or "theory without constants",
  where T*_{S n} = T_{S n} but T*_0 = ∅. This effectively removes the constants from the algebraic
  theory. However, they are still implicitly there in the nonconstant terms: we can give any nonempty
  T*-algebra a T-algebra structure.
  On the other hand, we can also pull back any algebra along the embedding T* ↪ T, and this gives a
  retraction of T*-algebras onto T-algebras.
  Note that if T_0 is nonempty, the empty T*-algebra, which can be constructed as
  `theory_algebra T* 0`, is not a T-algebra.

  Contents
  1. The punctured theory [punctured_theory]
  2. The embedding and pullback [punctured_theory_embedding] [algebra_to_punctured_theory_algebra]
  3. The lifting of T*-algebras to T-algebras [punctured_theory_algebra_to_algebra]
  4. The isomorphism that shows we have a retraction for T_0 nonempty
    [algebra_to_punctured_theory_algebra_to_algebra_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraCategory.

Local Open Scope algebraic_theories.
Local Open Scope vec.
Local Open Scope stn.

Section PuncturedTheory.

  Context (T : algebraic_theory).

(** * 1. The punctured theory *)

  Definition punctured_theory_data
    : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - intro n.
      induction n as [| n H].
      + exact (make_hSet _ isasetempty).
      + exact (T (S n)).
    - intros n i.
      induction n.
      + apply (negstn0 i).
      + exact (var i).
    - intros m n f g.
      induction m, n;
        try induction f;
        try induction (g firstelement);
      exact (f • g).
  Defined.

  Lemma punctured_is_theory
    : is_algebraic_theory punctured_theory_data.
  Proof.
    apply make_is_algebraic_theory.
    - intros l m n f g h.
      induction l, m, n;
        try induction f;
        try induction (g firstelement);
        try induction (h firstelement).
      apply subst_subst.
    - intros m n i f.
      induction m, n;
        try induction (negstn0 i);
        try induction (f firstelement).
      apply var_subst.
    - intros n f.
      induction n;
        try induction f.
      apply subst_var.
  Qed.

  Definition punctured_theory
    : algebraic_theory
    := make_algebraic_theory
      punctured_theory_data
      punctured_is_theory.

(** * 2. The embedding and pullback *)

  Definition punctured_theory_embedding_data
    : algebraic_theory_morphism_data punctured_theory T.
  Proof.
    intros n t.
    induction n.
    - induction t.
    - exact t.
  Defined.

  Lemma punctured_theory_embedding_is_morphism
    : is_algebraic_theory_morphism punctured_theory_embedding_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - intros n i.
      induction n.
      + exact (fromstn0 i).
      + reflexivity.
    - intros m n f g.
      induction m, n;
        try induction f;
        try induction (g firstelement).
      reflexivity.
  Qed.

  Definition punctured_theory_embedding
    : algebraic_theory_morphism punctured_theory T
    := make_algebraic_theory_morphism
      punctured_theory_embedding_data
      punctured_theory_embedding_is_morphism.

  Definition algebra_to_punctured_theory_algebra
    (A : algebra T)
    : algebra punctured_theory
    := algebra_pullback punctured_theory_embedding A.

(** * 3. The lifting of T*-algebras to T-algebras *)

  Section LiftPuncturedTheoryAlgebra.

    Context (A : algebra punctured_theory).
    Context (a0 : ∥ A ∥).

    Lemma isaprop_inflated_constant_image
      {m n : nat}
      (f : T 0)
      (g1 : stn 0 → T (S m))
      (g2 : stn 0 → T (S n))
      (a1 : stn (S m) → A)
      (a2 : stn (S n) → A)
      : action (f • g1 : punctured_theory (S m)) a1
      = action (f • g2 : punctured_theory (S n)) a2.
    Proof.
      refine (!_ @ maponpaths (λ x, action x a2) (subst_inflate_extend_tuple _ f _)).
      refine (!_ @ maponpaths (λ x, action x a1) (subst_inflate_extend_tuple _ f _)).
      refine (subst_action _ (inflate f : punctured_theory 1) _ a1 @ !_).
      refine (subst_action _ (inflate f : punctured_theory 1) _ a2 @ !_).
      do 2 refine (maponpaths (λ x, action _ x) (!homotweqinvweq (weqvecfun _) _) @ !_).
      pose (v := weqvecfun _ [(
        action (lift_constant _ f : punctured_theory (S m)) a1 ;
        action (lift_constant _ f : punctured_theory (S n)) a2
      )]).
      refine (maponpaths (λ x, action _ (weqvecfun 1 [(x)])) (!var_action A (● 0 : stn 2) v) @ !_).
      refine (maponpaths (λ x, action _ (weqvecfun 1 [(x)])) (!var_action A (● 1 : stn 2) v) @ !_).
      do 2 refine (maponpaths (λ x, action _ x) (move_action_through_vector_1 _ _ _) @ !_).
      refine (!_ @ subst_action A _ (weqvecfun _ [(var (stnpr 1 : stn 2))]) _).
      refine (!_ @ subst_action A _ (weqvecfun _ [(var (stnpr 0 : stn 2))]) _).
      apply (maponpaths (λ x, action x _)).
      refine (subst_inflate T f (weqvecfun _ [(var (● 0 : stn 2))]) @ !_).
      refine (subst_inflate T f (weqvecfun _ [(var (● 1 : stn 2))]) @ !_).
      apply maponpaths.
      now apply (invmaponpathsweq (invweq (weqvecfun _))).
    Qed.

    Definition inflated_constant_image
      (f : T 0)
      (a0' : ∥ A ∥)
      : A.
    Proof.
      simple refine (squash_to_set (setproperty _) _ _ a0').
      - intro a.
        exact (action (inflate f : punctured_theory 1) (weqvecfun _ [(a)])).
      - abstract (
          intros a a';
          apply isaprop_inflated_constant_image
        ).
    Defined.

    Definition punctured_theory_algebra_to_algebra_data
      : algebra_data T.
    Proof.
      use make_algebra_data.
      - exact A.
      - intros n f a.
        destruct n as [| n].
        + exact (inflated_constant_image f a0).
        + exact (action (f : punctured_theory (S n)) a).
    Defined.

    Lemma punctured_theory_algebra_to_is_algebra
      : is_algebra punctured_theory_algebra_to_algebra_data.
    Proof.
      unfold punctured_theory_algebra_to_algebra_data.
      refine (squash_rec (λ a, make_hProp _ (isaprop_is_algebra _)) _ a0).
      intro a0'.
      use make_is_algebra.
      - intros m n f g a.
        unfold AlgebraCategoryCore.subst_action_ax.
        destruct m as [| m], n as [| n].
        + refine (maponpaths (λ x, action x _) _).
          refine (_ @ subst_var _ _).
          apply maponpaths.
          now apply (invmaponpathsweq (invweq (weqvecfun _))).
        + refine (!maponpaths (λ x, action x a) (subst_inflate_extend_tuple _ _ _) @ _).
          refine (subst_action _ (inflate f : punctured_theory 1) _ _ @ _).
          apply isaprop_inflated_constant_image.
        + refine (maponpaths (λ x, action x (weqvecfun 1 [(a0')])) (inflate_subst _ f g) @ _).
          exact (subst_action _ (f : punctured_theory (S m)) _ _).
        + exact (subst_action _ (f : punctured_theory (S m)) (g : _ → punctured_theory (S n)) a).
      - intros n i a.
        destruct n as [| n].
        + exact (fromstn0 i).
        + exact (var_action _ i a).
    Qed.

    Definition punctured_theory_algebra_to_algebra
      : algebra T
      := make_algebra
        punctured_theory_algebra_to_algebra_data
        punctured_theory_algebra_to_is_algebra.

  End LiftPuncturedTheoryAlgebra.

(** * 4. The isomorphism that shows we have a retraction for T_0 nonempty *)

  Definition algebra_to_punctured_theory_algebra_to_algebra
    (t : ∥ T 0 ∥)
    (A : algebra T)
    : algebra T
    := punctured_theory_algebra_to_algebra
      (algebra_to_punctured_theory_algebra A)
      (hinhfun (λ t, action t (weqvecfun _ [()])) t).

  Lemma algebra_to_punctured_theory_algebra_to_algebra_iso_is_morphism
    (t : ∥ T 0 ∥)
    (A : algebra T)
    : is_algebra_morphism (idfun A : algebra_to_punctured_theory_algebra_to_algebra t A → A).
  Proof.
    intros n f a.
    induction n; cbn.
    - induction (squash_uniqueness f t).
      refine (subst_action _ f _ _ @ _).
      apply maponpaths.
      now apply (invmaponpathsweq (invweq (weqvecfun _))).
    - reflexivity.
  Qed.

  Definition algebra_to_punctured_theory_algebra_to_algebra_iso
    (t : ∥ T 0 ∥)
    (A : algebra T)
    : z_iso (algebra_to_punctured_theory_algebra_to_algebra t A) A.
  Proof.
    use make_algebra_z_iso.
    - exact (identity_z_iso _).
    - apply algebra_to_punctured_theory_algebra_to_algebra_iso_is_morphism.
  Defined.

End PuncturedTheory.
