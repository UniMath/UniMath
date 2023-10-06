Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition free_theory'_data (X : hSet) : algebraic_theory'_data.
Proof.
  use make_algebraic_theory'_data.
  - intro n.
    exact (setcoprod (stnset n) X).
  - exact (λ _ i, inl i).
  - intros m n f g.
    induction f as [f' | f'].
    + exact (g f').
    + exact (inr f').
Defined.

Definition free_is_theory' {X : hSet} : is_algebraic_theory' (free_theory'_data X).
Proof.
  use make_is_algebraic_theory'.
  - now do 4 intro.
  - do 2 intro.
    now induction f.
  - intros l m n f_l f_m f_n.
    now induction f_l.
Qed.

Definition free_theory (X : hSet) : algebraic_theory
  := make_algebraic_theory' _ (free_is_theory' (X := X)).

Definition free_functor : HSET ⟶ algebraic_theory_cat.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact free_theory.
    + intros a b c.
      use (make_algebraic_theory_morphism' (T := free_theory a) (T' := free_theory b)).
      * intros n x.
        induction x as [left | right].
        -- exact (inl left).
        -- exact (inr (c right)).
      * abstract (
          use make_is_algebraic_theory_morphism';
          [ intros m n f g;
            now induction f
          | intros n f;
            now induction f]
        ).
  - use tpair.
    + abstract (
        intro;
        use (algebraic_theory_morphism_eq (T := free_theory a) (T' := free_theory a));
        intros n f;
        now induction f
      ).
    + abstract (
        intros a b c d e;
        use (algebraic_theory_morphism_eq (T := free_theory a) (T' := free_theory c));
        intros n f;
        now induction f
      ).
Defined.

Definition forgetful_functor_data : functor_data algebraic_theory_cat HSET.
Proof.
  use make_functor_data.
  - intro T.
    exact ((T : algebraic_theory) 0).
  - intros T T' F.
    exact ((F : algebraic_theory_morphism T T') 0).
Defined.

Lemma forgetful_is_functor : is_functor forgetful_functor_data.
Proof.
  use tpair;
    easy.
Qed.

Definition forgetful_functor : algebraic_theory_cat ⟶ HSET
  := make_functor _ forgetful_is_functor.

Lemma lift_constant_eq
  (T : algebraic_theory)
  {n : nat}
  (f f' : (T 0 : hSet))
  (g : stn 0 → (T n : hSet))
  (H : f = f')
  : lift_constant n f = f' • g.
Proof.
  intros.
  refine (maponpaths (comp f) _ @ maponpaths (λ x, x • g) H).
  apply funextfun.
  intro x.
  apply fromempty.
  exact (negnatlthn0 _ (stnlt x)).
Qed.

Definition free_functor_is_free
  : are_adjoints free_functor forgetful_functor.
Proof.
  use adj_from_nathomweq.
  use tpair.
  - refine (λ A (T : algebraic_theory), _).
    use weq_iso.
    + exact (λ (F : algebraic_theory_morphism _ T) x, F 0 (inr x)).
    + intro F.
      use (make_algebraic_theory_morphism' (T := free_functor A) (T' := T)).
      * intros ? f.
        induction f as [i | a].
        -- exact (pr i).
        -- exact (lift_constant _ (F a)).
      * abstract (
          use make_is_algebraic_theory_morphism';
          [ intros ? ? f ?;
            induction f;
            [ exact (!algebraic_theory_comp_projects_component _ _ _ _ _)
            | exact (lift_constant_eq _ _ _ _ (idpath _) @ !algebraic_theory_comp_is_assoc _ _ _ _ _ _ _) ]
          | now intros ]
        ).
    + abstract (
        refine (λ (F : algebraic_theory_morphism _ _), _);
        apply algebraic_theory_morphism_eq;
        intros ? f;
        induction f;
        [ exact (!algebraic_theory_morphism_preserves_projections _ _)
        | exact (lift_constant_eq _ _ _ _ (idpath _) @ !algebraic_theory_morphism_preserves_composition F _ _ _ _
          : lift_constant _ _ = F _ (lift_constant _ _))]
      ).
    + abstract (
        intro;
        apply funextfun;
        intro;
        refine (lift_constant_eq _ _ _ _ (idpath _) @ algebraic_theory_comp_identity_projections _ _ _)
      ).
  - abstract (
      use tpair;
      repeat intro;
      easy
    ).
Defined.
