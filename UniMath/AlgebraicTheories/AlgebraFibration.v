(**************************************************************************************************

  The algebra fibration

  This file shows that algebras form a Grothendieck fibration (a displayed category with a cleaving)
  over algebraic theories.

  Contents
  1. The cleaving [algebra_cleaving]
  2. The fibration [algebra_fibration]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. The cleaving *)

Section Cleaving.

  Context {T T' : algebraic_theory}.
  Context (F : algebraic_theory_morphism T' T).
  Context (A : algebra T).

  Definition algebra_cleaving_algebra_data
    : algebra_data T'.
  Proof.
    use tpair.
    - exact A.
    - intros n f a.
      exact (action (F _ f) a).
  Defined.

  Lemma algebra_cleaving_is_algebra
    : is_algebra algebra_cleaving_algebra_data.
  Proof.
    repeat split.
    - do 5 intro.
      simpl.
      rewrite (algebraic_theory_morphism_preserves_composition F).
      apply algebra_is_assoc.
    - intro.
      rewrite <- algebra_is_unital.
      simpl.
      apply (maponpaths (λ i, _ _ i _)).
      apply algebraic_theory_morphism_preserves_id_pr.
    - do 5 intro.
      simpl.
      rewrite (maponpaths (λ x, x _) (nat_trans_ax (F : algebraic_theory_morphism _ _) _ _ _
        : (λ x, _ _ (# (T' : algebraic_theory) _ _)) = _)).
      apply algebra_is_natural.
  Qed.

  Definition algebra_cleaving_algebra
    : algebra T'
    := make_algebra _ algebra_cleaving_is_algebra.

  Definition algebra_cleaving_morphism
    : (algebra_cleaving_algebra : algebra_disp_cat _) -->[F] A.
  Proof.
    use (idfun _ ,, _ ,, tt).
    abstract now do 3 intro.
  Defined.

  Section Lift.

    Context {T'' : algebraic_theory}.
    Context {A'' : algebra T''}.
    Context (F' : algebraic_theory_morphism T'' T').
    Context (G' : (A'' : algebra_disp_cat _) -->[(F' : algebraic_theory_cat⟦_, _⟧) · F] A).

    Definition algebra_cleaving_induced_morphism
      : (A'' : algebra_disp_cat _) -->[F'] algebra_cleaving_algebra.
    Proof.
      use (pr1 G' ,, _ ,, tt).
      abstract (do 3 intro; now rewrite (pr12 G')).
    Defined.

    Definition algebra_lift
      : ∑ gg, (gg ;; algebra_cleaving_morphism) = G'.
    Proof.
      exists algebra_cleaving_induced_morphism.
      apply displayed_algebra_morphism_eq.
      exact (comp_disp_cartesian _ _ _ _).
    Defined.

    Lemma algebra_lift_is_unique
      : ∏ t : (∑ gg, (gg ;; algebra_cleaving_morphism) = G'), t = algebra_lift.
    Proof.
      intro t.
      apply subtypePath.
      {
        intro.
        apply homsets_disp.
      }
      apply displayed_algebra_morphism_eq.
      exact (!comp_disp_cartesian _ _ (pr11 t) _ @ maponpaths _ (pr2 t)).
    Qed.

  End Lift.

  Definition algebra_cleaving_is_cartesian
    : is_cartesian algebra_cleaving_morphism
    := (λ _ F' _ G', algebra_lift F' G' ,, algebra_lift_is_unique F' G').

End Cleaving.

Definition algebra_cleaving
  : cleaving algebra_disp_cat
  := λ _ _ F A,
    algebra_cleaving_algebra F A ,,
    algebra_cleaving_morphism F A ,,
    algebra_cleaving_is_cartesian F A.

(** * 2. The fibration *)

Definition algebra_fibration
  : fibration algebraic_theory_cat
  := _ ,, algebra_cleaving.
