(**
In this file, the cofree adjunction between a linear category and its Eilenberg-Moore category is constructed.
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.categories.Dialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.

Require Import UniMath.CategoryTheory.categories.CoEilenbergMoore.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalCoEilenbergMoore.

Require Import UniMath.Semantics.LinearLogic.LinearCategory.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section CofreeAdjunction.

  Context (𝕃 : linear_category).

  Definition eilenberg_moore_cofree
    : 𝕃 ⟶ cat_co_eilenberg_moore (linear_category_bang 𝕃).
  Proof.
    use functor_to_co_eilenberg_moore_cat.
    - apply (linear_category_bang 𝕃).
    - use nat_trans_comp.
      2: { apply nat_trans_functor_id_left. }
      exact (δ (linear_category_bang 𝕃)).
    - abstract (
          intro x;
          refine (_ @ Comonad_law1 (T := linear_category_bang 𝕃) x);
          refine (assoc' _ _ _ @ _);
          apply id_left).
    - abstract (
          intro x;
          cbn;
          rewrite id_left;
          exact (Comonad_law3 (T := linear_category_bang 𝕃) x)).
  Defined.

  Local Definition eilenberg_moore_forget
    : cat_co_eilenberg_moore (linear_category_bang 𝕃) ⟶ 𝕃.
  Proof.
    exact (functor_composite (pr1_category _) (pr1_category _)).
  Defined.

  Local Definition eilenberg_moore_adj_unit
    : functor_identity
        (cat_co_eilenberg_moore (linear_category_bang 𝕃)) ⟹
        eilenberg_moore_forget ∙ eilenberg_moore_cofree.
  Proof.
    use make_nat_trans.
    - intro x.
      use make_mor_co_eilenberg_moore.
      + exact (pr21 x).
      + abstract (
            refine (! pr22 x @ _);
            apply maponpaths,
              pathsinv0,
              id_left).
    - abstract (
          intros x y f;
          use eq_mor_co_eilenberg_moore;
          exact (! pr21 f)).
  Defined.

  Lemma eilenberg_moore_cmd_form_adj
    :  form_adjunction'
         (eilenberg_moore_forget,,
            eilenberg_moore_cofree,,
            eilenberg_moore_adj_unit,,
            ε (linear_category_bang 𝕃)).
  Proof.
    split.
    - exact (λ x, pr12 x).
    - intro x.
      use eq_mor_co_eilenberg_moore.
      cbn.
      refine (assoc' _ _ _ @ _).
      refine (id_left _ @ _).
      exact (Comonad_law2 (T := linear_category_bang 𝕃) x).
  Qed.

  Definition eilenberg_moore_cmd_adj
    : adjunction
    (cat_co_eilenberg_moore (linear_category_bang 𝕃)) 𝕃.
  Proof.
    use make_adjunction.
    - simple refine (_ ,, _ ,, _ ,, _).
      + exact eilenberg_moore_forget.
      + exact eilenberg_moore_cofree.
      + exact eilenberg_moore_adj_unit.
      + exact (ε (linear_category_bang 𝕃)).
    - exact eilenberg_moore_cmd_form_adj.
  Defined.

End CofreeAdjunction.
