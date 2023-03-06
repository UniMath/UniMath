(** construction of a (displayed) pseudofunctor from the operation [lifted_actegory] on actegories

author: Ralph Matthes 2023

*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.MonoidalOld.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.MonoidalOld.Actegories.
Require Import UniMath.CategoryTheory.MonoidalOld.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.MonoidalOld.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.MonoidalOld.ConstructionOfActegoryMorphisms.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.

Local Open Scope cat.

Section PseudofunctorFromLifting.

  Context {V : category} (Mon_V : monoidal V) {W : category} (Mon_W : monoidal W)
    {F : W ⟶ V} (U : fmonoidal Mon_W Mon_V F).

  Let dBV : disp_bicat bicat_of_cats := bidisp_actbicat_disp_bicat Mon_V.
  Let dBW : disp_bicat bicat_of_cats := bidisp_actbicat_disp_bicat Mon_W.

  Definition lifting_actegories_disp_psfunctor : disp_psfunctor dBV dBW (id_psfunctor _).
  Proof.
    use make_disp_psfunctor.
    - apply actbicat_disp_2cells_isaprop.
    - apply actbicat_disp_locally_groupoid.
    - intros C Act.
      exact (lifted_actegory Mon_V Act Mon_W U).
    - intros C D H ActC ActD ll.
      exact (lifted_lax_lineator Mon_V Mon_W U ActC ActD ll).
    - intros C D H K ξ ActC ActD Hl Kl islntξ.
      apply preserves_linearity_lifted_lax_lineator.
      exact islntξ.
    - abstract (intros C ActC w c;
                cbn;
                rewrite bifunctor_leftid;
                do 2 rewrite id_left;
                apply idpath).
    - abstract (intros C D E H K ActC ActD ActE Hl Kl w c;
        cbn;
        rewrite bifunctor_leftid;
        rewrite id_left, id_right;
        apply idpath).
  Defined.

  Definition lifting_actegories_psfunctor : psfunctor (actbicat Mon_V) (actbicat Mon_W)
    := total_psfunctor dBV dBW (id_psfunctor _) lifting_actegories_disp_psfunctor.

End PseudofunctorFromLifting.
