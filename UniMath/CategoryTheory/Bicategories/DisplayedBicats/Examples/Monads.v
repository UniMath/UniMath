(**
Monads as a bicategory. The construction has 3 layers.
In the first layer: we take algebras on the identity functor.
In the second layer: we add η an μ. This is done by adding 2-cells (as in Add2Cell)
In the third layer: we take the full subcategory and we add the monad laws.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.AlgebraMap.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Sigma.
Local Open Scope cat.

Section MonadBicategory.
  Variable (C : bicat).

  Definition plain_monad
    : bicat
    := bicat_algebra (ps_id_functor C).

  Definition plain_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 plain_monad.
  Proof.
    apply bicat_algebra_is_univalent_2_1.
    exact HC_1.
  Defined.

  Definition plain_monad_is_univalent_2_0
             (HC : is_univalent_2 C)
    : is_univalent_2_0 plain_monad.
  Proof.
    apply bicat_algebra_is_univalent_2_0.
    exact HC.
  Defined.

  Definition plain_monad_is_univalent_2
             (HC : is_univalent_2 C)
    : is_univalent_2 plain_monad.
  Proof.
    split.
    - apply plain_monad_is_univalent_2_0; assumption.
    - apply plain_monad_is_univalent_2_1.
      exact (pr2 HC).
  Defined.

  Definition add_unit
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact (var _ _).
    - exact (alg_map _).
  Defined.

  Definition add_mu
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact ((alg_map _) · (alg_map _)).
    - exact (alg_map _).
  Defined.

  Definition add_unit_mu
    : disp_bicat C
    := sigma_bicat _ _ (disp_dirprod_bicat add_unit add_mu).

  Definition lawless_monad := total_bicat add_unit_mu.

  Definition lawless_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 lawless_monad.
  Proof.
    apply sigma_is_univalent_2_1.
    - exact HC_1.
    - apply disp_alg_bicat_univalent_2_1.
    - apply is_univalent_2_1_dirprod_bicat.
      + apply add_cell_disp_cat_univalent_2_1.
      + apply add_cell_disp_cat_univalent_2_1.
  Defined.

  Definition lawless_monad_is_univalent_2_0
             (HC : is_univalent_2 C)
    : is_univalent_2_0 lawless_monad.
  Proof.
    pose (HC_1 := pr2 HC).
    apply sigma_is_univalent_2_0.
    - exact HC.
    - split.
      + apply disp_alg_bicat_univalent_2_0.
        apply HC.
      + apply disp_alg_bicat_univalent_2_1.
    - split.
      + apply is_univalent_2_0_dirprod_bicat.
        * apply total_is_univalent_2_1.
          ** exact (pr2 HC).
          ** apply disp_alg_bicat_univalent_2_1.
        * apply add_cell_disp_cat_univalent_2.
          ** exact (pr2 HC).
          ** apply disp_alg_bicat_univalent_2_1.
        * apply add_cell_disp_cat_univalent_2.
          ** exact (pr2 HC).
          ** apply disp_alg_bicat_univalent_2_1.
      + apply is_univalent_2_1_dirprod_bicat.
        * apply add_cell_disp_cat_univalent_2_1.
        * apply add_cell_disp_cat_univalent_2_1.
  Defined.

  Definition lawless_monad_is_univalent_2
             (HC : is_univalent_2 C)
    : is_univalent_2 lawless_monad.
  Proof.
    split.
    - apply lawless_monad_is_univalent_2_0; assumption.
    - apply lawless_monad_is_univalent_2_1.
      exact (pr2 HC).
  Defined.

  Definition monad_obj : lawless_monad → C
    := λ m, pr1 m.

  Definition monad_map : ∏ (m : lawless_monad), monad_obj m --> monad_obj m
    := λ m, pr12 m.

  Definition monad_unit : ∏ (m : lawless_monad), id₁ (monad_obj m) ==> monad_map m
    := λ m, pr122 m.

  Definition monad_mu
    : ∏ (m : lawless_monad), monad_map m · monad_map m ==> monad_map m
    := λ m, pr222 m.

  Definition monad_laws (m : lawless_monad) : UU
    := ((linvunitor (monad_map m))
          • (monad_unit m ▹ monad_map m)
          • monad_mu m
        =
        id₂ (monad_map m))
       ×
       ((rinvunitor (monad_map m))
          • (monad_map m ◃ monad_unit m)
          • monad_mu m
        =
        id₂ (monad_map m))
       ×
       ((monad_map m ◃ monad_mu m)
          • monad_mu m
        =
        (lassociator (monad_map m) (monad_map m) (monad_map m))
          • (monad_mu m ▹ monad_map m)
          • monad_mu m).

  Definition disp_monad : disp_bicat C
    := sigma_bicat _ _ (disp_fullsubbicat lawless_monad monad_laws).

  Definition monad := total_bicat disp_monad.

  Definition make_monad
             (X : C)
             (f : C⟦X,X⟧)
             (η : id₁ X ==> f)
             (μ : f · f ==> f)
             (ημ : linvunitor f • (η ▹ f) • μ
                   =
                   id₂ f)
             (μη : rinvunitor f • (f ◃ η) • μ
                   =
                   id₂ f)
             (μμ : (f ◃ μ) • μ
                   =
                   lassociator f f f • (μ ▹ f) • μ)
    : monad.
  Proof.
    use tpair.
    - exact X.
    - use tpair.
      + use tpair.
        * exact f.
        * split.
          ** exact η.
          ** exact μ.
      + repeat split.
        * exact ημ.
        * exact μη.
        * exact μμ.
  Defined.

  (*
  Definition monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 monad.
  Proof.
    apply sigma_is_univalent_2_1.
    - exact HC_1.
    - apply is_univalent_2_1_fullsubbicat.
      apply lawless_monad_is_univalent_2_1.
    exact HC_1.
  Defined.

  Definition monad_is_univalent_2_0
             (HC : is_univalent_2 C)
    : is_univalent_2_0 monad.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - exact (lawless_monad_is_univalent_2 HC).
    - intro ; simpl.
      repeat (apply isapropdirprod) ; apply C.
  Defined.

  Definition monad_is_univalent_2
             (HC : is_univalent_2 C)
    : is_univalent_2 monad.
  Proof.
    split.
    - apply monad_is_univalent_2_0; assumption.
    - apply monad_is_univalent_2_1.
      exact (pr2 HC).
  Defined.
   *)

End MonadBicategory.
