(**
Monads as a bicategory. The construction has 3 layers.
In the first layer: we take algebras on the identity functor.
In the second layer: we add η an μ. This is done by adding 2-cells (as in Add2Cell)
In the third layer: we take the full subcategory and we add the monad laws.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
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

Definition var
           {C : bicat}
           (F S : psfunctor C C)
  : pstrans
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         S (pr1_psfunctor (disp_alg_bicat F)))
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         S (pr1_psfunctor (disp_alg_bicat F)))
  := id₁ _.

Definition alg_map
           {C : bicat}
           (F : psfunctor C C)
  : pstrans
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         F (pr1_psfunctor (disp_alg_bicat F)))
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         (ps_id_functor C) (pr1_psfunctor (disp_alg_bicat F))).
Proof.
  use mk_pstrans.
  - use mk_pstrans_data.
    + intros X ; cbn in *.
      exact (pr2 X).
    + intros X Y f ; cbn in *.
      exact (pr2 f).
  - repeat split ; cbn.
    + intros X Y f g α.
      apply α.
    + intros.
      rewrite !id2_left, lwhisker_id2, psfunctor_id2.
      rewrite !id2_left, !id2_right.
      reflexivity.
    + intros.
      rewrite !id2_left, lwhisker_id2, psfunctor_id2.
      rewrite !id2_left, !id2_right.
      reflexivity.
Defined.

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
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 plain_monad.
  Proof.
    apply bicat_algebra_is_univalent_2_0.
    - exact HC_0.
    - exact HC_1.
  Defined.

  Definition add_unit
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact (var _ _).
    - exact (alg_map _).
  Defined.

  Definition add_bind
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact ((alg_map _) · (alg_map _)).
    - exact (alg_map _).
  Defined.

  Definition add_unit_bind
    : disp_bicat plain_monad
    := disp_dirprod_bicat add_unit add_bind.

  Definition lawless_monad := total_bicat add_unit_bind.

  Definition lawless_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 lawless_monad.
  Proof.
    apply is_univalent_2_1_total_dirprod.
    - exact (plain_monad_is_univalent_2_1 HC_1).
    - apply add_cell_disp_cat_locally_univalent.
    - apply add_cell_disp_cat_locally_univalent.
  Defined.

  Definition lawless_monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 lawless_monad.
  Proof.
    apply is_univalent_2_0_total_dirprod.
    - exact (plain_monad_is_univalent_2_0 HC_0 HC_1).
    - apply plain_monad_is_univalent_2_1.
      exact HC_1.
    - apply add_cell_disp_cat_univalent_2_0.
      + exact HC_1.
      + apply disp_alg_bicat_locally_univalent.
    - apply add_cell_disp_cat_univalent_2_0.
      + exact HC_1.
      + apply disp_alg_bicat_locally_univalent.
    - apply add_cell_disp_cat_locally_univalent.
    - apply add_cell_disp_cat_locally_univalent.
  Defined.

  Definition monad_obj : lawless_monad → C
    := λ m, pr1 (pr1 m).

  Definition monad_map : ∏ (m : lawless_monad), monad_obj m --> monad_obj m
    := λ m, pr2(pr1 m).

  Definition monad_unit : ∏ (m : lawless_monad), id₁ (monad_obj m) ==> monad_map m
    := λ m, pr1(pr2 m).

  Definition monad_bind
    : ∏ (m : lawless_monad), monad_map m · monad_map m ==> monad_map m
    := λ m, pr2(pr2 m).

  Definition monad_laws (m : lawless_monad) : UU
    := ((linvunitor (monad_map m))
          • (monad_unit m ▹ monad_map m)
          • monad_bind m
        =
        id₂ (monad_map m))
       ×
       ((rinvunitor (monad_map m))
          • (monad_map m ◃ monad_unit m)
          • monad_bind m
        =
        id₂ (monad_map m))
       ×
       ((monad_map m ◃ monad_bind m)
          • monad_bind m
        =
        (lassociator (monad_map m) (monad_map m) (monad_map m))
          • (monad_bind m ▹ monad_map m)
          • monad_bind m).

  Definition monad := fullsubbicat lawless_monad monad_laws.

  Definition mk_monad
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
    - use tpair.
      + use tpair.
        * exact X.
        * exact f.
      + split.
        * exact η.
        * exact μ.
    - repeat split.
      + exact ημ.
      + exact μη.
      + exact μμ.
  Defined.

  Definition monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 monad.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply lawless_monad_is_univalent_2_1.
    exact HC_1.
  Defined.

  Definition monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 monad.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - exact (lawless_monad_is_univalent_2_0 HC_0 HC_1).
    - exact (lawless_monad_is_univalent_2_1 HC_1).
    - intro ; simpl.
      repeat (apply isapropdirprod) ; apply C.
  Defined.
End MonadBicategory.