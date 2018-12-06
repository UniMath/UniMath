Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.identity.
Require Import UniMath.CategoryTheory.Bicategories.LaxTransformation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Sigma.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.

Definition TODO {A : UU} : A.
Admitted.

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

  Definition unit_left_data
    : laxtrans_data (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use mk_laxtrans_data.
    - intros X.
      exact (id₁ _).
    - intros X Y f
      ; cbn in * ; unfold total_prebicat_cell_struct in * ; cbn in *
      ; unfold alg_disp_cat_2cell in * ; cbn in *.
      exists (lunitor _ • rinvunitor _).
      apply TODO.
  Defined.

  Definition unit_left_laws
    : is_laxtrans unit_left_data.
  Proof.
    apply TODO.
  Qed.

  (* identity *)
  Definition unit_left
    : pstrans (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use tpair.
    - use tpair.
      + exact unit_left_data.
      + exact unit_left_laws.
    - apply TODO.
  Defined.

  Definition unit_right_data
    : laxtrans_data (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use mk_laxtrans_data.
    - intros X.
      cbn in * ; unfold total_prebicat_cell_struct in * ; cbn in *
      ; unfold alg_disp_cat_2cell in * ; cbn in *.
      exists (pr2 X).
      exact (id₂ _).
    - intros X Y f
      ; cbn in * ; unfold total_prebicat_cell_struct in * ; cbn in *
      ; unfold alg_disp_cat_2cell in * ; cbn in *.
      apply TODO.
  Defined.

  Definition unit_right_laws
    : is_laxtrans unit_right_data.
  Proof.
    apply TODO.
  Qed.

  (* algebra map *)
  Definition unit_right
    : pstrans (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use tpair.
    - use tpair.
      + exact unit_right_data.
      + exact unit_right_laws.
    - apply TODO.
  Defined.

  Definition add_unit
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact unit_left.
    - exact unit_right.
  Defined.

  (* composition of the algebra map *)
  Definition bind_left_data
    : laxtrans_data (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use mk_laxtrans_data.
    - intros X.
      cbn in *.
      exists (pr2 X · pr2 X).
      exact (lassociator _ _ _).
    - intros X Y f
      ; cbn in * ; unfold total_prebicat_cell_struct in * ; cbn in *
      ; unfold alg_disp_cat_2cell in * ; cbn in *.
      apply TODO.
  Defined.

  Definition bind_left_laws
    : is_laxtrans bind_left_data.
  Proof.
    apply TODO.
  Qed.

  Definition bind_left
    : pstrans (ps_id_functor plain_monad) (ps_id_functor plain_monad).
  Proof.
    use tpair.
    - use tpair.
      + exact bind_left_data.
      + exact bind_left_laws.
    - apply TODO.
  Defined.

  Definition add_bind
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact bind_left.
    - exact unit_right.
  Defined.

  Definition add_unit_bind
    : disp_bicat plain_monad
    := disp_dirprod_bicat add_unit add_bind.

  Definition lawless_monad := total_bicat add_unit_bind.

  Definition lawless_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 lawless_monad.
  Proof.
    apply total_is_locally_univalent.
    - exact (plain_monad_is_univalent_2_1 HC_1).
    - apply is_univalent_2_1_dirprod_bicat.
      * apply add_cell_disp_cat_locally_univalent.
      * apply add_cell_disp_cat_locally_univalent.
  Defined.

  Definition lawless_monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 lawless_monad.
  Proof.
    apply total_is_univalent_2_0.
    - exact (plain_monad_is_univalent_2_0 HC_0 HC_1).
    - apply is_univalent_2_0_dirprod_bicat.
      + exact (plain_monad_is_univalent_2_1 HC_1).
      + apply add_cell_disp_cat_univalent_2_0.
        * exact HC_1.
        * apply disp_alg_bicat_locally_univalent.
      + apply add_cell_disp_cat_univalent_2_0.
        * exact HC_1.
        * apply disp_alg_bicat_locally_univalent.
      + apply add_cell_disp_cat_locally_univalent.
      + apply add_cell_disp_cat_locally_univalent.
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