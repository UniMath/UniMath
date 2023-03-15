(* In this file, we construct the bicategory DAG of dagger categories as a displayed bicategory (over CAT) and we show that the displayed bicategory is univalent. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Transformations.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.
Require Import UniMath.CategoryTheory.DaggerCategories.FunctorCategory.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Definition CAT : bicat := bicat_of_cats.

Local Open Scope cat.

Section BicatOfDaggerCategories.

  Definition DAG_disp_cat_ob_mor
    : disp_cat_ob_mor CAT.
  Proof.
    exists (λ C, dagger C).
    exact (λ C D dC dD F, is_dagger_functor dC dD F).
  Defined.

  Definition DAG_disp_cat_id_comp
    : disp_cat_id_comp CAT DAG_disp_cat_ob_mor.
  Proof.
    exists (λ C dC, dagger_functor_id dC).
    exact (λ C D E F G dC dD dE dF dG, is_dagger_functor_comp dF dG).
  Qed.

  Definition DAG_disp_cat_data
    :  disp_cat_data CAT.
  Proof.
    exists DAG_disp_cat_ob_mor.
    exact DAG_disp_cat_id_comp.
  Defined.

  Definition DAG_disp_bicat : disp_bicat CAT
    := disp_cell_unit_bicat DAG_disp_cat_data.

  Definition DAG : bicat
    := total_bicat DAG_disp_bicat.

  Definition is_dagger_univalent (D : DAG)
    : UU
    := is_univalent_dagger (pr2 D).

  Definition UDAG_disp_bicat : disp_bicat DAG
    := disp_fullsubbicat DAG (λ D, is_dagger_univalent D).

  Definition UDAG_sigma_disp_bicat := sigma_bicat _ _ UDAG_disp_bicat.

End BicatOfDaggerCategories.

Section Destructors.

  Definition DAG_to_cat (C : DAG) : category := pr1 C.
  Coercion DAG_to_cat : ob >-> category.

  Definition DAG_to_dagger (C : DAG) : dagger C := pr2 C.

End Destructors.

Section DaggerFunctorCategories.

  Local Definition hom_equals_dagger_functor_cat
             (C D : DAG)
    : hom C D = dagger_functor_cat (DAG_to_dagger C) (DAG_to_dagger D).
  Proof.
    use subtypePath.
    { intro ; apply isaprop_has_homsets. }
    use total2_paths_f.
    - apply idpath.
    - use proofirrelevance.
      repeat (apply isapropdirprod)
      ; repeat (apply impred_isaprop ; intro)
      ; apply (cellset_property (C := DAG)).
  Defined.

End DaggerFunctorCategories.

Section DagDisplayedUnivalence.

  Lemma DAG_disp_univalent_2_0 : disp_univalent_2_0 DAG_disp_bicat.
  Proof.
    intros C1 C2 p dag1 dag2.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros C udag1 udag2.
    apply isweqimplimpl.
    - intro a.
      apply dagger_equality.
      repeat (apply funextsec ; intro).
      apply (pr1 a _).
    - intro ; apply isaset_dagger.
    - intro a.
      apply (isaprop_disp_adjoint_equivalence_cell_unit_bicat a)
      ; apply isaprop_is_dagger_functor.
  Qed.

  Lemma DAG_disp_univalent_2_1 : disp_univalent_2_1 DAG_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intro ; intros ; apply isaprop_is_dagger_functor.
  Qed.

  (* Notice that for global univalence, we don't use the premade lemma
     for disp_cell_unit_bicat, as is used in the local univalence.
     Otherwise, we would have to restrict ourselves to CatUniv instead of Cat
   *)

  Definition DAG_disp_univalent_2 : disp_univalent_2 DAG_disp_bicat
    := DAG_disp_univalent_2_0 ,, DAG_disp_univalent_2_1.

End DagDisplayedUnivalence.

Section Constructors.

  Definition make_dagger_transformation
             {C D : category}
             {F G : functor C D}
             (α : nat_trans F G)
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
    : (hom (C := DAG) (C,,dagC) (D,,dagD))
        ⟦make_dagger_functor _ _  dagF, make_dagger_functor _ _ dagG⟧
    := α ,, tt.

  Definition make_dagger_transformation'
             {C D : category}
             {F G : functor C D}
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             {α : nat_trans_data F G}
             (αn : is_nat_trans _ _ α)
    : (hom (C := DAG) (C,,dagC) (D,,dagD))
        ⟦make_dagger_functor _ _ dagF, make_dagger_functor _ _ dagG⟧
    := make_nat_trans _ _ α αn ,, tt.

End Constructors.
