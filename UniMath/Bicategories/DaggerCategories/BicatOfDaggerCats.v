(* In this file, we construct the bicategory of dagger categories using displayed bicategories and we show that the displayed bicategory is univalent. *)

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

  (* Don't know why the coercion doesn't work *)
  Definition DAG_to_dagger (C : DAG) : dagger (DAG_to_cat C) := pr2 C.

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

  Lemma isaprop_DAG_disp_left_adjoint_data
        {a b : CAT} {f : CAT⟦ a, b ⟧}
        (l : left_adjoint_data f) {aa : DAG_disp_bicat a} {bb : DAG_disp_bicat b}
        (ff : aa -->[ f] bb)
    : isaprop (disp_left_adjoint_data l ff).
  Proof.
    unfold disp_left_adjoint_data.
    use isaproptotal2.
    - intro ; apply isapropdirprod ; apply isapropunit.
    - intro ; intros ; apply isaprop_is_dagger_functor.
  Qed.

  Lemma isaprop_DAG_disp_left_adjoint_axioms
        {a b : CAT} {f : CAT⟦ a, b ⟧}
        {j : left_adjoint f} {aa : DAG_disp_bicat a} {bb : DAG_disp_bicat b}
        {ff : aa -->[ f] bb}
        (jj : disp_left_adjoint_data j ff)
    : isaprop (disp_left_adjoint_axioms j jj).
  Proof.
    apply isapropdirprod ; apply isasetaprop, isapropunit.
  Qed.

  Lemma isaprop_DAG_disp_left_equivalence_axioms
        {a b : CAT} {f : CAT⟦ a, b ⟧}
        {j : left_equivalence f} {aa : DAG_disp_bicat a} {bb : DAG_disp_bicat b}
        {ff : aa -->[ f] bb}
        (jj : disp_left_adjoint_data j ff)
    : isaprop (disp_left_equivalence_axioms j jj).
  Proof.
    apply isapropdirprod ; apply isaprop_is_disp_invertible_2cell.
  Qed.

  Lemma isaprop_disp_left_adjoint_equivalence_DAG
        {C D : DAG}
        {f : adjoint_equivalence (pr1 C) (pr1 D)}
        (ff : Core.mor_disp (pr2 C) (pr2 D) f)
    : isaprop (disp_left_adjoint_equivalence f ff).
  Proof.
    use isaproptotal2.
    - intro.
      apply isapropdirprod.
      + apply isaprop_DAG_disp_left_adjoint_axioms.
      + apply isaprop_DAG_disp_left_equivalence_axioms.
    - do 4 intro.
      apply isaprop_DAG_disp_left_adjoint_data.
  Qed.

  Lemma isaprop_disp_adjoint_equivalence_DAG
        {C D : DAG}
        {f : adjoint_equivalence (pr1 C) (pr1 D)}
        (ff : Core.mor_disp (pr2 C) (pr2 D) f)
    : isaprop (disp_adjoint_equivalence f (pr2 C) (pr2 D)).
  Proof.
    exact (isaprop_total2
             (_ ,, isaprop_is_dagger_functor _ _ _)
             (λ _ , _ ,, isaprop_disp_left_adjoint_equivalence_DAG _)
          ).
  Qed.

  Lemma DAG_disp_univalent_2_0 : disp_univalent_2_0 DAG_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros C udag1 udag2.
    apply isweqimplimpl.

    - intro a.
      apply dagger_equality.
      repeat (apply funextsec ; intro).
      apply (pr1 a _).
    - intro ; apply isaset_dagger.
    - intro a.
      apply (isaprop_disp_adjoint_equivalence_DAG (C := C ,, udag1) (D := C ,, udag2) a).
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

  Definition make_dagger_category
             {C : category} (d : dagger C)
    : ob DAG := C ,, d.

  Definition make_dagger_category'
             {C : category}
             {d : dagger_structure C}
             (dl : dagger_laws d)
    : ob DAG := C ,, d ,, dl.

  Definition make_dagger_laws
             {C : category} {d : dagger_structure C}
             (lid : dagger_law_id d)
             (lcomp : dagger_law_comp d)
             (lidemp : dagger_law_idemp d)
    : dagger_laws d
    := lid ,, lcomp ,, lidemp.

  Definition make_dagger_functor
             {C D : category}
             {F : functor C D}
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
    : DAG⟦make_dagger_category dagC, make_dagger_category dagD⟧
    := F ,, dagF.

  Definition make_dagger_transformation
             {C D : category}
             {F G : functor C D}
             (α : nat_trans F G)
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
    : (hom (make_dagger_category dagC) (make_dagger_category dagD))
        ⟦make_dagger_functor dagF, make_dagger_functor dagG⟧
    := α ,, tt.

  Definition make_dagger_transformation'
             {C D : category}
             {F G : functor C D}
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             {α : nat_trans_data F G}
             (αn : is_nat_trans _ _ α)
    : (hom (make_dagger_category dagC) (make_dagger_category dagD))
        ⟦make_dagger_functor dagF, make_dagger_functor dagG⟧
    := make_nat_trans _ _ α αn ,, tt.

End Constructors.
