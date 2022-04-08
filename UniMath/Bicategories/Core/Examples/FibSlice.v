Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Section FibSlice.
  Context (C : univalent_category).

  Definition fib_slice_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (∑ (D : disp_univalent_category C), cleaving D).
    - exact (λ D₁ D₂, cartesian_disp_functor
                        (functor_identity _)
                        (pr1 D₁)
                        (pr1 D₂)).
  Defined.

  Definition fib_slice_precategory_id_comp
    : precategory_id_comp fib_slice_precategory_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ D, disp_functor_identity (pr1 D)
                  ,,
                  disp_functor_identity_is_cartesian_disp_functor (pr1 D)).
    - exact (λ D₁ D₂ D₃ FF GG,
             disp_functor_over_id_composite (pr1 FF) (pr1 GG)
             ,,
             disp_functor_over_id_composite_is_cartesian (pr2 FF) (pr2 GG)).
  Defined.

  Definition fib_slice_precategory_data
    : precategory_data.
  Proof.
    simple refine (_ ,, _).
    - exact fib_slice_precategory_ob_mor.
    - exact fib_slice_precategory_id_comp.
  Defined.

  Definition fib_slice_prebicat_1_id_comp_cells
    : prebicat_1_id_comp_cells.
  Proof.
    simple refine (_ ,, _).
    - exact fib_slice_precategory_data.
    - exact (λ D₁ D₂ FF GG,
             disp_nat_trans
               (nat_trans_id _)
               (pr1 FF)
               (pr1 GG)).
  Defined.

  Definition fib_slice_prebicat_2_id_comp_struct
    : prebicat_2_id_comp_struct fib_slice_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ D₃ D₃ FF GG HH, disp_nat_trans_id _).
    - exact (λ D₁ D₂ D₃ D₃ FF GG HH, disp_nat_trans_id _).
    - exact (λ D₁ D₂ FF GG HH α β, disp_nat_trans_over_id_comp α β).
    - exact (λ D₁ D₂ D₃ FF GG₁ GG₂ α, disp_nat_trans_over_id_prewhisker (pr1 FF) α).
    - exact (λ D₁ D₂ D₃ FF₁ FF₂ GG α, disp_nat_trans_over_id_postwhisker (pr1 GG) α).
  Defined.

  Definition fib_slice_prebicat_data
    : prebicat_data.
  Proof.
    simple refine (_ ,, _).
    - exact fib_slice_prebicat_1_id_comp_cells.
    - exact fib_slice_prebicat_2_id_comp_struct.
  Defined.

  Definition fib_slice_prebicat_laws
    : prebicat_laws fib_slice_prebicat_data.
  Proof.
    repeat split.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros ? ? ? F G ; use disp_nat_trans_eq ; intros ; cbn.
      exact (disp_functor_id (pr1 G) _).
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros D₁ D₂ D₃ FF₁ FF₂ FF₃ GG α β.
      use disp_nat_trans_eq ; intros x xx ; cbn.
      rewrite (disp_functor_transportf _ (pr1 GG)).
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ FF GG HH II α β.
      use disp_nat_trans_eq ; intros x xx ; cbn in *.
      etrans.
      {
        apply maponpaths.
        exact (disp_nat_trans_ax β (α x xx)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intros D₁ D₂ D₃ F G.
      use disp_nat_trans_eq ; intros x xx ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite (disp_functor_id (pr1 G)).
      cbn.
      apply transportf_set.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ D₅ FF GG HH II.
      use disp_nat_trans_eq ; intros ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite (disp_functor_id (pr1 II)).
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition fib_slice_prebicat
    : prebicat.
  Proof.
    simple refine (_ ,, _).
    - exact fib_slice_prebicat_data.
    - exact fib_slice_prebicat_laws.
  Defined.

  Definition fib_slice_bicat
    : bicat.
  Proof.
    simple refine (_ ,, _).
    - exact fib_slice_prebicat.
    - intro ; intros.
      apply isaset_disp_nat_trans.
  Defined.

  Definition is_invertible_2cell_fib_slice
             {D₁ D₂ : fib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (α : G₁ ==> G₂)
             (Hα : (∏ (x : C)
                      (xx : pr1 D₁ x),
                    is_iso_disp (identity_iso x) (pr1 α x xx)))
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - exact (pointwise_inverse_disp_nat_trans α Hα).
    - apply pointwise_inverse_disp_nat_trans_over_id_left.
    - apply pointwise_inverse_disp_nat_trans_over_id_right.
  Defined.
End FibSlice.

Section OpFibSlice.
  Context (C : univalent_category).

  Definition opfib_slice_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (∑ (D : disp_univalent_category C), opcleaving D).
    - exact (λ D₁ D₂, opcartesian_disp_functor
                        (functor_identity _)
                        (pr1 D₁)
                        (pr1 D₂)).
  Defined.

  Definition opfib_slice_precategory_id_comp
    : precategory_id_comp opfib_slice_precategory_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ D, disp_functor_identity (pr1 D)
                  ,,
                  disp_functor_identity_is_opcartesian_disp_functor (pr1 D)).
    - exact (λ D₁ D₂ D₃ FF GG,
             disp_functor_over_id_composite (pr1 FF) (pr1 GG)
             ,,
             disp_functor_over_id_composite_is_opcartesian (pr2 FF) (pr2 GG)).
  Defined.

  Definition opfib_slice_precategory_data
    : precategory_data.
  Proof.
    simple refine (_ ,, _).
    - exact opfib_slice_precategory_ob_mor.
    - exact opfib_slice_precategory_id_comp.
  Defined.

  Definition opfib_slice_prebicat_1_id_comp_cells
    : prebicat_1_id_comp_cells.
  Proof.
    simple refine (_ ,, _).
    - exact opfib_slice_precategory_data.
    - exact (λ D₁ D₂ FF GG,
             disp_nat_trans
               (nat_trans_id _)
               (pr1 FF)
               (pr1 GG)).
  Defined.

  Definition opfib_slice_prebicat_2_id_comp_struct
    : prebicat_2_id_comp_struct opfib_slice_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ FF, disp_nat_trans_id (pr1 FF)).
    - exact (λ D₁ D₂ D₃ D₃ FF GG HH, disp_nat_trans_id _).
    - exact (λ D₁ D₂ D₃ D₃ FF GG HH, disp_nat_trans_id _).
    - exact (λ D₁ D₂ FF GG HH α β, disp_nat_trans_over_id_comp α β).
    - exact (λ D₁ D₂ D₃ FF GG₁ GG₂ α, disp_nat_trans_over_id_prewhisker (pr1 FF) α).
    - exact (λ D₁ D₂ D₃ FF₁ FF₂ GG α, disp_nat_trans_over_id_postwhisker (pr1 GG) α).
  Defined.

  Definition opfib_slice_prebicat_data
    : prebicat_data.
  Proof.
    simple refine (_ ,, _).
    - exact opfib_slice_prebicat_1_id_comp_cells.
    - exact opfib_slice_prebicat_2_id_comp_struct.
  Defined.

  Definition opfib_slice_prebicat_laws
    : prebicat_laws opfib_slice_prebicat_data.
  Proof.
    repeat split.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros ? ? ? F G ; use disp_nat_trans_eq ; intros ; cbn.
      exact (disp_functor_id (pr1 G) _).
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros D₁ D₂ D₃ FF₁ FF₂ FF₃ GG α β.
      use disp_nat_trans_eq ; intros x xx ; cbn.
      rewrite (disp_functor_transportf _ (pr1 GG)).
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ FF GG HH II α β.
      use disp_nat_trans_eq ; intros x xx ; cbn in *.
      etrans.
      {
        apply maponpaths.
        exact (disp_nat_trans_ax β (α x xx)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intros D₁ D₂ D₃ F G.
      use disp_nat_trans_eq ; intros x xx ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite (disp_functor_id (pr1 G)).
      cbn.
      apply transportf_set.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ D₅ FF GG HH II.
      use disp_nat_trans_eq ; intros ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite (disp_functor_id (pr1 II)).
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition opfib_slice_prebicat
    : prebicat.
  Proof.
    simple refine (_ ,, _).
    - exact opfib_slice_prebicat_data.
    - exact opfib_slice_prebicat_laws.
  Defined.

  Definition opfib_slice_bicat
    : bicat.
  Proof.
    simple refine (_ ,, _).
    - exact opfib_slice_prebicat.
    - intro ; intros.
      apply isaset_disp_nat_trans.
  Defined.

  Definition is_invertible_2cell_opfib_slice
             {D₁ D₂ : opfib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (α : G₁ ==> G₂)
             (Hα : (∏ (x : C)
                      (xx : pr1 D₁ x),
                    is_iso_disp (identity_iso x) (pr1 α x xx)))
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - exact (pointwise_inverse_disp_nat_trans α Hα).
    - apply pointwise_inverse_disp_nat_trans_over_id_left.
    - apply pointwise_inverse_disp_nat_trans_over_id_right.
  Defined.
End OpFibSlice.
