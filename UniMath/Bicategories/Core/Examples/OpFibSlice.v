(*********************************************************************************

 The opfibrational slice bicategory

 In this file, we define the opfibrational slice bicategory. More specifically,
 given a *univalent* category `C`, we define the opfibrational slice bicategory
 as follows:
 - Objects: (cloven) opfibrations over `C`
 - 1-cells: opcartesian functors making a triangle commute
 - 2-cells: natural transformations that satisfy some equality
 We also prove that this bicategory is univalent. For this, we need that the
 category `C` is univalent. In addition, we use the structure identity principle
 for displayed categories, which says that two displayed categories are equal if
 and only if we have an adjoint equivalence between them.

 Contents
 1. The opfibrational slice bicategory
 2. Invertible 2-cells in the opfibrational slice bicategory
 3. Local univalence of the opfibrational slice bicategory
 4. Adjoint equivalences in the opfibrational slice bicategory
 5. Global univalence of the opfibrational slice bicategory

 *********************************************************************************)
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
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Section OpFibSlice.
  Context (C : univalent_category).

  (**
   1. The opfibrational slice bicategory
   *)
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

  (**
   2. Invertible 2-cells in the opfibrational slice bicategory
   *)
  Definition is_invertible_2cell_opfib_slice
             {D₁ D₂ : opfib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (α : G₁ ==> G₂)
             (Hα : is_disp_nat_z_iso (nat_z_iso_id (functor_identity C)) α)
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - exact (pointwise_inverse_disp_nat_trans α Hα).
    - apply pointwise_inverse_disp_nat_trans_over_id_left.
    - apply pointwise_inverse_disp_nat_trans_over_id_right.
  Defined.

  Definition disp_nat_z_iso_to_inv2cell_opfib
             {D₁ D₂ : opfib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (τ : disp_nat_z_iso
                    (pr1 G₁) (pr1 G₂)
                    (nat_z_iso_id (functor_identity C)))
    : invertible_2cell G₁ G₂.
  Proof.
    use make_invertible_2cell.
    - exact (pr1 τ).
    - apply is_invertible_2cell_opfib_slice.
      exact (pr2 τ).
  Defined.

  Definition from_is_invertible_2cell_opfib_slice
             {D₁ D₂ : opfib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (α : G₁ ==> G₂)
             (Hα : is_invertible_2cell α)
    : is_disp_nat_z_iso (nat_z_iso_id (functor_identity C)) α.
  Proof.
    intros x xx.
    simple refine (_ ,, _ ,, _).
    - exact (pr1 (Hα^-1) x xx).
    - abstract
        (use transportb_transpose_right ;
         refine (_ @ maponpaths (λ z, pr1 z x xx) (vcomp_linv Hα)) ;
         cbn ;
         apply maponpaths_2 ;
         apply homset_property).
    - abstract
        (use transportb_transpose_right ;
         refine (_ @ maponpaths (λ z, pr1 z x xx) (vcomp_rinv Hα)) ;
         cbn ;
         apply maponpaths_2 ;
         apply homset_property).
  Defined.

  Definition inv2cell_to_disp_nat_z_iso_opfib
             {D₁ D₂ : opfib_slice_bicat}
             {G₁ G₂ : D₁ --> D₂}
             (τ : invertible_2cell G₁ G₂)
    : disp_nat_z_iso
        (pr1 G₁) (pr1 G₂)
        (nat_z_iso_id (functor_identity C))
    := pr1 τ ,, from_is_invertible_2cell_opfib_slice (pr1 τ) (pr2 τ).

  Definition invertible_2cell_opfib_slice_weq
             {D₁ D₂ : opfib_slice_bicat}
             (G₁ G₂ : D₁ --> D₂)
    : disp_nat_z_iso (pr1 G₁) (pr1 G₂) (nat_z_iso_id _)
      ≃
      invertible_2cell G₁ G₂.
  Proof.
    use weq_iso.
    - exact disp_nat_z_iso_to_inv2cell_opfib.
    - exact inv2cell_to_disp_nat_z_iso_opfib.
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_nat_z_iso | ] ;
         apply idpath).
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
  Defined.

  (**
   3. Local univalence of the opfibrational slice bicategory
   *)
  Proposition is_univalent_2_1_opfib_slice_bicat
    : is_univalent_2_1 opfib_slice_bicat.
  Proof.
    intros D₁ D₂ F G.
    use weqhomot.
    - refine (invertible_2cell_opfib_slice_weq F G
              ∘ disp_functor_eq_weq (pr1 F) (pr1 G) (pr1 D₂)
              ∘ path_sigma_hprop _ _ _ _)%weq.
      apply isaprop_is_opcartesian_disp_functor.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         use disp_nat_trans_eq ;
         intros x xx ; cbn ;
         apply idpath).
  Defined.

  (**
   4. Adjoint equivalences in the opfibrational slice bicategory
   *)
  Definition left_adjoint_equivalence_opfib_slice
             {D₁ D₂ : opfib_slice_bicat}
             (F : D₁ --> D₂)
             (HF : is_equiv_over_id (pr1 F))
    : left_adjoint_equivalence F.
  Proof.
    use equiv_to_adjequiv.
    simple refine (((_ ,, _) ,, (_ ,, _)) ,, _ ,, _).
    - exact HF.
    - exact (is_opcartesian_equiv_over_id (equiv_inv _ HF)).
    - exact (unit_over_id HF).
    - exact (counit_over_id HF).
    - use is_invertible_2cell_opfib_slice.
      intros x xx.
      exact (is_z_iso_unit_over_id HF x xx).
    - use is_invertible_2cell_opfib_slice.
      intros x xx.
      exact (is_z_iso_counit_over_id HF x xx).
  Defined.

  Definition adj_equiv_opfib_slice
             {D₁ D₂ : opfib_slice_bicat}
             (F : disp_functor (functor_identity C) (pr1 D₁) (pr1 D₂))
             (HF : is_equiv_over_id F)
    : adjoint_equivalence D₁ D₂.
  Proof.
    simple refine ((F ,, _) ,, _).
    - exact (is_opcartesian_equiv_over_id HF).
    - exact (left_adjoint_equivalence_opfib_slice (_ ,, _) HF).
  Defined.

  Proposition from_left_adjoint_equivalence_opfib_slice
              {D₁ D₂ : opfib_slice_bicat}
              (F : D₁ --> D₂)
              (HF : left_adjoint_equivalence F)
    : is_equiv_over_id (pr1 F).
  Proof.
    simple refine (((_ ,, (_ ,, _)) ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (pr1 (left_adjoint_right_adjoint HF)).
    - exact (left_adjoint_unit HF).
    - exact (left_adjoint_counit HF).
    - abstract
        (intros x xx ; cbn ;
         pose (p := maponpaths (λ z, pr1 z x xx) (internal_triangle1 HF)) ;
         cbn in p ;
         rewrite !mor_disp_transportf_postwhisker in p ;
         rewrite !transport_f_f in p ;
         rewrite id_right_disp in p ;
         unfold transportb in p ;
         rewrite transport_f_f in p ;
         rewrite id_right_disp in p ;
         unfold transportb in p ;
         rewrite mor_disp_transportf_postwhisker in p ;
         rewrite transport_f_f in p ;
         rewrite id_left_disp in p ;
         unfold transportb in p ;
         rewrite mor_disp_transportf_postwhisker in p ;
         rewrite transport_f_f in p ;
         refine (transportb_transpose_right p @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
    - abstract
        (intros x xx ; cbn ;
         pose (p := maponpaths (λ z, pr1 z x xx) (internal_triangle2 HF)) ;
         cbn in p ;
         rewrite !mor_disp_transportf_postwhisker in p ;
         rewrite !transport_f_f in p ;
         rewrite id_right_disp in p ;
         unfold transportb in p ;
         rewrite transport_f_f in p ;
         rewrite id_right_disp in p ;
         unfold transportb in p ;
         rewrite mor_disp_transportf_postwhisker in p ;
         rewrite transport_f_f in p ;
         rewrite id_left_disp in p ;
         unfold transportb in p ;
         rewrite mor_disp_transportf_postwhisker in p ;
         rewrite transport_f_f in p ;
         refine (transportb_transpose_right p @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
    - intros x xx.
      exact (from_is_invertible_2cell_opfib_slice _ (pr122 HF) x xx).
    - intros x xx.
      exact (from_is_invertible_2cell_opfib_slice _ (pr222 HF) x xx).
  Defined.

  Definition adj_equiv_opfib_slice_weq
             (D₁ D₂ : opfib_slice_bicat)
    : (∑ (F : disp_functor (functor_identity C) (pr1 D₁) (pr1 D₂)), is_equiv_over_id F)
      ≃
      adjoint_equivalence D₁ D₂.
  Proof.
    use weq_iso.
    - exact (λ F, adj_equiv_opfib_slice (pr1 F) (pr2 F)).
    - exact (λ F, pr11 F ,, from_left_adjoint_equivalence_opfib_slice _ (pr2 F)).
    - abstract
        (intros F ;
         use subtypePath ; [ intro ; apply (isaprop_is_equiv_over_id (pr1 D₁) (pr1 D₂)) | ] ;
         apply idpath).
    - abstract
        (intro F ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_left_adjoint_equivalence _ is_univalent_2_1_opfib_slice_bicat)
         | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_opcartesian_disp_functor | ] ;
         cbn ;
         apply idpath).
  Defined.

  (**
   5. Global univalence of the opfibrational slice bicategory
   *)
  Proposition is_univalent_2_0_opfib_slice_bicat
    : is_univalent_2_0 opfib_slice_bicat.
  Proof.
    intros D₁ D₂.
    use weqhomot.
    - refine (adj_equiv_opfib_slice_weq D₁ D₂
              ∘ univ_disp_cat_eq (pr1 D₁) (pr1 D₂) (pr1 D₁) (pr1 D₂)
              ∘ path_sigma_hprop _ _ _ _
              ∘ path_sigma_hprop _ _ _ _)%weq.
      + apply isaprop_opcleaving.
        apply (pr1 D₂).
      + apply isaprop_is_univalent_disp.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_left_adjoint_equivalence _ is_univalent_2_1_opfib_slice_bicat)
         | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_opcartesian_disp_functor | ] ;
         apply idpath).
  Defined.

  Proposition is_univalent_2_opfib_slice_bicat
    : is_univalent_2 opfib_slice_bicat.
  Proof.
    split.
    - exact is_univalent_2_0_opfib_slice_bicat.
    - exact is_univalent_2_1_opfib_slice_bicat.
  Defined.
End OpFibSlice.
