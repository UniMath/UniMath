(*******************************************************************
 Fibers of a display map bicategory

 In this file, we calculate the fibers of a display map bicategory

 1. To the fiber
 2. From the fiber
 3. The unit
 4. The counit
 5. The modifications
 6. The biequivalence

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.DisplayMapBicatCleaving.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Section FiberOfDisplayMap.
  Context {B : bicat}
          (D : arrow_subbicat B)
          (b : B).

  Let DD : disp_bicat B := disp_map_bicat_to_disp_bicat D.

  Let slice : bicat := disp_map_slice_bicat D b.

  Let fiber : bicat
    := strict_fiber_bicat DD (arrow_subbicat_local_iso_cleaving D) b.

  (**
   1. Calculation of operations in fiber
   *)
  Definition comp_disp_map_fiber
             {x y : fiber}
             {f g h : x --> y}
             (α : f ==> g)
             (β : g ==> h)
    : pr1 (α • β) = pr1 α • pr1 β.
  Proof.
    apply transportf_disp_map_bicat_cell.
  Qed.

  Definition lunitor_disp_map_fiber
             {x y : fiber}
             (f : x --> y)
    : pr1 (lunitor f) = lunitor (pr1 f).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    apply id2_left.
  Qed.

  Definition linvunitor_disp_map_fiber
             {x y : fiber}
             (f : x --> y)
    : pr1 (linvunitor f) = linvunitor (pr1 f).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    apply id2_right.
  Qed.

  Definition runitor_disp_map_fiber
             {x y : fiber}
             (f : x --> y)
    : pr1 (runitor f) = runitor (pr1 f).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    apply id2_left.
  Qed.

  Definition rinvunitor_disp_map_fiber
             {x y : fiber}
             (f : x --> y)
    : pr1 (rinvunitor f) = rinvunitor (pr1 f).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    apply id2_right.
  Qed.

  Definition lassociator_disp_map_fiber
             {w x y z : fiber}
             (f : w --> x)
             (g : x --> y)
             (h : y --> z)
    : pr1 (lassociator f g h) = lassociator (pr1 f) (pr1 g) (pr1 h).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    cbn.
    rewrite lwhisker_id2, id2_rwhisker, !id2_left, !id2_right.
    apply idpath.
  Qed.

  Definition rassociator_disp_map_fiber
             {w x y z : fiber}
             (f : w --> x)
             (g : x --> y)
             (h : y --> z)
    : pr1 (rassociator f g h) = rassociator (pr1 f) (pr1 g) (pr1 h).
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    cbn.
    rewrite lwhisker_id2, id2_rwhisker, !id2_left, !id2_right.
    apply idpath.
  Qed.

  Definition lwhisker_disp_map_fiber
             {x y z : fiber}
             (f : x --> y)
             {g h : y --> z}
             (α : g ==> h)
    : pr1 (f ◃ α) = _ ◃ pr1 α.
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    cbn.
    rewrite id2_left, id2_right.
    apply idpath.
  Qed.

  Definition rwhisker_disp_map_fiber
             {x y z : fiber}
             {f g : x --> y}
             (α : f ==> g)
             (h : y --> z)
    : pr1 (α ▹ h) = pr1 α ▹ _.
  Proof.
    etrans.
    {
      apply transportf_disp_map_bicat_cell.
    }
    cbn.
    rewrite id2_left, id2_right.
    apply idpath.
  Qed.

  Definition path_2cell_disp_map_fiber
             {x y : fiber}
             {f g : x --> y}
             (α β : f ==> g)
             (p : pr1 α = pr1 β)
    : α = β.
  Proof.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    exact p.
  Qed.

  (**
   2. To the fiber
   *)
  Definition to_fiber_disp_map_data
    : psfunctor_data slice fiber.
  Proof.
    use make_psfunctor_data.
    - exact (λ f, f).
    - exact (λ a₁ a₂ g,
             pr1 g
             ,,
             pr12 g
             ,,
             comp_of_invertible_2cell
               (runitor_invertible_2cell _)
               (pr22 g)).
    - refine (λ a₁ a₂ g₁ g₂ β, pr1 β ,, _).
      abstract
        (cbn ;
         rewrite lwhisker_id2, id2_left ;
         rewrite !vassocl ;
         apply maponpaths ;
         exact (pr2 β)).
    - refine (λ a, id2 _ ,, _).
      abstract
        (cbn ;
         rewrite id2_rwhisker, id2_right ;
         rewrite lwhisker_id2, id2_left ;
         apply idpath).
    - refine (λ a₁ a₂ a₃ g₁ g₂, id2 _ ,, _).
      abstract
        (cbn ;
         rewrite lwhisker_id2, id2_left ;
         rewrite id2_rwhisker, id2_right ;
         rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp ;
         rewrite !vassocr ;
         do 2 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite <- lunitor_lwhisker ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite lassociator_rassociator ;
         rewrite id2_left ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite linvunitor_lunitor ;
         rewrite lwhisker_id2 ;
         rewrite id2_left ;
         rewrite !vassocl ;
         rewrite runitor_triangle ;
         rewrite vcomp_runitor ;
         apply idpath).
  Defined.

  Definition to_fiber_disp_map_laws
    : psfunctor_laws to_fiber_disp_map_data.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _) ;
    intro ; intros ;
    use path_2cell_disp_map_fiber.
    - apply idpath.
    - rewrite comp_disp_map_fiber.
      apply idpath.
    - rewrite !comp_disp_map_fiber.
      rewrite lunitor_disp_map_fiber.
      rewrite rwhisker_disp_map_fiber.
      cbn.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - rewrite !comp_disp_map_fiber.
      rewrite runitor_disp_map_fiber.
      rewrite lwhisker_disp_map_fiber.
      cbn.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite !comp_disp_map_fiber.
      rewrite lwhisker_disp_map_fiber, rwhisker_disp_map_fiber.
      rewrite lassociator_disp_map_fiber.
      cbn.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      apply idpath.
    - rewrite !comp_disp_map_fiber.
      rewrite lwhisker_disp_map_fiber.
      cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    - rewrite !comp_disp_map_fiber.
      rewrite rwhisker_disp_map_fiber.
      cbn.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition to_fiber_disp_map
    : psfunctor slice fiber.
  Proof.
    use make_psfunctor.
    - exact to_fiber_disp_map_data.
    - exact to_fiber_disp_map_laws.
    - split.
      + intros.
        use strict_fiber_bicat_invertible_2cell.
        use is_invertible_to_is_disp_invertible ; cbn.
        is_iso.
      + intros.
        use strict_fiber_bicat_invertible_2cell.
        use is_invertible_to_is_disp_invertible ; cbn.
        is_iso.
  Defined.

  (**
   3. From the fiber
   *)
  Definition from_fiber_disp_map_data
    : psfunctor_data fiber slice.
  Proof.
    use make_psfunctor_data.
    - exact (λ f, f).
    - exact (λ a₁ a₂ g,
             pr1 g
             ,,
             pr12 g
             ,,
             comp_of_invertible_2cell
               (rinvunitor_invertible_2cell _)
               (pr22 g)).
    - refine (λ a₁ a₂ g₁ g₂ β, pr1 β ,, _).
      abstract
        (cbn ;
         rewrite !vassocl ;
         refine (maponpaths (λ z, _ • z) (pr2 β) @ _) ;
         rewrite lwhisker_id2 ;
         rewrite id2_left ;
         apply idpath).
    - refine (λ a, id2 _ ,, _).
      abstract
        (cbn ;
         rewrite id2_rwhisker ;
         rewrite id2_right ;
         rewrite !vassocr ;
         rewrite rinvunitor_runitor ;
         rewrite id2_left ;
         apply idpath).
    - refine (λ a₁ a₂ a₃ g₁ g₂, id2 _ ,, _).
      abstract
        (cbn ;
         rewrite id2_rwhisker ;
         rewrite id2_right ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <- lwhisker_vcomp ;
         rewrite !vassocr ;
         do 2 apply maponpaths_2 ;
         rewrite !lwhisker_hcomp ;
         rewrite triangle_r_inv ;
         rewrite <- rwhisker_hcomp, <- lwhisker_hcomp ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite rassociator_lassociator ;
         rewrite id2_left ;
         rewrite left_unit_inv_assoc ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite rinvunitor_natural ;
         rewrite <- rwhisker_hcomp ;
         apply maponpaths_2 ;
         refine (_ @ id2_right _) ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         cbn ;
         use vcomp_move_R_Mp ; [ is_iso | ] ;
         cbn ;
         rewrite id2_left ;
         rewrite <- runitor_triangle ;
         rewrite runitor_lunitor_identity ;
         rewrite lunitor_lwhisker ;
         apply idpath).
  Defined.

  Definition from_fiber_disp_map_laws
    : psfunctor_laws from_fiber_disp_map_data.
  Proof.
    repeat split ;
    intro ; intros ;
    use eq_2cell_disp_map_slice.
    - apply idpath.
    - cbn -[vcomp2].
      rewrite comp_disp_map_fiber.
      cbn.
      apply idpath.
    - cbn -[lunitor].
      rewrite lunitor_disp_map_fiber.
      cbn.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - cbn -[runitor].
      rewrite runitor_disp_map_fiber.
      cbn.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - cbn -[lassociator].
      rewrite lassociator_disp_map_fiber.
      cbn.
      rewrite id2_rwhisker, lwhisker_id2, !id2_left, !id2_right.
      apply idpath.
    - cbn -[lwhisker].
      rewrite lwhisker_disp_map_fiber.
      cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    - cbn -[rwhisker].
      rewrite rwhisker_disp_map_fiber.
      cbn.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition from_fiber_disp_map
    : psfunctor fiber slice.
  Proof.
    use make_psfunctor.
    - exact from_fiber_disp_map_data.
    - exact from_fiber_disp_map_laws.
    - split ; intros.
      + use invertible_2cell_in_disp_map_slice_bicat ; cbn.
        is_iso.
      + use invertible_2cell_in_disp_map_slice_bicat ; cbn.
        is_iso.
  Defined.

  (**
   4. The unit
   *)
  Definition to_fiber_disp_map_unit_data
    : pstrans_data
        (id_psfunctor _)
        (comp_psfunctor from_fiber_disp_map to_fiber_disp_map).
  Proof.
    use make_pstrans_data.
    - exact (λ f, id₁ _ ,, id_pred_mor D _ ,, linvunitor_invertible_2cell _).
    - cbn.
      refine (λ f₁ f₂ g, _).
      use make_invertible_2cell.
      + cbn.
        simple refine (_ ,, _).
        * cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract
            (cbn ;
             rewrite !vassocr ;
             rewrite rinvunitor_runitor ;
             rewrite id2_left ;
             rewrite lwhisker_hcomp ;
             rewrite <- linvunitor_natural ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite linvunitor_assoc ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite <- rwhisker_vcomp ;
             rewrite !vassocr ;
             use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
             rewrite rwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite id2_rwhisker ;
             rewrite !vassocl ;
             rewrite runitor_rwhisker ;
             rewrite lwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite lwhisker_id2 ;
             apply idpath).
      + apply invertible_2cell_in_disp_map_slice_bicat ; cbn.
        is_iso.
  Defined.

  Definition to_fiber_disp_map_unit_is_pstrans
    : is_pstrans to_fiber_disp_map_unit_data.
  Proof.
    repeat split.
    - intros x y f g α.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - intros x.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite id2_left.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite lunitor_runitor_identity, runitor_rinvunitor.
      rewrite runitor_lunitor_identity, lunitor_linvunitor.
      apply idpath.
    - intros x y z f g.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite id2_left.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite !vassocl.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      rewrite (maponpaths (λ z, _ • (_ • (_ • (_ • z)))) (vassocr _ _ _)).
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      rewrite lunitor_triangle.
      apply idpath.
  Qed.

  Definition to_fiber_disp_map_unit
    : pstrans
        (id_psfunctor _)
        (comp_psfunctor from_fiber_disp_map to_fiber_disp_map).
  Proof.
    use make_pstrans.
    - exact to_fiber_disp_map_unit_data.
    - exact to_fiber_disp_map_unit_is_pstrans.
  Defined.

  Definition to_fiber_disp_map_unit_inv_data
    : pstrans_data
        (comp_psfunctor from_fiber_disp_map to_fiber_disp_map)
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - exact (λ x, id₁ _ ,, id_pred_mor D _ ,, linvunitor_invertible_2cell _).
    - cbn.
      refine (λ x y f, _).
      use make_invertible_2cell.
      + cbn.
        simple refine (_ ,, _).
        * cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract
            (cbn ;
             rewrite !vassocr ;
             rewrite rinvunitor_runitor ;
             rewrite id2_left ;
             rewrite lwhisker_hcomp ;
             rewrite <- linvunitor_natural ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite linvunitor_assoc ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite <- rwhisker_vcomp ;
             rewrite !vassocr ;
             use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
             rewrite rwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite id2_rwhisker ;
             rewrite !vassocl ;
             rewrite runitor_rwhisker ;
             rewrite lwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite lwhisker_id2 ;
             apply idpath).
      + apply invertible_2cell_in_disp_map_slice_bicat ; cbn.
        is_iso.
  Defined.

  Definition to_fiber_disp_map_unit_inv_is_pstrans
    : is_pstrans to_fiber_disp_map_unit_inv_data.
  Proof.
    repeat split.
    - intros x y f g α.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - intros x.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite lwhisker_id2, !id2_left.
      rewrite id2_rwhisker, id2_right.
      rewrite runitor_lunitor_identity, lunitor_linvunitor.
      rewrite lunitor_runitor_identity, runitor_rinvunitor.
      apply idpath.
    - intros x y z f g.
      use eq_2cell_disp_map_slice.
      cbn.
      rewrite lwhisker_id2, !id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_Mp ; [ is_iso | ].
      cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      refine (!(id2_right _) @ _).
      apply maponpaths.
      rewrite <- runitor_triangle.
      rewrite (maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      apply idpath.
  Qed.

  Definition to_fiber_disp_map_unit_inv
    : pstrans
        (comp_psfunctor from_fiber_disp_map to_fiber_disp_map)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact to_fiber_disp_map_unit_inv_data.
    - exact to_fiber_disp_map_unit_inv_is_pstrans.
  Defined.

  (**
   5. The counit
   *)
  Definition to_fiber_disp_map_counit_data
    : pstrans_data
        (comp_psfunctor to_fiber_disp_map from_fiber_disp_map)
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - cbn.
      refine (λ f, id₁ _ ,, id_pred_mor D _ ,, _).
      exact (comp_of_invertible_2cell
               (runitor_invertible_2cell _)
               (linvunitor_invertible_2cell _)).
    - refine (λ x y f, _).
      use make_invertible_2cell.
      + simple refine (_ ,, _).
        * cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract
            (cbn ;
             rewrite lwhisker_id2, id2_left ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 3 apply maponpaths ;
             rewrite <- !lwhisker_vcomp ;
             rewrite !vassocl ;
             refine (!_) ;
             etrans ;
             [ do 4 apply maponpaths ;
               rewrite lwhisker_hcomp ;
               apply triangle_l_inv
             | ] ;
             rewrite <- rwhisker_hcomp ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             rewrite lunitor_triangle ;
             rewrite runitor_triangle ;
             rewrite vcomp_lunitor ;
             rewrite vcomp_runitor ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             rewrite <- lunitor_triangle ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite rwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite id2_rwhisker ;
             use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
             rewrite id2_right ;
             rewrite <- runitor_triangle ;
             rewrite runitor_lunitor_identity ;
             apply lunitor_lwhisker).
      + apply strict_fiber_bicat_invertible_2cell.
        use is_invertible_to_is_disp_invertible.
        cbn.
        is_iso.
  Defined.

  Opaque comp_psfunctor.

  Definition to_fiber_disp_map_counit_is_pstrans
    : is_pstrans to_fiber_disp_map_counit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros x y f g α.
      use path_2cell_disp_map_fiber.
      rewrite !comp_disp_map_fiber.
      rewrite lwhisker_disp_map_fiber.
      rewrite rwhisker_disp_map_fiber.
      cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - intros x.
      use path_2cell_disp_map_fiber.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_disp_map_fiber.
      }
      refine (!_).
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (comp_disp_map_fiber _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply runitor_disp_map_fiber.
        }
        apply maponpaths.
        apply linvunitor_disp_map_fiber.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply rwhisker_disp_map_fiber.
        }
        apply maponpaths.
        apply comp_disp_map_fiber.
      }
      cbn.
      rewrite lwhisker_id2, !id2_left.
      rewrite id2_rwhisker, id2_right.
      rewrite lunitor_runitor_identity, runitor_rinvunitor.
      rewrite runitor_lunitor_identity, lunitor_linvunitor.
      apply idpath.
    - intros x y z f g.
      use path_2cell_disp_map_fiber.
      refine (comp_disp_map_fiber _ _ @ _).
      refine (maponpaths (λ z, z • _) (lwhisker_disp_map_fiber _ _) @ _).
      refine (!_).
      refine (comp_disp_map_fiber _ _ @ _).
      refine (maponpaths
                (λ z, z • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, (z • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((z • _) • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, (((z • _) • _) • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((z • _) • _) • _) • _) • _)
                (lassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • z) • _) • _) • _) • _)
                (rwhisker_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • z) • _) • _) • _)
                (rassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • z) • _) • _)
                (lwhisker_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • _) • z) • _)
                (lassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • _) • _) • z)
                (rwhisker_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • _) • _) • (z ▹ _))
                (comp_disp_map_fiber _ _) @ _).
      cbn.
      rewrite lwhisker_id2, !id2_left.
      rewrite id2_rwhisker, id2_right.
      rewrite <- rwhisker_vcomp.
      rewrite <- lunitor_triangle.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite left_unit_inv_assoc₂.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
  Qed.

  Transparent comp_psfunctor.

  Definition to_fiber_disp_map_counit
    : pstrans
        (comp_psfunctor to_fiber_disp_map from_fiber_disp_map)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact to_fiber_disp_map_counit_data.
    - exact to_fiber_disp_map_counit_is_pstrans.
  Defined.

  Definition to_fiber_disp_map_counit_inv_data
    : pstrans_data
        (id_psfunctor _)
        (comp_psfunctor to_fiber_disp_map from_fiber_disp_map).
  Proof.
    use make_pstrans_data.
    - refine (λ x, id₁ _ ,, id_pred_mor D _ ,, _).
      exact (comp_of_invertible_2cell
               (runitor_invertible_2cell _)
               (linvunitor_invertible_2cell _)).
    - intros x y f.
      use make_invertible_2cell.
      + simple refine (_ ,, _).
        * cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract
            (cbn ;
             rewrite lwhisker_id2, id2_left ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite runitor_rinvunitor ;
             rewrite id2_left ;
             use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
             rewrite !vassocl ;
             rewrite runitor_rwhisker ;
             rewrite lwhisker_vcomp ;
             rewrite !vassocl ;
             rewrite linvunitor_lunitor ;
             rewrite id2_right ;
             rewrite runitor_triangle ;
             rewrite lunitor_triangle ;
             rewrite vcomp_lunitor ;
             rewrite vcomp_runitor ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             rewrite <- lunitor_triangle ;
             rewrite (maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite rwhisker_vcomp ;
             rewrite linvunitor_lunitor ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite <- runitor_triangle ;
             rewrite runitor_lunitor_identity ;
             rewrite lunitor_lwhisker ;
             apply idpath).
      + apply strict_fiber_bicat_invertible_2cell.
        use is_invertible_to_is_disp_invertible.
        cbn.
        is_iso.
  Defined.

  Opaque strict_fiber_bicat comp_psfunctor.

  Definition to_fiber_disp_map_counit_inv_is_pstrans
    : is_pstrans to_fiber_disp_map_counit_inv_data.
  Proof.
    repeat split.
    - intros x y f g  α.
      use path_2cell_disp_map_fiber.
      refine (comp_disp_map_fiber _ _ @ _ @ !(comp_disp_map_fiber _ _)).
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_disp_map_fiber.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply rwhisker_disp_map_fiber.
      }
      cbn.
      refine (!_).
      refine (vassocr _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply vcomp_lunitor.
      }
      refine (vassocl _ _ _ @ _ @ vassocr _ _ _).
      apply maponpaths.
      etrans.
      {
        apply rinvunitor_natural.
      }
      apply maponpaths.
      refine (!_).
      apply rwhisker_hcomp.
    - intros x.
      use path_2cell_disp_map_fiber.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply lwhisker_disp_map_fiber.
        }
        apply maponpaths.
        exact (comp_disp_map_fiber
                 (psfunctor_id to_fiber_disp_map x)
                 (##to_fiber_disp_map (psfunctor_id from_fiber_disp_map x))).
      }
      refine (!_).
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (comp_disp_map_fiber _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply runitor_disp_map_fiber.
        }
        apply maponpaths.
        apply linvunitor_disp_map_fiber.
      }
      etrans.
      {
        apply maponpaths.
        apply rwhisker_disp_map_fiber.
      }
      cbn.
      etrans.
      {
        apply maponpaths.
        apply id2_rwhisker.
      }
      refine (id2_right _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply id2_left.
        }
        apply lwhisker_id2.
      }
      refine (id2_left _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply lunitor_runitor_identity.
      }
      refine (runitor_rinvunitor _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply runitor_lunitor_identity.
      }
      apply lunitor_linvunitor.
    - intros x y z f g.
      use path_2cell_disp_map_fiber.
      refine (comp_disp_map_fiber _ _ @ _).
      refine (maponpaths (λ z, z • _) (lwhisker_disp_map_fiber _ _) @ _).
      refine (!_).
      refine (comp_disp_map_fiber _ _ @ _).
      refine (maponpaths
                (λ z, z • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, (z • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((z • _) • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, (((z • _) • _) • _) • _)
                (comp_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((z • _) • _) • _) • _) • _)
                (lassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • z) • _) • _) • _) • _)
                (rwhisker_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • z) • _) • _) • _)
                (rassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • z) • _) • _)
                (lwhisker_disp_map_fiber _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • _) • z) • _)
                (lassociator_disp_map_fiber _ _ _) @ _).
      refine (maponpaths
                (λ z, ((((_ • _) • _) • _) • _) • z)
                (rwhisker_disp_map_fiber _ _) @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (comp_disp_map_fiber
                 (psfunctor_comp
                    to_fiber_disp_map
                    (# from_fiber_disp_map f)
                    (# from_fiber_disp_map g))
                 (## to_fiber_disp_map (psfunctor_comp from_fiber_disp_map f g))).
      }
      cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply id2_left.
        }
        apply lwhisker_id2.
      }
      refine (id2_left _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply id2_rwhisker.
      }
      refine (id2_right _ @ _).
      etrans.
      {
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply rwhisker_vcomp.
        }
        refine (vassocr  _ _ _ @ _).
        apply maponpaths_2.
        apply lunitor_triangle.
      }
      do 3 refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply lwhisker_vcomp.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply left_unit_inv_assoc.
        }
        refine (vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply rassociator_lassociator.
        }
        apply id2_right.
      }
      etrans.
      {
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply lunitor_lwhisker.
      }
      refine (vassocr _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (rwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply rinvunitor_runitor.
        }
        apply id2_rwhisker.
      }
      apply id2_left.
  Qed.

  Transparent strict_fiber_bicat comp_psfunctor.

  Definition to_fiber_disp_map_counit_inv
    : pstrans
        (id_psfunctor _)
        (comp_psfunctor to_fiber_disp_map from_fiber_disp_map).
  Proof.
    use make_pstrans.
    - exact to_fiber_disp_map_counit_inv_data.
    - exact to_fiber_disp_map_counit_inv_is_pstrans.
  Defined.

  (**
   6. The modifications
   *)
  Definition disp_map_unit_inv_left_data
    : invertible_modification_data
        (id_pstrans _)
        (comp_pstrans to_fiber_disp_map_unit_inv to_fiber_disp_map_unit).
  Proof.
    intros x.
    use make_invertible_2cell.
    - simple refine (_ ,, _).
      + exact (linvunitor _).
      + abstract
          (cbn ;
           apply maponpaths ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite lunitor_runitor_identity ;
           rewrite lwhisker_hcomp, rwhisker_hcomp ;
           apply triangle_r).
    - apply invertible_2cell_in_disp_map_slice_bicat.
      cbn.
      is_iso.
  Defined.

  Definition disp_map_unit_inv_left_is_modification
    : is_modification disp_map_unit_inv_left_data.
  Proof.
    intros x y f.
    use eq_2cell_disp_map_slice.
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite <- lwhisker_vcomp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      apply idpath.
    }
    rewrite runitor_lunitor_identity.
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition disp_map_unit_inv_left
    : invertible_modification
        (id_pstrans _)
        (comp_pstrans to_fiber_disp_map_unit_inv to_fiber_disp_map_unit).
  Proof.
    use make_invertible_modification.
    - exact disp_map_unit_inv_left_data.
    - exact disp_map_unit_inv_left_is_modification.
  Defined.

  Definition disp_map_unit_inv_right_data
    : invertible_modification_data
        (comp_pstrans to_fiber_disp_map_unit to_fiber_disp_map_unit_inv)
        (id_pstrans _).
  Proof.
    intros x.
    use make_invertible_2cell.
    - simple refine (_ ,, _).
      + exact (lunitor _).
      + abstract
          (cbn ;
           refine (_ @ id2_right _) ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           rewrite lunitor_runitor_identity ;
           rewrite lwhisker_hcomp, rwhisker_hcomp ;
           refine (!_) ;
           apply triangle_r).
    - apply invertible_2cell_in_disp_map_slice_bicat.
      cbn.
      is_iso.
  Defined.

  Definition disp_map_unit_inv_right_is_modification
    : is_modification disp_map_unit_inv_right_data.
  Proof.
    intros x y f.
    use eq_2cell_disp_map_slice.
    cbn.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite <- lwhisker_vcomp.
    rewrite lunitor_triangle.
    use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite lwhisker_vcomp.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    apply idpath.
  Qed.

  Definition disp_map_unit_inv_right
    : invertible_modification
        (comp_pstrans to_fiber_disp_map_unit to_fiber_disp_map_unit_inv)
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact disp_map_unit_inv_right_data.
    - exact disp_map_unit_inv_right_is_modification.
  Defined.

  Definition disp_map_counit_inv_right_data
    : invertible_modification_data
        (id_pstrans _)
        (comp_pstrans to_fiber_disp_map_counit to_fiber_disp_map_counit_inv).
  Proof.
    intros x.
    use make_invertible_2cell.
    - simple refine (_ ,, _).
      + exact (linvunitor _).
      + abstract
          (cbn ;
           rewrite lwhisker_id2, id2_left ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite !vassocl ;
           rewrite lunitor_runitor_identity ;
           rewrite runitor_rwhisker ;
           rewrite lwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite linvunitor_lunitor ;
           rewrite id2_right ;
           rewrite <- rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite <- lunitor_lwhisker ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite linvunitor_lunitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite runitor_triangle ;
           rewrite vcomp_runitor ;
           apply idpath).
    - use strict_fiber_bicat_invertible_2cell.
      use is_invertible_to_is_disp_invertible.
      cbn.
      is_iso.
  Defined.

  Opaque comp_psfunctor strict_fiber_bicat.

  Definition disp_map_counit_inv_right_is_modification
    : is_modification disp_map_counit_inv_right_data.
  Proof.
    intros x y f.
    use path_2cell_disp_map_fiber.
    refine (comp_disp_map_fiber _ _ @ _ @ !(comp_disp_map_fiber _ _)).
    etrans.
    {
      apply maponpaths.
      apply lwhisker_disp_map_fiber.
    }
    etrans.
    {
      apply maponpaths_2.
      cbn.
      apply comp_disp_map_fiber.
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply lunitor_disp_map_fiber.
      }
      apply maponpaths.
      apply rinvunitor_disp_map_fiber.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply rwhisker_disp_map_fiber.
    }
    etrans.
    {
      apply maponpaths.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply rassociator_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply rwhisker_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply lassociator_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply lwhisker_disp_map_fiber.
      }
      apply maponpaths_2.
      apply rassociator_disp_map_fiber.
    }
    cbn.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      apply lunitor_lwhisker.
    }
    etrans.
    {
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply rwhisker_vcomp.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply runitor_lunitor_identity.
        }
        apply linvunitor_lunitor.
      }
      etrans.
      {
        apply maponpaths_2.
        apply id2_rwhisker.
      }
      apply id2_left.
    }
    refine (!_).
    etrans.
    {
      refine (vassocr _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply vcomp_lunitor.
      }
      apply vassocl.
    }
    do 2 refine (_ @ vassocr _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply rwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      apply lunitor_triangle.
    }
    refine (vassocl _ _ _ @ _).
    apply maponpaths.
    use vcomp_move_R_pM ; [ is_iso | ].
    use vcomp_move_L_Mp ; [ is_iso | ].
    apply lunitor_lwhisker.
  Qed.

  Transparent comp_psfunctor strict_fiber_bicat.

  Definition disp_map_counit_inv_right
    : invertible_modification
        (id_pstrans _)
        (comp_pstrans to_fiber_disp_map_counit to_fiber_disp_map_counit_inv).
  Proof.
    use make_invertible_modification.
    - exact disp_map_counit_inv_right_data.
    - exact disp_map_counit_inv_right_is_modification.
  Defined.

  Definition disp_map_counit_inv_left_data
    : invertible_modification_data
        (comp_pstrans to_fiber_disp_map_counit_inv to_fiber_disp_map_counit)
        (id_pstrans _).
  Proof.
    intros x.
    use make_invertible_2cell.
    - simple refine (_ ,, _).
      + exact (lunitor _).
      + abstract
          (cbn ;
           rewrite lwhisker_id2, id2_left ;
           rewrite !vassocl ;
           rewrite lunitor_runitor_identity ;
           rewrite runitor_rwhisker ;
           rewrite lwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite linvunitor_lunitor ;
           rewrite id2_right ;
           rewrite <- rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite <- lunitor_lwhisker ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite linvunitor_lunitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite runitor_triangle ;
           rewrite vcomp_runitor ;
           apply idpath).
    - use strict_fiber_bicat_invertible_2cell.
      use is_invertible_to_is_disp_invertible.
      cbn.
      is_iso.
  Defined.

  Opaque comp_psfunctor strict_fiber_bicat.

  Definition disp_map_counit_inv_left_is_modification
    : is_modification disp_map_counit_inv_left_data.
  Proof.
    intros x y f.
    use path_2cell_disp_map_fiber.
    refine (comp_disp_map_fiber _ _ @ _ @ !(comp_disp_map_fiber _ _)).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply rwhisker_disp_map_fiber.
    }
    etrans.
    {
      apply maponpaths.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply lunitor_disp_map_fiber.
      }
      apply maponpaths.
      apply rinvunitor_disp_map_fiber.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply lwhisker_disp_map_fiber.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply rassociator_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply rwhisker_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply lassociator_disp_map_fiber.
      }
      apply maponpaths_2.
      refine (comp_disp_map_fiber _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply lwhisker_disp_map_fiber.
      }
      apply maponpaths_2.
      apply rassociator_disp_map_fiber.
    }
    cbn.
    etrans.
    {
      do 4 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply lwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply lunitor_lwhisker.
      }
      apply maponpaths.
      apply runitor_lunitor_identity.
    }
    do 4 refine (vassocl _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply lunitor_lwhisker.
      }
      refine (rwhisker_vcomp _ _ _ @ _).
      cbn.
      apply maponpaths.
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply rinvunitor_runitor.
      }
      apply id2_right.
    }
    etrans.
    {
      apply maponpaths.
      apply lunitor_triangle.
    }
    apply vcomp_lunitor.
  Qed.

  Transparent comp_psfunctor strict_fiber_bicat.

  Definition disp_map_counit_inv_left
    : invertible_modification
        (comp_pstrans to_fiber_disp_map_counit_inv to_fiber_disp_map_counit)
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact disp_map_counit_inv_left_data.
    - exact disp_map_counit_inv_left_is_modification.
  Defined.

  (**
   7. The biequivalence
   *)
    Definition to_fiber_disp_map_is_biequivalence
    : is_biequivalence to_fiber_disp_map.
  Proof.
    use make_is_biequivalence.
    - exact from_fiber_disp_map.
    - exact to_fiber_disp_map_unit.
    - exact to_fiber_disp_map_unit_inv.
    - exact to_fiber_disp_map_counit.
    - exact to_fiber_disp_map_counit_inv.
    - exact disp_map_unit_inv_left.
    - exact disp_map_unit_inv_right.
    - exact disp_map_counit_inv_right.
    - exact disp_map_counit_inv_left.
  Defined.
End FiberOfDisplayMap.
