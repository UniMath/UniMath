(************************************************************************************

 Fibers of slice bicategories

 Each of the variations of slice bicategories has a local isocleaving, and thus we
 can talk about fiber categories. The slice of each of them is some variation of
 the hom-category:
 - for the lax slice, it is the hom-category
 - for the oplax slice, it is the opposite of the hom-category
 - for the slice, it is the core of the hom-category
 In addition, we determine the functor arising from a morphism in the base and the
 global cleaving. In all of the different variations of the slice bicategory, this
 functor is equivalent to precomposition.

 Contents
 1. Fiber of lax slice
 2. Fiber functor of lax slice
 3. Fiber of oplax slice
 4. Fiber functor of oplax slice
 5. Fiber of slice
 6. Fiber functor of oplax slice

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LaxSlice.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.
Require Import UniMath.Bicategories.DisplayedBicats.FiberCategory.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.SliceCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.FunctorFromCleaving.

Local Open Scope cat.

(**
 1. Fiber of lax slice
 *)
Section LaxSliceFiber.
  Context {B : bicat}
          (c a : B).

  Let fib : category
    := discrete_fiber_category
         (lax_slice_disp_bicat B a)
         (lax_slice_disp_2cells_isaprop B a)
         (lax_slice_disp_univalent_2_1 B a)
         (lax_slice_local_iso_cleaving a)
         c.

  Let homc : category
    := hom c a.

  Definition hom_to_lax_slice_fib_data
    : functor_data homc fib.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, α • linvunitor _).
  Defined.

  Definition hom_to_lax_slice_fib_is_functor
    : is_functor hom_to_lax_slice_fib_data.
  Proof.
    split.
    - intro f ; cbn.
      apply id2_left.
    - intros f g h α β ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply linvunitor_natural.
      }
      rewrite <- lwhisker_hcomp.
      apply maponpaths.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      refine (!(id2_right _) @ _).
      apply maponpaths.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
  Qed.

  Definition hom_to_lax_slice_fib
    : homc ⟶ fib.
  Proof.
    use make_functor.
    - exact hom_to_lax_slice_fib_data.
    - exact hom_to_lax_slice_fib_is_functor.
  Defined.

  Definition lax_slice_fib_to_hom_data
    : functor_data fib homc.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, α • lunitor _).
  Defined.

  Definition lax_slice_fib_to_hom_is_functor
    : is_functor lax_slice_fib_to_hom_data.
  Proof.
    split.
    - intros f ; cbn.
      apply linvunitor_lunitor.
    - intros f g h α β ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      apply lunitor_triangle.
  Qed.

  Definition lax_slice_fib_to_hom
    : fib ⟶ homc.
  Proof.
    use make_functor.
    - exact lax_slice_fib_to_hom_data.
    - exact lax_slice_fib_to_hom_is_functor.
  Defined.

  Definition equiv_lax_slice_fib_hom_unit
    : functor_identity fib
      ⟹
      lax_slice_fib_to_hom ∙ hom_to_lax_slice_fib.
  Proof.
    use make_nat_trans.
    - exact (λ f, linvunitor f).
    - abstract
        (intros f g α ; cbn ;
         do 2 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite lunitor_linvunitor ;
         rewrite id2_right ;
         rewrite !lwhisker_hcomp ;
         rewrite <- linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         apply maponpaths ;
         rewrite linvunitor_assoc ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite lwhisker_hcomp, rwhisker_hcomp ;
         apply triangle_r_inv).
  Defined.

  Definition equiv_lax_slice_fib_hom_counit
    : hom_to_lax_slice_fib ∙ lax_slice_fib_to_hom
      ⟹
      functor_identity homc.
  Proof.
    use make_nat_trans.
    - exact (λ f, id₂ f).
    - abstract
        (intros f g α ; cbn ;
         rewrite id2_left, id2_right ;
         rewrite !vassocl ;
         rewrite linvunitor_lunitor ;
         apply id2_right).
  Defined.

  Definition equiv_lax_slice_fib_hom
    : equivalence_of_cats fib homc.
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact lax_slice_fib_to_hom.
      + exact hom_to_lax_slice_fib.
      + exact equiv_lax_slice_fib_hom_unit.
      + exact equiv_lax_slice_fib_hom_counit.
    - split.
      + intro f.
        apply is_z_iso_discrete_fiber.
        apply lax_slice_invertible_2cell_is_left_disp_adj_equiv.
        cbn.
        is_iso.
      + intro f ; cbn.
        apply is_inv2cell_to_is_z_iso.
        is_iso.
  Defined.

  Definition adj_equivalence_lax_slice_fib_to_hom
    : adj_equivalence_of_cats lax_slice_fib_to_hom
    := adjointificiation equiv_lax_slice_fib_hom.

  Definition adj_equiv_lax_slice_fib_hom
    : adj_equiv fib homc
    := _ ,, adj_equivalence_lax_slice_fib_to_hom.
End LaxSliceFiber.

(**
 2. Fiber functor of lax slice
 *)
Section LaxSliceSubFiber.
  Context {B : bicat}
          (a : B)
          {c₁ c₂ : B}
          (f : c₁ --> c₂).

  Let fib₁ : category
    := discrete_fiber_category
         (lax_slice_disp_bicat B a)
         (lax_slice_disp_2cells_isaprop B a)
         (lax_slice_disp_univalent_2_1 B a)
         (lax_slice_local_iso_cleaving a)
         c₁.

  Let fib₂ : category
    := discrete_fiber_category
         (lax_slice_disp_bicat B a)
         (lax_slice_disp_2cells_isaprop B a)
         (lax_slice_disp_univalent_2_1 B a)
         (lax_slice_local_iso_cleaving a)
         c₂.

  Definition functor_from_lax_slice_cleaving_nat_trans
    : functor_from_cleaving
        (lax_slice_disp_bicat B a)
        (lax_slice_disp_2cells_isaprop B a)
        (lax_slice_disp_univalent_2_1 B a)
        (lax_slice_global_cleaving a)
        (lax_slice_local_iso_cleaving a)
        f
      ⟹
      lax_slice_fib_to_hom _ _
      ∙ pre_comp a f
      ∙ hom_to_lax_slice_fib _ _.
  Proof.
    use make_nat_trans.
    - exact (λ g, linvunitor _).
    - abstract
        (intros g₁ g₂ α ; cbn in * ;
         rewrite lwhisker_id2 ;
         rewrite id2_left, id2_right ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocr ;
         do 3 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite runitor_rwhisker ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite <- vcomp_whisker ;
         rewrite linvunitor_assoc ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <- lwhisker_lwhisker_rassociator ;
         rewrite !lwhisker_vcomp ;
         apply idpath).
  Defined.

  Definition functor_from_lax_slice_cleaving_nat_z_iso
    : nat_z_iso
        (functor_from_cleaving
           (lax_slice_disp_bicat B a)
           (lax_slice_disp_2cells_isaprop B a)
           (lax_slice_disp_univalent_2_1 B a)
           (lax_slice_global_cleaving a)
           (lax_slice_local_iso_cleaving a)
           f)
        (lax_slice_fib_to_hom _ _
         ∙ pre_comp a f
         ∙ hom_to_lax_slice_fib _ _).
  Proof.
    use make_nat_z_iso.
    - exact functor_from_lax_slice_cleaving_nat_trans.
    - intro g.
      apply is_z_iso_discrete_fiber.
      apply lax_slice_invertible_2cell_is_left_disp_adj_equiv.
      cbn.
      is_iso.
  Defined.
End LaxSliceSubFiber.

(**
 3. Fiber of oplax slice
 *)
Section OplaxSliceFiber.
  Context {B : bicat}
          (c a : B).

  Let fib : category
    := discrete_fiber_category
         (oplax_slice_disp_bicat B a)
         (oplax_slice_disp_2cells_isaprop B a)
         (oplax_slice_disp_univalent_2_1 B a)
         (oplax_slice_local_iso_cleaving a)
         c.

  Let homc : category
    := (hom c a)^op.

  Definition hom_to_oplax_slice_fib_data
    : functor_data homc fib.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, lunitor _ • α).
  Defined.

  Definition hom_to_oplax_slice_fib_is_functor
    : is_functor hom_to_oplax_slice_fib_data.
  Proof.
    split.
    - intro f ; cbn.
      apply id2_right.
    - intros f g h α β ; cbn.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition hom_to_oplax_slice_fib
    : homc ⟶ fib.
  Proof.
    use make_functor.
    - exact hom_to_oplax_slice_fib_data.
    - exact hom_to_oplax_slice_fib_is_functor.
  Defined.

  Definition oplax_slice_fib_to_hom_data
    : functor_data fib homc.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, linvunitor _ • α).
  Defined.

  Definition oplax_slice_fib_to_hom_is_functor
    : is_functor oplax_slice_fib_to_hom_data.
  Proof.
    split.
    - intros f ; cbn.
      apply linvunitor_lunitor.
    - intros f g h α β ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite vcomp_lunitor.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      use maponpaths_2.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
  Qed.

  Definition oplax_slice_fib_to_hom
    : fib ⟶ homc.
  Proof.
    use make_functor.
    - exact oplax_slice_fib_to_hom_data.
    - exact oplax_slice_fib_to_hom_is_functor.
  Defined.

  Definition equiv_oplax_slice_fib_hom_unit
    : functor_identity fib
      ⟹
      oplax_slice_fib_to_hom ∙ hom_to_oplax_slice_fib.
  Proof.
    use make_nat_trans.
    - exact (λ f, lunitor f).
    - abstract
        (intros f g α ; cbn ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocl ;
         do 3 apply maponpaths ;
         rewrite !vassocr ;
         rewrite !lwhisker_vcomp ;
         rewrite vcomp_lunitor ;
         rewrite !vassocr ;
         rewrite lunitor_linvunitor ;
         rewrite id2_left ;
         apply idpath).
  Defined.

  Definition equiv_oplax_slice_fib_hom_counit
    : hom_to_oplax_slice_fib ∙ oplax_slice_fib_to_hom
      ⟹
      functor_identity homc.
  Proof.
    use make_nat_trans.
    - exact (λ f, id₂ f).
    - abstract
        (intros f g α ; cbn ;
         rewrite id2_left, id2_right ;
         rewrite !vassocr ;
         rewrite linvunitor_lunitor ;
         apply id2_left).
  Defined.

  Definition equiv_oplax_slice_fib_hom
    : equivalence_of_cats fib homc.
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact oplax_slice_fib_to_hom.
      + exact hom_to_oplax_slice_fib.
      + exact equiv_oplax_slice_fib_hom_unit.
      + exact equiv_oplax_slice_fib_hom_counit.
    - split.
      + intro f.
        apply is_z_iso_discrete_fiber.
        apply oplax_slice_invertible_2cell_is_left_disp_adj_equiv.
        cbn.
        is_iso.
      + intro f.
        apply opp_is_z_isomorphism.
        apply is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
  Defined.

  Definition adj_equivalence_oplax_slice_fib_to_hom
    : adj_equivalence_of_cats oplax_slice_fib_to_hom
    := adjointificiation equiv_oplax_slice_fib_hom.

  Definition adj_equiv_oplax_slice_fib_hom
    : adj_equiv fib homc
    := _ ,, adj_equivalence_oplax_slice_fib_to_hom.
End OplaxSliceFiber.

(**
 4. Fiber functor of oplax slice
 *)
Section OplaxSliceSubFiber.
  Context {B : bicat}
          (a : B)
          {c₁ c₂ : B}
          (f : c₁ --> c₂).

  Let fib₁ : category
    := discrete_fiber_category
         (oplax_slice_disp_bicat B a)
         (oplax_slice_disp_2cells_isaprop B a)
         (oplax_slice_disp_univalent_2_1 B a)
         (oplax_slice_local_iso_cleaving a)
         c₁.

  Let fib₂ : category
    := discrete_fiber_category
         (oplax_slice_disp_bicat B a)
         (oplax_slice_disp_2cells_isaprop B a)
         (oplax_slice_disp_univalent_2_1 B a)
         (oplax_slice_local_iso_cleaving a)
         c₂.

  Definition functor_from_oplax_slice_cleaving_nat_trans
    : functor_from_cleaving
        (oplax_slice_disp_bicat B a)
        (oplax_slice_disp_2cells_isaprop B a)
        (oplax_slice_disp_univalent_2_1 B a)
        (oplax_slice_global_cleaving a)
        (oplax_slice_local_iso_cleaving a)
        f
      ⟹
      oplax_slice_fib_to_hom _ _
      ∙ functor_opp (pre_comp a f)
      ∙ hom_to_oplax_slice_fib _ _.
  Proof.
    use make_nat_trans.
    - exact (λ g, lunitor _).
    - abstract
        (intros g₁ g₂ α ; cbn in * ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite lwhisker_id2, id2_left, id2_right ;
         do 3 apply maponpaths ;
         rewrite vcomp_lunitor ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite <- lunitor_triangle ;
         rewrite !vassocr ;
         rewrite lwhisker_lwhisker ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <-vcomp_whisker ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite rwhisker_hcomp, lwhisker_hcomp ;
         rewrite triangle_r_inv ;
         apply idpath).
  Defined.

  Definition functor_from_oplax_slice_cleaving_nat_z_iso
    : nat_z_iso
        (functor_from_cleaving
           (oplax_slice_disp_bicat B a)
           (oplax_slice_disp_2cells_isaprop B a)
           (oplax_slice_disp_univalent_2_1 B a)
           (oplax_slice_global_cleaving a)
           (oplax_slice_local_iso_cleaving a)
           f)
        (oplax_slice_fib_to_hom _ _
         ∙ functor_opp (pre_comp a f)
         ∙ hom_to_oplax_slice_fib _ _).
  Proof.
    use make_nat_z_iso.
    - exact functor_from_oplax_slice_cleaving_nat_trans.
    - intro g.
      apply is_z_iso_discrete_fiber.
      apply oplax_slice_invertible_2cell_is_left_disp_adj_equiv.
      cbn.
      is_iso.
  Defined.
End OplaxSliceSubFiber.

(**
 5. Fiber of slice
 *)
Section SliceFiber.
  Context {B : bicat}
          (c a : B).

  Let fib : category
    := discrete_fiber_category
         (slice_disp_bicat a)
         (disp_2cells_isaprop_slice a)
         (disp_univalent_2_1_slice a)
         (slice_local_iso_cleaving a)
         c.

  Let homc : category
    := core (hom c a).

  Definition hom_to_slice_fib_data
    : functor_data homc fib.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α,
             comp_of_invertible_2cell
               (z_iso_to_inv2cell α)
               (linvunitor_invertible_2cell _)).
  Defined.

  Definition hom_to_slice_fib_is_functor
    : is_functor hom_to_slice_fib_data.
  Proof.
    split.
    - intro f.
      use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn.
      apply id2_left.
    - intros f g h α β.
      use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply linvunitor_natural.
      }
      rewrite <- lwhisker_hcomp.
      apply maponpaths.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      refine (!(id2_right _) @ _).
      apply maponpaths.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
  Qed.

  Definition hom_to_slice_fib
    : homc ⟶ fib.
  Proof.
    use make_functor.
    - exact hom_to_slice_fib_data.
    - exact hom_to_slice_fib_is_functor.
  Defined.

  Definition slice_fib_to_hom_data
    : functor_data fib homc.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - intros f g α.
      simple refine (_ ,, _).
      + exact (pr1 α • lunitor _).
      + use is_inv2cell_to_is_z_iso.
        is_iso.
        apply property_from_invertible_2cell.
  Defined.

  Definition slice_fib_to_hom_is_functor
    : is_functor slice_fib_to_hom_data.
  Proof.
    split.
    - intros f.
      use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn.
      apply linvunitor_lunitor.
    - intros f g h α β.
      use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      apply lunitor_triangle.
  Qed.

  Definition slice_fib_to_hom
    : fib ⟶ homc.
  Proof.
    use make_functor.
    - exact slice_fib_to_hom_data.
    - exact slice_fib_to_hom_is_functor.
  Defined.

  Definition equiv_slice_fib_hom_unit
    : functor_identity fib
      ⟹
      slice_fib_to_hom ∙ hom_to_slice_fib.
  Proof.
    use make_nat_trans.
    - exact (λ f, linvunitor_invertible_2cell f).
    - abstract
        (intros f g α ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn ;
         rewrite !vassocr ;
         do 2 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite lunitor_linvunitor ;
         rewrite id2_right ;
         rewrite !lwhisker_hcomp ;
         rewrite <- linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         apply maponpaths ;
         rewrite linvunitor_assoc ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite lwhisker_hcomp, rwhisker_hcomp ;
         apply triangle_r_inv).
  Defined.

  Definition equiv_slice_fib_hom_counit
    : hom_to_slice_fib ∙ slice_fib_to_hom
      ⟹
      functor_identity homc.
  Proof.
    use make_nat_trans.
    - exact (λ f, identity_z_iso f).
    - abstract
        (intros f g α ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn ;
         rewrite id2_left, id2_right ;
         rewrite !vassocl ;
         rewrite linvunitor_lunitor ;
         apply id2_right).
  Defined.

  Definition equiv_slice_fib_hom
    : equivalence_of_cats fib homc.
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact slice_fib_to_hom.
      + exact hom_to_slice_fib.
      + exact equiv_slice_fib_hom_unit.
      + exact equiv_slice_fib_hom_counit.
    - split.
      + intro f.
        apply is_z_iso_discrete_fiber.
        apply slice_is_inv2cell_to_is_disp_adj_equiv.
      + intro f ; cbn.
        apply is_z_iso_core.
  Defined.

  Definition adj_equivalence_slice_fib_to_hom
    : adj_equivalence_of_cats slice_fib_to_hom
    := adjointificiation equiv_slice_fib_hom.

  Definition adj_equiv_slice_fib_hom
    : adj_equiv fib homc
    := _ ,, adj_equivalence_slice_fib_to_hom.
End SliceFiber.

(**
 6. Fiber functor of oplax slice
 *)
Section SliceSubFiber.
  Context {B : bicat}
          (a : B)
          {c₁ c₂ : B}
          (f : c₁ --> c₂).

  Let fib₁ : category
    := discrete_fiber_category
         (slice_disp_bicat a)
         (disp_2cells_isaprop_slice a)
         (disp_univalent_2_1_slice a)
         (slice_local_iso_cleaving a)
         c₁.

  Let fib₂ : category
    := discrete_fiber_category
         (slice_disp_bicat a)
         (disp_2cells_isaprop_slice a)
         (disp_univalent_2_1_slice a)
         (slice_local_iso_cleaving a)
         c₂.

  Definition functor_from_slice_cleaving_nat_trans
    : functor_from_cleaving
        (slice_disp_bicat a)
        (disp_2cells_isaprop_slice a)
        (disp_univalent_2_1_slice a)
        (slice_global_cleaving a)
        (slice_local_iso_cleaving a)
        f
      ⟹
      slice_fib_to_hom _ _
      ∙ core_functor (pre_comp a f)
      ∙ hom_to_slice_fib _ _.
  Proof.
    use make_nat_trans.
    - exact (λ g, linvunitor_invertible_2cell _).
    - abstract
        (intros g₁ g₂ α ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn in * ;
         rewrite lwhisker_id2 ;
         rewrite id2_left, id2_right ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocr ;
         do 3 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite runitor_rwhisker ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite <- vcomp_whisker ;
         rewrite linvunitor_assoc ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <- lwhisker_lwhisker_rassociator ;
         rewrite !lwhisker_vcomp ;
         apply idpath).
  Defined.

  Definition functor_from_slice_cleaving_nat_z_iso
    : nat_z_iso
        (functor_from_cleaving
           (slice_disp_bicat a)
           (disp_2cells_isaprop_slice a)
           (disp_univalent_2_1_slice a)
           (slice_global_cleaving a)
           (slice_local_iso_cleaving a)
           f)
        (slice_fib_to_hom _ _
         ∙ core_functor (pre_comp a f)
         ∙ hom_to_slice_fib _ _).
  Proof.
    use make_nat_z_iso.
    - exact functor_from_slice_cleaving_nat_trans.
    - intro g.
      apply is_z_iso_discrete_fiber.
      apply slice_is_inv2cell_to_is_disp_adj_equiv.
  Defined.
End SliceSubFiber.
