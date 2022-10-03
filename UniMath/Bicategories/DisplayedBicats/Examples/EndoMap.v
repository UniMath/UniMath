(************************************************************************

 The bicategory of objects with an endomorphisms


 Note: if we would have defined this bicategory via algebras on a
 pseudofunctor, then we would have obtained a different notion of 1-cell.
 In this file, we define it in such a way, that the commutativity cell
 of 1-cells do not have to be invertible.

 Contents
 1. The definition via displayed bicategories
 2. The univalence

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section EndoMap.
  Context (B : bicat).

  (**
   1. The definition via displayed bicategories
   *)
  Definition disp_end_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ x, x --> x).
    - exact (λ x y mx my f, f · my ==> mx · f).
  Defined.

  Definition disp_end_cat_id_comp
    : disp_cat_id_comp B disp_end_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x mx, lunitor _ • rinvunitor _).
    - exact (λ x y z f g mx my mz mf mg,
             rassociator _ _ _
             • (_ ◃ mg)
             • lassociator _ _ _
             • (mf ▹ _)
             • rassociator _ _ _).
  Defined.

  Definition disp_end_cat_data
    : disp_cat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_end_ob_mor.
    - exact disp_end_cat_id_comp.
  Defined.

  Definition disp_end_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_end_cat_data.
    - exact (λ x y f g α mx my mf mg,
             mf • (_ ◃ α)
             =
             (α ▹ _) • mg).
  Defined.

  Definition disp_end_prebicat_ops
    : disp_prebicat_ops disp_end_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros x y f mx my mf ; cbn in *.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      apply idpath.
    - intros x y f mx my mf ; cbn in *.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite !vcomp_lunitor.
      rewrite !vassocr.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    - intros x y f mx my mf ; cbn in *.
      rewrite !vassocl.
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- runitor_triangle.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      apply idpath.
    - intros x y f mx my mf ; cbn in *.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite !lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite <- !lwhisker_hcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    - intros x y f mx my mf ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite <- left_unit_inv_assoc₂.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      rewrite left_unit_inv_assoc₂.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      apply idpath.
    - intros w x y z f g h mw mx my mz mf mg mh ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 7 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rassociator_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_lwhisker_rassociator.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rassociator_rassociator.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rassociator_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite <- rwhisker_lwhisker_rassociator.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    - intros w x y z f g h mw mx my mz mf mg mh ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocr.
      do 2 (use vcomp_move_L_Mp ; [ is_iso | ] ; cbn).
      rewrite !vassocl.
      do 2 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn).
      etrans.
      {
        do 5 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_lassociator.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          apply id2_left.
        }
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lassociator_lassociator.
      refine (!_).
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite <- lassociator_lassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2.
        apply id2_left.
      }
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intros x y f g h α β mx my mf mg mh mα mβ ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite mα.
      rewrite !vassocl.
      apply maponpaths.
      exact mβ.
    - intros x y z f g₁ g₂ α mx my mz mf mg₁ mg₂ mα ; cbn in *.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- mα.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      apply idpath.
    - intros x y z f₁ f₂ g α mx my mz mf₁ mf₂ mg mα ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite <- mα.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker_rassociator.
      apply idpath.
  Qed.

  Definition disp_end_prebicat_data
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_end_prebicat_1_id_comp_cells.
    - exact disp_end_prebicat_ops.
  Defined.

  Definition disp_end_prebicat_laws
    : disp_prebicat_laws disp_end_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply cellset_property.
  Qed.

  Definition disp_end_prebicat
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_end_prebicat_data.
    - exact disp_end_prebicat_laws.
  Defined.

  Definition disp_end : disp_bicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_end_prebicat.
    - intro ; intros.
      use isasetaprop.
      apply cellset_property.
  Defined.

  Definition end_bicat : bicat := total_bicat disp_end.

  Definition disp_2cells_isaprop_end_bicat
    : disp_2cells_isaprop disp_end.
  Proof.
    intros x y f g τ ex ey ef eg.
    apply cellset_property.
  Qed.

  Definition disp_locally_sym_end_bicat
    : disp_locally_sym disp_end.
  Proof.
    intros x y f g τ ex ey ef eg eτ ; cbn in eτ ; cbn.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    exact (!(eτ)).
  Qed.

  Definition disp_locally_groupoid_end_bicat
    : disp_locally_groupoid disp_end.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_end_bicat.
    - exact disp_2cells_isaprop_end_bicat.
  Qed.

  (**
   2. The univalence
   *)
  Definition disp_univalent_2_1_disp_end
    : disp_univalent_2_1 disp_end.
  Proof.
    intros x y f g p ex ey ef eg.
    induction p.
    use isweqimplimpl.
    - intro τ.
      pose (p := pr1 τ).
      cbn in p.
      rewrite lwhisker_id2, id2_rwhisker in p.
      rewrite id2_left, id2_right in p.
      cbn.
      exact p.
    - apply cellset_property.
    - use invproofirrelevance.
      intros τ₁ τ₂.
      use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ].
      apply disp_2cells_isaprop_end_bicat.
  Qed.

  Definition inv2cell_to_disp_adj_equiv_disp_end
             {x : B}
             {ex ey : disp_end x}
             (τ : invertible_2cell ex ey)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) ex ey.
  Proof.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _)))).
    - exact (lunitor _ • τ^-1 • rinvunitor _).
    - exact (lunitor _ • τ • rinvunitor _).
    - abstract
        (cbn ;
         rewrite <- !lwhisker_vcomp ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite <- linvunitor_assoc ;
         refine (!_) ;
         rewrite lwhisker_hcomp ;
         rewrite <- linvunitor_natural ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !rwhisker_hcomp ;
         rewrite <- triangle_r_inv ;
         rewrite <- !lwhisker_hcomp ;
         rewrite <- !rwhisker_hcomp ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite !vassocl ;
         etrans ;
         [ do 3 apply maponpaths ;
           rewrite !vassocr ;
           rewrite lunitor_triangle ;
           apply idpath
         | ] ;
         etrans ;
         [ do 2 apply maponpaths ;
           rewrite !vassocr ;
           rewrite vcomp_lunitor ;
           rewrite !vassocl;
           rewrite rwhisker_hcomp ;
           rewrite <- rinvunitor_natural ;
           apply idpath
         | ] ;
         rewrite !vassocr ;
         refine (_ @ id2_left _) ;
         apply maponpaths_2 ;
         use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
         rewrite !vassocl ;
         use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
         rewrite id2_left ;
         rewrite vcomp_lunitor ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite <- !lwhisker_vcomp ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite lunitor_lwhisker ;
         rewrite runitor_lunitor_identity ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite lunitor_lwhisker ;
         rewrite rwhisker_vcomp ;
         rewrite rinvunitor_runitor ;
         rewrite id2_rwhisker ;
         rewrite id2_right ;
         use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
         rewrite !vassocr ;
         rewrite rinvunitor_triangle ;
         rewrite rwhisker_hcomp ;
         rewrite <- rinvunitor_natural ;
         rewrite vcomp_lunitor ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite rinvunitor_natural ;
         rewrite <- rwhisker_hcomp ;
         apply idpath).
    - apply disp_2cells_isaprop_end_bicat.
    - apply disp_2cells_isaprop_end_bicat.
    - apply disp_locally_groupoid_end_bicat.
    - apply disp_locally_groupoid_end_bicat.
  Defined.

  Definition disp_adj_equiv_to_inv2cell_disp_end
             {x : B}
             {ex ey : disp_end x}
             (τ : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    ex ey)
    : invertible_2cell ex ey.
  Proof.
    use make_invertible_2cell.
    - exact (linvunitor _ • pr112 τ • runitor _).
    - use make_is_invertible_2cell.
      + exact (linvunitor _ • pr1 τ • runitor _).
      + abstract
          (rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           use (vcomp_rcancel (ex ◃ linvunitor _)) ; [ is_iso | ] ;
           refine (_ @ !(pr1 (pr212 τ))) ; cbn ;
           rewrite !vassocr ;
           rewrite <- linvunitor_assoc ;
           refine (!_) ;
           rewrite lwhisker_hcomp ;
           rewrite <- linvunitor_natural ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite linvunitor_assoc ;
           rewrite !vassocl ;
           rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rassociator_lassociator ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite <- vcomp_runitor ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- vcomp_runitor ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite <- runitor_triangle ;
           rewrite runitor_lunitor_identity ;
           rewrite !vassocl ;
           rewrite lwhisker_vcomp ;
           rewrite lunitor_linvunitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_right ;
           apply idpath).
      + abstract
          (rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           use (vcomp_lcancel (lunitor _ ▹ ey)) ; [ is_iso | ] ;
           refine (_ @ pr2 (pr212 τ)) ; cbn ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           rewrite lunitor_triangle ;
           rewrite <- vcomp_lunitor ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite lunitor_runitor_identity ;
           rewrite runitor_triangle ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite <- vcomp_runitor ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite lunitor_triangle ;
           apply idpath).
  Defined.

  Definition inv2cell_weq_disp_adj_equiv_disp_end
             (HB : is_univalent_2_1 B)
             {x : B}
             (ex ey : disp_end x)
    : invertible_2cell ex ey
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) ex ey.
  Proof.
    use make_weq.
    - exact inv2cell_to_disp_adj_equiv_disp_end.
    - use gradth.
      + exact disp_adj_equiv_to_inv2cell_disp_end.
      + abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite linvunitor_lunitor ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite rinvunitor_runitor ;
           apply id2_right).
      + abstract
          (intros τ ;
           use subtypePath ;
           [ intro ;
             use (isaprop_disp_left_adjoint_equivalence _ _ HB) ;
             apply disp_univalent_2_1_disp_end
           | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite lunitor_linvunitor ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite runitor_rinvunitor ;
           apply id2_right).
  Defined.

  Definition disp_univalent_2_0_disp_end
             (HB : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_end.
  Proof.
    intros x y p ex ey.
    induction p.
    use weqhomot.
    - exact (inv2cell_weq_disp_adj_equiv_disp_end HB ex ey
             ∘ make_weq _ (HB x x ex ey))%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           use (isaprop_disp_left_adjoint_equivalence _ _ HB) ;
           apply disp_univalent_2_1_disp_end
         | ] ;
         cbn ;
         rewrite id2_right ;
         apply idpath).
  Defined.
End EndoMap.
