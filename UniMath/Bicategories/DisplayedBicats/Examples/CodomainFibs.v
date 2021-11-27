(*********************************************************************

 Displayed bicategory of Street fibrations

 We define the displayed bicategory of Street fibrations over
 arbitrary bicategories such that the projection pseudofunctor gives
 the codomain of a Street fibration.

 1. Definition of the displayed bicategory
 2. Invertible 2-cells
 3. Local Univalence

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Faithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Local Open Scope cat.

Section CodomainStreetFibs.
  Context (B : bicat).

  Definition transportb_cell_of_internal_sfib_over
             {e₁ e₂ b₁ b₂ : B}
             {f g : b₁ --> b₂}
             {p₁ : e₁ --> b₁}
             {p₂ : e₂ --> b₂}
             {α β : f ==> g}
             (p : α = β)
             {fe : mor_of_internal_sfib_over p₁ p₂ f}
             {ge : mor_of_internal_sfib_over p₁ p₂ g}
             (γ : cell_of_internal_sfib_over β fe ge)
    : pr1 (transportb
             (λ α : f ==> g, cell_of_internal_sfib_over α fe ge)
             p
             γ)
      =
      γ.
  Proof.
    induction p.
    apply idpath.
  Qed.

  (**
   1. Definition of the displayed bicategory
   *)
  Definition cod_sfibs_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    simple refine (_ ,, _).
    - exact (λ b, ∑ (x : B) (f : x --> b), internal_sfib f).
    - exact (λ x y hx hy f, mor_of_internal_sfib_over (pr12 hx) (pr12 hy) f).
  Defined.

  Definition cod_sfibs_id_comp
    : disp_cat_id_comp B cod_sfibs_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x hx, id_mor_of_internal_sfib_over _).
    - exact (λ x y z f g hx hy hz hf hg, comp_mor_of_internal_sfib_over hf hg).
  Defined.

  Definition cod_sfibs_disp_cat_data
    : disp_cat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact cod_sfibs_disp_cat_ob_mor.
    - exact cod_sfibs_id_comp.
  Defined.

  Definition cod_sfibs_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (_ ,, _).
    - exact cod_sfibs_disp_cat_data.
    - exact (λ x y f g γ hx hy hf hg, cell_of_internal_sfib_over γ hf hg).
  Defined.

  Definition cod_sfibs_prebicat_ops
    : disp_prebicat_ops cod_sfibs_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros x y f hx hy hf ; cbn in *.
      refine (make_cell_of_internal_sfib_over (id2 _) _).
      abstract
        (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
         rewrite id2_rwhisker, lwhisker_id2 ;
         rewrite id2_left, id2_right ;
         apply idpath).
    - intros x y f hx hy hf ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (lunitor _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite <- rwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite runitor_rwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite lunitor_triangle ;
           rewrite vcomp_lunitor ;
           rewrite !vassocr ;
           rewrite <- linvunitor_assoc ;
           rewrite linvunitor_lunitor ;
           apply id2_left).
    - intros x y f hx hy hf ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (runitor _).
      +  abstract
           (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
            cbn ;
            rewrite <- !lwhisker_vcomp ;
            rewrite !vassocl ;
            rewrite runitor_rwhisker ;
            rewrite lwhisker_vcomp ;
            rewrite linvunitor_lunitor ;
            rewrite lwhisker_id2 ;
            rewrite id2_right ;
            rewrite runitor_triangle ;
            rewrite vcomp_runitor ;
            rewrite !vassocr ;
            apply maponpaths_2 ;
            exact (!(left_unit_assoc _ _))).
    - intros x y f hx hy hf ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (linvunitor _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite runitor_rwhisker ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite linvunitor_lunitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           rewrite <- linvunitor_assoc ;
           rewrite lwhisker_hcomp ;
           rewrite <- linvunitor_natural ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite linvunitor_assoc ;
           rewrite !vassocl ;
           rewrite rassociator_lassociator ;
           rewrite id2_right ;
           apply idpath).
    - intros x y f hx hy hf ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (rinvunitor _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !lwhisker_hcomp ;
           rewrite triangle_l_inv ;
           rewrite <- !lwhisker_hcomp, <- rwhisker_hcomp ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite runitor_triangle ;
           rewrite vcomp_runitor ;
           refine (!(id2_left _) @ _) ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite <- left_unit_assoc ;
           rewrite lwhisker_vcomp ;
           rewrite rinvunitor_runitor ;
           rewrite lwhisker_id2 ;
           apply idpath).
    - intros x₁ x₂ x₃ x₄ f g k hx₁ hx₂ hx₃ hx₄ hf hg hk ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (rassociator _ _ _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite lassociator_lassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite rwhisker_rwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_L_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite <- lassociator_lassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rwhisker_vcomp ;
           rewrite lassociator_rassociator ;
           rewrite id2_rwhisker ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite <- rwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_L_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite lassociator_lassociator ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite <- lwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- lassociator_lassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite rwhisker_vcomp ;
           rewrite lassociator_rassociator ;
           rewrite id2_rwhisker ;
           apply id2_right).
    - intros x₁ x₂ x₃ x₄ f g k hx₁ hx₂ hx₃ hx₄ hf hg hk ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (lassociator _ _ _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite <- !rwhisker_vcomp, <- !lwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite lassociator_lassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite rwhisker_rwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite <- lassociator_lassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rwhisker_vcomp ;
           rewrite lassociator_rassociator ;
           rewrite id2_rwhisker ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite <- rwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite lassociator_lassociator ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite <- lwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite <- lassociator_lassociator ;
           rewrite !vassocl ;
           apply idpath).
    - intros x₁ x₂ f g h α β hx₁ hx₂ hf hg hh hα hβ ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (hα • hβ).
      + abstract
          (unfold cell_of_internal_sfib_over_homot ;
           cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite (cell_of_internal_sfib_over_eq hα) ;
           rewrite !vassocl ;
           rewrite (cell_of_internal_sfib_over_eq hβ) ;
           apply idpath).
    - intros x₁ x₂ x₃ f₁ f₂ g α hx₁ hx₂ hx₃ hf₁ hf₂ hg hα ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (_ ◃ hα).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite !vassocl ;
           rewrite <- rwhisker_lwhisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite lwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- vcomp_whisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- lwhisker_lwhisker_rassociator ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !lwhisker_vcomp ;
           apply maponpaths ;
           exact (cell_of_internal_sfib_over_eq hα)).
    - intros x₁ x₂ x₃ f₁ f₂ g α hx₁ hx₂ hx₃ hf₁ hf₂ hg hα ; cbn in *.
      use make_cell_of_internal_sfib_over.
      + exact (hα ▹ _).
      + abstract
          (unfold cell_of_internal_sfib_over_homot, mor_of_internal_sfib_over_com ;
           cbn ;
           rewrite !vassocl ;
           rewrite rwhisker_rwhisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite rwhisker_lwhisker ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite <- vcomp_whisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite <- rwhisker_rwhisker_alt ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !rwhisker_vcomp ;
           apply maponpaths ;
           exact (cell_of_internal_sfib_over_eq hα)).
  Defined.

  Definition cod_sfibs_prebicat_data
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact cod_sfibs_prebicat_1_id_comp_cells.
    - exact cod_sfibs_prebicat_ops.
  Defined.

  Definition cod_sfibs_laws
    : disp_prebicat_laws cod_sfibs_prebicat_data.
  Proof.
    repeat split
    ; intro ; intros
    ; cbn in *
    ; (use subtypePath ; [ intro ; apply cellset_property | ]) ; cbn
    ; rewrite transportb_cell_of_internal_sfib_over ; cbn.
    - apply id2_left.
    - apply id2_right.
    - apply vassocr.
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - apply vcomp_lunitor.
    - apply vcomp_runitor.
    - apply lwhisker_lwhisker.
    - apply rwhisker_lwhisker.
    - apply rwhisker_rwhisker.
    - apply vcomp_whisker.
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - apply runitor_rwhisker.
    - apply lassociator_lassociator.
  Qed.

  Definition cod_sfibs_prebicat
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact cod_sfibs_prebicat_data.
    - exact cod_sfibs_laws.
  Defined.

  Definition cod_sfibs_has_disp_cellset
    : has_disp_cellset cod_sfibs_prebicat.
  Proof.
    intros x y f g γ hx hy hf hg.
    use isaset_total2.
    - apply cellset_property.
    - intro.
      apply isasetaprop.
      apply cellset_property.
  Defined.

  Definition cod_sfibs
    : disp_bicat B.
  Proof.
    simple refine (_ ,, _).
    - exact cod_sfibs_prebicat.
    - exact cod_sfibs_has_disp_cellset.
  Defined.

 (**
  2. Invertible 2-cells
  *)
  Definition invertible_2cell_to_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : f ==> g}
             (Hγ : is_invertible_2cell γ)
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             {hγ : hf ==>[ γ ] hg}
             (Hhγ : is_invertible_2cell (pr1 hγ))
    : is_disp_invertible_2cell Hγ hγ.
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - use make_cell_of_internal_sfib_over.
      + exact (Hhγ^-1).
      + abstract
          (unfold cell_of_internal_sfib_over_homot ;
           use vcomp_move_R_Mp ; [ is_iso | ] ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ;
           cbn ;
           exact (!(cell_of_internal_sfib_over_eq hγ))).
    - abstract
        (use subtypePath ; [ intro ; apply cellset_property | ] ;
         cbn ;
         rewrite transportb_cell_of_internal_sfib_over ; cbn ;
         apply vcomp_rinv).
    - abstract
        (cbn ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         cbn ;
         rewrite transportb_cell_of_internal_sfib_over ; cbn ;
         apply vcomp_linv).
  Defined.

  Definition disp_invertible_2cell_to_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : f ==> g}
             (Hγ : is_invertible_2cell γ)
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             {hγ : hf ==>[ γ ] hg}
             (Hhγ : is_disp_invertible_2cell Hγ hγ)
    : is_invertible_2cell (pr1 hγ).
  Proof.
    use make_is_invertible_2cell.
    - exact (pr11 Hhγ).
    - abstract
        (pose (maponpaths pr1 (pr12 Hhγ)) as p ;
         cbn in p ;
         rewrite transportb_cell_of_internal_sfib_over in p ;
         cbn in p ;
         exact p).
    - abstract
        (pose (maponpaths pr1 (pr22 Hhγ)) as p ;
         cbn in p ;
         rewrite transportb_cell_of_internal_sfib_over in p ;
         cbn in p ;
         exact p).
  Defined.

  Definition make_cod_sfibs_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : f ==> g}
             (Hγ : is_invertible_2cell γ)
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (hγ : hf ==>[ γ ] hg)
             (Hhγ : is_invertible_2cell (pr1 hγ))
    : disp_invertible_2cell (make_invertible_2cell Hγ) hf hg.
  Proof.
    refine (hγ ,, _).
    use invertible_2cell_to_disp_invertible_2cell.
    exact Hhγ.
  Defined.

  Definition inv_2cell_to_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : invertible_2cell f g}
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (α : ∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ))
    : disp_invertible_2cell γ hf hg.
  Proof.
    use make_cod_sfibs_disp_invertible_2cell.
    - exact (pr1 α).
    - exact (pr2 α).
  Defined.

  Definition disp_invertible_2cell_to_inv_2cell
             {x y : B}
             {f g : x --> y}
             {γ : invertible_2cell f g}
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (α : disp_invertible_2cell γ hf hg)
    : ∑ (hγ : hf ==>[ γ] hg), is_invertible_2cell (pr1 hγ).
  Proof.
    refine (pr1 α ,, _).
    use disp_invertible_2cell_to_invertible_2cell.
    - exact (pr2 γ).
    - exact (pr2 α).
  Defined.

  Definition inv_2cell_weq_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             (γ : invertible_2cell f g)
             {hx : cod_sfibs x}
             {hy : cod_sfibs y}
             (hf : hx -->[ f ] hy)
             (hg : hx -->[ g ] hy)
    : (∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ))
      ≃
      disp_invertible_2cell γ hf hg.
  Proof.
    use make_weq.
    - exact inv_2cell_to_disp_invertible_2cell.
    - use gradth.
      + exact disp_invertible_2cell_to_inv_2cell.
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           apply idpath).
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           apply idpath).
  Defined.

  (**
   3. Local Univalence
   *)
  Local Definition refactor_weq
        {x y : B}
        {f g : x --> y}
        (γ : invertible_2cell f g)
        {hx : cod_sfibs x}
        {hy : cod_sfibs y}
        (hf : hx -->[ f ] hy)
        (hg : hx -->[ g ] hy)
    : (∑ (γe : invertible_2cell (pr1 hf) (pr1 hg)),
       cell_of_internal_sfib_over_homot γ γe)
      ≃
      ∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ).
  Proof.
    use make_weq.
    - exact (λ α, ((pr11 α ,, pr2 α) ,, pr21 α)).
    - use gradth.
      + exact (λ α, (pr11 α ,, pr2 α) ,, pr21 α).
      + intro ; apply idpath.
      + intro ; apply idpath.
  Defined.

  Local Definition weq_on_fam
        (HB_2_1 : is_univalent_2_1 B)
        {x y : B}
        {f : x --> y}
        {hx : cod_sfibs x}
        {hy : cod_sfibs y}
        (hf hg : hx -->[ f] hy)
        (p : pr1 hf = pr1 hg)
    : (transportf
        (λ z,
         mor_preserves_cartesian (pr12 hx) (pr12 hy) z
         ×
         invertible_2cell (pr12 hx · f) (z · pr12 hy)) p (pr2 hf)
       =
       pr2 hg)
      ≃
      cell_of_internal_sfib_over_homot
        (id2_invertible_2cell f)
        (make_weq _ (HB_2_1 _ _ (pr1 hf) (pr1 hg)) p).
  Proof.
    induction hf as [ hf₁ hf₂ ].
    induction hg as [ hg₁ hg₂ ].
    cbn in *.
    induction p ; cbn.
    use weqimplimpl.
    - intro p.
      induction p.
      unfold cell_of_internal_sfib_over_homot.
      rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right.
      apply idpath.
    - unfold cell_of_internal_sfib_over_homot.
      intro p.
      use pathsdirprod.
      + apply isaprop_mor_preserves_cartesian.
      + rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right in p.
        unfold mor_of_internal_sfib_over_com in p.
        cbn in p.
        use subtypePath.
        {
          intro ; apply isaprop_is_invertible_2cell.
        }
        exact p.
    - use isasetdirprod.
      + apply isasetaprop.
        apply isaprop_mor_preserves_cartesian.
      + apply isaset_invertible_2cell.
    - apply cellset_property.
  Qed.

  Definition cod_sfibs_disp_univalent_2_1
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_1 cod_sfibs.
  Proof.
    intros x y f g p hx hy hf hg.
    induction p.
    use weqhomot.
    - exact (inv_2cell_weq_disp_invertible_2cell _ _ _
             ∘ refactor_weq _ _ _
             ∘ weqtotal2
                 (make_weq _ (HB_2_1 _ _ _ _))
                 (weq_on_fam _ _ _)
             ∘ total2_paths_equiv _ _ _)%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         cbn ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         apply idpath).
  Defined.
End CodomainStreetFibs.
