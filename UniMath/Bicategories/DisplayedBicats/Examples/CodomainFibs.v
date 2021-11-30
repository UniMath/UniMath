(*********************************************************************

 Displayed bicategory of Street fibrations

 We define the displayed bicategory of Street fibrations over
 arbitrary bicategories such that the projection pseudofunctor gives
 the codomain of a Street fibration.

 1. Definition of the displayed bicategory
 2. Invertible 2-cells
 3. Local Univalence
 4. Adjoint equivalences
 5. Global univalence

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
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
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
        (idtoiso_2_1 (pr1 hf) (pr1 hg) p).
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
                 (weq_on_fam _ _)
             ∘ total2_paths_equiv _ _ _)%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         cbn ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         apply idpath).
  Defined.

  (**
   4. Adjoint equivalences
   *)
  Section AdjEquivToDispAdjEquiv.
    Context (HB_2_0 : is_univalent_2_0 B)
            (HB_2_1 : is_univalent_2_1 B)
            {x : B}
            {hx hy : cod_sfibs x}
            (e : adjoint_equivalence (pr1 hx) (pr1 hy))
            (com : invertible_2cell (pr12 hx) (e · pr12 hy)).

    Local Definition adj_equiv_to_disp_adj_equiv_left_adj
      : hx -->[ internal_adjoint_equivalence_identity x] hy.
    Proof.
      use make_mor_of_internal_sfib_over.
      - exact e.
      - exact (equivalence_preserves_cartesian
                 (pr12 hx)
                 (pr12 hy)
                 e
                 com
                 (pr2 e)
                 HB_2_0
                 HB_2_1).
      - exact (comp_of_invertible_2cell
                 (runitor_invertible_2cell _)
                 com).
    Defined.

    Local Notation "'L'" := adj_equiv_to_disp_adj_equiv_left_adj.

    Local Definition adj_equiv_to_disp_adj_equiv_right_adj
      : hy -->[ internal_adjoint_equivalence_identity x] hx.
    Proof.
      use make_mor_of_internal_sfib_over.
      - exact (left_adjoint_right_adjoint e).
      - pose (einv := inv_adjequiv e).
        use (equivalence_preserves_cartesian
               (pr12 hy)
               (pr12 hx)
               einv
               _
               (pr2 einv)
               HB_2_0
               HB_2_1).
        exact (comp_of_invertible_2cell
                 (linvunitor_invertible_2cell _)
                 (comp_of_invertible_2cell
                    (rwhisker_of_invertible_2cell
                       _
                       (left_equivalence_unit_iso einv))
                    (comp_of_invertible_2cell
                       (rassociator_invertible_2cell _ _ _)
                       (lwhisker_of_invertible_2cell
                          _
                          (inv_of_invertible_2cell com))))).
      - refine (runitor _
                • linvunitor _
                • ((left_equivalence_counit_iso e)^-1 ▹ _)
                • rassociator _ _ _
                • (_ ◃ com^-1) ,, _).
        is_iso.
    Defined.

    Local Notation "'R'" := adj_equiv_to_disp_adj_equiv_right_adj.

    Local Lemma adj_equiv_to_disp_adj_equiv_unit_coh
      : @cell_of_internal_sfib_over_homot
          _ _ _ _ _ _ _
          (linvunitor (id₁ x))
          _ _
          (id_mor_of_internal_sfib_over (pr12 hx))
          (comp_mor_of_internal_sfib_over L R)
          (left_adjoint_unit (pr12 e)).
    Proof.
      unfold cell_of_internal_sfib_over_homot ; cbn.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite triangle_l_inv.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      {
        is_iso.
      }
      cbn.
      refine (!_).
      etrans.
      {
        rewrite !vassocl.
        rewrite vcomp_whisker.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_hcomp.
          rewrite <- linvunitor_natural.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- vcomp_runitor.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths ; clear com.
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      use vcomp_move_R_pM.
      {
        is_iso.
      }
      cbn.
      refine (!_).

      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        apply maponpaths.
        assert (linvunitor (pr1 e) • (pr121 (pr2 e) ▹ pr1 e)
                =
                rinvunitor _ • (pr1 e ◃ (pr222 (pr2 e))^-1) • lassociator _ _ _)
          as p.
        {
          refine (_ @ id2_left _).
          use vcomp_move_L_Mp.
          {
            is_iso.
          }
          cbn.
          rewrite !vassocr.
          exact (pr1 (pr122 e)).
        }
        apply maponpaths.
        exact p.
      }
      unfold left_adjoint_right_adjoint.
      use vcomp_move_R_Mp.
      {
        is_iso.
      }
      cbn.
      rewrite <- lassociator_lassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      refine (_ @ id2_right _).
      use vcomp_move_L_pM.
      {
        is_iso.
      }
      cbn.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lunitor_lwhisker.
        rewrite rwhisker_vcomp.
        rewrite runitor_rinvunitor.
        apply id2_rwhisker.
      }
      rewrite id2_left.
      rewrite rwhisker_vcomp.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      rewrite id2_rwhisker.
      apply idpath.
    Qed.

    Local Definition adj_equiv_to_disp_adj_equiv_unit
      : id_disp hx
        ==>[ left_adjoint_unit (internal_adjoint_equivalence_identity x) ]
        L ;; R.
    Proof.
      use make_cell_of_internal_sfib_over.
      - exact (left_adjoint_unit e).
      - exact adj_equiv_to_disp_adj_equiv_unit_coh.
    Defined.

    Local Notation "'η'" := adj_equiv_to_disp_adj_equiv_unit.

    Local Lemma adj_equiv_to_disp_adj_equiv_counit_coh
      : @cell_of_internal_sfib_over_homot
          _ _ _ _ _ _ _
          (lunitor (id₁ x))
          _ _
          (comp_mor_of_internal_sfib_over R L)
          (id_mor_of_internal_sfib_over (pr12 hy))
          (left_adjoint_counit (pr12 e)).
    Proof.
      unfold cell_of_internal_sfib_over_homot ; cbn.
      rewrite !vassocl.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocr.
        rewrite vcomp_runitor.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      assert (rassociator (pr112 e) (pr1 e) (pr12 hy) ▹ id₁ _
              • rassociator (pr112 e) (pr1 e · pr12 hy) (id₁ _)
              • (pr112 e ◃ runitor (pr1 e · pr12 hy))
              • lassociator (pr112 e) (pr1 e) (pr12 hy)
              =
              runitor _)
        as p.
      {
        rewrite !vassocl.
        rewrite !left_unit_assoc.
        rewrite !vassocl.
        rewrite <- vcomp_runitor.
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
        rewrite rassociator_lassociator.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        exact p.
      }
      rewrite <- vcomp_runitor.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite !id2_rwhisker.
        apply idpath.
      }
      rewrite id2_left.
      rewrite vcomp_runitor.
      apply idpath.
    Qed.

    Local Definition adj_equiv_to_disp_adj_equiv_counit
      : R ;; L
        ==>[ left_adjoint_counit (internal_adjoint_equivalence_identity x) ]
        id_disp hy.
    Proof.
      use make_cell_of_internal_sfib_over.
      - exact (left_adjoint_counit e).
      - exact adj_equiv_to_disp_adj_equiv_counit_coh.
    Defined.

    Local Notation "'ε'" := adj_equiv_to_disp_adj_equiv_counit.

    Local Definition adj_equiv_to_disp_adj_equiv_data
      : @disp_left_adjoint_data
          B cod_sfibs
          _ _
          (internal_adjoint_equivalence_identity x)
          (internal_adjoint_equivalence_identity x)
          hx hy
          L
      := (R ,, (η ,, ε)).

    Local Definition adj_equiv_to_disp_adj_equiv_adjoint_axioms
      : disp_left_adjoint_axioms
          (internal_adjoint_equivalence_identity x)
          adj_equiv_to_disp_adj_equiv_data.
    Proof.
      split ;
        simpl ;
        (use subtypePath ; [ intro ; apply cellset_property | ]) ;
        rewrite transportb_cell_of_internal_sfib_over ;
        cbn ;
        apply (pr2 e).
    Qed.

    Local Definition adj_equiv_to_disp_adj_equiv_equivalence_axioms
      : disp_left_equivalence_axioms
          (internal_adjoint_equivalence_identity x)
          adj_equiv_to_disp_adj_equiv_data.
    Proof.
      split ; apply invertible_2cell_to_disp_invertible_2cell ; apply (pr2 e).
    Defined.

    Definition adj_equiv_to_disp_adj_equiv
      : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) hx hy.
    Proof.
      simple refine (L ,, (_ ,, (_ ,, _))).
      - exact adj_equiv_to_disp_adj_equiv_data.
      - exact adj_equiv_to_disp_adj_equiv_adjoint_axioms.
      - exact adj_equiv_to_disp_adj_equiv_equivalence_axioms.
    Defined.
  End AdjEquivToDispAdjEquiv.

  Section DispAdjEquivToAdjEquiv.
    Context {x : B}
            {hx hy : cod_sfibs x}
            (e : disp_adjoint_equivalence
                   (internal_adjoint_equivalence_identity x)
                   hx hy).

    Local Definition disp_adj_equiv_to_left_adj_data
      : left_adjoint_data (pr11 e)
      := (pr1 (pr112 e) ,, (pr11 (pr212 e) ,, pr12 (pr212 e))).

    Local Definition disp_adj_equiv_to_left_adjoint_axioms
      : left_adjoint_axioms disp_adj_equiv_to_left_adj_data.
    Proof.
      split.
      - pose (maponpaths pr1 (pr1 (pr122 e))) as p.
        cbn in p.
        rewrite transportb_cell_of_internal_sfib_over in p.
        exact p.
      - pose (maponpaths pr1 (pr2 (pr122 e))) as p.
        cbn in p.
        rewrite transportb_cell_of_internal_sfib_over in p.
        exact p.
    Qed.

    Local Definition disp_adj_equiv_to_left_equivalence_axioms
      : left_equivalence_axioms disp_adj_equiv_to_left_adj_data.
    Proof.
      split.
      - exact (disp_invertible_2cell_to_invertible_2cell _ (pr1 (pr222 e))).
      - exact (disp_invertible_2cell_to_invertible_2cell _ (pr2 (pr222 e))).
    Defined.

    Local Definition disp_adj_equiv_to_left_adj_equiv
      : left_adjoint_equivalence (pr11 e).
    Proof.
      refine (disp_adj_equiv_to_left_adj_data ,, _).
      split.
      - exact disp_adj_equiv_to_left_adjoint_axioms.
      - exact disp_adj_equiv_to_left_equivalence_axioms.
    Defined.

    Definition disp_adj_equiv_to_adj_equiv
      : adjoint_equivalence (pr1 hx) (pr1 hy)
      := (pr11 e ,, disp_adj_equiv_to_left_adj_equiv).

    Definition disp_adj_equiv_to_adj_equiv_comm
      : invertible_2cell
          (pr12 hx)
          (disp_adj_equiv_to_adj_equiv · pr12 hy)
      := comp_of_invertible_2cell
           (rinvunitor_invertible_2cell _)
           (pr221 e).

    Definition disp_adj_equiv_to_adj_equiv_pair
      : ∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
        invertible_2cell
          (pr12 hx)
          (e · pr12 hy)
      := disp_adj_equiv_to_adj_equiv
         ,,
         disp_adj_equiv_to_adj_equiv_comm.
  End DispAdjEquivToAdjEquiv.

  Definition adj_equiv_to_disp_adj_equiv_to_adj_equiv
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
             {x : B}
             {hx hy : cod_sfibs x}
             (z : ∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
                  invertible_2cell (pr12 hx) (pr1 e · pr12 hy))
    : disp_adj_equiv_to_adj_equiv_pair
        (adj_equiv_to_disp_adj_equiv
           HB_2_0 HB_2_1 (pr1 z) (pr2 z))
      =
      z.
  Proof.
    use total2_paths_f.
    - simpl.
      use subtypePath.
      {
        intro ; apply isaprop_left_adjoint_equivalence.
        exact HB_2_1.
      }
      apply idpath.
    - use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      unfold invertible_2cell.
      rewrite pr1_transportf.
      unfold subtypePath.
      unfold adjoint_equivalence.
      etrans.
      {
        apply (@transportf_total2_paths_f
                 (pr1 hx --> pr1 hy)
                 left_adjoint_equivalence
                 (λ x, pr12 hx ==> x · pr12 hy)).
      }
      cbn.
      rewrite vassocr.
      rewrite rinvunitor_runitor.
      apply id2_left.
  Qed.

  Definition disp_adj_equiv_to_adj_equiv_to_disp_adj_equiv
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
             {x : B}
             {hx hy : cod_sfibs x}
             (z : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    hx hy)
    : adj_equiv_to_disp_adj_equiv
        HB_2_0 HB_2_1
        (disp_adj_equiv_to_adj_equiv z)
        (disp_adj_equiv_to_adj_equiv_comm z)
      =
      z.
  Proof.
    use subtypePath.
    {
      intro.
      use isaprop_disp_left_adjoint_equivalence.
      - exact HB_2_1.
      - apply cod_sfibs_disp_univalent_2_1.
        exact HB_2_1.
    }
    cbn.
    refine (maponpaths (λ z, _ ,, z) _).
    use pathsdirprod.
    - apply isaprop_mor_preserves_cartesian.
    - use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      cbn.
      rewrite vassocr.
      rewrite runitor_rinvunitor.
      apply id2_left.
  Qed.

  Definition adj_equiv_weq_disp_adj_equiv
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
             {x : B}
             (hx hy : cod_sfibs x)
    : (∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
       invertible_2cell (pr12 hx) (e · pr12 hy))
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) hx hy.
  Proof.
    use make_weq.
    - exact (λ e, adj_equiv_to_disp_adj_equiv HB_2_0 HB_2_1 (pr1 e) (pr2 e)).
    - use gradth.
      + exact disp_adj_equiv_to_adj_equiv_pair.
      + exact (adj_equiv_to_disp_adj_equiv_to_adj_equiv HB_2_0 HB_2_1).
      + exact (disp_adj_equiv_to_adj_equiv_to_disp_adj_equiv HB_2_0 HB_2_1).
  Defined.

  (**
   5. Global univalence
   *)
  Definition weq_fam_global
             (HB_2_1 : is_univalent_2_1 B)
             {x : B}
             (hx hy : ∑ (y : B) (f : y --> x ), internal_sfib f)
             (p : pr1 hx = pr1 hy)
    : (transportf
         (λ x1 : B, ∑ f : B ⟦ x1, x ⟧, internal_sfib f)
         p
         (pr2 hx)
       =
       pr2 hy)
      ≃
      invertible_2cell (pr12 hx) (idtoiso_2_0 _ _ p · pr12 hy).
  Proof.
    induction hx as [ hx₁ [ hx₂ hx₃ ] ].
    induction hy as [ hy₁ [ hy₂ hy₃ ] ].
    cbn in *.
    induction p ; cbn.
    refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
    - apply isaprop_internal_sfib.
      exact HB_2_1.
    - exact (cod_1cell_path_help hx₂ hy₂
             ∘ make_weq
                 _
                 (HB_2_1 _ _ _ _))%weq.
  Defined.

  Definition cod_sfibs_disp_univalent_2_0
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_0 : is_univalent_2_0 B)
    : disp_univalent_2_0 cod_sfibs.
  Proof.
    intros x y p hx hy.
    induction p.
    use weqhomot.
    - exact (adj_equiv_weq_disp_adj_equiv HB_2_0 HB_2_1 hx hy
             ∘ weqtotal2
                 (make_weq _ (HB_2_0 _ _))
                 (weq_fam_global HB_2_1 hx hy)
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use isaprop_disp_left_adjoint_equivalence.
        - exact HB_2_1.
        - apply cod_sfibs_disp_univalent_2_1.
          exact HB_2_1.
      }
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      use pathsdirprod.
      + apply isaprop_mor_preserves_cartesian.
      + use subtypePath.
        {
          intro ; apply isaprop_is_invertible_2cell.
        }
        cbn.
        rewrite id2_left.
        apply idpath.
  Qed.
End CodomainStreetFibs.
