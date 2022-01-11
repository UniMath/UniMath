(*****************************************************************************

 Every display map bicategory gives rise to a displayed bicategory

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.InternalStreetOpFibration.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

Section ArrowSubBicatToDispBicat.
  Context {B : bicat}
          (D : arrow_subbicat B).

  Definition disp_map_bicat_ob
             (y : B)
    : UU
    := ∑ (x : B) (h : x --> y), pred_ob D h.

  Definition make_disp_map_bicat_ob
             {x y : B}
             (h : x --> y)
             (H : pred_ob D h)
    : disp_map_bicat_ob y
    := (x ,, h ,, H).

  Definition disp_map_bicat_mor
             {y₁ y₂ : B}
             (h₁ : disp_map_bicat_ob y₁)
             (h₂ : disp_map_bicat_ob y₂)
             (g : y₁ --> y₂)
    : UU
    := ∑ (f : pr1 h₁ --> pr1 h₂),
       pred_mor D (pr12 h₁) (pr12 h₂) f
       ×
       invertible_2cell (pr12 h₁ · g) (f · pr12 h₂).

  Definition make_disp_map_bicat_mor
             {y₁ y₂ : B}
             {h₁ : disp_map_bicat_ob y₁}
             {h₂ : disp_map_bicat_ob y₂}
             (g : y₁ --> y₂)
             (f : pr1 h₁ --> pr1 h₂)
             (H : pred_mor D (pr12 h₁) (pr12 h₂) f)
             (γ : invertible_2cell (pr12 h₁ · g) (f · pr12 h₂))
    : disp_map_bicat_mor h₁ h₂ g
    := (f ,, H ,, γ).

  Definition disp_map_bicat_to_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_bicat_ob.
    - exact (λ _ _, disp_map_bicat_mor).
  Defined.

  Definition disp_map_bicat_to_disp_cat_id_comp
    : disp_cat_id_comp B disp_map_bicat_to_disp_cat_ob_mor.
  Proof.
    split.
    - intros y h.
      use make_disp_map_bicat_mor.
      + exact (id₁ _).
      + apply id_pred_mor.
      + exact (comp_of_invertible_2cell
                 (runitor_invertible_2cell _)
                 (linvunitor_invertible_2cell _)).
    - intros y₁ y₂ y₃ g₁ g₂ h₁ h₂ h₃ f₁ f₂.
      use make_disp_map_bicat_mor.
      + exact (pr1 f₁ · pr1 f₂).
      + exact (comp_pred_mor
                 D
                 (pr12 f₁) (pr12 f₂)).
      + exact (comp_of_invertible_2cell
                 (lassociator_invertible_2cell _ _ _)
                 (comp_of_invertible_2cell
                    (rwhisker_of_invertible_2cell _ (pr22 f₁))
                    (comp_of_invertible_2cell
                       (rassociator_invertible_2cell _ _ _)
                       (comp_of_invertible_2cell
                          (lwhisker_of_invertible_2cell _ (pr22 f₂))
                          (lassociator_invertible_2cell _ _ _))))).
  Defined.

  Definition disp_map_bicat_to_disp_cat_data
    : disp_cat_data B
    := (disp_map_bicat_to_disp_cat_ob_mor ,, disp_map_bicat_to_disp_cat_id_comp).

  Definition disp_map_bicat_cell
             {y₁ y₂ : B}
             {g₁ g₂ : y₁ --> y₂}
             {h₁ : disp_map_bicat_ob y₁}
             {h₂ : disp_map_bicat_ob y₂}
             (f₁ : disp_map_bicat_mor h₁ h₂ g₁)
             (f₂ : disp_map_bicat_mor h₁ h₂ g₂)
             (β : g₁ ==> g₂)
    : UU
    := ∑ (α : pr1 f₁ ==> pr1 f₂),
       pr122 f₁ • (α ▹ _)
       =
       (_ ◃ β) • pr122 f₂.

  Definition make_disp_map_bicat_cell
             {y₁ y₂ : B}
             {g₁ g₂ : y₁ --> y₂}
             {β : g₁ ==> g₂}
             {h₁ : disp_map_bicat_ob y₁}
             {h₂ : disp_map_bicat_ob y₂}
             {f₁ : disp_map_bicat_mor h₁ h₂ g₁}
             {f₂ : disp_map_bicat_mor h₁ h₂ g₂}
             (α : pr1 f₁ ==> pr1 f₂)
             (p : pr122 f₁ • (α ▹ _)
                  =
                  (_ ◃ β) • pr122 f₂)
    : disp_map_bicat_cell f₁ f₂ β
    := (α ,, p).

  Definition disp_map_bicat_to_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    refine (disp_map_bicat_to_disp_cat_data ,, _).
    exact (λ y₁ y₂ g₁ g₂ β h₁ h₂ f₁ f₂, disp_map_bicat_cell f₁ f₂ β).
  Defined.

  Definition disp_map_bicat_to_disp_prebicat_ops
    : disp_prebicat_ops disp_map_bicat_to_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros x y f hx hy hf ; cbn in *.
      use make_disp_map_bicat_cell.
      + exact (id2 _).
      + abstract
          (rewrite id2_rwhisker, lwhisker_id2 ;
           rewrite id2_left, id2_right ;
           apply idpath).
    - intros x y f hx hy hf ; cbn in *.
      use make_disp_map_bicat_cell.
      + exact (lunitor _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (runitor _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (linvunitor _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (rinvunitor _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (rassociator _ _ _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (lassociator _ _ _).
      + abstract
          (cbn ;
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
      use make_disp_map_bicat_cell.
      + exact (pr1 hα • pr1 hβ).
      + abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite (pr2 hα) ;
           rewrite !vassocl ;
           rewrite (pr2 hβ) ;
           apply idpath).
    - intros x₁ x₂ x₃ f₁ f₂ g α hx₁ hx₂ hx₃ hf₁ hf₂ hg hα ; cbn in *.
      use make_disp_map_bicat_cell.
      + exact (_ ◃ pr1 hα).
      + abstract
          (cbn ;
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
           exact (pr2 hα)).
    - intros x₁ x₂ x₃ f₁ f₂ g α hx₁ hx₂ hx₃ hf₁ hf₂ hg hα ; cbn in *.
      use make_disp_map_bicat_cell.
      + exact (pr1 hα ▹ _).
      + abstract
          (cbn ;
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
           exact (pr2 hα)).
  Defined.

  Definition transportf_disp_map_bicat_cell
             {y₁ y₂ : B}
             {g₁ g₂ : y₁ --> y₂}
             {β₁ β₂ : g₁ ==> g₂}
             (p : β₁ = β₂)
             {h₁ : disp_map_bicat_ob y₁}
             {h₂ : disp_map_bicat_ob y₂}
             {f₁ : disp_map_bicat_mor h₁ h₂ g₁}
             {f₂ : disp_map_bicat_mor h₁ h₂ g₂}
             (γ : disp_map_bicat_cell f₁ f₂ β₁)
    : pr1 (transportf
             (λ α, disp_map_bicat_cell f₁ f₂ α)
             p
             γ)
      =
      pr1 γ.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition transportb_disp_map_bicat_cell
             {y₁ y₂ : B}
             {g₁ g₂ : y₁ --> y₂}
             {β₁ β₂ : g₁ ==> g₂}
             (p : β₁ = β₂)
             {h₁ : disp_map_bicat_ob y₁}
             {h₂ : disp_map_bicat_ob y₂}
             {f₁ : disp_map_bicat_mor h₁ h₂ g₁}
             {f₂ : disp_map_bicat_mor h₁ h₂ g₂}
             (γ : disp_map_bicat_cell f₁ f₂ β₂)
    : pr1 (transportb
             (λ α, disp_map_bicat_cell f₁ f₂ α)
             p
             γ)
      =
      pr1 γ.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition disp_map_bicat_to_disp_prebicat_data
    : disp_prebicat_data B
    := (disp_map_bicat_to_disp_prebicat_1_id_comp_cells
        ,,
        disp_map_bicat_to_disp_prebicat_ops).

  Definition disp_map_bicat_to_disp_prebicat_laws
    : disp_prebicat_laws disp_map_bicat_to_disp_prebicat_data.
  Proof.
    repeat split
    ; intro ; intros
    ; cbn in *
    ; (use subtypePath ; [ intro ; apply cellset_property | ]) ; cbn
    ; rewrite transportb_disp_map_bicat_cell ; cbn.
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

  Definition disp_map_bicat_to_disp_prebicat
    : disp_prebicat B
    := (disp_map_bicat_to_disp_prebicat_data
        ,,
        disp_map_bicat_to_disp_prebicat_laws).

  Definition disp_map_bicat_to_disp_bicat
    : disp_bicat B.
  Proof.
    refine (disp_map_bicat_to_disp_prebicat ,, _).
    intro ; intros.
    use isaset_total2.
    - apply cellset_property.
    - intro.
      apply isasetaprop.
      apply cellset_property.
  Defined.

  (** Displayed invertible 2-cells *)
  Definition is_invertible_to_is_disp_invertible
             {x y : B}
             {f g : x --> y}
             {α : f ==> g}
             (Hα : is_invertible_2cell α)
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (αα : hf ==>[ α ] hg)
             (Hαα : is_invertible_2cell (pr1 αα))
    : is_disp_invertible_2cell Hα αα.
  Proof.
    simple refine (_ ,, _ ,, _).
    - use make_disp_map_bicat_cell.
      + exact (Hαα^-1).
      + abstract
          (use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite !vassocl ;
           rewrite (pr2 αα) ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           apply idpath).
    - abstract
        (use subtypePath ; [ intro ; apply cellset_property | ] ; cbn ;
         rewrite transportb_disp_map_bicat_cell ; cbn ;
         apply vcomp_rinv).
    - abstract
        (use subtypePath ; [ intro ; apply cellset_property | ] ; cbn ;
         rewrite transportb_disp_map_bicat_cell ; cbn ;
         apply vcomp_linv).
  Defined.

  Definition is_disp_invertible_to_is_invertible
             {x y : B}
             {f g : x --> y}
             {α : f ==> g}
             (Hα : is_invertible_2cell α)
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (αα : hf ==>[ α ] hg)
             (Hαα : is_disp_invertible_2cell Hα αα)
    : is_invertible_2cell (pr1 αα).
  Proof.
    use make_is_invertible_2cell.
    - exact (pr11 Hαα).
    - abstract
        (exact (maponpaths pr1 (pr12 Hαα) @ transportb_disp_map_bicat_cell _ _)).
    - abstract
        (exact (maponpaths pr1 (pr22 Hαα) @ transportb_disp_map_bicat_cell _ _)).
  Defined.
End ArrowSubBicatToDispBicat.
