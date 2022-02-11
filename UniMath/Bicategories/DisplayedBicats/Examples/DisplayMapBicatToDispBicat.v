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
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.InternalStreetOpFibration.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.Limits.Pullbacks.

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

  Definition make_disp_map_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : f ==> g}
             (Hγ : is_invertible_2cell γ)
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (hγ : hf ==>[ γ ] hg)
             (Hhγ : is_invertible_2cell (pr1 hγ))
    : disp_invertible_2cell (make_invertible_2cell Hγ) hf hg.
  Proof.
    refine (hγ ,, _).
    use is_invertible_to_is_disp_invertible.
    exact Hhγ.
  Defined.

  Definition disp_map_inv_2cell_to_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             {γ : invertible_2cell f g}
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (α : ∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ))
    : disp_invertible_2cell γ hf hg.
  Proof.
    use make_disp_map_disp_invertible_2cell.
    - exact (pr1 α).
    - exact (pr2 α).
  Defined.

  Definition disp_map_disp_invertible_2cell_to_inv_2cell
             {x y : B}
             {f g : x --> y}
             {γ : invertible_2cell f g}
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (α : disp_invertible_2cell γ hf hg)
    : ∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ).
  Proof.
    refine (pr1 α ,, _).
    use is_disp_invertible_to_is_invertible.
    - exact (pr2 γ).
    - exact (pr2 α).
  Defined.

  Definition disp_map_inv_2cell_weq_disp_invertible_2cell
             {x y : B}
             {f g : x --> y}
             (γ : invertible_2cell f g)
             {hx : disp_map_bicat_to_disp_bicat x}
             {hy : disp_map_bicat_to_disp_bicat y}
             (hf : hx -->[ f ] hy)
             (hg : hx -->[ g ] hy)
    : (∑ (hγ : hf ==>[ γ ] hg), is_invertible_2cell (pr1 hγ))
      ≃
      disp_invertible_2cell γ hf hg.
  Proof.
    use make_weq.
    - exact disp_map_inv_2cell_to_disp_invertible_2cell.
    - use gradth.
      + exact disp_map_disp_invertible_2cell_to_inv_2cell.
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
        {hx : disp_map_bicat_to_disp_bicat x}
        {hy : disp_map_bicat_to_disp_bicat y}
        (hf : hx -->[ f ] hy)
        (hg : hx -->[ g ] hy)
    : (∑ (γe : invertible_2cell (pr1 hf) (pr1 hg)),
       pr122 hf • (γe ▹ pr12 hy) = (pr12 hx ◃ γ) • pr122 hg)
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
        (HD : arrow_subbicat_props D)
        {x y : B}
        {f : x --> y}
        {hx : disp_map_bicat_to_disp_bicat x}
        {hy : disp_map_bicat_to_disp_bicat y}
        (hf hg : hx -->[ f] hy)
        (p : pr1 hf = pr1 hg)
    : (transportf
         (λ z,
          pred_mor D (pr12 hx) (pr12 hy) z
          ×
          invertible_2cell (pr12 hx · f) (z · pr12 hy))
         p
         (pr2 hf)
       =
       pr2 hg)
      ≃
      (pr122 hf • (idtoiso_2_1 (pr1 hf) (pr1 hg) p ▹ pr12 hy)
       =
       (pr12 hx ◃ id₂ f) • pr122 hg).
  Proof.
    induction hf as [ hf₁ hf₂ ].
    induction hg as [ hg₁ hg₂ ].
    cbn in *.
    induction p ; cbn.
    use weqimplimpl.
    - intro p.
      induction p.
      rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right.
      apply idpath.
    - intro p.
      use pathsdirprod.
      + apply (pr2 HD).
      + rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right in p.
        use subtypePath.
        {
          intro ; apply isaprop_is_invertible_2cell.
        }
        exact p.
    - use isasetdirprod.
      + apply isasetaprop.
        apply (pr2 HD).
      + apply isaset_invertible_2cell.
    - apply cellset_property.
  Qed.

  Definition disp_map_disp_univalent_2_1
             (HD : arrow_subbicat_props D)
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_1 disp_map_bicat_to_disp_bicat.
  Proof.
    intros x y f g p hx hy hf hg.
    induction p.
    use weqhomot.
    - refine (disp_map_inv_2cell_weq_disp_invertible_2cell _ _ _
             ∘ refactor_weq _ _ _
             ∘ weqtotal2
                 (make_weq _ (HB_2_1 _ _ _ _))
                 _
             ∘ total2_paths_equiv _ _ _)%weq.
      exact (weq_on_fam HD _ _).
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
    Context (HB : is_univalent_2 B)
            {x : B}
            {hx hy : disp_map_bicat_to_disp_bicat x}
            (e : adjoint_equivalence (pr1 hx) (pr1 hy))
            (com : invertible_2cell (pr12 hx) (e · pr12 hy)).

    Local Definition adj_equiv_to_disp_adj_equiv_left_adj
      : hx -->[ internal_adjoint_equivalence_identity x] hy.
    Proof.
      use make_disp_map_bicat_mor.
      - exact e.
      - apply (arrow_subbicat_contains_equiv_over_id HB D).
        + exact e.
        + exact com.
      - exact (comp_of_invertible_2cell
                 (runitor_invertible_2cell _)
                 com).
    Defined.

    Local Notation "'L'" := adj_equiv_to_disp_adj_equiv_left_adj.

    Local Definition adj_equiv_to_disp_adj_equiv_right_adj
      : hy -->[ internal_adjoint_equivalence_identity x] hx.
    Proof.
      use make_disp_map_bicat_mor.
      - exact (left_adjoint_right_adjoint e).
      - pose (einv := inv_adjequiv e).
        apply (arrow_subbicat_contains_equiv_over_id
                 HB D).
        + exact (pr2 einv).
        + exact (comp_of_invertible_2cell
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
      : pr122 (id_disp hx) • (left_adjoint_unit e ▹ pr12 hx)
        =
        (pr12 hx ◃ left_adjoint_unit (internal_adjoint_equivalence_identity x))
        • pr122 (L ;; R)%mor_disp.
    Proof.
      cbn.
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
      use make_disp_map_bicat_cell.
      - exact (left_adjoint_unit e).
      - exact adj_equiv_to_disp_adj_equiv_unit_coh.
    Defined.

    Local Notation "'η'" := adj_equiv_to_disp_adj_equiv_unit.

    Local Lemma adj_equiv_to_disp_adj_equiv_counit_coh
      : pr122 (R ;; L)%mor_disp
        • (left_adjoint_counit e ▹ pr12 hy)
        =
        (pr12 hy ◃ left_adjoint_counit (internal_adjoint_equivalence_identity x))
        • pr122 (id_disp hy).
    Proof.
      cbn.
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
      use make_disp_map_bicat_cell.
      - exact (left_adjoint_counit e).
      - exact adj_equiv_to_disp_adj_equiv_counit_coh.
    Defined.

    Local Notation "'ε'" := adj_equiv_to_disp_adj_equiv_counit.

    Local Definition adj_equiv_to_disp_adj_equiv_data
      : @disp_left_adjoint_data
          B
          disp_map_bicat_to_disp_bicat
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
      split.
      - simpl.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        rewrite transportb_disp_map_bicat_cell.
        cbn.
        apply (pr2 e).
      - simpl.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        rewrite transportb_disp_map_bicat_cell.
        cbn.
        apply (pr2 e).
    Qed.

    Local Definition adj_equiv_to_disp_adj_equiv_equivalence_axioms
      : disp_left_equivalence_axioms
          (internal_adjoint_equivalence_identity x)
          adj_equiv_to_disp_adj_equiv_data.
    Proof.
      split.
      - apply is_invertible_to_is_disp_invertible.
        apply (pr2 e).
      - apply is_invertible_to_is_disp_invertible.
        apply (pr2 e).
    Defined.

    Definition disp_map_bicat_adj_equiv_to_disp_adj_equiv
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
            {hx hy : disp_map_bicat_to_disp_bicat x}
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
        rewrite transportb_disp_map_bicat_cell in p.
        exact p.
      - pose (maponpaths pr1 (pr2 (pr122 e))) as p.
        cbn in p.
        rewrite transportb_disp_map_bicat_cell in p.
        exact p.
    Qed.

    Local Definition disp_adj_equiv_to_left_equivalence_axioms
      : left_equivalence_axioms disp_adj_equiv_to_left_adj_data.
    Proof.
      split.
      - exact (is_disp_invertible_to_is_invertible _ _ (pr1 (pr222 e))).
      - exact (is_disp_invertible_to_is_invertible _ _ (pr2 (pr222 e))).
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

    Definition disp_map_bicat_disp_adj_equiv_to_adj_equiv_pair
      : ∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
        invertible_2cell
          (pr12 hx)
          (e · pr12 hy)
      := disp_adj_equiv_to_adj_equiv
         ,,
         disp_adj_equiv_to_adj_equiv_comm.
  End DispAdjEquivToAdjEquiv.

  Definition adj_equiv_to_disp_adj_equiv_to_adj_equiv
             (HB : is_univalent_2 B)
             {x : B}
             {hx hy : disp_map_bicat_to_disp_bicat x}
             (z : ∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
                  invertible_2cell (pr12 hx) (pr1 e · pr12 hy))
    : disp_map_bicat_disp_adj_equiv_to_adj_equiv_pair
        (disp_map_bicat_adj_equiv_to_disp_adj_equiv
           HB (pr1 z) (pr2 z))
      =
      z.
  Proof.
    use total2_paths_f.
    - simpl.
      use subtypePath.
      {
        intro ; apply isaprop_left_adjoint_equivalence.
        exact (pr2 HB).
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
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
             {x : B}
             {hx hy : disp_map_bicat_to_disp_bicat x}
             (z : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    hx hy)
    : disp_map_bicat_adj_equiv_to_disp_adj_equiv
        HB
        (disp_adj_equiv_to_adj_equiv z)
        (disp_adj_equiv_to_adj_equiv_comm z)
      =
      z.
  Proof.
    use subtypePath.
    {
      intro.
      use isaprop_disp_left_adjoint_equivalence.
      - exact (pr2 HB).
      - apply disp_map_disp_univalent_2_1.
        + exact HD.
        + exact (pr2 HB).
    }
    cbn.
    refine (maponpaths (λ z, _ ,, z) _).
    use pathsdirprod.
    - apply HD.
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
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
             {x : B}
             (hx hy : disp_map_bicat_to_disp_bicat x)
    : (∑ (e : adjoint_equivalence (pr1 hx) (pr1 hy)),
       invertible_2cell (pr12 hx) (e · pr12 hy))
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) hx hy.
  Proof.
    use make_weq.
    - exact (λ e, disp_map_bicat_adj_equiv_to_disp_adj_equiv HB (pr1 e) (pr2 e)).
    - use gradth.
      + exact disp_map_bicat_disp_adj_equiv_to_adj_equiv_pair.
      + exact (adj_equiv_to_disp_adj_equiv_to_adj_equiv HB).
      + exact (disp_adj_equiv_to_adj_equiv_to_disp_adj_equiv HB HD).
  Defined.

  (**
   5. Global univalence
   *)
  Definition weq_fam_global
             (HB_2_1 : is_univalent_2_1 B)
             (HD : arrow_subbicat_props D)
             {x : B}
             (hx hy : disp_map_bicat_to_disp_bicat x)
             (p : pr1 hx = pr1 hy)
    : (transportf
         (λ z, ∑ (h : z --> x), pred_ob D h)
         p
         (pr2 hx)
       =
       pr2 hy)
      ≃
      invertible_2cell
        (pr12 hx)
        (pr1 (idtoiso_2_0 (pr1 hx) (pr1 hy) p) · pr12 hy).
  Proof.
    induction hx as [ hx₁ [ hx₂ hx₃ ] ].
    induction hy as [ hy₁ [ hy₂ hy₃ ] ].
    cbn in *.
    induction p ; cbn.
    refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
    - apply HD.
    - exact (cod_1cell_path_help hx₂ hy₂
             ∘ make_weq
                 _
                 (HB_2_1 _ _ _ _))%weq.
  Defined.

  Definition disp_map_bicat_disp_univalent_2_0
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
    : disp_univalent_2_0 disp_map_bicat_to_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x hx hy.
    use weqhomot.
    - exact (adj_equiv_weq_disp_adj_equiv HB HD hx hy
             ∘ weqtotal2
                 (make_weq _ (pr1 HB _ _))
                 (weq_fam_global (pr2 HB) HD _ _)
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use isaprop_disp_left_adjoint_equivalence.
        - exact (pr2 HB).
        - apply disp_map_disp_univalent_2_1.
          + exact HD.
          + exact (pr2 HB).
      }
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      use pathsdirprod.
      + apply HD.
      + use subtypePath.
        {
          intro ; apply isaprop_is_invertible_2cell.
        }
        cbn.
        rewrite id2_left.
        apply idpath.
  Qed.

  Definition disp_map_bicat_disp_univalent_2
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
    : disp_univalent_2 disp_map_bicat_to_disp_bicat.
  Proof.
    split.
    - apply disp_map_bicat_disp_univalent_2_0.
      + exact HB.
      + exact HD.
    - apply disp_map_disp_univalent_2_1.
      + exact HD.
      + exact (pr2 HB).
  Defined.
End ArrowSubBicatToDispBicat.

Definition cod_sfibs
           (B : bicat)
  : disp_bicat B
  := disp_map_bicat_to_disp_bicat (sfib_subbicat B).

Definition cod_sopfibs
           (B : bicat)
  : disp_bicat B
  := disp_map_bicat_to_disp_bicat (sopfib_subbicat B).
