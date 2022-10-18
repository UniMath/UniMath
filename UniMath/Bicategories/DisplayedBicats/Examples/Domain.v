Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section DomainArrow.
  Variable (B : bicat)
           (a : B).

  Definition dom_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    use tpair.
    - exact (λ c, c --> a).
    - exact (λ c₁ c₂ t₁ t₂ s, t₁ ==> s · t₂).
  Defined.

  Definition dom_disp_cat_id_comp
    : disp_cat_id_comp B dom_disp_cat_ob_mor.
  Proof.
    use tpair.
    - exact (λ c t, linvunitor _).
    - exact (λ c₁ c₂ c₃ s₁ s₂ t₁ t₂ t₃ α β, α • (s₁ ◃ β) • lassociator _ _ _).
  Defined.

  Definition dom_disp_cat_data
    : disp_cat_data B.
  Proof.
    use tpair.
    - exact dom_disp_cat_ob_mor.
    - exact dom_disp_cat_id_comp.
  Defined.

  Definition dom_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    use tpair.
    - exact dom_disp_cat_data.
    - exact (λ c₁ c₂ s₁ s₂ α t₁ t₂ ss₁ ss₂, ss₁ • (α ▹ t₂) = ss₂).
  Defined.

  Definition dom_disp_prebicat_ops
    : disp_prebicat_ops dom_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split ; cbn.
    - intros.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intros.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ;cbn.
      rewrite <- vcomp_lunitor.
      rewrite <- lunitor_triangle.
      apply idpath.
    - intros.
      rewrite !vassocl.
      refine (_ @ id2_right _).
      apply maponpaths.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
    - intros.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      rewrite <- lunitor_triangle.
      apply idpath.
    - intros.
      rewrite !vassocl.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      apply id2_right.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply lassociator_lassociator.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? α β.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite α.
      rewrite β.
      apply idpath.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? α.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      rewrite α.
      apply idpath.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? α.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      rewrite α.
      apply idpath.
  Qed.

  Definition dom_disp_prebicat_data
    : disp_prebicat_data B.
  Proof.
    use tpair.
    - exact dom_disp_prebicat_1_id_comp_cells.
    - exact dom_disp_prebicat_ops.
  Defined.

  Definition dom_disp_prebicat_laws
    : disp_prebicat_laws dom_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply B.
  Qed.

  Definition dom_disp_prebicat
    : disp_prebicat B.
  Proof.
    use tpair.
    - exact dom_disp_prebicat_data.
    - exact dom_disp_prebicat_laws.
  Defined.

  Definition dom_disp_bicat
    : disp_bicat B.
  Proof.
    use tpair.
    - exact dom_disp_prebicat.
    - intro ; intros.
      apply isasetaprop.
      apply B.
  Defined.

  Definition dom_disp_2cells_isaprop
    : disp_2cells_isaprop dom_disp_bicat.
  Proof.
    intro ; intros.
    apply B.
  Qed.

  Definition dom_disp_locally_sym
    : disp_locally_sym dom_disp_bicat.
  Proof.
    intros c₁ c₂ s₁ s₂ α t₁ t₂ φ₁ φ₂ p ; cbn in *.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    exact (!p).
  Qed.

  Definition dom_disp_locally_groupoid
    : disp_locally_groupoid dom_disp_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - exact dom_disp_locally_sym.
    - exact dom_disp_2cells_isaprop.
  Defined.

  Definition dom_disp_univalent_2_1
    : disp_univalent_2_1 dom_disp_bicat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros c₁ c₂ s t₁ t₂ φ₁ φ₂.
    use isweqimplimpl.
    - intros α.
      pose (pr1 α) as p ; cbn in p.
      rewrite id2_rwhisker in p.
      rewrite id2_right in p.
      exact p.
    - apply B.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
      + intros.
        apply B.
  Qed.

  Definition dom_invertible_2cell_is_left_disp_adj_equiv
             {c : B}
             {t₁ t₂ : dom_disp_bicat c}
             (f : t₁ -->[ id₁ _ ] t₂)
             (Hf : is_invertible_2cell f)
    : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity c) f.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
    - exact (linvunitor _ • Hf^-1 • linvunitor _).
    - abstract
        (cbn ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite !lwhisker_hcomp ;
         rewrite triangle_l_inv ;
         rewrite <- !lwhisker_hcomp, <- rwhisker_hcomp ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         use vcomp_move_L_Mp ; [ is_iso | ] ; cbn ;
         rewrite lwhisker_hcomp ;
         rewrite <- linvunitor_natural ;
         apply maponpaths ;
         rewrite linvunitor_assoc ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite rwhisker_hcomp ;
         rewrite <- triangle_l_inv ;
         rewrite <- lwhisker_hcomp ;
         rewrite !vassocl ;
         rewrite lassociator_rassociator ;
         apply id2_right).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         refine (_ @ id2_right _) ;
         apply maponpaths ;
         do 2 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn ;
         rewrite id2_right ;
         rewrite <- vcomp_lunitor ;
         rewrite lunitor_triangle ;
         apply idpath).
    - apply dom_disp_2cells_isaprop.
    - apply dom_disp_2cells_isaprop.
    - apply dom_disp_locally_groupoid.
    - apply dom_disp_locally_groupoid.
  Defined.

  Definition dom_invertible_2cell_to_disp_adj_equiv
             {c : B}
             {t₁ t₂ : dom_disp_bicat c}
    : invertible_2cell t₁ t₂
      →
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) t₁ t₂.
  Proof.
    intros α.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _)))).
    - exact (α • linvunitor _).
    - exact (α^-1 • linvunitor _).
    - abstract
        (cbn ;
         rewrite linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite vcomp_rinv ;
         rewrite id2_left ;
         rewrite lwhisker_hcomp ;
         rewrite triangle_l_inv ;
         rewrite <- rwhisker_hcomp ;
         apply maponpaths ;
         apply lunitor_V_id_is_left_unit_V_id).
    - abstract
        (cbn ;
         rewrite linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         rewrite !vassocl ;
         refine (_ @ id2_right _) ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite vcomp_linv ;
         rewrite id2_left ;
         rewrite lwhisker_hcomp ;
         rewrite triangle_l_inv ;
         rewrite <- rwhisker_hcomp ;
         rewrite rwhisker_vcomp ;
         rewrite lunitor_runitor_identity ;
         rewrite rinvunitor_runitor ;
         apply id2_rwhisker).
    - apply dom_disp_2cells_isaprop.
    - apply dom_disp_2cells_isaprop.
    - apply dom_disp_locally_groupoid.
    - apply dom_disp_locally_groupoid.
  Defined.

  Definition dom_disp_adj_equiv_to_invertible_2cell
             {c : B}
             {t₁ t₂ : dom_disp_bicat c}
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) t₁ t₂
      →
      invertible_2cell t₁ t₂.
  Proof.
    intros e.
    use make_invertible_2cell.
    - exact (pr1 e • lunitor _).
    - use make_is_invertible_2cell.
      + exact (pr112 e • lunitor _).
      + abstract
          (pose (pr1 (pr212 e)) as m ;
           cbn in m ;
           rewrite !vassocl in m ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite <- vcomp_lunitor ;
           rewrite <- lunitor_triangle ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite !vassocl ;
           exact (!m)).
      + abstract
          (pose (pr2 (pr212 e)) as m ;
           cbn in m ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite <- vcomp_lunitor ;
           rewrite <- lunitor_triangle ;
           rewrite !vassocr ;
           exact m).
  Defined.

  Definition dom_invertible_2cell_weq_disp_adj_equiv
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             (t₁ t₂ : dom_disp_bicat c)
    : invertible_2cell t₁ t₂
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) t₁ t₂.
  Proof.
    use make_weq.
    - exact dom_invertible_2cell_to_disp_adj_equiv.
    - use isweq_iso.
      + exact dom_disp_adj_equiv_to_invertible_2cell.
      + abstract
          (intros α ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite vassocl ;
           rewrite linvunitor_lunitor ;
           apply id2_right).
      + abstract
          (intros α ;
           use subtypePath ;
           [ intro ;
             use isaprop_disp_left_adjoint_equivalence ;
             [ exact HB_2_1
             |  apply dom_disp_univalent_2_1 ]
           | ] ;
           cbn ;
           rewrite vassocl ;
           rewrite lunitor_linvunitor ;
           apply id2_right).
  Defined.

  Definition dom_disp_univalent_2_0
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_0 dom_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros c t₁ t₂.
    use weqhomot.
    - exact (dom_invertible_2cell_weq_disp_adj_equiv HB_2_1 t₁ t₂
             ∘ make_weq _ (HB_2_1 _ _ _ _))%weq.
    - abstract
        (intros p ;
         cbn in p ;
         induction p ;
         use subtypePath ;
           [ intro ;
             use isaprop_disp_left_adjoint_equivalence ;
             [ exact HB_2_1
             |  apply dom_disp_univalent_2_1 ]
           | ] ;
           apply id2_left).
  Qed.
End DomainArrow.
