Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.

Open Scope cat.

Section Algebra.
  Context `{C : bicat}.
  Variable (F : psfunctor C C).

  Definition alg_disp_cat : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ X, C⟦F X,X⟧).
    - intros X Y f g h.
      exact (f · h ==> #F h · g).
  Defined.

  Definition alg_disp_cat_id_comp : disp_cat_id_comp C alg_disp_cat.
  Proof.
    split ; cbn.
    - intros X f.
      exact (runitor f • linvunitor f • (laxfunctor_id F X ▹ f)).
    - intros X Y Z f g hX hY hZ α β ; cbn in *.
      exact ((lassociator hX f g)
               • (α ▹ g)
               • rassociator (#F f) hY g
               • (#F f ◃ β)
               • lassociator (#F f) (#F g) hZ
               • (laxfunctor_comp F f g ▹ hZ)).
  Defined.

  Definition alg_disp_cat_2cell : disp_2cell_struct alg_disp_cat.
  Proof.
    intros X Y f g α hX hY αf αg ; cbn in *.
    exact ((hX ◃ α) • αg = αf • (##F α ▹ hY)).
  Defined.

  Definition disp_alg_prebicat_1 : disp_prebicat_1_id_comp_cells C.
  Proof.
    use tpair.
    - use tpair.
      + exact alg_disp_cat.
      + exact alg_disp_cat_id_comp.
    - exact alg_disp_cat_2cell.
  Defined.

  Definition disp_alg_lunitor
             {X Y : C}
             (f : C⟦X,Y⟧)
             (hX : C⟦F X,X⟧)
             (hY : C⟦F Y,Y⟧)
             (hf : hX · f ==> # F f · hY)
    : disp_2cells (lunitor f) (@id_disp C disp_alg_prebicat_1 X hX;; hf) hf.
  Proof.
    cbn. red.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    { is_iso.
      refine (laxfunctor_is_iso _ (lunitor f,,_)).
      is_iso.
    }
    cbn.
    rewrite laxfunctor_linvunitor.
    rewrite !vassocl.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    assert ((lunitor hX ▹ f) • hf • (linvunitor (# F f) ▹ hY)
            =
            rassociator _ _ _ • (_ ◃ hf) • lassociator _ _ _) as ->.
    {
      use vcomp_move_R_Mp.
      { is_iso. }
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite !vassocl.
      rewrite <- lunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite lunitor_natural.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      reflexivity.
    }
    rewrite !vassocl.
    rewrite rwhisker_rwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    rewrite vcomp_whisker.
    reflexivity.
  Qed.

  Definition disp_alg_runitor_help
             {X Y : C}
             (f : C⟦X,Y⟧)
             (hX : C⟦F X,X⟧)
             (hY : C⟦F Y,Y⟧)
             (hf : hX · f ==> # F f · hY)
    : (hX ◃ runitor f) • hf
      =
      (lassociator hX f (identity Y))
        • (hf ▹ identity Y)
        • rassociator (# F f) hY (identity Y)
        • (# F f ◃ runitor hY).
  Proof.
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    rewrite !vassocl.
    rewrite runitor_triangle.
    rewrite !vassocr.
    rewrite rinvunitor_triangle.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    reflexivity.
  Qed.

  Definition disp_alg_runitor
             {X Y : C}
             (f : C⟦X,Y⟧)
             (hX : disp_alg_prebicat_1 X)
             (hY : C⟦F Y,Y⟧)
             (hf : hX -->[ f ] hY)
    : disp_2cells (runitor f) (hf;; @id_disp C disp_alg_prebicat_1 Y hY) hf.
  Proof.
    cbn ; red.
    rewrite disp_alg_runitor_help.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    apply maponpaths.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
      refine (laxfunctor_is_iso F (runitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite !vassocl.
    apply maponpaths.
    rewrite psfunctor_rinvunitor.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite !vassocl.
    rewrite rwhisker_lwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    symmetry.
    apply triangle_l_inv.
  Qed.

  Definition disp_alg_lassociator
             {W X Y Z : C}
             {f : C ⟦W,X⟧}
             {g : C ⟦X,Y⟧}
             {h : C ⟦Y,Z⟧}
             {hW : disp_alg_prebicat_1 W}
             {hX : disp_alg_prebicat_1 X}
             {hY : disp_alg_prebicat_1 Y}
             {hZ : disp_alg_prebicat_1 Z}
             (hf : hW -->[ f] hX)
             (hg : hX -->[ g] hY)
             (hh : hY -->[ h] hZ)
    : disp_2cells (rassociator f g h) ((hf;; hg)%mor_disp;; hh) (hf;; (hg;; hh)%mor_disp).
  Proof.
    cbn ; red.
    assert ((hW ◃ rassociator f g h) • lassociator hW f (g · h)
            =
            lassociator hW (f · g) h • (lassociator _ _ _ ▹ h) • rassociator _ _ _) as X0.
    {
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      rewrite pentagon.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_left.
      reflexivity.
    }
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite X0.
    rewrite !vassocl.
    apply maponpaths.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    { is_iso. refine (laxfunctor_is_iso F (rassociator f g h ,, _)). is_iso. }
    cbn.
    pose (laxfunctor_lassociator F f g h).
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite (maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    rewrite rwhisker_lwhisker.
    rewrite !vassocl.
    rewrite !rwhisker_vcomp.
    rewrite vassocl in p.
    rewrite p.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    pose (pentagon hZ (#F h) (#F g) (#F f)).
    rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp in p0.
    rewrite vassocr in p0.
    rewrite <- p0.
    rewrite <- lwhisker_vcomp.
    use vcomp_move_R_pM.
    { is_iso. }
    use vcomp_move_R_pM.
    { is_iso. }
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    assert ((#F f ◃ rassociator hX g h)
              • lassociator (#F f) hX (g · h)
              • lassociator (#F f · hX) g h
              • (rassociator (#F f) hX g ▹ h) = lassociator _ _ _) as X1.
    {
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite pentagon.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker, id2_right.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2, id2_left.
      reflexivity.
    }
    rewrite !vassocr.
    rewrite X1.
    rewrite <- rwhisker_lwhisker.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    assert ((rassociator (#F f) (#F g) (hY · h))
              • (#F f ◃ lassociator (#F g) hY h)
              • lassociator (#F f) (#F g · hY) h
              • (lassociator (#F f) (#F g) hY ▹ h)
            =
            lassociator _ _ _).
    {
      rewrite !vassocl.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite <- pentagon.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    }
    rewrite !vassocr.
    rewrite X2.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite lassociator_rassociator.
    rewrite id2_left.
    rewrite rwhisker_rwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite vcomp_whisker.
    reflexivity.
  Qed.

  Definition disp_alg_ops : disp_prebicat_ops disp_alg_prebicat_1.
  Proof.
    repeat split.
    - intros X Y f hX hY α ; cbn ; unfold alg_disp_cat_2cell.
      rewrite lwhisker_id2, id2_left.
      rewrite laxfunctor_id2, id2_rwhisker, id2_right.
      reflexivity.
    - intros X Y f hX hY hf.
      exact (disp_alg_lunitor f hX hY hf).
    - intros X Y f hX hY hf.
      exact (disp_alg_runitor f hX hY hf).
    - intros X Y f hX hY hf ; cbn ; red.
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      { is_iso.
        refine (laxfunctor_is_iso F (linvunitor f ,, _)).
        is_iso.
      }
      symmetry.
      exact (disp_alg_lunitor f hX hY hf).
    - intros X Y f hX hY hf ; cbn ; red.
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      { is_iso.
        refine (laxfunctor_is_iso F (rinvunitor f ,, _)).
        is_iso.
      }
      cbn.
      symmetry.
      exact (disp_alg_runitor f hX hY hf).
    - intros W X Y Z f g h hW hX hY hZ hf hg hh.
      exact (disp_alg_lassociator hf hg hh).
    - intros W X Y Z f g h hW hX hY hZ hf hg hh.
      cbn ; red.
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      { is_iso.
        refine (laxfunctor_is_iso F (lassociator f g h ,, _)).
        is_iso.
      }
      cbn.
      symmetry.
      exact (disp_alg_lassociator hf hg hh).
    - intros X Y f g h α β hX hY hf hg hh hα hβ ; cbn ; red.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite hβ.
      rewrite !vassocr.
      rewrite hα.
      rewrite !vassocl.
      rewrite !rwhisker_vcomp.
      rewrite <- !laxfunctor_vcomp.
      reflexivity.
    - intros X Y Z f g₁ g₂ α hX hY hZ hf hg₁ hg₂ hα ; cbn ; red.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite laxfunctor_lwhisker.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite <- hα.
      rewrite <- lwhisker_vcomp.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply (maponpaths (λ z, (z • _) • _)).
      rewrite vcomp_whisker.
      reflexivity.
    - intros X Y Z f g₁ g₂ α hX hY hZ hf hg₁ hg₂ hα ; cbn ; red.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite laxfunctor_rwhisker.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite rwhisker_vcomp.
      rewrite hα.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      reflexivity.
  Qed.

  Definition disp_alg_ops_laws : disp_prebicat_laws (_ ,, disp_alg_ops).
  Proof.
    repeat split ; intro ; intros ; apply C.
  Qed.

  Definition disp_alg_prebicat : disp_prebicat C
    := (_ ,, disp_alg_ops_laws).

  Definition disp_alg_bicat : disp_bicat C.
  Proof.
    refine (disp_alg_prebicat ,, _).
    intros X Y f g α hX hY hf hg hα hβ.
    apply isasetaprop.
    cbn in * ; unfold alg_disp_cat_2cell in *.
    exact (pr2 C _ _ _ _ ((hX ◃ α) • hg) (hf • (## F α ▹ hY))).
  Defined.
End Algebra.
