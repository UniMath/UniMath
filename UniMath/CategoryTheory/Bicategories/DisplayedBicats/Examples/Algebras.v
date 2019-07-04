(**
Lax algebras on a pseudofunctor.
Morphisms are 2-cells which witness a certain diagram commutes. Since this 2-cell is not necessarily invertible, these are lax algebras.
We define it as a displayed bicategory. We also prove that the total category is univalent if the base is univalent.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section Algebra.
  Context `{C : bicat}.
  Variable (F : psfunctor C C).

  Definition alg_disp_cat : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ X, C⟦F X,X⟧).
    - intros X Y f g h.
      exact (invertible_2cell (f · h) (#F h · g)).
  Defined.

  Definition alg_disp_cat_id_comp : disp_cat_id_comp C alg_disp_cat.
  Proof.
    split ; cbn.
    - intros X f.
      refine (runitor f • linvunitor f • (psfunctor_id F X ▹ f) ,, _).
      is_iso.
      exact (psfunctor_id F X).
    - intros X Y Z f g hX hY hZ α β.
      refine ((lassociator hX f g)
               • (α ▹ g)
               • rassociator (#F f) hY g
               • (#F f ◃ β)
               • lassociator (#F f) (#F g) hZ
               • (psfunctor_comp F f g ▹ hZ) ,, _).
      is_iso.
      + exact α.
      + exact β.
      + exact (psfunctor_comp F f g).
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
             (hf : invertible_2cell (hX · f) (#F f · hY))
    : disp_2cells (lunitor f) (@id_disp C disp_alg_prebicat_1 X hX;; hf) hf.
  Proof.
    cbn ; red ; cbn.
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
      refine (psfunctor_is_iso _ (lunitor f,,_)).
      is_iso.
    }
    cbn.
    rewrite psfunctor_linvunitor.
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
    cbn ; red ; cbn.
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
      refine (psfunctor_is_iso F (runitor f ,, _)).
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
    cbn ; red ; cbn.
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
    { is_iso. refine (psfunctor_is_iso F (rassociator f g h ,, _)). is_iso. }
    cbn.
    pose (psfunctor_lassociator F f g h).
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite (maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    rewrite rwhisker_lwhisker.
    rewrite !vassocl.
    rewrite !rwhisker_vcomp.
    rewrite vassocl in p.
    cbn in p.
    etrans.
    {
      do 5 apply maponpaths.
      exact p.
    }
    clear p.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    pose (pentagon hZ (#F h) (#F g) (#F f)) as p.
    rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp in p.
    rewrite vassocr in p.
    rewrite <- p.
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
            lassociator _ _ _) as X2.
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
      rewrite psfunctor_id2, id2_rwhisker, id2_right.
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
        refine (psfunctor_is_iso F (linvunitor f ,, _)).
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
        refine (psfunctor_is_iso F (rinvunitor f ,, _)).
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
        refine (psfunctor_is_iso F (lassociator f g h ,, _)).
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
      rewrite <- !psfunctor_vcomp.
      reflexivity.
    - intros X Y Z f g₁ g₂ α hX hY hZ hf hg₁ hg₂ hα ; cbn ; red ; cbn.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite psfunctor_lwhisker.
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
    - intros X Y Z f g₁ g₂ α hX hY hZ hf hg₁ hg₂ hα ; cbn ; red ; cbn.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite psfunctor_rwhisker.
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

  Definition disp_alg_bicat_disp_is_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_alg_bicat a}
             {bb : disp_alg_bicat b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
             (xx : ff ==>[x] gg)
    : is_disp_invertible_2cell x xx.
  Proof.
    use tpair.
    - cbn in *.
      unfold alg_disp_cat_2cell in *.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite vassocr.
      use vcomp_move_L_Mp.
      {
        is_iso.
        refine (psfunctor_is_iso F (x ^-1 ,, _)).
        is_iso.
      }
      cbn.
      exact (!xx).
    - split ; apply C.
  Defined.

  Definition disp_alg_bicat_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_alg_bicat a}
             {bb : disp_alg_bicat b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
    : isaprop (disp_invertible_2cell x ff gg).
  Proof.
    apply invproofirrelevance.
    intro ; intro.
    use subtypePath.
    - intro.
      apply isaprop_is_disp_invertible_2cell.
    - apply C.
  Defined.

  Definition disp_alg_bicat_univalent_2_1
    : disp_univalent_2_1 disp_alg_bicat.
  Proof.
    intros a b f g p aa bb ff gg.
    induction p.
    apply isweqimplimpl.
    - cbn ; unfold idfun.
      intros x.
      pose (pr1 x) as d.
      cbn in *.
      unfold alg_disp_cat_2cell in *.
      rewrite lwhisker_id2 in d.
      rewrite id2_left in d.
      rewrite psfunctor_id2 in d.
      rewrite id2_rwhisker in d.
      rewrite id2_right in d.
      use subtypePath.
      { intro ; apply isaprop_is_invertible_2cell. }
      exact (!d).
    - apply isaset_invertible_2cell.
    - apply disp_alg_bicat_disp_invertible_2cell.
  Defined.

  Section Invertible2CellToDispAdjointEquivalence.
    Context {a : C}.
    Variable (aa bb : disp_alg_bicat a)
             (x : invertible_2cell aa bb).

    Local Definition left_adjoint_2cell
      : aa -->[ internal_adjoint_equivalence_identity a] bb.
    Proof.
      refine (runitor aa • x • linvunitor bb • (psfunctor_id F a ▹ bb) ,, _).
      is_iso.
      - exact x.
      - exact (psfunctor_id F a).
    Defined.

    Local Definition right_adjoint_2cell
      : bb -->[ left_adjoint_right_adjoint (internal_adjoint_equivalence_identity a)] aa.
    Proof.
      refine (runitor bb • inv_cell x • linvunitor aa • (psfunctor_id F a ▹ aa) ,, _).
      is_iso.
      exact (psfunctor_id F a).
    Defined.

    Local Definition η_2cell
      : (id_disp aa)
          ==>[ left_adjoint_unit (internal_adjoint_equivalence_identity a) ]
          left_adjoint_2cell;;right_adjoint_2cell.
    Proof.
      cbn ; unfold alg_disp_cat_2cell, left_adjoint_2cell, right_adjoint_2cell ; cbn.
      rewrite !(maponpaths (λ z, z ▹ _) (vassocl _ _ _)).
      rewrite !(maponpaths (λ z, (_ • z) ▹ _) (vassocr _ _ _)).
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !(maponpaths (λ z, (_ • z) ▹ _) (vassocl _ _ _)).
      rewrite <- vcomp_whisker.
      rewrite <- (runitor_natural _ _ _ _ (x^-1)).
      rewrite <- rwhisker_hcomp.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • z))))) (vassocr _ _ _)).
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • (_ • z)))))) (vassocr _ _ _)).
      rewrite lwhisker_vcomp, rwhisker_vcomp.
      rewrite vcomp_rinv, id2_rwhisker, lwhisker_id2, id2_left.
      rewrite psfunctor_linvunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- runitor_natural.
      rewrite lwhisker_hcomp.
      assert ((linvunitor (id₁ a) ⋆⋆ id₂ aa)
                • lassociator aa (id₁ a) (id₁ a)
                • (runitor aa ▹ id₁ a)
                • (linvunitor aa ▹ id₁ a)
              =
              (id₂ (id₁ a) ⋆⋆ linvunitor aa)
                • (runitor (id₁ (F a) · aa))
                • rinvunitor _
             ) as ->.
      {
        rewrite runitor_natural.
        rewrite triangle_l_inv.
        rewrite <- rwhisker_hcomp.
        rewrite rwhisker_vcomp.
        rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
        rewrite left_unit_inv_assoc₂.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        rewrite !vassocr.
        rewrite runitor_rinvunitor, id2_left.
        use vcomp_move_L_Mp.
        { is_iso. }
        cbn.
        symmetry.
        apply linvunitor_assoc.
      }
      rewrite !vassocl.
      repeat (apply maponpaths).
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite <- left_unit_inv_assoc.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rinvunitor_runitor, lwhisker_id2, id2_left.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- !rwhisker_hcomp.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      use vcomp_move_R_Mp.
      { is_iso. apply F. }
      cbn.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. apply F. }
      cbn.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite <- rinvunitor_natural, <- linvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      reflexivity.
    Qed.

    Local Definition ε_2cell
      : (right_adjoint_2cell;; left_adjoint_2cell)
          ==>[ left_adjoint_counit (internal_adjoint_equivalence_identity a) ]
          id_disp bb.
    Proof.
      cbn ; unfold alg_disp_cat_2cell, left_adjoint_2cell, right_adjoint_2cell ; cbn.
      rewrite !(maponpaths (λ z, z ▹ _) (vassocl _ _ _)).
      rewrite !(maponpaths (λ z, (_ • z) ▹ _) (vassocr _ _ _)).
      rewrite (linvunitor_natural (x ^-1)).
      rewrite <- lwhisker_hcomp.
      rewrite !(maponpaths (λ z, (_ • z) ▹ _) (vassocl _ _ _)).
      rewrite <- vcomp_whisker.
      rewrite <- (runitor_natural _ _ _ _ x).
      rewrite <- rwhisker_hcomp.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • z))))) (vassocr _ _ _)).
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • z)))) (vassocr _ _ _)).
      rewrite rwhisker_vcomp, lwhisker_vcomp.
      rewrite vcomp_lid, lwhisker_id2, id2_rwhisker, id2_left.
      rewrite <- runitor_natural.
      rewrite <- !rwhisker_hcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      assert ((bb ◃ lunitor (id₁ a))
                • (linvunitor bb ▹ id₁ a)
              =
              (lassociator bb (id₁ a) (id₁ a))
                • (runitor bb ▹ id₁ a)
                • (linvunitor bb ▹ id₁ a))
        as ->.
      {
        apply (maponpaths (λ z, z • _)).
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite triangle_r.
        reflexivity.
      }
      rewrite !vassocl.
      repeat (apply maponpaths).
      rewrite <- runitor_triangle.
      apply maponpaths.
      refine (!(id2_right _) @ _).
      apply maponpaths.
      rewrite psfunctor_F_lunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv, id2_rwhisker, id2_left.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. }
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn ; rewrite id2_left.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker.
      rewrite !lwhisker_hcomp, !rwhisker_hcomp.
      rewrite !vassocr.
      rewrite triangle_l_inv.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      use vcomp_move_R_Mp.
      { is_iso. apply F. }
      cbn.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. apply F. }
      cbn.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite <- rinvunitor_natural, <- linvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      reflexivity.
    Qed.

    Definition disp_alg_bicat_adjoint_equivalence
      : disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb.
    Proof.
      use tpair.
      - exact left_adjoint_2cell.
      - use tpair.
        + use tpair.
          * exact right_adjoint_2cell.
          * split.
            ** exact η_2cell.
            ** exact ε_2cell.
        + refine ((_ ,, _) ,, (_ ,, _)).
          * apply C.
          * apply C.
          * apply disp_alg_bicat_disp_is_invertible_2cell.
          * apply disp_alg_bicat_disp_is_invertible_2cell.
    Defined.
  End Invertible2CellToDispAdjointEquivalence.

  Section DispAdjointEquivalenceToInvertible2cell.
    Context {a : C}.
    Variable (aa bb : disp_alg_bicat a)
             (x : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity a)
                    aa bb).

    Local Definition invertible_2cell_map_alg
      : aa ==> bb
      := (rinvunitor _)
           • (aa ◃ linvunitor (id₁ a))
           • lassociator aa (id₁ a) (id₁ a)
           • (cell_from_invertible_2cell (pr1 x) ▹ id₁ a)
           • rassociator (# F (id₁ a)) bb (id₁ a)
           • (inv_cell (psfunctor_id F a) ▹ (bb · _))
           • lunitor (bb · id₁ a)
           • runitor bb.

    Local Definition invertible_2cell_inv_alg
      : bb ==> aa
      := (rinvunitor bb)
           • linvunitor (bb · id₁ a)
           • (psfunctor_id F a ▹ (bb · id₁ a))
           • (# F (id₁ a) ◃ cell_from_invertible_2cell (disp_left_adjoint_right_adjoint _ (pr12 x)))
           • lassociator (# F (id₁ a)) (# F (id₁ a)) aa
           • (psfunctor_comp F (id₁ a) (id₁ a) ▹ aa)
           • (##F (lunitor (id₁ a)) ▹ aa)
           • (inv_cell (psfunctor_id F a) ▹ aa)
           • lunitor aa.

    Definition invertible_2cell_map_alg'
      : aa ==> bb
      := (linvunitor aa)
           • (psfunctor_id F a ▹ aa)
           • (# F (id₁ a) ◃ rinvunitor aa)
           • (# F (id₁ a) ◃ cell_from_invertible_2cell (pr1 x))
           • lassociator (# F (id₁ a)) (# F (id₁ a)) bb
           • (psfunctor_comp F (id₁ a) (id₁ a) ▹ bb)
           • (## F (lunitor (id₁ a)) ▹ bb)
           • ((psfunctor_id F a)^-1 ▹ bb)
           • lunitor bb.

    Local Definition invertible_2cell_inv_alg'
      : bb ==> aa
      := (rinvunitor bb)
           • (bb ◃ linvunitor (id₁ a))
           • lassociator bb (id₁ a) (id₁ a)
           • (cell_from_invertible_2cell (disp_left_adjoint_right_adjoint _ (pr12 x)) ▹ id₁ a)
           • rassociator _ _ _
           • (# F (id₁ a) ◃ runitor aa)
           • ((psfunctor_id F a)^-1 ▹ aa)
           • lunitor aa.

    Definition invertible_2cell_map_alg''
      : aa ==> bb
      := (rinvunitor aa)
           • cell_from_invertible_2cell (pr1 x)
           • ((psfunctor_id F a)^-1 ▹ bb)
           • lunitor bb.

    Local Definition invertible_2cell_map_alg_eq
      : invertible_2cell_map_alg = invertible_2cell_map_alg'.
    Proof.
      unfold invertible_2cell_map_alg, invertible_2cell_map_alg'.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite (vcomp_whisker (psfunctor_id F a)).
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rwhisker_hcomp, lwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      repeat (apply maponpaths).
      rewrite !vassocr.
      rewrite <- left_unit_inv_assoc.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite psfunctor_F_lunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv, id2_rwhisker, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite !rwhisker_vcomp.
      rewrite vcomp_rinv, id2_rwhisker, id2_left.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rassociator_lassociator, id2_left.
      rewrite !vassocr.
      rewrite !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite lunitor_assoc.
      rewrite !vassocl.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_runitor.
      apply id2_left.
    Qed.

    Local Definition invertible_2cell_map_alg_eq2
      : invertible_2cell_map_alg = invertible_2cell_map_alg''.
    Proof.
      unfold invertible_2cell_map_alg, invertible_2cell_map_alg'' ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite <- rwhisker_rwhisker_alt.
      rewrite <- lunitor_triangle.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite rassociator_lassociator, id2_left.
      rewrite !vassocr.
      rewrite !rwhisker_vcomp.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      rewrite runitor_rinvunitor, id2_left.
      reflexivity.
    Qed.

    Local Definition invertible_2cell_inv_alg_eq
      : invertible_2cell_inv_alg = invertible_2cell_inv_alg'.
    Proof.
      unfold invertible_2cell_inv_alg, invertible_2cell_inv_alg'.
      rewrite !vassocl.
      repeat (apply maponpaths).
      rewrite psfunctor_F_lunitor.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • z)))) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_rinv, id2_left.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite !rwhisker_vcomp.
      rewrite vcomp_rinv, id2_rwhisker, id2_left.
      rewrite !vassocr.
      repeat (apply maponpaths_2).
      rewrite !vassocl.
      rewrite runitor_triangle, lunitor_triangle.
      rewrite vcomp_lunitor, vcomp_runitor.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      refine (!(id2_left _) @ _).
      apply maponpaths_2.
      rewrite <- rwhisker_hcomp.
      rewrite vcomp_runitor.
      exact (!(runitor_rinvunitor bb)).
    Qed.

    Local Definition map_inv_alg
      : invertible_2cell_map_alg • invertible_2cell_inv_alg = id₂ aa.
    Proof.
      unfold invertible_2cell_map_alg, invertible_2cell_inv_alg ; cbn.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • (_ • (_ • z)))))))
                           (vassocr _ _ _)).
      rewrite runitor_rinvunitor, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • (_ • z))))))
                           (vassocr _ _ _)).
      rewrite lunitor_linvunitor, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • z)))))
                           (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_lid.
      rewrite id2_rwhisker, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      pose (disp_left_adjoint_unit _ x) as t1.
      cbn in t1.
      unfold alg_disp_cat_2cell in *.
      cbn in t1.
      rewrite !vassocr in t1.
      etrans.
      {
        apply maponpaths.
        do 3 apply maponpaths_2.
        apply t1.
      }
      clear t1.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite <- psfunctor_vcomp.
      rewrite linvunitor_lunitor.
      rewrite psfunctor_id2.
      rewrite id2_rwhisker, id2_left.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker, id2_left.
      apply linvunitor_lunitor.
    Qed.

    Local Definition inv_map_alg
      : invertible_2cell_inv_alg • invertible_2cell_map_alg = id₂ bb.
    Proof.
      rewrite invertible_2cell_map_alg_eq, invertible_2cell_inv_alg_eq.
      unfold invertible_2cell_map_alg', invertible_2cell_inv_alg' ; cbn.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • (_ • (_ • z)))))))
                           (vassocr _ _ _)).
      rewrite lunitor_linvunitor, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • (_ • z))))))
                           (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_lid.
      rewrite id2_rwhisker, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • z)))))
                           (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      pose (disp_left_adjoint_counit _ x) as t1.
      cbn in t1.
      unfold alg_disp_cat_2cell in *.
      cbn in t1.
      rewrite !vassocr in t1.
      etrans.
      {
        do 2 apply maponpaths.
        do 2 apply maponpaths_2.
        apply (!t1).
      }
      clear t1.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker, id2_left.
      apply linvunitor_lunitor.
    Qed.

    Definition disp_alg_bicat_adjoint_equivalence_inv
      : invertible_2cell aa bb.
    Proof.
      use tpair.
      - exact invertible_2cell_map_alg.
      - use tpair.
        + exact invertible_2cell_inv_alg.
        + split.
          * exact map_inv_alg.
          * exact inv_map_alg.
    Defined.
  End DispAdjointEquivalenceToInvertible2cell.

  Definition disp_alg_bicat_adjoint_equivalence_weq
             (HC : is_univalent_2_1 C)
             {a : C}
             (aa bb : disp_alg_bicat a)
    : invertible_2cell aa bb
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb.
  Proof.
    use make_weq.
    - exact (disp_alg_bicat_adjoint_equivalence aa bb).
    - use isweq_iso.
      + exact (disp_alg_bicat_adjoint_equivalence_inv aa bb).
      + intros x.
        use subtypePath.
        * intro.
          apply isaprop_is_invertible_2cell.
        * cbn.
          abstract (rewrite invertible_2cell_map_alg_eq2 ;
                    unfold invertible_2cell_map_alg'' ; cbn ; unfold left_adjoint_2cell ;
                    rewrite !vassocr ;
                    rewrite rinvunitor_runitor, id2_left ;
                    rewrite !vassocl ;
                    rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
                    rewrite rwhisker_vcomp, vcomp_rinv ;
                    rewrite id2_rwhisker, id2_left ;
                    rewrite linvunitor_lunitor, id2_right ;
                    reflexivity).
      + intros x.
        use subtypePath.
        * intro.
          apply isaprop_disp_left_adjoint_equivalence.
          ** exact HC.
          ** exact disp_alg_bicat_univalent_2_1.
        * cbn.
          unfold left_adjoint_2cell.
          unfold disp_alg_bicat_adjoint_equivalence_inv ; cbn.
          apply subtypePath.
          { intro ; apply isaprop_is_invertible_2cell. }
          cbn.
          abstract (rewrite invertible_2cell_map_alg_eq2 ;
                    unfold invertible_2cell_map_alg'' ; cbn ; unfold left_adjoint_2cell ;
                    rewrite !vassocr ;
                    rewrite runitor_rinvunitor, id2_left ;
                    rewrite !vassocl ;
                    rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
                    rewrite lunitor_linvunitor, id2_left ;
                    rewrite rwhisker_vcomp, vcomp_lid ;
                    rewrite id2_rwhisker, id2_right ;
                    reflexivity).
  Defined.

  Definition disp_alg_bicat_univalent_2_0
             (HC : is_univalent_2_1 C)
    : disp_univalent_2_0 disp_alg_bicat.
  Proof.
    intros a b p aa bb.
    induction p.
    use weqhomot.
    - exact (disp_alg_bicat_adjoint_equivalence_weq HC aa bb ∘ (_ ,, HC _ _ aa bb))%weq.
    - intros p.
      induction p ; cbn ; unfold idfun.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence C disp_alg_bicat).
        * exact HC.
        * exact disp_alg_bicat_univalent_2_1.
      + cbn ; unfold left_adjoint_2cell ; cbn.
        use subtypePath.
        { intro ; apply isaprop_is_invertible_2cell. }
        cbn.
        rewrite id2_right.
        reflexivity.
  Defined.

  Definition bicat_algebra := total_bicat disp_alg_bicat.

  Definition bicat_algebra_is_univalent_2_1
             (HC : is_univalent_2_1 C)
    : is_univalent_2_1 bicat_algebra.
  Proof.
    apply total_is_univalent_2_1.
    - exact HC.
    - exact disp_alg_bicat_univalent_2_1.
  Defined.

  Definition bicat_algebra_is_univalent_2_0
             (HC : is_univalent_2 C)
    : is_univalent_2_0 bicat_algebra.
  Proof.
    apply total_is_univalent_2_0.
    - exact (pr1 HC).
    - exact (disp_alg_bicat_univalent_2_0 (pr2 HC)).
  Defined.

  Definition bicat_algebra_is_univalent_2
             (HC : is_univalent_2 C)
    : is_univalent_2 bicat_algebra.
  Proof.
    split.
    - apply bicat_algebra_is_univalent_2_0. assumption.
    - apply bicat_algebra_is_univalent_2_1. exact (pr2 HC).
  Defined.
End Algebra.
