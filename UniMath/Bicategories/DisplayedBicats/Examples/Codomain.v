(**************************************************************

 The codomain displayed bicategory

 We look at the codomain displayed bicategory in this file.
 We restrict ourselves to locally groupoidal bicategories.
 1. The definition
 2. Displayed univalence

 ***************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition cod_1cell_path_help
           {B : bicat}
           {b c : B}
           (f₁ f₂ : B ⟦ b , c ⟧)
  : invertible_2cell f₁ f₂ ≃ invertible_2cell f₁ (id₁ _ · f₂).
Proof.
  use make_weq.
  - intro α.
    refine (α • linvunitor _ ,, _).
    is_iso.
    apply α.
  - use isweq_iso.
    + intro α.
      use make_invertible_2cell.
      * exact (α • lunitor _).
      * is_iso.
        apply property_from_invertible_2cell.
    + abstract
        (intro p ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         cbn ;
         rewrite vassocl ;
         rewrite linvunitor_lunitor ;
         apply id2_right).
    + abstract
        (intros α ; cbn ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         cbn ;
         rewrite vassocl ;
         rewrite lunitor_linvunitor ;
         apply id2_right).
Defined.

(**
 1. Definition of the displayed bicategory
 *)
Section CodomainArrow.
  Variable (B : bicat).

  Definition cod_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells (prod_bicat B B).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ X, pr2 X --> pr1 X).
        * exact (λ X Y fX fY f, invertible_2cell (fX · pr1 f) (pr2 f · fY)).
      + use tpair.
        * refine (λ X fX, (runitor _ • linvunitor _ ,, _)).
          is_iso.
        * refine (λ X Y Z f g fX fY fZ ff fg,
                 (lassociator _ _ _
                  • (pr1 ff ▹ _)
                  • rassociator _ _ _
                  • (_ ◃ pr1 fg)
                  • lassociator _ _ _
                  ,, _)).
          cbn ; is_iso.
          ** exact (pr2 ff).
          ** exact (pr2 fg).
    - exact (λ X Y f g α fX fY ff fg,
             pr1 ff • (pr2 α ▹ _)
             =
             (_ ◃ pr1 α) • pr1 fg).
  Defined.

  Definition cod_disp_prebicat_ops
    : disp_prebicat_ops cod_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite id2_rwhisker, id2_right.
      rewrite lwhisker_id2, id2_left.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      rewrite linvunitor_lunitor.
      apply id2_right.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocl.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite linvunitor_lunitor, id2_right.
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite left_unit_assoc.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite rassociator_lassociator, id2_right.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite !rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- left_unit_inv_assoc.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      apply idpath.
    - intros X₁ X₂ X₃ X₄ f g h fX₁ fX₂ fX₃ fX₄ pf pg ph.
      simpl ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        etrans.
        {
          do 8 apply maponpaths_2.
          apply lassociator_lassociator.
        }
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        apply lassociator_lassociator.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_L_Mp.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocl.
        do 4 apply maponpaths.
        exact (!(lassociator_lassociator _ _ _ _)).
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator, lwhisker_id2.
        apply id2_left.
      }
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_R_pM.
      { is_iso. }
      simpl.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. }
      simpl.
      rewrite lassociator_lassociator.
      apply idpath.
    - intros X₁ X₂ X₃ X₄ f g h fX₁ fX₂ fX₃ fX₄ pf pg ph.
      simpl ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 7 apply maponpaths_2.
        rewrite lassociator_lassociator.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator, id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lassociator_lassociator.
      rewrite vassocr.
      apply idpath.
    - intros X Y f g h p q fX fY pf pg ph pp pq.
      simpl ; cbn in *.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite pp.
      rewrite !vassocl.
      rewrite pq.
      rewrite !vassocr.
      apply maponpaths_2.
      apply lwhisker_vcomp.
    - intros X Y Z f g₁ g₂ p fX fY fZ pf pg₁ pg₂ pp.
      simpl ; cbn in *.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      exact pp.
    - intros X Y Z f₁ f₂ g p fX fY fZ pf₁ pf₂ pg pp.
      simpl ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      rewrite <- pp.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      apply idpath.
  Qed.

  Definition cod_disp_prebicat_data
    : disp_prebicat_data (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_disp_prebicat_1_id_comp_cells.
    - exact cod_disp_prebicat_ops.
  Defined.

  Definition cod_disp_prebicat_laws
    : disp_prebicat_laws cod_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply B.
  Qed.

  Definition cod_disp_prebicat
    : disp_prebicat (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_disp_prebicat_data.
    - exact cod_disp_prebicat_laws.
  Defined.

  Definition cod_has_disp_cellset
    : has_disp_cellset cod_disp_prebicat.
  Proof.
    intros X Y f g p fX fY pf pg.
    apply isasetaprop.
    apply B.
  Qed.

  Definition cod_disp_bicat_help
    : disp_bicat (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_disp_prebicat.
    - exact cod_has_disp_cellset.
  Defined.

  Definition cod_disp_bicat
    : disp_bicat B
    := sigma_bicat _ _ cod_disp_bicat_help.
End CodomainArrow.

(** Some projections and builders *)
Definition dom
           {B : bicat}
           {X : B}
           (f : cod_disp_bicat B X)
  : B
  := pr1 f.

Definition ar
           {B : bicat}
           {X : B}
           (f : cod_disp_bicat B X)
  : dom f --> X
  := pr2 f.

Definition make_ar
           {B : bicat}
           {X Y : B}
           (f : X --> Y)
  : cod_disp_bicat B Y
  := (X ,, f).

Definition make_disp_1cell_cod
           {B : bicat}
           {X Y : B}
           {f : X --> Y}
           {dX : cod_disp_bicat B X}
           {dY : cod_disp_bicat B Y}
           (h : dom dX --> dom dY)
           (p : invertible_2cell (pr2 dX · f) (h · pr2 dY))
  : dX -->[ f ] dY
  := h ,, p.

Definition coherent_homot
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           (α : f ==> g)
           {dX : cod_disp_bicat B X}
           {dY : cod_disp_bicat B Y}
           {df : dX -->[ f ] dY}
           {dg : dX -->[ g ] dY}
           (h : pr1 df ==> pr1 dg)
  : UU
  := pr12 df • (h ▹ pr2 dY)
     =
     (pr2 dX ◃ α) • pr12 dg.

Definition make_disp_2cell_cod
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           {α : f ==> g}
           {dX : cod_disp_bicat B X}
           {dY : cod_disp_bicat B Y}
           {df : dX -->[ f ] dY}
           {dg : dX -->[ g ] dY}
           (h : pr1 df ==> pr1 dg)
           (hh : coherent_homot α h)
  : df ==>[ α ] dg
  := h ,, hh.

Definition is_disp_invertible_2cell_cod
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           {α : invertible_2cell f g}
           {dX : cod_disp_bicat B X}
           {dY : cod_disp_bicat B Y}
           {ff : dX -->[ f ] dY}
           {gg : dX -->[ g ] dY}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_invertible_2cell (pr1 αα))
  : is_disp_invertible_2cell α αα.
Proof.
  use tpair.
  - use tpair.
    + exact (Hαα^-1).
    + abstract
        (simpl ;
         use vcomp_move_R_Mp ; is_iso ;
         simpl ;
         rewrite !vassocl ;
         use vcomp_move_L_pM ; is_iso ;
         simpl ;
         refine (!_) ;
         apply αα).
  - split.
    + abstract
        (use subtypePath ; [ intro ; apply B | ] ;
         simpl ;
         unfold transportb ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         unfold idfun ; cbn ;
         apply vcomp_rinv).
    + abstract
        (use subtypePath ; [ intro ; apply B | ] ;
         simpl ;
         unfold transportb ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         cbn ;
         apply vcomp_linv).
Defined.

Definition transportf_cell_of_cod_over
           {B : bicat}
           {b₁ b₂ : B}
           {f₁ f₂ : b₁ --> b₂}
           {α β : f₁ ==> f₂}
           {h₁ : cod_disp_bicat B b₁}
           {h₂ : cod_disp_bicat B b₂}
           {ff₁ : h₁ -->[ f₁ ] h₂}
           {ff₂ : h₁ -->[ f₂ ] h₂}
           (p : α = β)
           (αα : ff₁ ==>[ α ] ff₂)
  : pr1 (transportf
           (λ z, ff₁ ==>[ z ] ff₂)
           p
           αα)
    =
    pr1 αα.
Proof.
  cbn.
  rewrite pr1_transportf, transportf_const.
  apply idpath.
Qed.

Definition transportb_cell_of_cod_over
           {B : bicat}
           {b₁ b₂ : B}
           {f₁ f₂ : b₁ --> b₂}
           {α β : f₁ ==> f₂}
           {h₁ : cod_disp_bicat B b₁}
           {h₂ : cod_disp_bicat B b₂}
           {ff₁ : h₁ -->[ f₁ ] h₂}
           {ff₂ : h₁ -->[ f₂ ] h₂}
           (p : α = β)
           (ββ : ff₁ ==>[ β ] ff₂)
  : pr1 (transportb
           (λ z, ff₁ ==>[ z ] ff₂)
           p
           ββ)
    =
    pr1 ββ.
Proof.
  apply transportf_cell_of_cod_over.
Qed.

Definition from_is_disp_invertible_2cell_cod
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           {α : invertible_2cell f g}
           {dX : cod_disp_bicat B X}
           {dY : cod_disp_bicat B Y}
           {ff : dX -->[ f ] dY}
           {gg : dX -->[ g ] dY}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_disp_invertible_2cell α αα)
  : is_invertible_2cell (pr1 αα).
Proof.
  use make_is_invertible_2cell.
  - exact (pr11 Hαα).
  - abstract
      (exact (maponpaths pr1 (pr12 Hαα) @ transportb_cell_of_cod_over _ _)).
  - abstract
      (exact (maponpaths pr1 (pr22 Hαα) @ transportb_cell_of_cod_over _ _)).
Defined.

Definition disp_locally_groupoid_cod
           (B : bicat)
           (inv_B : locally_groupoid B)
  : disp_locally_groupoid (cod_disp_bicat B).
Proof.
  intro ; intros.
  apply is_disp_invertible_2cell_cod.
  apply inv_B.
Defined.

Definition disp_locally_groupoid_cod_one_types
  : disp_locally_groupoid (cod_disp_bicat one_types).
Proof.
  use disp_locally_groupoid_cod.
  exact @one_type_2cell_iso.
Defined.

(**
 2. The univalence
*)
Section UnivalenceOfCodomain.
  Context (B : bicat).

  Definition cod_invertible_2_cell_to_disp_invertible_help
             {c₁ c₂ : B}
             {f : B ⟦ c₁, c₂ ⟧}
             {φ₁ : cod_disp_bicat B c₁}
             {φ₂ : cod_disp_bicat B c₂}
             {ψ₁ ψ₂ : φ₁ -->[ f] φ₂}
             (α : invertible_2cell (pr1 ψ₁) (pr1 ψ₂))
             (Hα : coherent_homot (id2_invertible_2cell f) (pr1 α))
    : disp_invertible_2cell (id2_invertible_2cell f) ψ₁ ψ₂.
  Proof.
    simple refine (_ ,, _).
    - use make_disp_2cell_cod.
      + exact (pr1 α).
      + exact Hα.
    - apply is_disp_invertible_2cell_cod.
      exact (pr2 α).
  Defined.

  Definition cod_invertible_2_cell_to_disp_invertible
             {c₁ c₂ : B}
             {f : B ⟦ c₁, c₂ ⟧}
             {φ₁ : cod_disp_bicat B c₁}
             {φ₂ : cod_disp_bicat B c₂}
             {ψ₁ ψ₂ : φ₁ -->[ f] φ₂}
    : (∑ (α : invertible_2cell (pr1 ψ₁) (pr1 ψ₂)),
       coherent_homot (id2_invertible_2cell f) (pr1 α))
      →
      disp_invertible_2cell (id2_invertible_2cell f) ψ₁ ψ₂.
  Proof.
    intro α.
    exact (cod_invertible_2_cell_to_disp_invertible_help _ (pr2 α)).
  Defined.

  Definition cod_disp_invertible_invertible_2_cell
             {c₁ c₂ : B}
             {f : B ⟦ c₁, c₂ ⟧}
             {φ₁ : cod_disp_bicat B c₁}
             {φ₂ : cod_disp_bicat B c₂}
             {ψ₁ ψ₂ : φ₁ -->[ f] φ₂}
    : disp_invertible_2cell (id2_invertible_2cell f) ψ₁ ψ₂
      →
      ∑ (α : invertible_2cell (pr1 ψ₁) (pr1 ψ₂)),
      coherent_homot (id2_invertible_2cell f) (pr1 α).
  Proof.
    intro α.
    simple refine ((_ ,, _) ,, _).
    - exact (pr11 α).
    - simpl.
      use make_is_invertible_2cell.
      + exact (pr1 (disp_inv_cell α)).
      + abstract
          (pose (maponpaths pr1 (disp_vcomp_rinv α)) as p ;
           cbn in p ;
           unfold transportb in p ;
           rewrite pr1_transportf, transportf_const in p ;
           exact p).
      + abstract
          (pose (maponpaths pr1 (disp_vcomp_linv α)) as p ;
           cbn in p ;
           unfold transportb in p ;
           rewrite pr1_transportf, transportf_const in p ;
           exact p).
    - exact (pr21 α).
  Defined.

  Definition cod_invertible_2_cell_weq_disp_invertible
             {c₁ c₂ : B}
             {f : B ⟦ c₁, c₂ ⟧}
             {φ₁ : cod_disp_bicat B c₁}
             {φ₂ : cod_disp_bicat B c₂}
             {ψ₁ ψ₂ : φ₁ -->[ f] φ₂}
    : (∑ (α : invertible_2cell (pr1 ψ₁) (pr1 ψ₂)),
       coherent_homot (id2_invertible_2cell f) (pr1 α))
      ≃
      disp_invertible_2cell (id2_invertible_2cell f) ψ₁ ψ₂.
  Proof.
    use make_weq.
    - exact cod_invertible_2_cell_to_disp_invertible.
    - use isweq_iso.
      + exact cod_disp_invertible_invertible_2_cell.
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply B | ] ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           apply idpath).
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           use subtypePath ; [ intro ; apply B | ] ;
           apply idpath).
  Defined.

  Definition cod_2cell_path
             {c₁ c₂ : B}
             {f : B ⟦ c₁, c₂ ⟧}
             {φ₁ : cod_disp_bicat B c₁}
             {φ₂ : cod_disp_bicat B c₂}
             {ψ₁ ψ₂ : φ₁ -->[ f ] φ₂}
             (p : pr1 ψ₁ = pr1 ψ₂)
    : (transportf (λ x, invertible_2cell (pr2 φ₁ · f) (x · pr2 φ₂)) p (pr2 ψ₁) = pr2 ψ₂)
      ≃
      coherent_homot (id₂ f) (pr1 (idtoiso_2_1 (pr1 ψ₁) (pr1 ψ₂) p)).
  Proof.
    induction ψ₁ as [ψ₁ q₁].
    induction ψ₂ as [ψ₂ q₂].
    cbn in *.
    induction p.
    cbn.
    unfold coherent_homot.
    cbn.
    rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite lwhisker_id2.
    rewrite id2_left.
    apply path_sigma_hprop.
    apply isaprop_is_invertible_2cell.
  Qed.

  Definition cod_disp_univalent_2_1
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_1 (cod_disp_bicat B).
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros c₁ c₂ f φ₁ φ₂ ψ₁ ψ₂.
    use weqhomot.
    - exact (cod_invertible_2_cell_weq_disp_invertible
             ∘ weqtotal2 (make_weq _ (HB_2_1 _ _ _ _)) cod_2cell_path
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro ; apply isaprop_is_disp_invertible_2cell.
      }
      use subtypePath.
      {
        intro ; apply B.
      }
      apply idpath.
  Defined.

  Definition cod_1cell_path
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             (f₁ f₂ : cod_disp_bicat B c)
             (p : pr1 f₁ = pr1 f₂)
    : (transportf (λ b, B ⟦ b, c ⟧) p (pr2 f₁) = pr2 f₂)
      ≃
      invertible_2cell (pr2 f₁) (idtoiso_2_0 _ _ p · pr2 f₂).
  Proof.
    induction f₁ as [ c₁ f₁ ].
    induction f₂ as [ c₂ f₂ ].
    cbn in *.
    induction p.
    exact (cod_1cell_path_help f₁ f₂ ∘ make_weq _ (HB_2_1 _ _ _ _))%weq.
  Defined.

  Section AdjEquivToDispAdjEquiv.
    Context {c : B}
            {f₁ f₂ : cod_disp_bicat B c}
            (e : adjoint_equivalence (pr1 f₁) (pr1 f₂))
            (α : invertible_2cell (pr2 f₁) (pr1 e · pr2 f₂)).

    Let l : pr1 f₁ --> pr1 f₂ := pr1 e.
    Let r : pr1 f₂ --> pr1 f₁ := left_adjoint_right_adjoint e.
    Let η : invertible_2cell (id₁ _) (l · r) := left_equivalence_unit_iso e.
    Let ε : invertible_2cell (r · l) (id₁ _) := left_equivalence_counit_iso e.

    Definition cod_adj_equiv_to_disp_adj_equiv_map
      : f₁ -->[ internal_adjoint_equivalence_identity c] f₂.
    Proof.
      use make_disp_1cell_cod.
      - exact l.
      - refine (runitor _ • α ,, _).
        is_iso.
        apply α.
    Defined.

    Definition cod_adj_equiv_to_disp_adj_equiv_right_adj
      : f₂ -->[ internal_adjoint_equivalence_identity c] f₁.
    Proof.
      use make_disp_1cell_cod.
      - exact r.
      - simpl.
        use make_invertible_2cell.
        + refine (runitor _
                  • linvunitor _
                  • (ε^-1 ▹ _)
                  • rassociator _ _ _
                  • (_ ◃ α^-1)).
        + is_iso.
    Defined.

    Definition cod_adj_equiv_to_disp_adj_equiv_unit
      : pr1 (id_disp f₁)
        ==>
        pr1 (cod_adj_equiv_to_disp_adj_equiv_map
        ;;
        cod_adj_equiv_to_disp_adj_equiv_right_adj)
      := η.

    Definition cod_adj_equiv_to_disp_adj_equiv_unit_homot
      : coherent_homot
          (left_adjoint_unit (internal_adjoint_equivalence_identity c))
          cod_adj_equiv_to_disp_adj_equiv_unit.
    Proof.
      unfold coherent_homot, cod_adj_equiv_to_disp_adj_equiv_unit ; cbn.
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
      apply maponpaths ; clear α.
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

    Definition cod_adj_equiv_to_disp_adj_equiv_counit
      : pr1 (cod_adj_equiv_to_disp_adj_equiv_right_adj
        ;;
        cod_adj_equiv_to_disp_adj_equiv_map)
        ==>
        pr1 (id_disp f₂)
      := pr2 (pr212 e).

    Definition cod_adj_equiv_to_disp_adj_equiv_counit_homot
      : coherent_homot
          (left_adjoint_counit
             (internal_adjoint_equivalence_identity c))
          cod_adj_equiv_to_disp_adj_equiv_counit.
    Proof.
      unfold coherent_homot, cod_adj_equiv_to_disp_adj_equiv_counit ; cbn.
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
      assert (rassociator (pr112 e) (pr1 e) (pr2 f₂) ▹ id₁ c
              • rassociator (pr112 e) (pr1 e · pr2 f₂) (id₁ c)
              • (pr112 e ◃ runitor (pr1 e · pr2 f₂))
              • lassociator (pr112 e) (pr1 e) (pr2 f₂)
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

    Definition cod_adj_equiv_to_disp_adj_equiv_disp_adj
      : disp_left_adjoint_equivalence
          (internal_adjoint_equivalence_identity c)
          cod_adj_equiv_to_disp_adj_equiv_map.
    Proof.
      simple refine (_ ,, (_ ,, _)).
      - simple refine (_ ,, (_ ,, _)).
        + apply cod_adj_equiv_to_disp_adj_equiv_right_adj.
        + use make_disp_2cell_cod.
          * apply cod_adj_equiv_to_disp_adj_equiv_unit.
          * exact cod_adj_equiv_to_disp_adj_equiv_unit_homot.
        + use make_disp_2cell_cod.
          * apply cod_adj_equiv_to_disp_adj_equiv_counit.
          * exact cod_adj_equiv_to_disp_adj_equiv_counit_homot.
      - simple refine (_ ,, _).
        + cbn.
          use subtypePath.
          {
            intro.
            apply B.
          }
          cbn.
          etrans.
          {
            exact (pr1 (pr122 e)).
          }
          refine (!_).
          refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _).
          rewrite transportf_const.
          apply idpath.
        + cbn.
          use subtypePath.
          {
            intro.
            apply B.
          }
          cbn.
          etrans.
          {
            exact (pr2 (pr122 e)).
          }
          refine (!_).
          refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _).
          rewrite transportf_const.
          apply idpath.
      - split.
        + apply is_disp_invertible_2cell_cod ; cbn.
          apply η.
        + apply is_disp_invertible_2cell_cod ; cbn.
          apply ε.
    Qed.

    Definition cod_adj_equiv_to_disp_adj_equiv_help
      : disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂.
    Proof.
      simple refine (_ ,, _).
      - exact cod_adj_equiv_to_disp_adj_equiv_map.
      - exact cod_adj_equiv_to_disp_adj_equiv_disp_adj.
    Defined.
  End AdjEquivToDispAdjEquiv.

  Definition cod_adj_equiv_to_disp_adj_equiv
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
    : (∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)),
       invertible_2cell (pr2 f₁) (pr1 y · pr2 f₂))
      →
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂.
  Proof.
    intro e.
    exact (cod_adj_equiv_to_disp_adj_equiv_help (pr1 e) (pr2 e)).
  Defined.

  Definition cod_disp_adj_equiv_to_adj_equiv
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂
      →
      ∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)),
      invertible_2cell (pr2 f₁) (pr1 y · pr2 f₂).
  Proof.
    intro e.
    simple refine (_ ,, _).
    - simple refine (_ ,, _).
      + exact (pr11 e).
      + simpl.
        simple refine (_ ,, (_ ,, _)).
        * simple refine (_ ,, (_ ,, _)).
          ** exact (pr1 (pr112 e)).
          ** exact (pr11 (pr212 e)).
          ** exact (pr12 (pr212 e)).
        * split.
          ** abstract
               (refine (maponpaths pr1 (pr1 (pr122 e)) @ _) ;
                unfold transportb ;
                cbn ;
                refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _) ;
                rewrite transportf_const ;
                apply idpath).
          ** abstract
               (refine (maponpaths pr1 (pr2 (pr122 e)) @ _) ;
                unfold transportb ;
                cbn ;
                refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _) ;
                rewrite transportf_const ;
                apply idpath).
        * split.
          ** exact (from_is_disp_invertible_2cell_cod _ (pr12 (pr22 e))).
          ** exact (from_is_disp_invertible_2cell_cod _ (pr22 (pr22 e))).
    - refine (rinvunitor _ • pr121 e ,, _).
      is_iso.
      exact (pr221 e).
  Defined.

  Definition cod_adj_equiv_to_disp_to_adj
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
             (e : ∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)),
                  invertible_2cell (pr2 f₁) (pr1 y · pr2 f₂))
    : cod_disp_adj_equiv_to_adj_equiv
        (cod_adj_equiv_to_disp_adj_equiv e)
      =
      e.
  Proof.
    use total2_paths_f.
    - simpl.
      use subtypePath.
      {
        intro ; apply isaprop_left_adjoint_equivalence.
        exact HB_2_1.
      }
      apply idpath.
    - unfold subtypePath.
      etrans.
      {
        apply (transportf_total2_paths_f (λ x, invertible_2cell (pr2 f₁) (x · pr2 f₂))).
      }
      cbn.
      use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      cbn.
      rewrite vassocr.
      rewrite rinvunitor_runitor.
      apply id2_left.
  Qed.

  Definition cod_disp_adj_to_adj_to_disp
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
             (e : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity c)
                    f₁ f₂)
    : cod_adj_equiv_to_disp_adj_equiv
        (cod_disp_adj_equiv_to_adj_equiv e)
      =
      e.
  Proof.
    use subtypePath.
    {
      intro.
      use isaprop_disp_left_adjoint_equivalence.
      - exact HB_2_1.
      - apply cod_disp_univalent_2_1.
        exact HB_2_1.
    }
    cbn.
    unfold cod_adj_equiv_to_disp_adj_equiv_map, make_disp_1cell_cod.
    use maponpaths.
    use subtypePath.
    {
      intro ; apply isaprop_is_invertible_2cell.
    }
    cbn.
    rewrite vassocr.
    rewrite runitor_rinvunitor.
    apply id2_left.
  Qed.

  Definition cod_adj_equiv_weq_disp_adj_equiv
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             (f₁ f₂ : cod_disp_bicat B c)
    : (∑ y : adjoint_equivalence (pr1 f₁) (pr1 f₂),
             invertible_2cell (pr2 f₁) (pr1 y · pr2 f₂))
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂.
  Proof.
    use make_weq.
    - exact cod_adj_equiv_to_disp_adj_equiv.
    - use isweq_iso.
      + exact cod_disp_adj_equiv_to_adj_equiv.
      + exact (cod_adj_equiv_to_disp_to_adj HB_2_1).
      + exact (cod_disp_adj_to_adj_to_disp HB_2_1).
  Defined.

  Definition cod_disp_univalent_2_0
             (HB_2 : is_univalent_2 B)
    : disp_univalent_2_0 (cod_disp_bicat B).
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros c f₁ f₂.
    use weqhomot.
    - exact (cod_adj_equiv_weq_disp_adj_equiv (pr2 HB_2) f₁ f₂
             ∘ weqtotal2 (make_weq _ (pr1 HB_2 _ _)) (cod_1cell_path (pr2 HB_2) f₁ f₂)
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use isaprop_disp_left_adjoint_equivalence.
        - exact (pr2 HB_2).
        - apply cod_disp_univalent_2_1.
          exact (pr2 HB_2).
      }
      cbn ; unfold cod_adj_equiv_to_disp_adj_equiv_map, make_disp_1cell_cod ; cbn.
      apply maponpaths.
      use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      cbn.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition cod_disp_univalent_2
             (HB_2 : is_univalent_2 B)
    : disp_univalent_2 (cod_disp_bicat B).
  Proof.
    split.
    - exact (cod_disp_univalent_2_0 HB_2).
    - exact (cod_disp_univalent_2_1 (pr2 HB_2)).
  Defined.
End UnivalenceOfCodomain.
