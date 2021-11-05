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
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section CodomainArrow.
  Variable (B : bicat).

  Definition cod_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells (prod_bicat B B).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ X, pr2 X --> pr1 X).
        * exact (λ X Y fX fY f, fX · pr1 f ==> pr2 f · fY).
      + use tpair.
        * exact (λ X fX, runitor _ • linvunitor _).
        * exact (λ X Y Z f g fX fY fZ ff fg,
                 lassociator _ _ _
                 • (ff ▹ _)
                 • rassociator _ _ _
                 • (_ ◃ fg)
                 • lassociator _ _ _).
    - exact (λ X Y f g α fX fY ff fg,
             ff • (pr2 α ▹ _)
             =
             (_ ◃ pr1 α) • fg).
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
           (p : pr2 dX · f ==> h · pr2 dY)
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
  := pr2 df • (h ▹ pr2 dY)
     =
     (pr2 dX ◃ α) • pr2 dg.

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

Definition disp_locally_groupoid_cod
           (B : bicat)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
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


(*
Section UnivalenceOfCodomain.
  Context (B : bicat).

  Definition cod_univalent_2_1
             (HB_2_1 : is_univalent_2_1 B)
    : is_univalent_2_1 (total_bicat (cod_disp_bicat B)).
  Proof.
    use sigma_is_univalent_2_1.
    - exact HB_2_1.
    - use trivial_is_univalent_2_1.
      exact HB_2_1.
    - admit.
  Admitted.


  Definition cod_univalent_2_0
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
    : is_univalent_2_0 (total_bicat (cod_disp_bicat B)).
  Proof.
    use sigma_is_univalent_2_0.
    - split.
      + exact HB_2_0.
      + exact HB_2_1.
    - split.
      + use trivial_is_univalent_2_0.
        * exact HB_2_1.
        * exact HB_2_0.
        * exact HB_2_1.
      + use trivial_is_univalent_2_1.
        exact HB_2_1.
    - split.
      + admit.
      + admit.
  Admitted.
End UnivalenceOfCodomain.
 *)


(** MOVE ??? *)
Definition transportf_total2_paths_f
           {A : UU}
           {B : A → UU}
           (C : A → UU)
           {a₁ a₂ : A}
           {b₁ : B a₁}
           {b₂ : B a₂}
           (p : a₁ = a₂)
           (q : transportf B p b₁ = b₂)
           (c₁ : C a₁)
  : transportf
      (λ z, C (pr1 z))
      (@total2_paths_f
         A B
         (a₁ ,, b₁) (a₂ ,, b₂)
         p
         q)
      c₁
    =
    transportf
      C
      p
      c₁.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.


Section UnivalenceOfCodomain.
  Context (B : bicat)
          (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                   is_invertible_2cell x).

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
    - apply disp_locally_groupoid_cod.
      exact inv_B.
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
    - apply inv_B.
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
    - use gradth.
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
    : (transportf (λ x, pr2 φ₁ · f ==> x · pr2 φ₂) p (pr2 ψ₁) = pr2 ψ₂)
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
    apply idweq.
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

  Definition cod_1cell_path_help
             {b c : B}
             (f₁ f₂ : B ⟦ b , c ⟧)
    : invertible_2cell f₁ f₂ ≃ f₁ ==> id₁ _ · f₂.
  Proof.
    use make_weq.
    - intro α.
      exact (α • linvunitor _).
    - use gradth.
      + intro α.
        use make_invertible_2cell.
        * exact (α • lunitor _).
        * apply inv_B.
      + abstract
          (intro p ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite vassocl ;
           rewrite linvunitor_lunitor ;
           apply id2_right).
      + abstract
          (intros α ; cbn ;
           rewrite vassocl ;
           rewrite lunitor_linvunitor ;
           apply id2_right).
  Defined.

  Definition cod_1cell_path
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             (f₁ f₂ : cod_disp_bicat B c)
             (p : pr1 f₁ = pr1 f₂)
    : (transportf (λ b, B ⟦ b, c ⟧) p (pr2 f₁) = pr2 f₂)
      ≃
      pr2 f₁ ==> idtoiso_2_0 _ _ p · pr2 f₂.
  Proof.
    induction f₁ as [ c₁ f₁ ].
    induction f₂ as [ c₂ f₂ ].
    cbn in *.
    induction p.
    exact (cod_1cell_path_help f₁ f₂ ∘ make_weq _ (HB_2_1 _ _ _ _))%weq.
  Defined.

  Definition TODO {A : UU} : A.
  Admitted.

  Definition cod_adj_equiv_to_disp_adj_equiv
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
    : (∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)), pr2 f₁ ==> pr1 y · pr2 f₂)
      →
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂.
  Proof.
    intro e.
    induction e as [ e α ].
    simple refine (_ ,, _).
    - use make_disp_1cell_cod.
      + exact (pr1 e).
      + exact (runitor _ • α).
    - simpl.
      simple refine (_ ,, (_ ,, _)).
      + simple refine (_ ,, (_ ,, _)).
        * use make_disp_1cell_cod.
          ** exact (pr112 e).
          ** simpl.
             refine (_ • (_ ◃ (inv_B _ _ _ _ α)^-1)).
             refine (_ • rassociator _ _ _).
             refine (_ • ((inv_B _ _ _ _ (pr2 (pr212 e)))^-1 ▹ _)).
             exact (runitor _ • linvunitor _).
        * use make_disp_2cell_cod.
          ** exact (pr1 (pr212 e)).
          ** cbn.
             apply TODO.
        * use make_disp_2cell_cod.
          ** exact (pr2 (pr212 e)).
          ** cbn.
             unfold coherent_homot.
             cbn.
             rewrite !vassocl.
             apply TODO.
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             use subtypePath ; [ intro ; apply B | ] ;
             cbn ;
             etrans ; [ exact (pr1 (pr122 e)) | ] ;
             refine (!_) ;
             refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _) ;
             rewrite transportf_const ;
             apply idpath).
        * abstract
            (cbn ;
             use subtypePath ; [ intro ; apply B | ] ;
             cbn ;
             etrans ; [ exact (pr2 (pr122 e)) | ] ;
             refine (!_) ;
             refine (@pr1_transportf _ (λ _, _) _ _ _ _ _ @ _) ;
             rewrite transportf_const ;
             apply idpath).
      + simple refine (_ ,, _).
        * abstract
            (apply disp_locally_groupoid_cod ;
             exact inv_B).
        * abstract
            (apply disp_locally_groupoid_cod ;
             exact inv_B).
  Defined.

  Definition cod_disp_adj_equiv_to_adj_equiv
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂
      →
      ∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)), pr2 f₁ ==> pr1 y · pr2 f₂.
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
        * split ; apply inv_B.
    - exact (rinvunitor _ • pr21 e).
  Defined.

  Definition cod_adj_equiv_to_disp_to_adj
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             {f₁ f₂ : cod_disp_bicat B c}
             (e : ∑ (y : adjoint_equivalence (pr1 f₁) (pr1 f₂)),
                  pr2 f₁ ==> pr1 y · pr2 f₂)
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
        apply (transportf_total2_paths_f (λ x, pr2 f₁ ==> x · pr2 f₂)).
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
    unfold make_disp_1cell_cod.
    use maponpaths.
    rewrite vassocr.
    rewrite runitor_rinvunitor.
    apply id2_left.
  Qed.

  Definition cod_adj_equiv_weq_disp_adj_equiv
             (HB_2_1 : is_univalent_2_1 B)
             {c : B}
             (f₁ f₂ : cod_disp_bicat B c)
    : (∑ y : adjoint_equivalence (pr1 f₁) (pr1 f₂), pr2 f₁ ==> pr1 y · pr2 f₂)
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity c) f₁ f₂.
  Proof.
    use make_weq.
    - exact cod_adj_equiv_to_disp_adj_equiv.
    - use gradth.
      + exact cod_disp_adj_equiv_to_adj_equiv.
      + exact (cod_adj_equiv_to_disp_to_adj HB_2_1).
      + exact (cod_disp_adj_to_adj_to_disp HB_2_1).
  Defined.

  Definition cod_disp_univalent_2_0
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_0 (cod_disp_bicat B).
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros c f₁ f₂.
    use weqhomot.
    - refine (cod_adj_equiv_weq_disp_adj_equiv HB_2_1 f₁ f₂
             ∘ weqtotal2 (make_weq _ (HB_2_0 _ _)) (cod_1cell_path HB_2_1 f₁ f₂)
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use isaprop_disp_left_adjoint_equivalence.
        - exact HB_2_1.
        - apply cod_disp_univalent_2_1.
          exact HB_2_1.
      }
      cbn.
      unfold make_disp_1cell_cod.
      rewrite id2_left.
      apply idpath.
  Qed.
End UnivalenceOfCodomain.
