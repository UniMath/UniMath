(*******************************************************************************

 Cartesian  objects

 We define the notions of cartesian objects internal to
 arbitrary bicategories. To define this notion, we use two steps. We first
 define objects 'with terminal objects' and objects 'with products'.

 Each of these concepts can be defined in 2 ways. We can use a representable
 variation or we use adjunctions. This is similar for categories: we can
 define whether a category has limits/colimits by saying that a certain functor
 has a right or a left adjoint.

 Contents
 1. The representable definition of cartesian objects
 2. Being cartesian is a proposition
 3. The definitions of cartesian objects via adjunctions
 4. Equivalence of the two definitions of cartesian object

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.

Local Open Scope cat.

(**
 1. The representable definition of cartesian objects
 *)
Definition cartesian_terminal
           {B : bicat}
           (b : B)
  : UU
  := (∏ (x : B), Terminal (hom x b))
     ×
     (∏ (x y : B) (f : x --> y), preserves_terminal (pre_comp b f)).

Definition cartesian_prod
           {B : bicat}
           (b : B)
  : UU
  := (∏ (x : B), BinProducts (hom x b))
     ×
     (∏ (x y : B) (f : x --> y), preserves_binproduct (pre_comp b f)).

Definition cartesian_ob
           {B : bicat}
           (b : B)
  : UU
  := cartesian_terminal b × cartesian_prod b.

(**
 2. Being cartesian is a proposition
 *)
Definition isaprop_cartesian_terminal
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cartesian_terminal b).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isaprop_Terminal.
    apply is_univ_hom.
    exact HB.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_terminal.
Qed.

Definition isaprop_cartesian_prod
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cartesian_prod b).
Proof.
  use isapropdirprod.
  - do 3 (use impred ; intro).
    apply isaprop_BinProduct.
    apply is_univ_hom.
    exact HB.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_binproduct.
Qed.

Definition isaprop_cartesian_ob
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cartesian_ob b).
Proof.
  use isapropdirprod.
  - apply isaprop_cartesian_terminal.
    exact HB.
  - apply isaprop_cartesian_prod.
    exact HB.
Qed.

(**
 3. The definitions of cartesian objects via adjunctions
 *)
Section CartesianViaAdjunction.
  Context {B : bicat}
          (b : B).

  Section Terminal.
    Context (T : bifinal_obj B).

    Let f : b --> pr1 T
      := is_bifinal_1cell_property (pr2 T) b.

    Definition cartesian_terminal_via_adj
      : UU
      := left_adjoint f.

    Definition isaprop_cartesian_terminal_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cartesian_terminal_via_adj.
    Proof.
      apply isaprop_left_adjoint.
      exact HB.
    Qed.
  End Terminal.

  Section Prod.
    Context (prod : has_binprod B).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).

    Definition cartesian_prod_via_adj
      : UU
      := left_adjoint δ.

    Definition isaprop_cartesian_prod_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cartesian_prod_via_adj.
    Proof.
      apply isaprop_left_adjoint.
      exact HB.
    Qed.
  End Prod.

  Section Cartesian.
    Context (T : bifinal_obj B)
            (prod : has_binprod B).

    Definition cartesian_ob_via_adj
      : UU
      := cartesian_terminal_via_adj T × cartesian_prod_via_adj prod.

    Definition isaprop_cartesian_ob_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cartesian_ob_via_adj.
    Proof.
      apply isapropdirprod.
      - apply isaprop_cartesian_terminal_via_adj.
        exact HB.
      - apply isaprop_cartesian_prod_via_adj.
        exact HB.
    Qed.
  End Cartesian.
End CartesianViaAdjunction.

(**
4. Equivalence of the two definitions of cartesian object
 *)
Section EquivalenceCartesian.
  Context {B : bicat}
          (T : bifinal_obj B)
          (prod : has_binprod B)
          (b : B).

  Section ToAdj.
    Context (Hb : cartesian_terminal b).

    Let term : Terminal (hom (pr1 T) b) := pr1 Hb (pr1 T).

    Let l : b --> pr1 T := is_bifinal_1cell_property (pr2 T) b.
    Let r : pr1 T --> b := pr1 term.

    Local Definition cartesian_terminal_to_cartesian_terminal_via_adj_unit
      : id₁ b ==> l · r
      := TerminalArrow (_ ,, pr2 Hb _ _ l _ (pr2 term)) (id₁ b).

    Let η : id₁ b ==> l · r
      := cartesian_terminal_to_cartesian_terminal_via_adj_unit.

    Local Definition cartesian_terminal_to_cartesian_terminal_via_adj_counit
      : r · l ==> id₁ (pr1 T)
      := is_bifinal_2cell_property (pr2 T) (pr1 T) (r · l) (id₁ (pr1 T)).

    Let ε : r · l ==> id₁ (pr1 T)
      := cartesian_terminal_to_cartesian_terminal_via_adj_counit.

    Definition cartesian_terminal_to_cartesian_terminal_via_adj
      : cartesian_terminal_via_adj b T.
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact r.
      - exact η.
      - exact ε.
      - apply (is_bifinal_eq_property (pr2 T)).
      - apply (@TerminalArrowEq _ term).
    Defined.
  End ToAdj.

  Section FromAdj.
    Context (Hb : cartesian_terminal_via_adj b T).

    Let l : b --> pr1 T := is_bifinal_1cell_property (pr2 T) b.
    Let r : pr1 T --> b := left_adjoint_right_adjoint (pr1 Hb).
    Let η : id₁ b ==> l · r := left_adjoint_unit (pr1 Hb).
    Let ε : r · l ==> id₁ (pr1 T) := left_adjoint_counit (pr1 Hb).
    Let p
      : rinvunitor r • (r ◃ η) • lassociator r l r • (ε ▹ r) • lunitor r
        =
        id₂ r
      := internal_triangle2 (pr2 Hb).

    Definition cartesian_terminal_via_adj_to_cartesian_terminal_1cell
               (x : B)
      : x --> b
      := is_bifinal_1cell_property (pr2 T) x · r.

    Definition cartesian_terminal_via_adj_to_cartesian_terminal_2cell
               (x : B)
               (f : x --> b)
      : f ==> cartesian_terminal_via_adj_to_cartesian_terminal_1cell x
      := rinvunitor _
         • (_ ◃ η)
         • lassociator _ _ _
         • (is_bifinal_2cell_property (pr2 T) _ _ _ ▹ r).

    Definition cartesian_terminal_via_adj_to_cartesian_terminal_eq
               (x : B)
               (f : x --> b)
      : isaprop (f ==> cartesian_terminal_via_adj_to_cartesian_terminal_1cell x).
    Proof.
      use invproofirrelevance.
      intros α β.
      refine (!(id2_right _) @ _ @ id2_right _).
      unfold cartesian_terminal_via_adj_to_cartesian_terminal_1cell.
      rewrite <- lwhisker_id2.
      rewrite <- p.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !left_unit_inv_assoc.
      rewrite !vassocr.
      rewrite !rinvunitor_natural.
      rewrite <- !rwhisker_hcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite !lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      rewrite !vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite !lwhisker_hcomp.
      rewrite inverse_pentagon_4.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
      rewrite !vassocr.
      rewrite <- !rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      apply maponpaths.
      apply (is_bifinal_eq_property (pr2 T)).
    Qed.

    Definition cartesian_terminal_via_adj_to_cartesian_terminal_obj
               (x : B)
      : Terminal (hom x b).
    Proof.
      use make_Terminal.
      - exact (cartesian_terminal_via_adj_to_cartesian_terminal_1cell x).
      - intro f.
        use iscontraprop1.
        + exact (cartesian_terminal_via_adj_to_cartesian_terminal_eq x f).
        + exact (cartesian_terminal_via_adj_to_cartesian_terminal_2cell x f).
    Defined.

    Definition cartesian_terminal_via_adj_to_cartesian_terminal_preserves
               {x y : B}
               (f : x --> y)
      : preserves_terminal (pre_comp b f).
    Proof.
      use preserves_terminal_if_preserves_chosen.
      - apply cartesian_terminal_via_adj_to_cartesian_terminal_obj.
      - use (iso_to_Terminal
               (cartesian_terminal_via_adj_to_cartesian_terminal_obj x)).
        use inv2cell_to_z_iso.
        refine (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     _)
                  (rassociator_invertible_2cell _ _ _)).
        apply (is_bifinal_invertible_2cell_property (pr2 T)).
    Defined.

    Definition cartesian_terminal_via_adj_to_cartesian_terminal
      : cartesian_terminal b.
    Proof.
      split.
      - exact cartesian_terminal_via_adj_to_cartesian_terminal_obj.
      - exact @cartesian_terminal_via_adj_to_cartesian_terminal_preserves.
    Defined.
  End FromAdj.

  Definition cartesian_terminal_weq_cartesian_terminal_via_adj
             (HB : is_univalent_2_1 B)
    : cartesian_terminal b ≃ cartesian_terminal_via_adj b T.
  Proof.
    use weqimplimpl.
    - exact cartesian_terminal_to_cartesian_terminal_via_adj.
    - exact cartesian_terminal_via_adj_to_cartesian_terminal.
    - apply isaprop_cartesian_terminal.
      exact HB.
    - apply isaprop_cartesian_terminal_via_adj.
      exact HB.
  Defined.

  Section ToAdj.
    Context (Hb : cartesian_prod b).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).

    Let product
      : BinProduct
          (hom (pr1 (prod b b)) b)
          (binprod_cone_pr1 (pr1 (prod b b)))
          (binprod_cone_pr2 (pr1 (prod b b)))
      := pr1 Hb (pr1 (prod b b))
                (binprod_cone_pr1 (pr1 (prod b b)))
                (binprod_cone_pr2 (pr1 (prod b b))).

    Let r : pr1 (prod b b) --> b
      := BinProductObject _ product.

    Local Definition cartesian_prod_to_cartesian_prod_via_adj_unit
      : id₁ b ==> δ · r.
    Proof.
      use (BinProductArrow
             _
             (make_BinProduct
                _ _ _ _ _ _
                (pr2 Hb _ _ δ _ _ _ _ _ (pr2 product)))).
      - exact ((binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1).
      - exact ((binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1).
    Defined.

    Let η : id₁ b ==> δ · r
      := cartesian_prod_to_cartesian_prod_via_adj_unit.

    Local Definition cartesian_prod_to_cartesian_prod_via_adj_counit
      : r · δ ==> id₁ _.
    Proof.
      use (binprod_ump_2cell (pr2 (prod b b))).
      - exact (rassociator _ _ _
               • (r ◃ binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b))
               • runitor _
               • BinProductPr1 _ product
               • linvunitor _).
      - exact (rassociator _ _ _
               • (r ◃ binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b))
               • runitor _
               • BinProductPr2 _ product
               • linvunitor _).
    Defined.

    Let ε : r · δ ==> id₁ _
      := cartesian_prod_to_cartesian_prod_via_adj_counit.

    Local Lemma cartesian_prod_to_cartesian_prod_via_adj_triangle1
      : linvunitor δ • (η ▹ δ) • rassociator δ r δ • (δ ◃ ε) • runitor δ
        =
        id₂ δ.
    Proof.
      use (binprod_ump_2cell_unique_alt (pr2 (prod b b))).
      - rewrite id2_rwhisker.
        rewrite <- !rwhisker_vcomp.
        rewrite <- lunitor_lwhisker.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          rewrite lwhisker_vcomp.
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply binprod_ump_2cell_pr1.
          }
          rewrite !vassocl.
          rewrite linvunitor_lunitor.
          rewrite id2_right.
          apply idpath.
        }
        rewrite <- !lwhisker_vcomp.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_lwhisker_rassociator.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite runitor_triangle.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite vcomp_runitor.
          rewrite !vassocl.
          apply maponpaths.
          apply (BinProductPr1Commutes
                   _ _ _
                   (make_BinProduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 product)))).
        }
        etrans.
        {
          rewrite !vassocr.
          rewrite <- linvunitor_assoc.
          rewrite lwhisker_hcomp.
          rewrite <- linvunitor_natural.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite runitor_lunitor_identity.
            rewrite linvunitor_lunitor.
            apply id2_left.
          }
          apply vcomp_rinv.
        }
        apply idpath.
      - rewrite id2_rwhisker.
        rewrite <- !rwhisker_vcomp.
        rewrite <- lunitor_lwhisker.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          rewrite lwhisker_vcomp.
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply binprod_ump_2cell_pr2.
          }
          rewrite !vassocl.
          rewrite linvunitor_lunitor.
          rewrite id2_right.
          apply idpath.
        }
        rewrite <- !lwhisker_vcomp.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_lwhisker_rassociator.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite runitor_triangle.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite vcomp_runitor.
          rewrite !vassocl.
          apply maponpaths.
          apply (BinProductPr2Commutes
                   _ _ _
                   (make_BinProduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 product)))).
        }
        etrans.
        {
          rewrite !vassocr.
          rewrite <- linvunitor_assoc.
          rewrite lwhisker_hcomp.
          rewrite <- linvunitor_natural.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite runitor_lunitor_identity.
            rewrite linvunitor_lunitor.
            apply id2_left.
          }
          apply vcomp_rinv.
        }
        apply idpath.
    Qed.

    Local Lemma cartesian_prod_to_cartesian_prod_via_adj_triangle2
      : rinvunitor r • (r ◃ η) • lassociator r δ r • (ε ▹ r) • lunitor r
        =
        id₂ r.
    Proof.
      use (BinProductArrowsEq _ _ _ (product)) ; cbn.
      - rewrite !vassocl.
        rewrite id2_left.
        rewrite <- vcomp_lunitor.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite lwhisker_vcomp.
          apply maponpaths.
          apply (BinProductPr1Commutes
                   _ _ _
                   (make_BinProduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 product)))).
        }
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite lwhisker_id2.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rinvunitor_runitor.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite linvunitor_lunitor.
        apply id2_right.
      - rewrite !vassocl.
        rewrite id2_left.
        rewrite <- vcomp_lunitor.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite lwhisker_vcomp.
          apply maponpaths.
          apply (BinProductPr2Commutes
                   _ _ _
                   (make_BinProduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 product)))).
        }
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite lwhisker_id2.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rinvunitor_runitor.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite linvunitor_lunitor.
        apply id2_right.
    Qed.

    Definition cartesian_prod_to_cartesian_prod_via_adj
      : cartesian_prod_via_adj b prod.
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact r.
      - exact η.
      - exact ε.
      - exact cartesian_prod_to_cartesian_prod_via_adj_triangle1.
      - exact cartesian_prod_to_cartesian_prod_via_adj_triangle2.
    Defined.
  End ToAdj.

  Section FromAdj.
    Context (Hb : cartesian_prod_via_adj b prod).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).
    Let r : pr1 (prod b b) --> b := left_adjoint_right_adjoint (pr1 Hb).
    Let η : id₁ b ==> δ · r := left_adjoint_unit (pr1 Hb).
    Let ε : r · δ ==> id₁ _ := left_adjoint_counit (pr1 Hb).
    Let p
      : rinvunitor r • (r ◃ η) • lassociator r δ r • (ε ▹ r) • lunitor r
        =
        id₂ r
      := internal_triangle2 (pr2 Hb).

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_1cell
                     {x : B}
                     (f g : x --> b)
      : x --> b
      := binprod_ump_1cell (pr2 (prod b b)) f g · r.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_pr1_help
      : r ==> binprod_cone_pr1 (pr1 (prod b b))
      := rinvunitor _
         • (r ◃ (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1)
         • lassociator _ _ _
         • (ε ▹ _)
         • lunitor _.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_pr1
                     {x : B}
                     (f g : x --> b)
      : cartesian_prod_via_adj_to_cartesian_prod_1cell f g ==> f
      := (_ ◃ cartesian_prod_via_adj_to_cartesian_prod_pr1_help)
         • binprod_ump_1cell_pr1 (pr2 (prod b b)) _ f g.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_pr2_help
      : r ==> binprod_cone_pr2 (pr1 (prod b b))
      := rinvunitor _
         • (r ◃ (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1)
         • lassociator _ _ _
         • (ε ▹ _)
         • lunitor _.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_pr2
                     {x : B}
                     (f g : x --> b)
      : cartesian_prod_via_adj_to_cartesian_prod_1cell f g ==> g
      := (_ ◃ cartesian_prod_via_adj_to_cartesian_prod_pr2_help)
         • binprod_ump_1cell_pr2 (pr2 (prod b b)) _ f g.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_2cell
                     {x : B}
                     {f g k : x --> b}
                     (α : k ==> f)
                     (β : k ==> g)
      : k ==> cartesian_prod_via_adj_to_cartesian_prod_1cell f g.
    Proof.
      refine (rinvunitor _
              • (_ ◃ η)
              • lassociator _ _ _
              • (binprod_ump_2cell (pr2 (prod b b)) _ _ ▹ r)).
      - exact (rassociator _ _ _
               • (k ◃ binprod_ump_1cell_pr1 (pr2 (prod b b)) _ _ _)
               • runitor _
               • α
               • (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ _ _)^-1).
      - exact (rassociator _ _ _
               • (k ◃ binprod_ump_1cell_pr2 (pr2 (prod b b)) _ _ _)
               • runitor _
               • β
               • (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ _ _)^-1).
    Defined.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_2cell_pr1
                     {x : B}
                     {f g k : x --> b}
                     (α : k ==> f)
                     (β : k ==> g)
      : cartesian_prod_via_adj_to_cartesian_prod_2cell α β
        • cartesian_prod_via_adj_to_cartesian_prod_pr1 f g
        =
        α.
    Proof.
      unfold cartesian_prod_via_adj_to_cartesian_prod_2cell.
      unfold cartesian_prod_via_adj_to_cartesian_prod_pr1.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        refine (vcomp_whisker _ _ @ _).
        apply maponpaths.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      refine (_ @ lwhisker_id2 _ _).
      apply maponpaths.
      unfold cartesian_prod_via_adj_to_cartesian_prod_pr1_help.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite left_unit_inv_assoc.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite lwhisker_hcomp.
          rewrite inverse_pentagon_4.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- lunitor_V_id_is_left_unit_V_id.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (pr12 Hb).
    Qed.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_2cell_pr2
                     {x : B}
                     {f g k : x --> b}
                     (α : k ==> f)
                     (β : k ==> g)
      : cartesian_prod_via_adj_to_cartesian_prod_2cell α β
        • cartesian_prod_via_adj_to_cartesian_prod_pr2 f g
        =
        β.
    Proof.
      unfold cartesian_prod_via_adj_to_cartesian_prod_2cell.
      unfold cartesian_prod_via_adj_to_cartesian_prod_pr2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        refine (vcomp_whisker _ _ @ _).
        apply maponpaths.
        apply binprod_ump_2cell_pr2.
      }
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      refine (_ @ lwhisker_id2 _ _).
      apply maponpaths.
      unfold cartesian_prod_via_adj_to_cartesian_prod_pr2_help.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite left_unit_inv_assoc.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite lwhisker_hcomp.
          rewrite inverse_pentagon_4.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- lunitor_V_id_is_left_unit_V_id.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (pr12 Hb).
    Qed.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_eq
                     {x : B}
                     {f g k : x --> b}
                     (α : k ==> f)
                     (β : k ==> g)
                     (φ : ∑ (fg : k ==> cartesian_prod_via_adj_to_cartesian_prod_1cell f g),
                          fg • cartesian_prod_via_adj_to_cartesian_prod_pr1 f g = α
                          ×
                          fg • cartesian_prod_via_adj_to_cartesian_prod_pr2 f g = β)
      : φ
        =
        cartesian_prod_via_adj_to_cartesian_prod_2cell α β
        ,,
        cartesian_prod_via_adj_to_cartesian_prod_2cell_pr1 α β
        ,,
        cartesian_prod_via_adj_to_cartesian_prod_2cell_pr2 α β.
    Proof.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      cbn.
      refine (!(id2_right _) @ _).
      unfold cartesian_prod_via_adj_to_cartesian_prod_1cell.
      rewrite <- lwhisker_id2.
      rewrite <- p.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !left_unit_inv_assoc.
      rewrite !vassocr.
      rewrite !rinvunitor_natural.
      rewrite <- !rwhisker_hcomp.
      unfold cartesian_prod_via_adj_to_cartesian_prod_2cell.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite !lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      rewrite !vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite !lwhisker_hcomp.
      rewrite inverse_pentagon_4.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
      rewrite !vassocr.
      rewrite <- !rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      use (binprod_ump_2cell_unique_alt (pr2 (prod b b))).
      - rewrite binprod_ump_2cell_pr1.
        rewrite <- !rwhisker_vcomp.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ; cbn.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite !vassocl.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        refine (_ @ pr12 φ).
        unfold cartesian_prod_via_adj_to_cartesian_prod_pr1 ; cbn.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        unfold cartesian_prod_via_adj_to_cartesian_prod_pr1_help.
        rewrite !vassocl.
        rewrite <- rinvunitor_triangle.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite lassociator_rassociator.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        apply runitor_rwhisker.
      - rewrite binprod_ump_2cell_pr2.
        rewrite <- !rwhisker_vcomp.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ; cbn.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite !vassocl.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        refine (_ @ pr22 φ).
        unfold cartesian_prod_via_adj_to_cartesian_prod_pr2 ; cbn.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        unfold cartesian_prod_via_adj_to_cartesian_prod_pr2_help.
        rewrite !vassocl.
        rewrite <- rinvunitor_triangle.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite lassociator_rassociator.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        apply runitor_rwhisker.
    Qed.

    Local Definition cartesian_prod_via_adj_to_cartesian_prod_obj
                     (x : B)
      : BinProducts (hom x b).
    Proof.
      intros f g.
      use make_BinProduct.
      - exact (cartesian_prod_via_adj_to_cartesian_prod_1cell f g).
      - exact (cartesian_prod_via_adj_to_cartesian_prod_pr1 f g).
      - exact (cartesian_prod_via_adj_to_cartesian_prod_pr2 f g).
      - intros k α β.
        use make_iscontr.
        + simple refine (_ ,, (_ ,, _)).
          * exact (cartesian_prod_via_adj_to_cartesian_prod_2cell α β).
          * exact (cartesian_prod_via_adj_to_cartesian_prod_2cell_pr1 α β).
          * exact (cartesian_prod_via_adj_to_cartesian_prod_2cell_pr2 α β).
        + apply cartesian_prod_via_adj_to_cartesian_prod_eq.
    Defined.

    Local Definition help_inv2cell
                     {x y : B}
                     (f : x --> y)
                     (h₁ h₂ : y --> b)
      : invertible_2cell
          (f
           · BinProductObject
               (hom y b)
               (cartesian_prod_via_adj_to_cartesian_prod_obj y h₁ h₂))
          (BinProductObject
             (hom x b)
             (cartesian_prod_via_adj_to_cartesian_prod_obj x (f · h₁) (f · h₂))).
    Proof.
      refine (comp_of_invertible_2cell
                (lassociator_invertible_2cell _ _ _)
                (rwhisker_of_invertible_2cell
                   _
                   _)).
      use make_invertible_2cell.
      - use (binprod_ump_2cell (pr2 (prod b b))).
        + exact (rassociator _ _ _
                 • (_ ◃ binprod_ump_1cell_pr1 (pr2 (prod b b)) _ h₁ h₂)
                 • (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ _ _)^-1).
        + exact (rassociator _ _ _
                 • (_ ◃ binprod_ump_1cell_pr2 (pr2 (prod b b)) _ h₁ h₂)
                 • (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ _ _)^-1).
      - use binprod_ump_2cell_invertible.
        + is_iso.
          apply property_from_invertible_2cell.
        + is_iso.
          apply property_from_invertible_2cell.
    Defined.

    Definition cartesian_prod_via_adj_to_cartesian_prod_preserves
               {x y : B}
               (f : x --> y)
      : preserves_binproduct (pre_comp b f).
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      - apply cartesian_prod_via_adj_to_cartesian_prod_obj.
      - intros h₁ h₂.
        use (isBinProduct_eq_arrow
               _ _
               (pr2 (iso_to_BinProduct
                       _
                       (cartesian_prod_via_adj_to_cartesian_prod_obj x (f · h₁) (f · h₂))
                       (z_iso_to_iso
                          (inv2cell_to_z_iso
                             (help_inv2cell f h₁ h₂)))))).
        + cbn.
          unfold cartesian_prod_via_adj_to_cartesian_prod_pr1.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            etrans.
            {
              apply maponpaths_2.
              apply vcomp_whisker.
            }
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply binprod_ump_2cell_pr1.
            }
            rewrite !vassocl.
            rewrite vcomp_linv.
            rewrite id2_right.
            apply idpath.
          }
          rewrite !vassocr.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply lwhisker_lwhisker.
          }
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            apply id2_left.
          }
          apply lwhisker_vcomp.
        + cbn.
          unfold cartesian_prod_via_adj_to_cartesian_prod_pr2.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            etrans.
            {
              apply maponpaths_2.
              apply vcomp_whisker.
            }
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply binprod_ump_2cell_pr2.
            }
            rewrite !vassocl.
            rewrite vcomp_linv.
            rewrite id2_right.
            apply idpath.
          }
          rewrite !vassocr.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply lwhisker_lwhisker.
          }
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            apply id2_left.
          }
          apply lwhisker_vcomp.
    Qed.

    Definition cartesian_prod_via_adj_to_cartesian_prod
      : cartesian_prod b.
    Proof.
      split.
      - exact cartesian_prod_via_adj_to_cartesian_prod_obj.
      - exact @cartesian_prod_via_adj_to_cartesian_prod_preserves.
    Defined.
  End FromAdj.

  Definition cartesian_prod_weq_cartesian_prod_via_adj
             (HB : is_univalent_2_1 B)
    : cartesian_prod b ≃ cartesian_prod_via_adj b prod.
  Proof.
    use weqimplimpl.
    - exact cartesian_prod_to_cartesian_prod_via_adj.
    - exact cartesian_prod_via_adj_to_cartesian_prod.
    - apply isaprop_cartesian_prod.
      exact HB.
    - apply isaprop_cartesian_prod_via_adj.
      exact HB.
  Defined.

  Definition cartesian_weq_cartesian_via_adj
             (HB : is_univalent_2_1 B)
    : cartesian_ob b ≃ cartesian_ob_via_adj b T prod.
  Proof.
    use weqdirprodf.
    - exact (cartesian_terminal_weq_cartesian_terminal_via_adj HB).
    - exact (cartesian_prod_weq_cartesian_prod_via_adj HB).
  Defined.
End EquivalenceCartesian.
