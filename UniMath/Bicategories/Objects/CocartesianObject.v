(*******************************************************************************

 Cocartesian objects

 We define the notions of cocartesian objects internal to arbitrary
 bicategories. This notion is defined dually to the notion of cartesian objects.
 For the representable definition, we work with initial objects and coproducts,
 and for the definition using adjunctions, we use left adjoints instead of right
 adjoints.

 Contents
 1. The representable definition of cocartesian objects
 2. Being cocartesian is a proposition
 3. The definitions of cocartesian objects via adjunctions
 4. Equivalence of the two definitions

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
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
 1. The representable definition of cocartesian objects
 *)
Definition cocartesian_initial
           {B : bicat}
           (b : B)
  : UU
  := (∏ (x : B), Initial (hom x b))
     ×
     (∏ (x y : B) (f : x --> y), preserves_initial (pre_comp b f)).

Definition cocartesian_coprod
           {B : bicat}
           (b : B)
  : UU
  := (∏ (x : B), BinCoproducts (hom x b))
     ×
     (∏ (x y : B) (f : x --> y), preserves_bincoproduct (pre_comp b f)).

Definition cocartesian_ob
           {B : bicat}
           (b : B)
  : UU
  := cocartesian_initial b × cocartesian_coprod b.

(**
 2. Being cocartesian is a proposition
 *)
Definition isaprop_cocartesian_initial
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cocartesian_initial b).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isaprop_Initial.
    apply is_univ_hom.
    exact HB.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_initial.
Qed.

Definition isaprop_cocartesian_coprod
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cocartesian_coprod b).
Proof.
  use isapropdirprod.
  - do 3 (use impred ; intro).
    apply isaprop_BinCoproduct.
    apply is_univ_hom.
    exact HB.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_bincoproduct.
Qed.

Definition isaprop_cocartesian_ob
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : isaprop (cocartesian_ob b).
Proof.
  use isapropdirprod.
  - apply isaprop_cocartesian_initial.
    exact HB.
  - apply isaprop_cocartesian_coprod.
    exact HB.
Qed.

(**
 3. The definitions of cocartesian objects via adjunctions
 *)
Section CocartesianViaAdjunction.
  Context {B : bicat}
          (b : B).

  Section TerminalAndInitial.
    Context (T : bifinal_obj B).

    Let f : b --> pr1 T
      := is_bifinal_1cell_property (pr2 T) b.

    Definition cocartesian_initial_via_adj
      : UU
      := internal_right_adj f.

    Definition isaprop_cocartesian_initial_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cocartesian_initial_via_adj.
    Proof.
      apply isaprop_internal_right_adj.
      exact HB.
    Qed.
  End TerminalAndInitial.

  Section ProdAndCoprod.
    Context (prod : has_binprod B).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).

    Definition cocartesian_coprod_via_adj
      : UU
      := internal_right_adj δ.

    Definition isaprop_cocartesian_coprod_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cocartesian_coprod_via_adj.
    Proof.
      apply isaprop_internal_right_adj.
      exact HB.
    Qed.
  End ProdAndCoprod.

  Section Cocartesian.
    Context (T : bifinal_obj B)
            (prod : has_binprod B).

    Definition cocartesian_ob_via_adj
      : UU
      := cocartesian_initial_via_adj T × cocartesian_coprod_via_adj prod.

    Definition isaprop_cocartesian_ob_via_adj
               (HB : is_univalent_2_1 B)
      : isaprop cocartesian_ob_via_adj.
    Proof.
      apply isapropdirprod.
      - apply isaprop_cocartesian_initial_via_adj.
        exact HB.
      - apply isaprop_cocartesian_coprod_via_adj.
        exact HB.
    Qed.
  End Cocartesian.
End CocartesianViaAdjunction.

(**
 4. Equivalence of the two definitions
 *)
Section EquivalenceCocartesian.
  Context {B : bicat}
          (T : bifinal_obj B)
          (prod : has_binprod B)
          (b : B).

  Section ToAdj.
    Context (Hb : cocartesian_initial b).

    Let init : Initial (hom (pr1 T) b) := pr1 Hb (pr1 T).

    Let l : b --> pr1 T := is_bifinal_1cell_property (pr2 T) b.
    Let r : pr1 T --> b := pr1 init.

    Local Definition cocartesian_initial_to_cocartesian_initial_via_adj_unit
      : id₁ (pr1 T) ==> r · l
      := is_bifinal_2cell_property (pr2 T) _ (id₁ _) (r · l).

    Let η : id₁ (pr1 T) ==> r · l
      := cocartesian_initial_to_cocartesian_initial_via_adj_unit.

    Local Definition cocartesian_initial_to_cocartesian_initial_via_adj_counit
      : l · r ==> id₁ b
      := InitialArrow (make_Initial _ (pr2 Hb _ _ l _ (pr2 init))) (id₁ b).

    Let ε : l · r ==> id₁ b
      := cocartesian_initial_to_cocartesian_initial_via_adj_counit.

    Definition cocartesian_initial_to_cocartesian_initial_via_adj
      : cocartesian_initial_via_adj b T.
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact r.
      - exact η.
      - exact ε.
      - apply (@InitialArrowEq _ init).
      - apply (is_bifinal_eq_property (pr2 T)).
    Defined.
  End ToAdj.

  Section FromAdj.
    Context (Hb : cocartesian_initial_via_adj b T).

    Let r : b --> pr1 T := is_bifinal_1cell_property (pr2 T) b.
    Let l : pr1 T --> b := pr11 Hb.
    Let η : id₁ (pr1 T) ==> l · r := pr121 Hb.
    Let ε : r · l ==> id₁ b := pr221 Hb.
    Let p
      : linvunitor l • (η ▹ l) • rassociator l r l • (l ◃ ε) • runitor l
        =
        id₂ l
        := pr12 Hb.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial_1cell
               (x : B)
      : x --> b
      := is_bifinal_1cell_property (pr2 T) x · l.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial_2cell
               (x : B)
               (f : x --> b)
      : cocartesian_initial_via_adj_to_cocartesian_initial_1cell x ==> f
      := (is_bifinal_2cell_property (pr2 T) _ _ _ ▹ l)
         • rassociator _ _ _
         • (_ ◃ ε)
         • runitor _.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial_eq
               (x : B)
               (f : x --> b)
      : isaprop (cocartesian_initial_via_adj_to_cocartesian_initial_1cell x ==> f).
    Proof.
      use invproofirrelevance.
      intros α β.
      refine (!(id2_left _) @ _ @ id2_left _).
      unfold cocartesian_initial_via_adj_to_cocartesian_initial_1cell.
      rewrite <- lwhisker_id2.
      rewrite <- p.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      assert (is_bifinal_1cell_property (pr2 T) x ◃ runitor l
              =
              lassociator _ _ _ • runitor (_ · _)) as q.
      {
        use vcomp_move_L_pM ; [ is_iso | ].
        apply runitor_triangle.
      }
      rewrite !q.
      rewrite !vassocl.
      rewrite <- !vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite !lwhisker_lwhisker.
      rewrite !vassocl.
      rewrite <- !vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite !lwhisker_hcomp.
      rewrite !inverse_pentagon_5.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
      rewrite !vassocl.
      rewrite <- !rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply (is_bifinal_eq_property (pr2 T)).
    Qed.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial_obj
               (x : B)
      : Initial (hom x b).
    Proof.
      use make_Initial.
      - exact (cocartesian_initial_via_adj_to_cocartesian_initial_1cell x).
      - intro f.
        use iscontraprop1.
        + exact (cocartesian_initial_via_adj_to_cocartesian_initial_eq x f).
        + exact (cocartesian_initial_via_adj_to_cocartesian_initial_2cell x f).
    Defined.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial_preserves
               {x y : B}
               (f : x --> y)
      : preserves_initial (pre_comp b f).
    Proof.
      use preserves_initial_if_preserves_chosen.
      - apply cocartesian_initial_via_adj_to_cocartesian_initial_obj.
      - use (iso_to_Initial
               (cocartesian_initial_via_adj_to_cocartesian_initial_obj x)).
        use inv2cell_to_z_iso.
        refine (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     _)
                  (rassociator_invertible_2cell _ _ _)).
        apply (is_bifinal_invertible_2cell_property (pr2 T)).
    Defined.

    Definition cocartesian_initial_via_adj_to_cocartesian_initial
      : cocartesian_initial b.
    Proof.
      split.
      - exact cocartesian_initial_via_adj_to_cocartesian_initial_obj.
      - exact @cocartesian_initial_via_adj_to_cocartesian_initial_preserves.
    Defined.
  End FromAdj.

  Definition cocartesian_initial_weq_cocartesian_initial_via_adj
             (HB : is_univalent_2_1 B)
    : cocartesian_initial b ≃ cocartesian_initial_via_adj b T.
  Proof.
    use weqimplimpl.
    - exact cocartesian_initial_to_cocartesian_initial_via_adj.
    - exact cocartesian_initial_via_adj_to_cocartesian_initial.
    - apply isaprop_cocartesian_initial.
      exact HB.
    - apply isaprop_cocartesian_initial_via_adj.
      exact HB.
  Defined.

  Section ToAdj.
    Context (Hb : cocartesian_coprod b).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).

    Let coproduct
      : @BinCoproduct
          (hom (pr1 (prod b b)) b)
          (binprod_cone_pr1 (pr1 (prod b b)))
          (binprod_cone_pr2 (pr1 (prod b b)))
      := pr1 Hb (pr1 (prod b b))
                (binprod_cone_pr1 (pr1 (prod b b)))
                (binprod_cone_pr2 (pr1 (prod b b))).

    Let r : pr1 (prod b b) --> b
      := BinCoproductObject coproduct.

    Local Definition cocartesian_coprod_to_cocartesian_coprod_via_adj_unit
      : id₁ _ ==> r · δ.
    Proof.
      use (binprod_ump_2cell (pr2 (prod b b))).
      - exact (lunitor _
               • BinCoproductIn1 coproduct
               • rinvunitor _
               • (r ◃ (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1)
               • lassociator _ _ _).
      - exact (lunitor _
               • BinCoproductIn2 coproduct
               • rinvunitor _
               • (r ◃ (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b))^-1)
               • lassociator _ _ _).
    Defined.

    Let η : id₁ _ ==> r · δ
      := cocartesian_coprod_to_cocartesian_coprod_via_adj_unit.

    Local Definition cartesian_prod_to_cartesian_prod_via_adj_counit
      : δ · r ==> id₁ b.
    Proof.
      use (BinCoproductArrow
             (make_BinCoproduct
                _ _ _ _ _ _
                (pr2 Hb _ _ δ _ _ _ _ _ (pr2 coproduct)))) ; cbn.
      - exact (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b)).
      - exact (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b)).
    Defined.

    Let ε : δ · r ==> id₁ _
      := cartesian_prod_to_cartesian_prod_via_adj_counit.

    Local Lemma cocartesian_coprod_to_cocartesian_coprod_via_adj_triangle_1
      : linvunitor r • (η ▹ r) • rassociator r δ r • (r ◃ ε) • runitor r
        =
        id₂ r.
    Proof.
      use (BinCoproductArrowsEq _ _ _ (coproduct)) ; cbn.
      - rewrite !vassocr.
        rewrite linvunitor_natural.
        rewrite <- lwhisker_hcomp.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite lwhisker_vcomp.
          apply maponpaths.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 coproduct)))).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite lwhisker_id2.
          apply id2_left.
        }
        apply rinvunitor_runitor.
      - rewrite !vassocr.
        rewrite linvunitor_natural.
        rewrite <- lwhisker_hcomp.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite lwhisker_vcomp.
          apply maponpaths.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 coproduct)))).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite lwhisker_id2.
          apply id2_left.
        }
        apply rinvunitor_runitor.
    Qed.

    Local Lemma cocartesian_coprod_to_cocartesian_coprod_via_adj_triangle_2
      : rinvunitor δ • (δ ◃ η) • lassociator δ r δ • (ε ▹ δ) • lunitor δ
        =
        id₂ δ.
    Proof.
      use (binprod_ump_2cell_unique_alt (pr2 (prod b b))).
      - rewrite id2_rwhisker.
        rewrite <- !rwhisker_vcomp.
        etrans.
        {
          apply maponpaths.
          refine (_
                  @ maponpaths
                      (λ z, rassociator _ _ _ • z)
                      (!(lunitor_assoc (binprod_cone_pr1 (pr1 (prod b b))) δ))).
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite !rwhisker_hcomp.
          rewrite inverse_pentagon_2.
          rewrite <- !rwhisker_hcomp.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite !rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- !rwhisker_hcomp, <- !lwhisker_hcomp.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        rewrite id2_right.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          rewrite !vassocl.
          rewrite vcomp_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rinvunitor_triangle.
          rewrite rwhisker_hcomp.
          rewrite <- rinvunitor_natural.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite lunitor_runitor_identity.
          rewrite rinvunitor_runitor.
          apply id2_left.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 coproduct)))).
        }
        apply vcomp_rinv.
      - rewrite id2_rwhisker.
        rewrite <- !rwhisker_vcomp.
        etrans.
        {
          apply maponpaths.
          refine (_
                  @ maponpaths
                      (λ z, rassociator _ _ _ • z)
                      (!(lunitor_assoc (binprod_cone_pr2 (pr1 (prod b b))) δ))).
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite !rwhisker_hcomp.
          rewrite inverse_pentagon_2.
          rewrite <- !rwhisker_hcomp.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite !rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- !rwhisker_hcomp, <- !lwhisker_hcomp.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        rewrite id2_right.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          rewrite !vassocl.
          rewrite vcomp_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rinvunitor_triangle.
          rewrite rwhisker_hcomp.
          rewrite <- rinvunitor_natural.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite lunitor_runitor_identity.
          rewrite rinvunitor_runitor.
          apply id2_left.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (pr2 Hb _ _ δ _ _ _ _ _ (pr2 coproduct)))).
        }
        apply vcomp_rinv.
    Qed.

    Definition cocartesian_coprod_to_cocartesian_coprod_via_adj
      : cocartesian_coprod_via_adj b prod.
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact r.
      - exact η.
      - exact ε.
      - exact cocartesian_coprod_to_cocartesian_coprod_via_adj_triangle_1.
      - exact cocartesian_coprod_to_cocartesian_coprod_via_adj_triangle_2.
    Defined.
  End ToAdj.

  Section FromAdj.
    Context (Hb : cocartesian_coprod_via_adj b prod).

    Let δ : b --> pr1 (prod b b)
      := binprod_ump_1cell (pr2 (prod b b)) (id₁ b) (id₁ b).
    Let r : pr1 (prod b b) --> b := pr11 Hb.
    Let η : id₁ _ ==> r · δ := pr121 Hb.
    Let ε : δ · r ==> id₁ _ := pr221 Hb.
    Let p : linvunitor r • (η ▹ r) • rassociator r δ r • (r ◃ ε) • runitor r
            =
            id2 r
      := pr12 Hb.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell
                     {x : B}
                     (f g : x --> b)
      : x --> b
      := binprod_ump_1cell (pr2 (prod b b)) f g · r.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_in1_help
      : binprod_cone_pr1 (pr1 (prod b b)) ==> r
      := linvunitor _
         • (η ▹ _)
         • rassociator _ _ _
         • (r ◃ (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ (id₁ b) (id₁ b)))
         • runitor _.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_in1
                     {x : B}
                     (f g : x --> b)
      : f ==> cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell f g
      := (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ f g)^-1
         • (_ ◃ cocartesian_coprod_via_adj_to_cocartesian_coprod_in1_help).

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_in2_help
      : binprod_cone_pr2 (pr1 (prod b b)) ==> r
      := linvunitor _
         • (η ▹ _)
         • rassociator _ _ _
         • (r ◃ (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ (id₁ b) (id₁ b)))
         • runitor _.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_in2
                     {x : B}
                     (f g : x --> b)
      : g ==> cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell f g
      := (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ f g)^-1
         • (_ ◃ cocartesian_coprod_via_adj_to_cocartesian_coprod_in2_help).

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell
                     {x : B}
                     {f g k : x --> b}
                     (α : f ==> k)
                     (β : g ==> k)
      : cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell f g ==> k.
    Proof.
      refine ((binprod_ump_2cell (pr2 (prod b b)) _ _ ▹ r)
              • rassociator _ _ _
              • (_ ◃ ε)
              • runitor _).
      - exact (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ _ _
               • α
               • rinvunitor _
               • (_ ◃ (binprod_ump_1cell_pr1 (pr2 (prod b b)) _ _ _)^-1)
               • lassociator _ _ _).
      - exact (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ _ _
               • β
               • rinvunitor _
               • (_ ◃ (binprod_ump_1cell_pr2 (pr2 (prod b b)) _ _ _)^-1)
               • lassociator _ _ _).
    Defined.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in1
                     {x : B}
                     {f g k : x --> b}
                     (α : f ==> k)
                     (β : g ==> k)
      : cocartesian_coprod_via_adj_to_cocartesian_coprod_in1 f g
        • cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell α β
        =
        α.
    Proof.
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell.
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in1.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        refine (!(vcomp_whisker _ _) @ _).
        apply maponpaths_2.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      refine (_ @ id2_right _).
      rewrite !vassocl.
      apply maponpaths.
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
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in1_help.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite lwhisker_hcomp.
        apply triangle_r_inv.
      }
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite !lwhisker_hcomp.
          rewrite <- inverse_pentagon_3.
          rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite runitor_triangle.
        apply idpath.
      }
      rewrite <- vcomp_runitor.
      rewrite !vassocr.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite runitor_lunitor_identity.
      rewrite vcomp_lunitor.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        rewrite <- lunitor_triangle.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (pr22 Hb).
    Qed.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in2
                     {x : B}
                     {f g k : x --> b}
                     (α : f ==> k)
                     (β : g ==> k)
      : cocartesian_coprod_via_adj_to_cocartesian_coprod_in2 f g
        • cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell α β
        =
        β.
    Proof.
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell.
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        refine (!(vcomp_whisker _ _) @ _).
        apply maponpaths_2.
        apply binprod_ump_2cell_pr2.
      }
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      refine (_ @ id2_right _).
      rewrite !vassocl.
      apply maponpaths.
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
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in2_help.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite lwhisker_hcomp.
        apply triangle_r_inv.
      }
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite !lwhisker_hcomp.
          rewrite <- inverse_pentagon_3.
          rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite runitor_triangle.
        apply idpath.
      }
      rewrite <- vcomp_runitor.
      rewrite !vassocr.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite runitor_lunitor_identity.
      rewrite vcomp_lunitor.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        rewrite <- lunitor_triangle.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (pr22 Hb).
    Qed.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_eq
                     {x : B}
                     {f g k : x --> b}
                     (α : f ==> k)
                     (β : g ==> k)
                     (φ : ∑ (fg : cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell
                                    f g
                                  ==>
                                  k),
                         cocartesian_coprod_via_adj_to_cocartesian_coprod_in1 f g
                         • fg
                         =
                         α
                         ×
                         cocartesian_coprod_via_adj_to_cocartesian_coprod_in2 f g
                         • fg
                         =
                         β)
      : φ
        =
        cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell α β
        ,,
        cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in1 α β
        ,,
        cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in2 α β.
    Proof.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      cbn.
      refine (!(id2_left _) @ _).
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell.
      rewrite <- lwhisker_id2.
      rewrite <- p.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        apply maponpaths_2.
        refine (_ @ maponpaths
                      (λ z, lassociator _ _ _ • z)
                      (runitor_triangle (binprod_ump_1cell (pr2 (prod b b)) f g) r)).
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite <- vcomp_runitor.
      unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell.
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_5.
        rewrite <- rwhisker_hcomp.
        rewrite !vassocl.
        rewrite <- rwhisker_rwhisker_alt.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite !lwhisker_hcomp.
        rewrite triangle_l_inv.
        rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
        rewrite !rwhisker_vcomp.
        apply idpath.
      }
      apply maponpaths.
      use (binprod_ump_2cell_unique_alt (pr2 (prod b b))).
      - rewrite binprod_ump_2cell_pr1.
        rewrite <- !rwhisker_vcomp.
        rewrite <- (pr12 φ).
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rinvunitor_natural.
          rewrite <- rwhisker_hcomp.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          rewrite <- rwhisker_rwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in1.
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in1_help.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite <- runitor_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite runitor_rinvunitor.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        refine (lassociator_lassociator _ _ _ _ @ _).
        apply maponpaths_2.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        refine (!(lwhisker_lwhisker _ _ _) @ _).
        rewrite !vassocl.
        apply maponpaths.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell.
        rewrite <- rinvunitor_triangle.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite runitor_rinvunitor.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      - rewrite binprod_ump_2cell_pr2.
        rewrite <- !rwhisker_vcomp.
        rewrite <- (pr22 φ).
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rinvunitor_natural.
          rewrite <- rwhisker_hcomp.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          rewrite <- rwhisker_rwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in2.
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in2_help.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite <- runitor_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite runitor_rinvunitor.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        refine (lassociator_lassociator _ _ _ _ @ _).
        apply maponpaths_2.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        refine (!(lwhisker_lwhisker _ _ _) @ _).
        rewrite !vassocl.
        apply maponpaths.
        unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell.
        rewrite <- rinvunitor_triangle.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite runitor_rinvunitor.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
    Qed.

    Local Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_obj
                     (x : B)
      : BinCoproducts (hom x b).
    Proof.
      intros f g.
      use make_BinCoproduct.
      - exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell f g).
      - exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_in1 f g).
      - exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_in2 f g).
      - intros k α β.
        use make_iscontr.
        + simple refine (_ ,, (_ ,, _)).
          * exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell α β).
          * exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in1 α β).
          * exact (cocartesian_coprod_via_adj_to_cocartesian_coprod_2cell_in2 α β).
        + apply cocartesian_coprod_via_adj_to_cocartesian_coprod_eq.
    Defined.

    Local Definition help_inv2cell
                     {x y : B}
                     (f : x --> y)
                     (h₁ h₂ : y --> b)
      : invertible_2cell
          (f · cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell h₁ h₂)
          (cocartesian_coprod_via_adj_to_cocartesian_coprod_1cell
             (f · h₁) (f · h₂)).
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

    Definition cocartesian_coprod_via_adj_to_cocartesian_coprod_preserves
               {x y : B}
               (f : x --> y)
      : preserves_bincoproduct (pre_comp b f).
    Proof.
      use preserves_bincoproduct_if_preserves_chosen.
      - apply cocartesian_coprod_via_adj_to_cocartesian_coprod_obj.
      - intros h₁ h₂.
        use (isBinCoproduct_eq_arrow
               _ _
               (z_iso_to_isBinCoproduct
                  _
                  (cocartesian_coprod_via_adj_to_cocartesian_coprod_obj x (f · h₁) (f · h₂))
                  (inv2cell_to_z_iso
                     (help_inv2cell f h₁ h₂)))).
        + cbn.
          unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in1.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply vcomp_whisker.
            }
            rewrite !vassocl.
            rewrite binprod_ump_2cell_pr1.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply lwhisker_lwhisker_rassociator.
            }
            rewrite !vassocl.
            apply maponpaths.
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            apply id2_left.
          }
          rewrite !vassocr.
          rewrite vcomp_linv.
          rewrite id2_left.
          rewrite !lwhisker_vcomp.
          apply idpath.
        + cbn.
          unfold cocartesian_coprod_via_adj_to_cocartesian_coprod_in2.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply vcomp_whisker.
            }
            rewrite !vassocl.
            rewrite binprod_ump_2cell_pr2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply lwhisker_lwhisker_rassociator.
            }
            rewrite !vassocl.
            apply maponpaths.
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            apply id2_left.
          }
          rewrite !vassocr.
          rewrite vcomp_linv.
          rewrite id2_left.
          rewrite !lwhisker_vcomp.
          apply idpath.
    Qed.

    Definition cocartesian_coprod_via_adj_to_cocartesian_coprod
      : cocartesian_coprod b.
    Proof.
      split.
      - exact cocartesian_coprod_via_adj_to_cocartesian_coprod_obj.
      - exact @cocartesian_coprod_via_adj_to_cocartesian_coprod_preserves.
    Defined.
  End FromAdj.

  Definition cocartesian_coprod_weq_cocartesian_coprod_via_adj
             (HB : is_univalent_2_1 B)
    : cocartesian_coprod b ≃ cocartesian_coprod_via_adj b prod.
  Proof.
    use weqimplimpl.
    - exact cocartesian_coprod_to_cocartesian_coprod_via_adj.
    - exact cocartesian_coprod_via_adj_to_cocartesian_coprod.
    - apply isaprop_cocartesian_coprod.
      exact HB.
    - apply isaprop_cocartesian_coprod_via_adj.
      exact HB.
  Defined.

  Definition cocartesian_weq_cocartesian_via_adj
             (HB : is_univalent_2_1 B)
    : cocartesian_ob b ≃ cocartesian_ob_via_adj b T prod.
  Proof.
    use weqdirprodf.
    - exact (cocartesian_initial_weq_cocartesian_initial_via_adj HB).
    - exact (cocartesian_coprod_weq_cocartesian_coprod_via_adj HB).
  Defined.
End EquivalenceCocartesian.
