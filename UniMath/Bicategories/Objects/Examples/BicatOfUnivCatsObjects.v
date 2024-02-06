(******************************************************************

 Characterizations of (co)cartesian univalent categories

 In this file we characterize cartesian and cocartesian objects in
 the bicategory of univalent categories. Note: we already gave a
 characterization of such objects via adjoints. More specifically,
 for cartesian objects both the diagonal and the unique map to the
 terminal object should have right adjoints whereas for cocartesian
 objects, these two 1-cells should have left adjoints.

 This characterization via adjoints gives a direct connection to
 limits and colimits. A category has products if and only if the
 diagonal functor has a right adjoint and dually for coproducts.

 Contents
 1. Characterization of cartesian objects
 1.1. Categories with a terminal object
 1.2. Categories with binary products
 2. Characterization of cocartesian objects
 2.1. Categories with an initial object
 2.2. Categories with binary coproducts

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.
Require Import UniMath.Bicategories.Objects.CartesianObject.
Require Import UniMath.Bicategories.Objects.CocartesianObject.

Local Open Scope cat.

(**
 1. Characterization of cartesian objects
 *)

(**
 1.1. Categories with a terminal object
 *)
Section TerminalToAdj.
  Context (C : bicat_of_univ_cats)
          (T : Terminal (pr1 C)).

  Definition terminal_to_right_adj
    : unit_category ⟶ pr1 C
    := constant_functor _ _ T.

  Definition terminal_to_unit
    : functor_identity _ ⟹ functor_to_unit _ ∙ terminal_to_right_adj.
  Proof.
    use make_nat_trans.
    - exact (λ x, TerminalArrow _ _).
    - abstract
        (intros x y f ;
         apply TerminalArrowEq).
  Defined.

  Definition terminal_to_counit
    : terminal_to_right_adj ∙ functor_to_unit _ ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - intro.
      apply isapropunit.
    - abstract
        (intros x y f ;
         apply isasetunit).
  Defined.

  Definition terminal_to_cartesian_terminal_via_adj_data
    : left_adjoint_data (is_bifinal_1cell_property (pr2 bifinal_cats) C).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact terminal_to_right_adj.
    - exact terminal_to_unit.
    - exact terminal_to_counit.
  Defined.

  Definition terminal_to_cartesian_terminal_via_adj_axioms
    : left_adjoint_axioms terminal_to_cartesian_terminal_via_adj_data.
  Proof.
    split.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro.
      apply idpath.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro.
      apply TerminalArrowEq.
  Qed.

  Definition terminal_to_cartesian_terminal_via_adj
    : cartesian_terminal_via_adj C bifinal_cats.
  Proof.
    simple refine (_ ,, _).
    - exact terminal_to_cartesian_terminal_via_adj_data.
    - exact terminal_to_cartesian_terminal_via_adj_axioms.
  Defined.
End TerminalToAdj.

Section AdjToTerminal.
  Context (C : bicat_of_univ_cats)
          (HC : cartesian_terminal_via_adj C bifinal_cats).

  Let R : unit_category ⟶ pr1 C := pr11 HC.
  Let η : functor_identity _  ⟹ functor_to_unit _ ∙ R := pr121 HC.
  Let ε : R ∙ functor_to_unit _ ⟹ functor_identity _ := pr221 HC.

  Definition cartesian_terminal_via_adj_to_terminal_unique
             (x : pr1 C)
    : isaprop (x --> R tt).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    pose (nat_trans_eq_pointwise (pr22 HC) tt) as p.
    cbn in p.
    rewrite !id_left, !id_right in p.
    refine (!(id_right _) @ _ @ id_right _).
    etrans.
    {
      apply maponpaths.
      exact (!p).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_ax η).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!p).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_ax η).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
    apply maponpaths.
    apply isasetunit.
  Qed.

  Definition cartesian_terminal_via_adj_to_terminal
    : Terminal (pr1 C).
  Proof.
    use make_Terminal.
    - exact (R tt).
    - intro x.
      use iscontraprop1.
      + exact (cartesian_terminal_via_adj_to_terminal_unique x).
      + exact (pr1 η x).
  Defined.
End AdjToTerminal.

Definition terminal_weq_cartesian_terminal_via_adj
           (C : bicat_of_univ_cats)
  : Terminal (pr1 C) ≃ cartesian_terminal_via_adj C bifinal_cats.
Proof.
  use weqimplimpl.
  - exact (terminal_to_cartesian_terminal_via_adj C).
  - exact (cartesian_terminal_via_adj_to_terminal C).
  - apply isaprop_Terminal.
    exact (pr2 C).
  - apply isaprop_cartesian_terminal_via_adj.
    exact univalent_cat_is_univalent_2_1.
Defined.

Definition terminal_weq_cartesian_terminal
           (C : bicat_of_univ_cats)
  : Terminal (pr1 C) ≃ cartesian_terminal C
  := (invweq (cartesian_terminal_weq_cartesian_terminal_via_adj
                bifinal_cats
                C
                univalent_cat_is_univalent_2_1)
     ∘ terminal_weq_cartesian_terminal_via_adj C)%weq.

(**
 1.2. Categories with binary products
 *)
Section AdjFromProducts.
  Context (C : bicat_of_univ_cats)
          (prodC : BinProducts (pr1 C)).

  Definition binproducts_to_cartesian_prod_via_adj_right_adj_data
    : functor_data
        (category_binproduct (pr1 C) (pr1 C))
        (pr1 C).
  Proof.
    use make_functor_data.
    - exact (λ x, BinProductObject _ (prodC (pr1 x) (pr2 x))).
    - exact (λ x y f, BinProductOfArrows _ _ _ (pr1 f) (pr2 f)).
  Defined.

  Definition binproducts_to_cartesian_prod_via_adj_right_adj_is_functor
    : is_functor binproducts_to_cartesian_prod_via_adj_right_adj_data.
  Proof.
    split.
    - intro x ; cbn.
      use BinProductArrowsEq.
      + rewrite BinProductOfArrowsPr1.
        rewrite id_left, id_right.
        apply idpath.
      + rewrite BinProductOfArrowsPr2.
        rewrite id_left, id_right.
        apply idpath.
    - intros x y z f g ; cbn.
      rewrite BinProductOfArrows_comp.
      apply idpath.
  Qed.

  Definition binproducts_to_cartesian_prod_via_adj_right_adj
    : category_binproduct (pr1 C) (pr1 C) ⟶ pr1 C.
  Proof.
    use make_functor.
    - exact binproducts_to_cartesian_prod_via_adj_right_adj_data.
    - exact binproducts_to_cartesian_prod_via_adj_right_adj_is_functor.
  Defined.

  Definition binproducts_to_cartesian_prod_via_adj_unit
    : functor_identity (pr1 C)
      ⟹
      bindelta_pair_functor (functor_identity _) (functor_identity _)
      ∙ binproducts_to_cartesian_prod_via_adj_right_adj.
  Proof.
    use make_nat_trans.
    - exact (λ x, BinProductArrow _ _ (identity x) (identity x)).
    - abstract
        (intros x y f ; cbn ;
         use BinProductArrowsEq ;
         [ rewrite !assoc' ;
           rewrite BinProductOfArrowsPr1 ;
           rewrite BinProductPr1Commutes ;
           rewrite !assoc ;
           rewrite BinProductPr1Commutes ;
           rewrite id_left, id_right ;
           apply idpath
         | rewrite !assoc' ;
           rewrite BinProductOfArrowsPr2 ;
           rewrite BinProductPr2Commutes ;
           rewrite !assoc ;
           rewrite BinProductPr2Commutes ;
           rewrite id_left, id_right ;
           apply idpath ]).
  Defined.

  Definition binproducts_to_cartesian_prod_via_adj_counit
    : binproducts_to_cartesian_prod_via_adj_right_adj
      ∙ bindelta_pair_functor (functor_identity _) (functor_identity _)
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (λ x, BinProductPr1 _ _ ,, BinProductPr2 _ _).
    - abstract
        (intros x y f ;
         use pathsdirprod ; cbn ;
         [ apply BinProductOfArrowsPr1
         | apply BinProductOfArrowsPr2 ]).
  Defined.

  Definition binproducts_to_cartesian_prod_via_adj_data
    : left_adjoint_data
        (binprod_ump_1cell
           (pr2 (has_binprod_bicat_of_univ_cats C C))
           (id₁ C) (id₁ C)).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact binproducts_to_cartesian_prod_via_adj_right_adj.
    - exact binproducts_to_cartesian_prod_via_adj_unit.
    - exact binproducts_to_cartesian_prod_via_adj_counit.
  Defined.

  Definition binproducts_to_cartesian_prod_via_adj_axioms
    : left_adjoint_axioms binproducts_to_cartesian_prod_via_adj_data.
  Proof.
    split.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      use pathsdirprod ; cbn.
      + rewrite !id_left, !id_right.
        apply BinProductPr1Commutes.
      + rewrite !id_left, !id_right.
        apply BinProductPr2Commutes.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      rewrite !id_left, !id_right.
      use BinProductArrowsEq.
      + rewrite !id_left.
        rewrite !assoc'.
        rewrite BinProductOfArrowsPr1.
        rewrite !assoc.
        rewrite BinProductPr1Commutes.
        apply id_left.
      + rewrite !id_left.
        rewrite !assoc'.
        rewrite BinProductOfArrowsPr2.
        rewrite !assoc.
        rewrite BinProductPr2Commutes.
        apply id_left.
  Qed.

  Definition binproducts_to_cartesian_prod_via_adj
    : cartesian_prod_via_adj C has_binprod_bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact binproducts_to_cartesian_prod_via_adj_data.
    - exact binproducts_to_cartesian_prod_via_adj_axioms.
  Defined.
End AdjFromProducts.

Section ProductsFromAdj.
  Context (C : bicat_of_univ_cats)
          (RC : cartesian_prod_via_adj C has_binprod_bicat_of_univ_cats).

  Let R : category_binproduct (pr1 C) (pr1 C) ⟶ pr1 C := pr11 RC.
  Let η : functor_identity _
          ⟹
          bindelta_pair_functor (functor_identity _) (functor_identity _) ∙ R
    := pr121 RC.
  Let ε : R ∙ bindelta_pair_functor (functor_identity _) (functor_identity _)
          ⟹
          functor_identity _
    := pr221 RC.

  Section Products.
    Context (x y : pr1 C).

    Local Definition cartesian_prod_via_adj_to_binproduct_obj
      : pr1 C
      := R (x ,, y).

    Local Definition cartesian_prod_via_adj_to_binproduct_pr1
      : cartesian_prod_via_adj_to_binproduct_obj --> x
      := pr1 (ε (x ,, y)).

    Local Definition cartesian_prod_via_adj_to_binproduct_pr2
      : cartesian_prod_via_adj_to_binproduct_obj --> y
      := pr2 (ε (x ,, y)).

    Context (w : pr1 C)
            (f : w --> x)
            (g : w --> y).

    Local Definition cartesian_prod_via_adj_to_binproduct_pair_unique
      : isaprop
          (∑ (fg : w --> cartesian_prod_via_adj_to_binproduct_obj),
           fg · cartesian_prod_via_adj_to_binproduct_pr1 = f
           ×
           fg · cartesian_prod_via_adj_to_binproduct_pr2 = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      pose (p := nat_trans_eq_pointwise (pr22 RC) (x ,, y)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      refine (!(id_right _) @ _ @ id_right _).
      refine (maponpaths (λ z, _ · z) (!p) @ _ @ maponpaths (λ z, _ · z) p).
      rewrite !assoc.
      refine (maponpaths (λ z, z · _) (nat_trans_ax η _ _ _) @ _).
      refine (_ @ maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ _))).
      rewrite !assoc'.
      apply maponpaths.
      refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
      apply maponpaths.
      apply pathsdirprod ; cbn.
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Local Definition cartesian_prod_via_adj_to_binproduct_pair
      : w --> cartesian_prod_via_adj_to_binproduct_obj
      := η w
         · @functor_on_morphisms _ _ R (w ,, w) (x ,, y) (f ,, g).

    Local Definition cartesian_prod_via_adj_to_binproduct_pair_pr1
      : cartesian_prod_via_adj_to_binproduct_pair
        · cartesian_prod_via_adj_to_binproduct_pr1
        =
        f.
    Proof.
      unfold cartesian_prod_via_adj_to_binproduct_pair.
      unfold cartesian_prod_via_adj_to_binproduct_pr1.
      pose (p := maponpaths pr1 (nat_trans_eq_pointwise (pr12 RC) w)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (nat_trans_ax ε (w ,, w) (x ,,y) (f ,, g))).
      }
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      apply id_left.
    Qed.

    Local Definition cartesian_prod_via_adj_to_binproduct_pair_pr2
      : cartesian_prod_via_adj_to_binproduct_pair
        · cartesian_prod_via_adj_to_binproduct_pr2
        =
        g.
    Proof.
      unfold cartesian_prod_via_adj_to_binproduct_pair.
      unfold cartesian_prod_via_adj_to_binproduct_pr2.
      pose (p := maponpaths dirprod_pr2 (nat_trans_eq_pointwise (pr12 RC) w)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 dirprod_pr2
                 (nat_trans_ax ε (w ,, w) (x ,,y) (f ,, g))).
      }
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      apply id_left.
    Qed.
  End Products.

  Definition cartesian_prod_via_adj_to_binproduct
    : BinProducts (pr1 C).
  Proof.
    intros x y.
    use make_BinProduct.
    - exact (cartesian_prod_via_adj_to_binproduct_obj x y).
    - exact (cartesian_prod_via_adj_to_binproduct_pr1 x y).
    - exact (cartesian_prod_via_adj_to_binproduct_pr2 x y).
    - intros w f g.
      use iscontraprop1.
      + exact (cartesian_prod_via_adj_to_binproduct_pair_unique x y w f g).
      + simple refine (_ ,, (_ ,, _)).
        * exact (cartesian_prod_via_adj_to_binproduct_pair x y w f g).
        * exact (cartesian_prod_via_adj_to_binproduct_pair_pr1 x y w f g).
        * exact (cartesian_prod_via_adj_to_binproduct_pair_pr2 x y w f g).
  Defined.
End ProductsFromAdj.

Definition binproducts_weq_cartesian_prod_via_adj
             (C : bicat_of_univ_cats)
  : BinProducts (pr1 C)
    ≃
    cartesian_prod_via_adj C has_binprod_bicat_of_univ_cats.
Proof.
  use weqimplimpl.
  - exact (binproducts_to_cartesian_prod_via_adj C).
  - exact (cartesian_prod_via_adj_to_binproduct C).
  - use impred ; intro x.
    use impred ; intro y.
    apply isaprop_BinProduct.
    exact (pr2 C).
  - apply isaprop_cartesian_prod_via_adj.
    exact univalent_cat_is_univalent_2_1.
Defined.

Definition prods_weq_cartesian_prod
           (C : bicat_of_univ_cats)
  : BinProducts (pr1 C) ≃ cartesian_prod C
  := (invweq (cartesian_prod_weq_cartesian_prod_via_adj
                has_binprod_bicat_of_univ_cats
                C
                univalent_cat_is_univalent_2_1)
      ∘ binproducts_weq_cartesian_prod_via_adj C)%weq.

Definition terminal_prods_weq_cartesian_ob
           (C : bicat_of_univ_cats)
  : Terminal (pr1 C) × BinProducts (pr1 C) ≃ cartesian_ob C.
Proof.
  use weqdirprodf.
  - exact (terminal_weq_cartesian_terminal C).
  - exact (prods_weq_cartesian_prod C).
Defined.

(**
 2. Characterization of cocartesian objects
 *)

(**
 2.1. Categories with an initial object
 *)
Section InitialToAdj.
  Context (C : bicat_of_univ_cats)
          (I : Initial (pr1 C)).

  Definition initial_to_left_adj
    : unit_category ⟶ pr1 C
    := constant_functor _ _ I.

  Definition initial_to_unit
    : functor_identity _ ⟹ initial_to_left_adj ∙ functor_to_unit _.
  Proof.
    use make_nat_trans.
    - intro.
      apply isapropunit.
    - abstract
        (intros x y f ;
         apply isasetunit).
  Defined.

  Definition initial_to_counit
    : functor_to_unit _ ∙ initial_to_left_adj ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (λ _, InitialArrow _ _).
    - abstract
        (intros x y f ;
         apply InitialArrowEq).
  Defined.

  Definition initial_to_cocartesian_initial_via_adj_data
    : internal_right_adj_data (is_bifinal_1cell_property (pr2 bifinal_cats) C).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact initial_to_left_adj.
    - exact initial_to_unit.
    - exact initial_to_counit.
  Defined.

  Definition initial_to_cocartesian_initial_via_adj_axioms
    : internal_right_adj_axioms initial_to_cocartesian_initial_via_adj_data.
  Proof.
    split.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro.
      apply InitialArrowEq.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro.
      apply idpath.
  Qed.

  Definition initial_to_cocartesian_initial_via_adj
    : cocartesian_initial_via_adj C bifinal_cats.
  Proof.
    simple refine (_ ,, _).
    - exact initial_to_cocartesian_initial_via_adj_data.
    - exact initial_to_cocartesian_initial_via_adj_axioms.
  Defined.
End InitialToAdj.

Section AdjToInitial.
  Context (C : bicat_of_univ_cats)
          (HC : cocartesian_initial_via_adj C bifinal_cats).

  Let L : unit_category ⟶ pr1 C := pr11 HC.
  Let η : functor_identity _  ⟹ L ∙ functor_to_unit _ := pr121 HC.
  Let ε : functor_to_unit _ ∙ L ⟹ functor_identity _ := pr221 HC.

  Definition cocartesian_initial_via_adj_to_initial_unique
             (x : pr1 C)
    : isaprop (L tt --> x).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    pose (nat_trans_eq_pointwise (pr12 HC) tt) as p.
    cbn in p.
    rewrite !id_left, !id_right in p.
    refine (!(id_left _) @ _ @ id_left _).
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax ε).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax ε).
    }
    apply maponpaths_2.
    apply maponpaths.
    apply isasetunit.
  Qed.

  Definition cocartesian_initial_via_adj_to_initial
    : Initial (pr1 C).
  Proof.
    use make_Initial.
    - exact (L tt).
    - intro x.
      use iscontraprop1.
      + exact (cocartesian_initial_via_adj_to_initial_unique x).
      + exact (pr1 ε x).
  Defined.
End AdjToInitial.

Definition initial_weq_cocartesian_initial_via_adj
           (C : bicat_of_univ_cats)
  : Initial (pr1 C) ≃ cocartesian_initial_via_adj C bifinal_cats.
Proof.
  use weqimplimpl.
  - exact (initial_to_cocartesian_initial_via_adj C).
  - exact (cocartesian_initial_via_adj_to_initial C).
  - apply isaprop_Initial.
    exact (pr2 C).
  - apply isaprop_cocartesian_initial_via_adj.
    exact univalent_cat_is_univalent_2_1.
Defined.

Definition initial_weq_cocartesian_initial
           (C : bicat_of_univ_cats)
  : Initial (pr1 C) ≃ cocartesian_initial C
  := (invweq (cocartesian_initial_weq_cocartesian_initial_via_adj
                bifinal_cats
                C
                univalent_cat_is_univalent_2_1)
      ∘ initial_weq_cocartesian_initial_via_adj C)%weq.

(**
 2.2. Categories with binary coproducts
 *)
Section AdjToCoprod.
  Context (C : bicat_of_univ_cats)
          (coprodC : BinCoproducts (pr1 C)).

  Definition coprods_to_cocartesian_coprod_via_adj_adj_data
    : functor_data (category_binproduct (pr1 C) (pr1 C)) (pr1 C).
  Proof.
    use make_functor_data.
    - exact (λ x, coprodC (pr1 x) (pr2 x)).
    - exact (λ x y f, BinCoproductOfArrows _ _ _ (pr1 f) (pr2 f)).
  Defined.

  Definition coprods_to_cocartesian_coprod_via_adj_adj_is_functor
    : is_functor coprods_to_cocartesian_coprod_via_adj_adj_data.
  Proof.
    split.
    - intros x ; cbn.
      use BinCoproductArrowsEq.
      + rewrite BinCoproductOfArrowsIn1.
        rewrite id_left, id_right.
        apply idpath.
      + rewrite BinCoproductOfArrowsIn2.
        rewrite id_left, id_right.
        apply idpath.
    - intros x y z f g ; cbn.
      refine (!_).
      apply BinCoproductOfArrows_comp.
  Qed.

  Definition coprods_to_cocartesian_coprod_via_adj_adj
    : category_binproduct (pr1 C) (pr1 C) ⟶ pr1 C.
  Proof.
    use make_functor.
    - exact coprods_to_cocartesian_coprod_via_adj_adj_data.
    - exact coprods_to_cocartesian_coprod_via_adj_adj_is_functor.
  Defined.

  Definition coprods_to_cocartesian_coprod_via_adj_unit
    : functor_identity _
      ⟹
      coprods_to_cocartesian_coprod_via_adj_adj
      ∙ bindelta_pair_functor (functor_identity _) (functor_identity _).
  Proof.
    use make_nat_trans.
    - exact (λ x, BinCoproductIn1 _ ,, BinCoproductIn2 _).
    - abstract
        (intros x y f ;
         use pathsdirprod ;
         cbn ;
         refine (!_) ;
         [ apply BinCoproductOfArrowsIn1 | apply BinCoproductOfArrowsIn2 ]).
  Defined.

  Definition coprods_to_cocartesian_coprod_via_adj_counit
    : bindelta_pair_functor (functor_identity _) (functor_identity _)
      ∙ coprods_to_cocartesian_coprod_via_adj_adj
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (λ x, BinCoproductArrow _ (identity x) (identity x)).
    - abstract
        (intros x y f ; cbn ;
         use BinCoproductArrowsEq ;
         [ rewrite !assoc ;
           rewrite BinCoproductOfArrowsIn1 ;
           rewrite BinCoproductIn1Commutes ;
           rewrite !assoc' ;
           rewrite BinCoproductIn1Commutes ;
           rewrite id_left, id_right ;
           apply idpath
         | rewrite !assoc ;
           rewrite BinCoproductOfArrowsIn2 ;
           rewrite BinCoproductIn2Commutes ;
           rewrite !assoc' ;
           rewrite BinCoproductIn2Commutes ;
           rewrite id_left, id_right ;
           apply idpath ]).
  Defined.

  Definition coprods_to_cocartesian_coprod_via_adj_data
    : internal_right_adj_data
        (binprod_ump_1cell
           (pr2 (has_binprod_bicat_of_univ_cats C C)) (id₁ C) (id₁ C)).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact coprods_to_cocartesian_coprod_via_adj_adj.
    - exact coprods_to_cocartesian_coprod_via_adj_unit.
    - exact coprods_to_cocartesian_coprod_via_adj_counit.
  Defined.

  Definition coprods_to_cocartesian_coprod_via_adj_axioms
    : internal_right_adj_axioms coprods_to_cocartesian_coprod_via_adj_data.
  Proof.
    split.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      rewrite !id_left, !id_right.
      use BinCoproductArrowsEq.
      + rewrite !assoc.
        rewrite BinCoproductOfArrowsIn1.
        rewrite !assoc'.
        rewrite BinCoproductIn1Commutes.
        apply idpath.
      + rewrite !assoc.
        rewrite BinCoproductOfArrowsIn2.
        rewrite !assoc'.
        rewrite BinCoproductIn2Commutes.
        apply idpath.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      use pathsdirprod ; cbn.
      + rewrite !id_left, !id_right.
        apply BinCoproductIn1Commutes.
      + rewrite !id_left, !id_right.
        apply BinCoproductIn2Commutes.
  Qed.

  Definition coprods_to_cocartesian_coprod_via_adj
    : cocartesian_coprod_via_adj C has_binprod_bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact coprods_to_cocartesian_coprod_via_adj_data.
    - exact coprods_to_cocartesian_coprod_via_adj_axioms.
  Defined.
End AdjToCoprod.

Section CoprodToAdj.
  Context (C : bicat_of_univ_cats)
          (LC : cocartesian_coprod_via_adj C has_binprod_bicat_of_univ_cats).

  Let L : category_binproduct (pr1 C) (pr1 C) ⟶ pr1 C := pr11 LC.
  Let η : functor_identity _
          ⟹
          L ∙ bindelta_pair_functor (functor_identity _) (functor_identity _)
    := pr121 LC.
  Let ε : bindelta_pair_functor (functor_identity _) (functor_identity _) ∙ L
          ⟹
          functor_identity _
    := pr221 LC.

  Section Coproducts.
    Context (x y : pr1 C).

    Definition cocartesian_coprod_via_adj_to_coprods_obj
      : pr1 C
      := L (x ,, y).

    Definition cocartesian_coprod_via_adj_to_coprods_in1
      : x --> cocartesian_coprod_via_adj_to_coprods_obj
      := pr1 (η (x ,, y)).

    Definition cocartesian_coprod_via_adj_to_coprods_in2
      : y --> cocartesian_coprod_via_adj_to_coprods_obj
      := pr2 (η (x ,, y)).

    Context (z : pr1 C)
            (f : x --> z)
            (g : y --> z).

    Definition cocartesian_coprod_via_adj_to_coprods_unique
      : isaprop
          (∑ (fg : cocartesian_coprod_via_adj_to_coprods_obj --> z),
           cocartesian_coprod_via_adj_to_coprods_in1 · fg = f
           ×
           cocartesian_coprod_via_adj_to_coprods_in2 · fg = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      pose (p := nat_trans_eq_pointwise (pr12 LC) (x ,, y)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      refine (!(id_left _) @ _ @ id_left _).
      refine (maponpaths (λ z, z · _) (!p) @ _ @ maponpaths (λ z, z · _) p).
      rewrite !assoc'.
      refine (maponpaths (λ z, _ · z) (!(nat_trans_ax ε _ _ _)) @ _).
      refine (_ @ maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ _)).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
      apply maponpaths.
      use pathsdirprod ; cbn.
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition cocartesian_coprod_via_adj_to_coprods_sum
      : cocartesian_coprod_via_adj_to_coprods_obj --> z
      := @functor_on_morphisms _ _ L (x ,, y) (z ,, z) (f ,, g) · ε z.

    Definition cocartesian_coprod_via_adj_to_coprods_sum_in1
      : cocartesian_coprod_via_adj_to_coprods_in1
        · cocartesian_coprod_via_adj_to_coprods_sum
        =
        f.
    Proof.
      unfold cocartesian_coprod_via_adj_to_coprods_in1.
      unfold cocartesian_coprod_via_adj_to_coprods_sum.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpaths
                 pr1
                 (!(nat_trans_ax η (x ,, y) (z ,, z) (f ,, g)))).
      }
      cbn.
      rewrite !assoc'.
      pose (p := maponpaths pr1 (nat_trans_eq_pointwise (pr22 LC) z)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      refine (_ @ id_right _).
      apply maponpaths.
      exact p.
    Qed.

    Definition cocartesian_coprod_via_adj_to_coprods_sum_in2
      : cocartesian_coprod_via_adj_to_coprods_in2
        · cocartesian_coprod_via_adj_to_coprods_sum
        =
        g.
    Proof.
      unfold cocartesian_coprod_via_adj_to_coprods_in2.
      unfold cocartesian_coprod_via_adj_to_coprods_sum.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpaths
                 dirprod_pr2
                 (!(nat_trans_ax η (x ,, y) (z ,, z) (f ,, g)))).
      }
      cbn.
      rewrite !assoc'.
      pose (p := maponpaths dirprod_pr2 (nat_trans_eq_pointwise (pr22 LC) z)).
      cbn in p.
      rewrite !id_left, !id_right in p.
      refine (_ @ id_right _).
      apply maponpaths.
      exact p.
    Qed.
  End Coproducts.

  Definition cocartesian_coprod_via_adj_to_coprods
    : BinCoproducts (pr1 C).
  Proof.
    intros x y.
    use make_BinCoproduct.
    - exact (cocartesian_coprod_via_adj_to_coprods_obj x y).
    - exact (cocartesian_coprod_via_adj_to_coprods_in1 x y).
    - exact (cocartesian_coprod_via_adj_to_coprods_in2 x y).
    - intros z f g.
      use iscontraprop1.
      + exact (cocartesian_coprod_via_adj_to_coprods_unique x y z f g).
      + simple refine (_ ,, _ ,, _).
        * exact (cocartesian_coprod_via_adj_to_coprods_sum x y z f g).
        * exact (cocartesian_coprod_via_adj_to_coprods_sum_in1 x y z f g).
        * exact (cocartesian_coprod_via_adj_to_coprods_sum_in2 x y z f g).
  Defined.
End CoprodToAdj.

Definition coprods_weq_cocartesian_coprod_via_adj
           (C : bicat_of_univ_cats)
  : BinCoproducts (pr1 C)
    ≃
    cocartesian_coprod_via_adj C has_binprod_bicat_of_univ_cats.
Proof.
  use weqimplimpl.
  - exact (coprods_to_cocartesian_coprod_via_adj C).
  - exact (cocartesian_coprod_via_adj_to_coprods C).
  - use impred ; intro x.
    use impred ; intro y.
    apply isaprop_BinCoproduct.
    exact (pr2 C).
  - apply isaprop_cocartesian_coprod_via_adj.
    exact univalent_cat_is_univalent_2_1.
Defined.

Definition coprods_weq_cocartesian_coprod
           (C : bicat_of_univ_cats)
  : BinCoproducts (pr1 C) ≃ cocartesian_coprod C
  := (invweq (cocartesian_coprod_weq_cocartesian_coprod_via_adj
                has_binprod_bicat_of_univ_cats
                C
                univalent_cat_is_univalent_2_1)
      ∘ coprods_weq_cocartesian_coprod_via_adj C)%weq.

Definition initial_coprods_weq_cocartesian_ob
           (C : bicat_of_univ_cats)
  : Initial (pr1 C) × BinCoproducts (pr1 C) ≃ cocartesian_ob C.
Proof.
  use weqdirprodf.
  - exact (initial_weq_cocartesian_initial C).
  - exact (coprods_weq_cocartesian_coprod C).
Defined.
