Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.DisplayedCartesianMonoidal.

Local Open Scope cat.

Section BinopCategory.


  Definition Binop_disp_cat : disp_cat SET.
  Proof.
    use disp_struct.
    - exact (λ X, binop (pr1 X)).
    - exact (λ X Y m n f, isbinopfun (X := (X,,m)) (Y := (Y,,n)) f).
    - intros X Y m n f.
      apply isapropisbinopfun.
    - intros X m x1 x2.
      apply idpath.
    - intros X Y Z m n o f g pf pg.
      cbn in *.
      exact (isbinopfuncomp (make_binopfun (X := (X,,m)) (Y := (Y,,n)) f pf)
            (make_binopfun (X := (Y,,n)) (Y := (Z,,o)) g pg)).
  Defined.

  Lemma Binop_disp_cat_locally_prop : locally_propositional Binop_disp_cat.
  Proof.
    intro; intros; apply isapropisbinopfun.
  Qed.

  Definition Binop_cat : category := total_category Binop_disp_cat.

  Definition Binop_dispBinproducts : dispBinProducts Binop_disp_cat BinProductsHSET.
  Proof.
    intros X Y m n.
    use make_dispBinProduct_locally_prop.
    - exact Binop_disp_cat_locally_prop.
    - use tpair.
      + intros xy1 xy2.
        exact (m (pr1 xy1) (pr1 xy2),, n (pr2 xy1) (pr2 xy2)).
      + split; intros x1 x2; apply idpath.
    - intros Z f g o pf pg.
      cbn. intros x1 x2.
      apply dirprodeq; cbn.
      + rewrite pf. apply idpath.
      + rewrite pg. apply idpath.
  Defined.

  Definition Binop_dispTerminal : dispTerminal Binop_disp_cat TerminalHSET.
  Proof.
    use make_dispTerminal_locally_prop.
    - exact Binop_disp_cat_locally_prop.
    - exact (fun _ _ => tt).
    - cbn.
      intros X m. intros ? ?. apply idpath.
  Defined.

  Definition Binop_cat_cart_monoidal_via_cartesian : monoidal Binop_cat.
  Proof.
    use cartesian_monoidal.
    - apply (total_category_Binproducts _ BinProductsHSET Binop_dispBinproducts).
    - apply (total_category_Terminal _ TerminalHSET Binop_dispTerminal).
  Defined.

End BinopCategory.

Section BinopIsCartesianMonoidal.

  Local Notation BO := Binop_cat.
  Local Notation DBO := Binop_disp_cat.

  Definition BO_cart_disp_monoidal : disp_monoidal DBO SET_cartesian_monoidal
    := displayedcartesianmonoidalcat BinProductsHSET TerminalHSET Binop_disp_cat Binop_dispBinproducts Binop_dispTerminal.

 Section ElementaryProof.

  Definition BO_disp_tensor_data : disp_bifunctor_data SET_cartesian_monoidal DBO DBO DBO.
  Proof.
    repeat (use tpair).
    - intros X Y m n.
      intros xy1 xy2.
      exact (m (pr1 xy1) (pr1 xy2),, n (pr2 xy1) (pr2 xy2)).
    - intros X Y Z f m n o pf.
      intros x1 x2.
      use total2_paths_b.
      + apply idpath.
      + cbn in *. apply pf.
    - intros X Y1 Y2 g m m1 m2 pg.
      intros xy1 xy2.
      use total2_paths_b.
      + cbn in *; apply pg.
      + cbn in *.
        unfold transportb.
        rewrite transportf_const.
        apply idpath.
  Defined.

  Definition BO_disp_tensor : disp_tensor DBO SET_cartesian_monoidal.
  Proof.
    use make_disp_bifunctor_locally_prop.
    - exact Binop_disp_cat_locally_prop.
    - exact BO_disp_tensor_data.
  Defined.

  Definition BO_cart_disp_monoidal_data : disp_monoidal_data DBO SET_cartesian_monoidal.
  Proof.
    use tpair.
    - exact BO_disp_tensor.
    - use tpair.
      + intros t1 t2 ; induction t1 ; induction t2 ; exact tt.
      + repeat split.
  Defined.

  Definition BO_cart_disp_monoidal_elementary : disp_monoidal DBO SET_cartesian_monoidal.
  Proof.
    use make_disp_monoidal_locally_prop.
    - exact Binop_disp_cat_locally_prop.
    - exact BO_cart_disp_monoidal_data.
  Defined.

 End ElementaryProof.

  Definition Binop_cat_cart_monoidal : monoidal Binop_cat
    := total_monoidal BO_cart_disp_monoidal.

  Lemma Forgetful_BO_to_set_preserves_unit_strictly
    : preserves_unit_strictly (projection_preserves_unit BO_cart_disp_monoidal).
  Proof.
    apply projection_preservesunit_strictly.
  Qed.

  Lemma Forgetful_ptset_to_set_preserves_tensor_strictly
    : preserves_tensor_strictly (projection_preserves_tensordata BO_cart_disp_monoidal).
  Proof.
    apply projection_preservestensor_strictly.
  Qed.


End BinopIsCartesianMonoidal.
