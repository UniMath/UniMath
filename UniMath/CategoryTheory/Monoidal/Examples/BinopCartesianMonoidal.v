Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.


Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Local Open Scope cat.

Section BinopCategory.

  Definition Binop_disp_cat_ob_mor : disp_cat_ob_mor SET.
  Proof.
    use tpair.
    - exact (λ X, binop (pr1 X)).
    - exact (λ X Y m n f, isbinopfun (X := (X,,m)) (Y := (Y,,n)) f).
  Defined.

  Definition Binop_disp_cat_id_comp : disp_cat_id_comp SET Binop_disp_cat_ob_mor.
  Proof.
    use tpair.
    - intros X m x1 x2.
      apply idpath.
    - intros X Y Z f g m n o pf pg.
      exact (isbinopfuncomp (make_binopfun (X := (X,,m)) (Y := (Y,,n)) f pf)
            (make_binopfun (X := (Y,,n)) (Y := (Z,,o)) g pg)).

      (* etrans. { apply maponpaths. apply pf. } ; apply pg. *)
  Defined.

  Definition Binop_disp_cat_data : disp_cat_data SET
    := (Binop_disp_cat_ob_mor,, Binop_disp_cat_id_comp).

  Definition Binop_disp_cat_axioms : disp_cat_axioms SET Binop_disp_cat_data.
  Proof.
    repeat (use tpair).
    - intros ? Y ; intros.
      repeat (apply funextsec ; intro).
      apply Y.
    - intros ? Y ; intros.
      repeat (apply funextsec ; intro).
      apply Y.
    - intros ? ? ? W ; intros.
      repeat (apply funextsec ; intro).
      apply W.
    - intros ? Y ; intros.
      repeat (apply impred_isaset ; intro).
      apply isasetaprop.
      apply Y.
  Qed.

  Definition Binop_disp_cat : disp_cat SET
    := (Binop_disp_cat_data,, Binop_disp_cat_axioms).

  Definition Binop_cat : category := total_category Binop_disp_cat.

  Definition Binop_dispBinproducts : dispBinProducts Binop_disp_cat BinProductsHSET.
  Proof.
    intros X Y m n.
    use tpair.
    - use tpair.
      + intros xy1 xy2.
        exact (m (pr1 xy1) (pr1 xy2),, n (pr2 xy1) (pr2 xy2)).
      + split; intros x1 x2; apply idpath.
    - cbn. intros Z f g o pf pg.
      use unique_exists.
      + cbn. intros x1 x2.
        apply dirprodeq; cbn.
        * rewrite pf. apply idpath.
        * rewrite pg. apply idpath.
      + split; apply isapropisbinopfun.
      + intro pfg.
        apply isapropdirprod; apply isasetaprop, isapropisbinopfun.
      + intro pfg.
        cbn.
        intros.
        apply isapropisbinopfun.
  Defined.

  (** todo: provide a general construction of terminal objects in total categories *)
  Definition Binop_cat_cart_monoidal_via_cartesian : monoidal Binop_cat.
  Proof.
    use cartesianmonoidalcat.
    - apply (total_category_Binproducts _ BinProductsHSET Binop_dispBinproducts).
    - use tpair.
      + exists unitHSET.
        cbn.
        exact (fun _ _ => tt).
      + cbn.
        intro t. induction t as [X m].
        cbn in m.
        use unique_exists.
        * exact (fun _ => tt).
        * intros ? ?. apply idpath.
        * intro f.
          apply isapropisbinopfun.
        * intro f.
          intro H.
          apply funextfun.
          intro y.
          case (f y).
          apply idpath.
  Defined.


End BinopCategory.

Section BinopIsCartesianMonoidal.

  Local Notation BO := Binop_cat.
  Local Notation DBO := Binop_disp_cat.

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
      + cbn in * ; apply pg.
      + cbn in *.
        unfold transportb.
        rewrite transportf_const.
        apply idpath.
  Defined.

  Definition BO_disp_tensor_laws : is_disp_bifunctor BO_disp_tensor_data.
  Proof.
    repeat (use tpair).
    - intros X Y m n.
      apply isapropisbinopfun.
    - intros X Y m n.
      apply isapropisbinopfun.
    - intros X Y Z W f g m n o p pf pg.
      apply isapropisbinopfun.
    - intros X Y Z W f g m n o p pf pg.
      apply isapropisbinopfun.
    - intros X Y Z W f g m n o p pf pg.
      apply isapropisbinopfun.
  Qed.

  Definition BO_disp_tensor : disp_tensor DBO SET_cartesian_monoidal
    := (BO_disp_tensor_data,, BO_disp_tensor_laws).

  Definition BO_cart_disp_monoidal_data : disp_monoidal_data DBO SET_cartesian_monoidal.
  Proof.
    use tpair.
    - exact (BO_disp_tensor).
    - repeat (use tpair).
      + intros t1 t2 ; induction t1 ; induction t2 ; exact tt.
      + intro ; intros ; intro ; intro.
        apply idpath.
      + intro ; intros ; intro ; intro.
        apply idpath.
      + intro ; intros ; intro ; intro.
        apply idpath.
  Defined.

  Definition BO_cart_disp_monoidal_laws : disp_monoidal_laws BO_cart_disp_monoidal_data.
  Proof.
    repeat (use tpair).
    - intros X Y Z W f m n o p pf.
      apply isapropisbinopfun.
    - intros X Y Z W f m n o p pf.
      apply isapropisbinopfun.
    - intros X Y Z W f m n o p pf.
      apply isapropisbinopfun.
    - intros X Y Z m n o.
      use tpair.
      + intros a b.
        use total2_paths_f.
        * use total2_paths_f.
          -- apply idpath.
          -- apply idpath_transportf.
        * apply idpath_transportf.
      + use tpair.
        * apply isapropisbinopfun.
        * apply isapropisbinopfun.
    - intros X Y f x y pf.
      apply isapropisbinopfun.
    - intros X x.
      use tpair.
      + intros x1 x2.
        apply idpath.
      + use tpair.
        * apply isapropisbinopfun.
        * apply isapropisbinopfun.
    - intros X Y f x y pf.
      apply isapropisbinopfun.
    - intros X x.
      use tpair.
      + intros x1 x2.
        apply idpath.
      + use tpair.
        * apply isapropisbinopfun.
        * apply isapropisbinopfun.
    - intros X Y x y.
      apply isapropisbinopfun.
    - intro ; intros.
      apply isapropisbinopfun.
  Qed.

  Definition BO_cart_disp_monoidal : disp_monoidal DBO SET_cartesian_monoidal
    := (BO_cart_disp_monoidal_data,, BO_cart_disp_monoidal_laws).

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
