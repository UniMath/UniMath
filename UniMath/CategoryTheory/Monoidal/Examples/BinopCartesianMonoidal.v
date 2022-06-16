Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.


Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.


Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SetCartesianMonoidal.

Local Open Scope cat.

(* Import BifunctorNotations.
Import MonoidalNotations. *)

Section BinopCategory.

  Definition Binop_data (X : hSet) : UU := X -> X -> X.
  Definition Binop_law {X : hSet} (m : Binop_data X) : UU
    := ∏ x y z : X, m (m x y) z = m x (m y z).
  Definition Binop (X : hSet) : UU
    := ∑ m : Binop_data X, Binop_law m.
  Definition Binop_to_data {X : hSet} (m : Binop X) : Binop_data X := pr1 m.
  Coercion Binop_to_data : Binop >-> Binop_data.

  Definition preserve_binop {X Y : hSet} (m : Binop X) (n : Binop Y) (f : X → Y)
    : UU := ∏ x1 x2 : X, (pr1 n) (f x1) (f x2) = f (pr1 m x1 x2).

  Lemma isaprop_preserve_binop {X Y : hSet} (m : Binop X) (n : Binop Y) (f : X → Y)
    : isaprop (preserve_binop m n f).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply Y.
  Qed.

  Definition Binop_disp_cat_ob_mor : disp_cat_ob_mor SET.
  Proof.
    use tpair.
    - exact (λ X, Binop X).
    - exact (λ _ _ m n f, preserve_binop m n f).
  Defined.

  Definition Binop_disp_cat_id_comp : disp_cat_id_comp SET Binop_disp_cat_ob_mor.
  Proof.
    use tpair.
    - intros X m x1 x2.
      apply idpath.
    - intros X Y Z f g m n o pf pg x1 x2.
      cbn in *.
      use pathscomp0.
      3: {
        apply maponpaths.
        apply pf.
      }
      apply pg.
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

End BinopCategory.

Section BinopIsCartesianMonoidal.

  Local Notation BO := Binop_cat.
  Local Notation DBO := Binop_disp_cat.

  Definition BO_disp_tensor_data : disp_bifunctor_data SET_cart_monoidal DBO DBO DBO.
  Proof.
    repeat (use tpair).
    - intros X Y m n.
      use tpair.
      + intros xy1 xy2.
        cbn in *.
        exact (pr1 m (pr1 xy1) (pr1 xy2),, pr1 n (pr2 xy1) (pr2 xy2)).
      + intros x y z.
        use total2_paths_b.
        * apply m.
        * simpl.
          etrans. { apply n. }
          unfold transportb.
          rewrite transportf_const.
          apply idpath.
          (* use pathscomp0.
          3: { Check (! transportf_const ( (! pr2 m (pr1 x) (pr1 y) (pr1 z))) (pr1 Y)). *)
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
      apply isaprop_preserve_binop.
    - intros X Y m n.
      apply isaprop_preserve_binop.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_binop.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_binop.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_binop.
  Qed.

  Definition BO_disp_tensor : disp_tensor DBO SET_cart_monoidal
    := (BO_disp_tensor_data,, BO_disp_tensor_laws).

  Definition BO_cart_disp_monoidal_data : disp_monoidal_data DBO SET_cart_monoidal.
  Proof.
    use tpair.
    - exact (BO_disp_tensor).
    - repeat (use tpair).
      + intros t1 t2 ; induction t1 ; induction t2 ; exact tt.
      + intros i j k.
        induction i ; induction j ; induction k.
        apply idpath.
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
      apply isaprop_preserve_binop.
    - intros X Y Z W f m n o p pf.
      apply isaprop_preserve_binop.
    - intros X Y Z W f m n o p pf.
      apply isaprop_preserve_binop.
    - intros X Y Z m n o.
      use tpair.
      + intros a b.
        use total2_paths_f.
        * use total2_paths_f.
          -- apply idpath.
          -- apply idpath_transportf.
        * apply idpath_transportf.
      + use tpair.
        * apply isaprop_preserve_binop.
        * apply isaprop_preserve_binop.
    - intros X Y f x y pf.
      apply isaprop_preserve_binop.
    - intros X x.
      use tpair.
      + intros x1 x2.
        apply idpath.
      + use tpair.
        * apply isaprop_preserve_binop.
        * apply isaprop_preserve_binop.
    - intros X Y f x y pf.
      apply isaprop_preserve_binop.
    - intros X x.
      use tpair.
      + intros x1 x2.
        apply idpath.
      + use tpair.
        * apply isaprop_preserve_binop.
        * apply isaprop_preserve_binop.
    - intros X Y x y.
      apply isaprop_preserve_binop.
    - intro ; intros.
      apply isaprop_preserve_binop.
  Qed.

  Definition BO_cart_disp_monoidal : disp_monoidal DBO SET_cart_monoidal
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
