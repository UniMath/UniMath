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
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedCartesianMonoidalCategoriesWhiskered.

Local Open Scope cat.

Import DisplayedBifunctorNotations.

Section PointedSetCategory.

  Definition preserve_ptset {X Y : hSet} (x : X) (y : Y) (f : X → Y)
    : UU := f x = y.

  Lemma isaprop_preserve_ptset {X Y : hSet} (x : X) (y : Y) (f : X → Y)
    : isaprop (preserve_ptset x y f).
  Proof.
    apply Y.
  Qed.

  Definition id_preserve_ptset {X : hSet} (x : X)
    : preserve_ptset x x (idfun X).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_preserve_ptset {X Y Z : hSet}
             {x : X} {y : Y} {z : Z}
             {f : X → Y} {g : Y→ Z}
             (pf : preserve_ptset x y f)
             (pg : preserve_ptset y z g)
    : preserve_ptset x z (funcomp f g).
  Proof.
    unfold preserve_ptset.
    unfold funcomp.
    etrans. {
      apply maponpaths.
      apply pf.
    }
    apply pg.
  Qed.

  Definition ptset_disp_cat : disp_cat SET.
  Proof.
    use disp_struct.
    - exact (λ X, pr1 X).
    - exact (λ _ _ m n f, preserve_ptset m n f).
    - intros x y m n f. apply isaprop_preserve_ptset.
    - intros X x.
      apply id_preserve_ptset.
    - intros X Y Z f g x y z pf pg.
      apply (comp_preserve_ptset pf pg).
  Defined.

  Definition ptset_cat : category := total_category ptset_disp_cat.

  Definition ptset_dispBinproducts : dispBinProducts ptset_disp_cat BinProductsHSET.
  Proof.
    intros X Y x y.
    use tpair.
    - use tpair.
      + exact (x ,, y).
      + split; apply idpath.
    - cbn. intros Z f g z pf pg.
      use unique_exists.
      + cbn. unfold preserve_ptset. unfold prodtofuntoprod. cbn. rewrite pf, pg.
        apply idpath.
      + cbn. split.
        * (* show_id_type. *) apply X.
        * apply Y.
      + intro pfg.
        apply isapropdirprod; apply isasetaprop, isaprop_preserve_ptset.
      + intro pfg.
        cbn.
        intros.
        apply isaprop_preserve_ptset.
  Defined.

  Definition ptset_dispTerminal : dispTerminal ptset_disp_cat TerminalHSET.
  Proof.
    use tpair.
    - exact tt.
    - cbn.
      intros X x.
      use tpair.
      + apply idpath.
      + intro f. apply isaprop_preserve_ptset.
  Defined.

  Definition PS_cat_cart_monoidal_via_cartesian : monoidal ptset_cat.
  Proof.
    use cartesianmonoidalcat.
    - apply (total_category_Binproducts _ BinProductsHSET ptset_dispBinproducts).
    - apply (total_category_Terminal _ TerminalHSET ptset_dispTerminal).
  Defined.

End PointedSetCategory.

Section PointedSetIsCartesianMonoidal.

  Local Notation PS := ptset_cat.
  Local Notation DPS := ptset_disp_cat.

  Definition PS_cart_disp_monoidal : disp_monoidal DPS SET_cartesian_monoidal
    := displayedcartesianmonoidalcat BinProductsHSET TerminalHSET ptset_disp_cat ptset_dispBinproducts ptset_dispTerminal.

  Section ElementaryProof.

  Definition PS_disp_tensor_data : disp_bifunctor_data SET_cartesian_monoidal DPS DPS DPS.
  Proof.
    repeat (use tpair).
    - exact (λ _ _ x y, x,,y).
    - intros X Y Z f x y z pf.
      use total2_paths_b.
      + apply idpath.
      + cbn in *. apply pf.
    - intros X Y1 Y2 g x y1 y2 pg.
      use total2_paths_b.
      + cbn in * ; apply pg.
      + cbn in *.
        unfold transportb.
        rewrite transportf_const.
        apply idpath.
  Defined.

  Lemma PS_disp_tensor_laws : is_disp_bifunctor PS_disp_tensor_data.
  Proof.
    repeat split; red; intros; apply isaprop_preserve_ptset.
  Qed.

  Definition PS_disp_tensor : disp_tensor DPS SET_cartesian_monoidal
    := (PS_disp_tensor_data,, PS_disp_tensor_laws).

  Definition PS_cart_disp_monoidal_data : disp_monoidal_data DPS SET_cartesian_monoidal.
  Proof.
    use tpair.
    - exact PS_disp_tensor.
    - use tpair.
      + exact tt.
      + repeat split.
  Defined.

  Lemma PS_cart_disp_monoidal_laws : disp_monoidal_laws PS_cart_disp_monoidal_data.
  Proof.
    repeat split; try (red; intros; apply isaprop_preserve_ptset); try (apply isaprop_preserve_ptset).
  Qed.

  Definition PS_cart_disp_monoidal_elementary : disp_monoidal DPS SET_cartesian_monoidal
    := (PS_cart_disp_monoidal_data,, PS_cart_disp_monoidal_laws).

  End ElementaryProof.

  Definition PS_cat_cart_monoidal : monoidal ptset_cat
    := total_monoidal PS_cart_disp_monoidal.

  Lemma Forgetful_ptset_to_set_preserves_unit_strictly
    : preserves_unit_strictly (projection_preserves_unit PS_cart_disp_monoidal).
  Proof.
    apply projection_preservesunit_strictly.
  Qed.

  Lemma Forgetful_ptset_to_set_preserves_tensor_strictly
    : preserves_tensor_strictly (projection_preserves_tensordata PS_cart_disp_monoidal).
  Proof.
    apply projection_preservestensor_strictly.
  Qed.


End PointedSetIsCartesianMonoidal.
