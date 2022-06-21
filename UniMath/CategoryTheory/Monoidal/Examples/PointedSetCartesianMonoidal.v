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
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

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

  Definition comp_preserve_ptset {X Y Z : hSet}
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

  Definition ptset_disp_cat_ob_mor : disp_cat_ob_mor SET.
  Proof.
    use tpair.
    - exact (λ X, pr1 X).
    - exact (λ _ _ m n f, preserve_ptset m n f).
  Defined.

  Definition ptset_disp_cat_id_comp : disp_cat_id_comp SET ptset_disp_cat_ob_mor.
  Proof.
    use tpair.
    - intros X x.
      apply id_preserve_ptset.
    - intros X Y Z f g x y z pf pg.
      apply (comp_preserve_ptset pf pg).
  Defined.

  Definition ptset_disp_cat_data : disp_cat_data SET
    := (ptset_disp_cat_ob_mor,, ptset_disp_cat_id_comp).

  Definition ptset_disp_cat_axioms : disp_cat_axioms SET ptset_disp_cat_data.
  Proof.
    repeat (use tpair).
    - intros ? Y ; intros.
      apply Y.
    - intros ? Y ; intros.
      apply Y.
    - intros ? ? ? W ; intros.
      apply W.
    - intros ? Y ; intros.
      apply isasetaprop.
      apply Y.
  Qed.

  Definition ptset_disp_cat : disp_cat SET
    := (ptset_disp_cat_data,, ptset_disp_cat_axioms).

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

  (** todo: provide a general construction of terminal objects in total categories *)
  Definition PS_cat_cart_monoidal_via_cartesian : monoidal ptset_cat.
  Proof.
    use cartesianmonoidalcat.
    - apply (total_category_Binproducts _ BinProductsHSET ptset_dispBinproducts).
    - use tpair.
      + exists unitHSET.
        exact tt.
      + cbn.
        intro t. induction t as [X x].
        cbn in x.
        use unique_exists.
        * exact (fun _ => tt).
        * apply idpath.
        * intro f.
          apply isaprop_preserve_ptset.
        * intro f.
          intro H.
          apply funextfun.
          intro y.
          case (f y).
          apply idpath.
  Defined.

End PointedSetCategory.

Section PointedSetIsCartesianMonoidal.

  Local Notation PS := ptset_cat.
  Local Notation DPS := ptset_disp_cat.

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

  Definition PS_disp_tensor_laws : is_disp_bifunctor PS_disp_tensor_data.
  Proof.
    repeat (use tpair).
    - intros X Y x y.
      apply isaprop_preserve_ptset.
    - intros X Y x y.
      apply isaprop_preserve_ptset.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_ptset.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_ptset.
    - intros X Y Z W f g m n o p pf pg.
      apply isaprop_preserve_ptset.
  Qed.

  Definition PS_disp_tensor : disp_tensor DPS SET_cartesian_monoidal
    := (PS_disp_tensor_data,, PS_disp_tensor_laws).

  Definition PS_cart_disp_monoidal_data : disp_monoidal_data DPS SET_cartesian_monoidal.
  Proof.
    use tpair.
    - exact (PS_disp_tensor).
    - repeat (use tpair).
      + exact tt.
      + intros X x.
        apply idpath.
      + intros X x.
        apply idpath.
      + intros X Y Z x y z.
        apply idpath.
  Defined.

  Definition PS_cart_disp_monoidal_laws : disp_monoidal_laws PS_cart_disp_monoidal_data.
  Proof.
    repeat (use tpair).
    - intros X Y Z W f x y z w pf.
      apply isaprop_preserve_ptset.
    - intros X Y Z W f x y z w pf.
      apply isaprop_preserve_ptset.
    - intros X Y Z W f x y z w pf.
      apply isaprop_preserve_ptset.
    - intros X Y Z x y z.
      use tpair.
      + apply idpath.

        (*
        assert (p0 : αinv_{ SET_cart_monoidal} X Y Z
                     = Isos.inv_from_z_iso (z_iso_from_associator_iso SET_cart_monoidal X Y Z)).
        {
          apply idpath.
        }

        rewrite p0.

        assert (p :  Isos.inv_from_z_iso (z_iso_from_associator_iso SET_cart_monoidal X Y Z)  = (λ xyz :  pr1 X × (pr1 Y × pr1 Z), (pr1 xyz,, pr12 xyz),, pr22 xyz)).
        {
          Check Isos.inv_z_iso_unique'.
          apply Isos.inv_iso_unique.
         *)
      + use tpair.
        * apply isaprop_preserve_ptset.
        * apply isaprop_preserve_ptset.
    - intros X Y f x y pf.
      apply isaprop_preserve_ptset.
    - intros X x.
      use tpair.
      + apply idpath.
      + use tpair.
        * apply isaprop_preserve_ptset.
        * apply isaprop_preserve_ptset.
    - intros X Y f x y pf.
      apply isaprop_preserve_ptset.
    - intros X x.
      use tpair.
      + apply idpath.
      + use tpair.
        * apply isaprop_preserve_ptset.
        * apply isaprop_preserve_ptset.
    - intros X Y x y.
      apply isaprop_preserve_ptset.
    - intros X Y Z W x y z w.
      apply isaprop_preserve_ptset.
  Qed.

  Definition PS_cart_disp_monoidal : disp_monoidal DPS SET_cartesian_monoidal
    := (PS_cart_disp_monoidal_data,, PS_cart_disp_monoidal_laws).

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
