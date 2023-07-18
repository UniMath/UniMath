(*********************************************************************

 The fiberwise core of an indexed category

 In this file, we define the fiberwise core of an indexed category.
 More specifically, if we have a category `Φ` indexed over `C`, then
 the fiberwise core of `Φ` is defined to be the core of `Φ x` on every
 object `x`.

 Contents
 1. The data
 2. The laws
 3. The fiberwise core

 *********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.

Local Open Scope cat.

Section FiberwiseCore.
  Context {C : category}
          (Φ : indexed_cat C).

  (**
   1. The data
   *)
  Definition core_indexed_cat_data
    : indexed_cat_data C.
  Proof.
    use make_indexed_cat_data.
    - exact (λ x, univalent_core (Φ x)).
    - exact (λ x y f, core_functor (Φ $ f)).
    - intros x.
      use make_nat_trans.
      + exact (λ xx, indexed_cat_id_z_iso Φ xx).
      + intros xx yy ff ; cbn.
        use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ].
        cbn.
        apply (nat_trans_ax (indexed_cat_id Φ x)).
    - intros x y z f g.
      use make_nat_trans.
      + exact (λ xx, indexed_cat_comp_z_iso Φ f g xx).
      + intros xx yy ff ; cbn.
        use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ].
        cbn.
        apply (nat_trans_ax (indexed_cat_comp Φ f g)).
  Defined.

  Definition core_indexed_cat_isos
    : indexed_cat_isos core_indexed_cat_data.
  Proof.
    split ; intros ; apply is_pregroupoid_core.
  Defined.

  (**
   2. The laws
   *)
  Proposition core_indexed_cat_laws
    : indexed_cat_laws core_indexed_cat_data.
  Proof.
    repeat split.
    - intros x y f xx ; cbn in *.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_isomorphism.
      }
      cbn.
      refine (indexed_cat_lunitor Φ f xx @ _).
      apply maponpaths.
      refine (_ @ !(@idtoiso_core (Φ y) _ _ _)).
      apply idpath.
    - intros x y f xx ; cbn in *.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_isomorphism.
      }
      cbn.
      refine (indexed_cat_runitor Φ f xx @ _).
      apply maponpaths.
      refine (_ @ !(@idtoiso_core (Φ y) _ _ _)).
      apply idpath.
    - intros w x y z f g h ww ; cbn in *.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_isomorphism.
      }
      cbn.
      refine (_ @ indexed_cat_lassociator Φ f g h ww).
      apply maponpaths.
      refine (@idtoiso_core (Φ z) _ _ _ @ _).
      apply idpath.
  Qed.

  (**
   3. The fiberwise core
   *)
  Definition core_indexed_cat
    : indexed_cat C.
  Proof.
    use make_indexed_cat.
    - exact core_indexed_cat_data.
    - exact core_indexed_cat_isos.
    - exact core_indexed_cat_laws.
  Defined.
End FiberwiseCore.
