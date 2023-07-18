(*********************************************************************

 The fiberwise opposite of an indexed category

 In this file, we define the fiberwise opposite of indexed categories.
 More specifically, if we have a category `Φ` indexed over `C`, then
 the fiberwise opposite of `Φ` is defined to be the opposite of `Φ x`
 on every object `x`.

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
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.

Local Open Scope cat.

Section FiberwiseOp.
  Context {C : category}
          (Φ : indexed_cat C).

  (**
   1. The data
   *)
  Definition op_indexed_cat_data
    : indexed_cat_data C.
  Proof.
    use make_indexed_cat_data.
    - exact (λ x, op_unicat (Φ x)).
    - exact (λ x y f, functor_opp (Φ $ f)).
    - exact (λ x,
             nat_trans_comp
               _ _ _
               (functor_identity_op _)
               (op_nt (nat_z_iso_inv (indexed_cat_id_nat_z_iso Φ x)))).
    - exact (λ x y z f g,
             nat_trans_comp
               _ _ _
               (functor_comp_op_nat_z_iso _ _)
               (op_nt (nat_z_iso_inv (indexed_cat_comp_nat_z_iso Φ f g)))).
  Defined.

  Definition op_indexed_cat_isos
    : indexed_cat_isos op_indexed_cat_data.
  Proof.
    split.
    - intros x xx.
      use opp_is_z_isomorphism.
      use is_z_isomorphism_comp.
      + apply (is_z_iso_inv_from_z_iso (indexed_cat_id_z_iso Φ xx)).
      + cbn.
        apply is_z_isomorphism_identity.
    - intros x y z f g xx.
      use opp_is_z_isomorphism.
      use is_z_isomorphism_comp.
      + apply (is_z_iso_inv_from_z_iso (indexed_cat_comp_z_iso Φ f g xx)).
      + cbn.
        apply is_z_isomorphism_identity.
  Defined.

  (**
   2. The laws
   *)
  Proposition op_indexed_cat_laws
    : indexed_cat_laws op_indexed_cat_data.
  Proof.
    repeat split.
    - intros x y f xx ; cbn in *.
      rewrite !id_right.
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_id Φ xx))
        with (inv_from_z_iso (indexed_cat_id_z_iso Φ xx)).
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ (identity x) f xx))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ (identity x) f xx)).
      rewrite functor_on_inv_from_z_iso.
      rewrite !assoc.
      use z_iso_inv_on_left ; cbn.
      refine (_ @ !(id_left _)).
      refine (!_).
      use z_iso_inv_on_left ; cbn.
      refine (_ @ !(indexed_cat_lunitor_alt Φ f xx)).
      refine (@idtoiso_opp (Φ y) _ _ _ @ _).
      rewrite maponpathsinv0.
      apply idpath.
    - intros x y f xx ; cbn in *.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply id_right.
        }
        apply maponpaths_2.
        apply id_right.
      }
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_id Φ ((Φ $ f) xx)))
        with (inv_from_z_iso (indexed_cat_id_z_iso Φ ((Φ $ f) xx))).
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ f (identity y) xx))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ f (identity y) xx)).
      rewrite !assoc.
      refine (!_).
      use z_iso_inv_on_left ; cbn.
      refine (_ @ !(id_left _)).
      refine (!_).
      use z_iso_inv_on_left ; cbn.
      refine (_ @ !(indexed_cat_runitor_alt Φ f xx)).
      refine (@idtoiso_opp (Φ y) _ _ _ @ _).
      rewrite maponpathsinv0.
      apply idpath.
    - intros w x y z f g h ww ; cbn in *.
      rewrite !id_right.
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ f (g · h) ww))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ f (g · h) ww)).
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ g h ((Φ $ f) ww)))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ g h ((Φ $ f) ww))).
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ (f · g) h ww))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ (f · g) h ww)).
      change (is_z_isomorphism_mor (is_z_isomorphism_indexed_cat_comp Φ f g ww))
        with (inv_from_z_iso (indexed_cat_comp_z_iso Φ f g ww)).
      rewrite functor_on_inv_from_z_iso.
      refine (assoc _ _ _ @ _).
      use z_iso_inv_on_left ; cbn.
      refine (!(id_left _) @ _).
      refine (!_).
      use z_iso_inv_on_left ; cbn.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        exact (!(indexed_cat_lassociator Φ f g h ww)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply z_iso_after_z_iso_inv.
      }
      rewrite id_left.
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply z_iso_after_z_iso_inv.
      }
      rewrite id_left.
      etrans.
      {
        apply maponpaths_2.
        apply (@idtoiso_opp (Φ z)).
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (!_).
        apply (maponpathsinv0 (λ k, (Φ $ k) ww)).
      }
      etrans.
      {
        refine (!_).
        apply pr1_idtoiso_concat.
      }
      rewrite <- (maponpathscomp0 (λ k, (Φ $ k) ww)).
      rewrite pathsinv0l.
      apply idpath.
  Qed.

  (**
   3. The fiberwise core
   *)
  Definition op_indexed_cat
    : indexed_cat C.
  Proof.
    use make_indexed_cat.
    - exact op_indexed_cat_data.
    - exact op_indexed_cat_isos.
    - exact op_indexed_cat_laws.
  Defined.
End FiberwiseOp.
