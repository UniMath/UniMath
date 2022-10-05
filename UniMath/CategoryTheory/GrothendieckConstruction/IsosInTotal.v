(*******************************************************************************

 Isos in the Grothendieck construction

 In this file we classify isomophisms in the total category of a functor from
 a strict category `C` to the category of strict categories.

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.

Local Open Scope cat.

Section IsoInTotal.
  Context {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
          {x y : total_setcategory_of_set_functor F}
          (f : x --> y)
          (H₁ : is_z_isomorphism (pr1 f)).

  Let fiso : z_iso (pr1 x) (pr1 y) := _ ,, H₁.

  Local Lemma inverse_path_1
    : pr1 (# F (inv_from_z_iso fiso)) (pr1 (# F (pr1 f)) (pr2 x)) = pr2 x.
  Proof.
    etrans.
    {
      exact (maponpaths
               (λ z, pr11 z (pr2 x))
               (!(functor_comp F (pr1 f) (inv_from_z_iso fiso)))).
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply (z_iso_inv_after_z_iso fiso).
    }
    etrans.
    {
      exact (maponpaths
               (λ z, pr11 z (pr2 x))
               (functor_id F _)).
    }
    apply idpath.
  Qed.

  Local Lemma inverse_path_2
    : pr1 (# F (pr1 f)) (pr1 (# F (inv_from_z_iso fiso)) (pr2 y)) = pr2 y.
  Proof.
    etrans.
    {
      exact (maponpaths
               (λ z, pr11 z (pr2 y))
               (!(functor_comp F (inv_from_z_iso fiso) (pr1 f)))).
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply (z_iso_after_z_iso_inv fiso).
    }
    etrans.
    {
      exact (maponpaths
               (λ z, pr11 z (pr2 y))
               (functor_id F _)).
    }
    apply idpath.
  Qed.

  Context (inv2 : pr1 (# F (inv_from_z_iso fiso)) (pr2 y) --> pr2 x)
          (H₂ : # (pr1 (# F (inv_from_z_iso fiso))) (pr2 f) · inv2
                =
                idtoiso inverse_path_1)
          (H₃ : # (pr1 (# F (pr1 f))) inv2 · pr2 f
                =
                idtoiso inverse_path_2).

  Local Definition is_z_iso_total_setcategory_of_set_functor_inv
    : y --> x
    := inv_from_z_iso fiso ,, inv2.

  Local Definition is_z_iso_total_setcategory_of_set_functor_is_inverse
    : is_inverse_in_precat f is_z_iso_total_setcategory_of_set_functor_inv.
  Proof.
    split.
    - use eq_mor_category_of_set_functor.
      + apply (z_iso_inv_after_z_iso fiso).
      + cbn.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact H₂.
        }
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp F _ _) _)).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_id F _) _)).
        }
        apply setcategory_eq_idtoiso.
    - use eq_mor_category_of_set_functor.
      + apply (z_iso_after_z_iso_inv fiso).
      + cbn.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact H₃.
        }
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp F _ _) _)).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_id F _) _)).
        }
        apply setcategory_eq_idtoiso.
  Qed.

  Definition is_z_iso_total_setcategory_of_set_functor
    : is_z_isomorphism f.
  Proof.
    use make_is_z_isomorphism.
    - exact is_z_iso_total_setcategory_of_set_functor_inv.
    - exact is_z_iso_total_setcategory_of_set_functor_is_inverse.
  Defined.
End IsoInTotal.
