(*******************************************************************************

 We show that the functor `∫ F ⟶ C` is a Street opfibration

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.Projection.

Local Open Scope cat.

Section IsOpcartesianTotalSetCategory.
  Context {C : setcategory}
          (G : C ⟶ cat_of_setcategory)
          {e₁ e₂ : total_setcategory_of_set_functor G}
          {f : e₁ --> e₂}
          (Hf : is_z_isomorphism (pr2 f)).

  Section Factorization.
    Context {e₃ : total_setcategory_of_set_functor G}
            (g : e₁ --> e₃)
            (h : pr1 e₂ --> pr1 e₃)
            (p : pr1 g = pr1 f · h).

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_unique
      : isaprop
          (∑ φ, # (pr1_total_category_of_set_functor G) φ = h
               ×
               f · φ = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_mor_category_of_set_functor.
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - pose (q := eq_mor_category_of_set_functor_pr2 (pr22 φ₁ @ !(pr22 φ₂))).
        cbn in q.
        use (cancel_z_iso'
               (# (pr1 (# G (pr11 φ₁))) (pr2 f) ,, _)).
        {
          cbn.
          apply functor_on_is_z_isomorphism.
          exact Hf.
        }
        cbn.
        use (cancel_z_iso'
               (idtoiso
                  (eq_in_set_fiber (functor_comp G (pr1 f) (pr11 φ₁)) (pr2 e₁)))).
        rewrite !assoc.
        refine (q @ _) ; clear q.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (from_eq_cat_of_setcategory
                   (maponpaths (λ z, #G z) (pr12 φ₁ @ !(pr12 φ₂)))
                   (pr2 f)).
        }
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (maponpaths
                      (λ z, (pr11 z) (pr2 e₂))
                      (!(maponpaths
                           (λ z, # G z)
                           (pr12 φ₁ @ ! pr12 φ₂))))).
          }
          apply setcategory_refl_idtoiso.
        }
        rewrite id_right.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G (pr1 f) (pr11 φ₂)) (pr2 e₁))).
        }
        apply setcategory_eq_idtoiso.
    Qed.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_eq
      : pr1 (# G h) (pr1 (# G (pr1 f)) (pr2 e₁))
        =
        pr1 (# G (pr1 g)) (pr2 e₁).
    Proof.
      refine (!(eq_in_set_fiber (functor_comp G (pr1 f) h) (pr2 e₁)) @ _).
      apply maponpaths_2.
      do 2 apply maponpaths.
      exact (!p).
    Qed.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor
      : e₂ --> e₃.
    Proof.
      refine (h ,, #(pr1 (#G h)) (inv_from_z_iso (_ ,, Hf)) · idtoiso _ · pr2 g).
      apply is_opcartesian_total_setcategory_of_set_functor_factor_eq.
    Defined.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_comm
      : f · is_opcartesian_total_setcategory_of_set_functor_factor
        =
        g.
    Proof.
      unfold is_opcartesian_total_setcategory_of_set_functor_factor.
      use eq_mor_category_of_set_functor.
      - cbn.
        exact (!p).
      - cbn.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            refine (!_).
            apply functor_comp.
          }
          etrans.
          {
            apply maponpaths.
            exact (z_iso_inv_after_z_iso (pr2 f ,, Hf)).
          }
          apply functor_id.
        }
        rewrite id_left.
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp G _ _) _)).
        }
        apply setcategory_eq_idtoiso.
    Qed.
  End Factorization.

  Definition is_opcartesian_total_setcategory_of_set_functor
    : is_opcartesian_sopfib
        (pr1_total_category_of_set_functor G)
        f.
  Proof.
    intros e₃ g h p.
    use iscontraprop1.
    - exact (is_opcartesian_total_setcategory_of_set_functor_factor_unique g h).
    - simple refine (_ ,, (_ ,, _)).
      + exact (is_opcartesian_total_setcategory_of_set_functor_factor g h p).
      + abstract
          (cbn ;
           apply idpath).
      + exact (is_opcartesian_total_setcategory_of_set_functor_factor_comm g h p).
  Defined.
End IsOpcartesianTotalSetCategory.

Definition street_opfib_pr1_total_setcategory
          {C : setcategory}
          (G : C ⟶ cat_of_setcategory)
  : street_opfib
      (pr1_total_category_of_set_functor G).
Proof.
  intros x y f.
  simple refine (_ ,, (_ ,, _) ,, _ ,, _).
  - exact (y ,, pr1 (#G f) (pr2 x)).
  - exact (f ,, identity _).
  - apply identity_z_iso.
  - exact (!(id_right f)).
  - apply is_opcartesian_total_setcategory_of_set_functor.
    apply is_z_isomorphism_identity.
Defined.
