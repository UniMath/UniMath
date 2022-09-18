(*******************************************************************************

 The projection

 Given a strict functor `F : C ⟶ StrictCat`, then we have a projection going
 from `∫ F` to `C`.
 In addition, the Grothendieck construction is pseudofunctorial.

 Contents
 1. The projection
 2. Action on 1-cells
 3. Action on 2-cells
 4. Identitor
 5. Compositor

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.

Local Open Scope cat.

(**
 1. The projection
 *)
Definition pr1_total_category_of_set_functor_data
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : functor_data
      (total_setcategory_of_set_functor F)
      C.
Proof.
  use make_functor_data.
  - exact (λ x, pr1 x).
  - exact (λ _ _ f, pr1 f).
Defined.

Definition pr1_total_category_of_set_is_functor
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : is_functor (pr1_total_category_of_set_functor_data F).
Proof.
  split ; intro ; intros ; apply idpath.
Qed.

Definition pr1_total_category_of_set_functor
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : total_setcategory_of_set_functor F ⟶ C.
Proof.
  use make_functor.
  - exact (pr1_total_category_of_set_functor_data F).
  - exact (pr1_total_category_of_set_is_functor F).
Defined.

(**
 2. Action on 1-cells
 *)
Section FunctorTotalCategoryFromSetFunctor.
  Context {C₁ C₂ : setcategory}
          (F : C₁ ⟶ C₂)
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F ∙ G₂).

  Definition functor_total_category_of_set_functor_eq
             {x y : total_precategory_of_set_functor G₁}
             (f : x --> y)
    : pr1 (# G₂ (# F (pr1 f))) (pr1 (pr1 α (pr1 x)) (pr2 x))
      =
      pr1 (α (pr1 y)) (pr1 (# G₁ (pr1 f)) (pr2 x)).
  Proof.
    exact (!(eqtohomot (maponpaths (λ z, pr11 z) (nat_trans_ax α _ _ (pr1 f))) (pr2 x))).
  Qed.

  Definition functor_total_category_of_set_functor_data
    : functor_data
        (total_setcategory_of_set_functor G₁)
        (total_setcategory_of_set_functor G₂).
  Proof.
    use make_functor_data.
    - exact (λ x, F (pr1 x) ,, pr1 (pr1 α (pr1 x)) (pr2 x)).
    - refine (λ x y f, #F (pr1 f) ,, _).
      exact (idtoiso (functor_total_category_of_set_functor_eq f)
             · # (pr1 (α (pr1 y))) (pr2 f)).
  Defined.

  Definition is_functor_functor_total_category_of_set_functor
    : is_functor functor_total_category_of_set_functor_data.
  Proof.
    split.
    - intro x.
      use eq_mor_category_of_set_functor ; cbn.
      + apply functor_id.
      + etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (pr1_maponpaths_idtoiso
                   (α (pr1 x))
                   (eq_in_set_fiber (functor_id G₁ (pr1 x)) (pr2 x))).
        }
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (maponpaths
                      (pr1 (α (pr1 x)))
                      (eq_in_set_fiber (functor_id G₁ (pr1 x)) (pr2 x)))).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber
                      (functor_id G₂ (F (pr1 x))) (pr1 (pr1 α (pr1 x)) (pr2 x)))).
        }
        apply setcategory_eq_idtoiso.
    - intros x y z f g.
      use eq_mor_category_of_set_functor ; cbn.
      + apply functor_comp.
      + cbn.
        refine (!_).
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber
                      (functor_comp G₂ (# F (pr1 f)) (# F (pr1 g)))
                      (pr1 (pr1 α (pr1 x)) (pr2 x)))).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          etrans.
          {
            apply functor_comp.
          }
          apply maponpaths_2.
          refine (!_).
          apply  (pr1_maponpaths_idtoiso
                    (# G₂ (# F (pr1 g)))
                    (functor_total_category_of_set_functor_eq f)).
        }
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          refine (!_).
          exact (pr1_idtoiso_concat
                   (maponpaths
                      (λ q, pr1 (# G₂ q) (pr1 (pr1 α (pr1 x)) (pr2 x)))
                      (functor_comp F (pr1 f) (pr1 g))
                       @ eq_in_set_fiber
                           (functor_comp G₂ (# F (pr1 f)) (# F (pr1 g)))
                           (pr1 (pr1 α (pr1 x)) (pr2 x)))
                   (maponpaths
                      (pr1 (# G₂ (# F (pr1 g))))
                      (functor_total_category_of_set_functor_eq f))).
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply functor_comp.
          }
          apply maponpaths.
          apply functor_comp.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            exact (pr1_maponpaths_idtoiso
                     (α (pr1 z))
                     (eq_in_set_fiber (functor_comp G₁ (pr1 f) (pr1 g)) (pr2 x))).
          }
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (maponpaths
                      (pr1 (α (pr1 z)))
                      (eq_in_set_fiber (functor_comp G₁ (pr1 f) (pr1 g)) (pr2 x)))).
        }
        etrans.
        {
          apply maponpaths.
          exact (from_eq_cat_of_setcategory
                   (nat_trans_ax α _ _ (pr1 g))
                   (pr2 f)).
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        cbn.
        apply setcategory_eq_idtoiso_comp.
  Qed.

  Definition functor_total_category_of_set_functor
    : total_setcategory_of_set_functor G₁ ⟶ total_setcategory_of_set_functor G₂.
  Proof.
    use make_functor.
    - exact functor_total_category_of_set_functor_data.
    - exact is_functor_functor_total_category_of_set_functor.
  Defined.

  Definition functor_total_category_of_set_functor_comm
    : pr1_total_category_of_set_functor G₁ ∙ F
      ⟹
      functor_total_category_of_set_functor ∙ pr1_total_category_of_set_functor G₂.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ; cbn ;
         exact (id_right _ @ !(id_left _))).
  Defined.

  Definition is_nat_z_iso_functor_total_category_of_set_functor_comm
    : is_nat_z_iso functor_total_category_of_set_functor_comm.
  Proof.
    intro ; cbn.
    apply identity_is_z_iso.
  Defined.
End FunctorTotalCategoryFromSetFunctor.

(**
 3. Action on 2-cells
 *)
Section NatTransTotalCategoryFromNatTrans.
  Context {C₁ C₂ : setcategory}
          {F₁ F₂ : C₁ ⟶ C₂}
          (α : F₁ ⟹ F₂)
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          (β₁ : G₁ ⟹ F₁ ∙ G₂)
          (β₂ : G₁ ⟹ F₂ ∙ G₂)
          (p : ∏ (x : C₁), pr1 β₁ x ∙ # (pr1 G₂) (pr1 α x) = pr1 β₂ x).

  Definition nat_trans_total_category_of_set_functor_eq
             (x : total_precategory_of_set_functor G₁)
    : pr1 (# G₂ (α (pr1 x))) (pr1 (pr1 β₁ (pr1 x)) (pr2 x))
      =
      pr1 (pr1 β₂ (pr1 x)) (pr2 x).
  Proof.
    exact (eqtohomot (maponpaths (λ z, pr11 z) (p (pr1 x))) (pr2 x)).
  Qed.

  Definition nat_trans_total_category_of_set_functor_data
    : nat_trans_data
        (functor_total_category_of_set_functor F₁ β₁)
        (functor_total_category_of_set_functor F₂ β₂).
  Proof.
    refine (λ x, α (pr1 x) ,, _).
    exact (idtoiso (nat_trans_total_category_of_set_functor_eq x)).
  Defined.

  Definition nat_trans_total_category_of_set_functor_is_nat_trans
    : is_nat_trans
        _ _
        nat_trans_total_category_of_set_functor_data.
  Proof.
    intros x y f.
    use eq_mor_category_of_set_functor.
    - apply nat_trans_ax.
    - cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# G₂ (α (pr1 y)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp G₂ (# F₁ (pr1 f)) (α (pr1 y)))
                    (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            exact (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber
                        (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                        (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
          }
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₂ (# F₂ (pr1 f)))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (_
                    @ eq_in_set_fiber
                        (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                        (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 ((_
                  @ eq_in_set_fiber
                      (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                      (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))
                  @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (from_eq_cat_of_setcategory (p (pr1 y)) (pr2 f)).
      }
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        exact (pr1_idtoiso_concat
                 _
                 (nat_trans_total_category_of_set_functor_eq y)).
      }
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply pr1_idtoiso_concat.
      }
      etrans.
      {
        apply maponpaths.
        apply setcategory_refl_idtoiso.
      }
      etrans.
      {
        apply id_right.
      }
      apply maponpaths_2.
      apply setcategory_eq_idtoiso.
  Qed.

  Definition nat_trans_total_category_of_set_functor
    : functor_total_category_of_set_functor F₁ β₁
        ⟹
        functor_total_category_of_set_functor F₂ β₂.
  Proof.
    use make_nat_trans.
    - exact nat_trans_total_category_of_set_functor_data.
    - exact nat_trans_total_category_of_set_functor_is_nat_trans.
  Defined.
End NatTransTotalCategoryFromNatTrans.

(**
 4. Identitor
 *)
Definition functor_total_category_of_set_functor_on_id_data
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : nat_trans_data
      (functor_identity _)
      (functor_total_category_of_set_functor
         (functor_identity C)
         (nat_trans_id F))
  := λ _, identity _.

Definition functor_total_category_of_set_functor_on_id_is_nat_trans
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : is_nat_trans
      _ _
      (functor_total_category_of_set_functor_on_id_data F).
Proof.
  intros x y f.
  refine (id_right _ @ _ @ !(id_left _)).
  use eq_mor_category_of_set_functor.
  - apply idpath.
  - cbn.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply setcategory_refl_idtoiso.
    }
    apply id_left.
Qed.

Definition functor_total_category_of_set_functor_on_id
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : functor_identity _
    ⟹
    functor_total_category_of_set_functor
      (functor_identity C)
      (nat_trans_id F).
Proof.
  use make_nat_trans.
  - exact (functor_total_category_of_set_functor_on_id_data F).
  - exact (functor_total_category_of_set_functor_on_id_is_nat_trans F).
Defined.

Definition is_nat_z_iso_functor_total_category_of_set_functor_on_id
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_nat_z_iso (functor_total_category_of_set_functor_on_id_data F).
Proof.
  intro.
  apply identity_is_z_iso.
Defined.

(**
 5. Compositor
 *)
Definition functor_total_category_of_set_functor_on_comp_data
           {C₁ C₂ C₃ : setcategory}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁ ⟶ cat_of_setcategory}
           {G₂ : C₂ ⟶ cat_of_setcategory}
           {G₃ : C₃ ⟶ cat_of_setcategory}
           (α : G₁ ⟹ F₁ ∙ G₂)
           (β : G₂ ⟹ F₂ ∙ G₃)
  : nat_trans_data
      (functor_total_category_of_set_functor F₁ α
       ∙ functor_total_category_of_set_functor F₂ β)
      (functor_total_category_of_set_functor
         (F₁ ∙ F₂)
         (nat_trans_comp _ _ _ α (pre_whisker F₁ β)))
  := λ _, identity _.

Definition functor_total_category_of_set_functor_on_comp_is_nat_trans
           {C₁ C₂ C₃ : setcategory}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁ ⟶ cat_of_setcategory}
           {G₂ : C₂ ⟶ cat_of_setcategory}
           {G₃ : C₃ ⟶ cat_of_setcategory}
           (α : G₁ ⟹ F₁ ∙ G₂)
           (β : G₂ ⟹ F₂ ∙ G₃)
  : is_nat_trans
      _ _
      (functor_total_category_of_set_functor_on_comp_data α β).
Proof.
  intros x y f.
  refine (id_right _ @ _ @ !(id_left _)).
  use eq_mor_category_of_set_functor ; cbn.
  - apply idpath.
  - cbn.
    refine (_ @ !(id_left _)).
    etrans.
    {
      apply maponpaths.
      apply functor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (pr1_maponpaths_idtoiso (β (F₁ (pr1 y)))).
    }
    etrans.
    {
      refine (!_).
      exact (pr1_idtoiso_concat
               _
               (maponpaths
                  (pr1 (β (F₁ (pr1 y))))
                  (functor_total_category_of_set_functor_eq F₁ α f))).
    }
    apply setcategory_eq_idtoiso.
Qed.

Definition functor_total_category_of_set_functor_on_comp
           {C₁ C₂ C₃ : setcategory}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁ ⟶ cat_of_setcategory}
           {G₂ : C₂ ⟶ cat_of_setcategory}
           {G₃ : C₃ ⟶ cat_of_setcategory}
           (α : G₁ ⟹ F₁ ∙ G₂)
           (β : G₂ ⟹ F₂ ∙ G₃)
  : functor_total_category_of_set_functor F₁ α
    ∙ functor_total_category_of_set_functor F₂ β
    ⟹
    functor_total_category_of_set_functor
      (F₁ ∙ F₂)
      (nat_trans_comp _ _ _ α (pre_whisker F₁ β)).
Proof.
  use make_nat_trans.
  - exact (functor_total_category_of_set_functor_on_comp_data α β).
  - exact (functor_total_category_of_set_functor_on_comp_is_nat_trans α β).
Defined.

Definition is_nat_z_iso_functor_total_category_of_set_functor_on_comp
           {C₁ C₂ C₃ : setcategory}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁ ⟶ cat_of_setcategory}
           {G₂ : C₂ ⟶ cat_of_setcategory}
           {G₃ : C₃ ⟶ cat_of_setcategory}
           (α : G₁ ⟹ F₁ ∙ G₂)
           (β : G₂ ⟹ F₂ ∙ G₃)
  : is_nat_z_iso
      (functor_total_category_of_set_functor_on_comp α β).
Proof.
  intro.
  apply identity_is_z_iso.
Defined.
