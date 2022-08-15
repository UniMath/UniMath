(*******************************************************************************

 Pullbacks from the Grothendieck construction

 We show that the following square is a pullback square

    ∫ G₁ ⟶ ∫ G₂
      |       |
      V       V
      C₁ ⟶   C₂

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
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.Projection.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.IsosInTotal.

Local Open Scope cat.

Definition TODO { A : UU } : A.
Admitted.

Section PullbackFromTotal.
  Context {C₁ C₂ : setcategory}
          {F : C₁ ⟶ C₂}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F ∙ G₂)
          (Hα : is_nat_z_iso α).

  Let αiso : nat_z_iso G₁ (F ∙ G₂) := α ,, Hα.
  Let αinv : F ∙ G₂ ⟹ G₁ := nat_z_iso_inv αiso.

  Local Lemma α_iso_α_inv
              (x : C₁)
              (y : pr1 (G₂ (F x)))
    : pr1 (α x) (pr1 (αinv x) y) = y.
  Proof.
    exact (maponpaths
             (λ z, pr11 z y)
             (z_iso_after_z_iso_inv
                (nat_z_iso_pointwise_z_iso αiso x))).
  Qed.

  Local Lemma α_iso_α_inv_on_mor
              (x : C₁)
              {y₁ y₂ : pr1 (G₂ (F x))}
              (f : y₁ --> y₂)
    : # (pr1 (α x)) (# (pr1 (αinv x)) f)
      =
      idtoiso (α_iso_α_inv x y₁)
      · f
      · idtoiso (!(α_iso_α_inv x y₂)).
  Proof.
    refine (from_eq_cat_of_setcategory
             (z_iso_after_z_iso_inv
                (nat_z_iso_pointwise_z_iso αiso x)) f @ _) ; cbn.
    apply setcategory_eq_idtoiso_comp.
  Qed.

  Local Lemma α_inv_α_iso
              (x : C₁)
              (y : pr1 (G₁ x))
    : pr1 (αinv x) (pr1 (α x) y) = y.
  Proof.
    exact (maponpaths
             (λ z, pr11 z y)
             (z_iso_inv_after_z_iso
                (nat_z_iso_pointwise_z_iso αiso x))).
  Qed.

  Local Lemma α_inv_α_iso_on_mor
              (x : C₁)
              {y₁ y₂ : pr1 (G₁ x)}
              (f : y₁ --> y₂)
    : # (pr1 (αinv x)) (# (pr1 (α x)) f)
      =
      idtoiso (α_inv_α_iso x y₁)
      · f
      · idtoiso (!(α_inv_α_iso x y₂)).
  Proof.
    refine (from_eq_cat_of_setcategory
              (z_iso_inv_after_z_iso
                 (nat_z_iso_pointwise_z_iso αiso x)) f @ _) ; cbn.
    apply setcategory_eq_idtoiso_comp.
  Qed.

  Section PbMor.
    Context {C₀ : setcategory}
            (P₁ : C₀ ⟶ C₁)
            (P₂ : C₀ ⟶ total_setcategory_of_set_functor G₂)
            (β : P₁ ∙ F ⟹ P₂ ∙ pr1_total_category_of_set_functor G₂)
            (Hβ : is_nat_z_iso β).

    Definition total_set_category_pb_ump_1_mor_eq
               {x y : C₀}
               (f : x --> y)
      : pr1 (# G₁ (# P₁ f)) ((pr11 (αinv (P₁ x))) ((pr11 (# G₂ (pr1 (Hβ x)))) (pr2 (P₂ x))))
        =
        pr1 (αinv (P₁ y)) (pr1 (# G₂ (pr1 (Hβ y))) (pr1 (# G₂ (pr1 (# P₂ f))) (pr2 (P₂ x)))).
    Proof.
      pose (maponpaths
              (λ z, pr11 z ((pr11 (# G₂ (pr1 (Hβ x)))) (pr2 (P₂ x))))
              (nat_trans_ax αinv _ _ (#P₁ f)))
        as p.
      cbn -[αinv] in p.
      refine (!p @ _).
      apply maponpaths.
      refine (maponpaths
                (λ z, pr11 z (pr2 (P₂ x)))
                (!(functor_comp G₂ (pr1 (Hβ x)) (# F (# P₁ f)))) @ _).
      refine (!(maponpaths
                  (λ z, pr1 (# G₂ z) (pr2 (P₂ x)))
                  (nat_trans_ax (nat_z_iso_inv (β ,, Hβ)) _ _ f)) @ _).
      exact (maponpaths
               (λ z, pr11 z (pr2 (P₂ x)))
               (functor_comp G₂ _ _)).
    Qed.

    Definition total_set_category_pb_ump_1_mor_data
      : functor_data
          C₀
          (total_setcategory_of_set_functor G₁).
    Proof.
      use make_functor_data.
      - refine (λ x, P₁ x ,, _).
        apply (αinv (P₁ x)).
        apply (# G₂ (pr1 (Hβ x))).
        exact (pr2 (P₂ x)).
      - refine (λ x y f,
                #P₁ f
                ,,
                _ · #(pr1 (αinv (P₁ y))) (# (pr1 (# G₂ (pr1 (Hβ y)))) (pr2 (# P₂ f)))).
        apply idtoiso.
        exact (total_set_category_pb_ump_1_mor_eq f).
    Defined.

    Definition total_set_category_pb_ump_1_mor_is_functor
      : is_functor total_set_category_pb_ump_1_mor_data.
    Proof.
      split.
      - intro x.
        use eq_mor_category_of_set_functor.
        + apply functor_id.
        + cbn -[αinv].
          etrans.
          {
            do 3 apply maponpaths.
            exact (eq_mor_category_of_set_functor_pr2 (functor_id P₂ x)).
          }
          cbn -[αinv].
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply (pr1_idtoiso_concat
                         _
                         (eq_in_set_fiber (functor_id G₂ _) _)).
              }
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ x)))).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (αinv (P₁ x))).
          }
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq _)).
          }
          refine (!_).
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber (functor_id G₁ (P₁ x)) _)).
          }
          apply setcategory_eq_idtoiso.
      - intros x y z f g.
        use eq_mor_category_of_set_functor.
        + apply functor_comp.
        + cbn -[αinv].
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                exact (eq_mor_category_of_set_functor_pr2 (functor_comp P₂ f g)).
              }
              refine (functor_comp _ _ _ @ _).
              apply maponpaths.
              apply functor_comp.
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths.
            apply functor_comp.
          }
          cbn -[αinv].
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ z)))).
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
          }
          refine (assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ z)))).
                }
                refine (!_).
                apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
              }
              refine (!_).
              apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq (f · g))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq (f · g) @ _)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₁ (# P₁ g))).
            }
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _)).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (_ @ eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _)).
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (from_eq_cat_of_setcategory
                     (!(nat_trans_ax αinv _ _ (# P₁ g)))
                     (# (pr1 (# G₂ (pr1 (Hβ y)))) (pr2 (# P₂ f)))).
          }
          etrans.
          {
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_idtoiso_concat
                     ((_ @ eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _) @ _)).
          }
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_idtoiso_concat _ (total_set_category_pb_ump_1_mor_eq g)).
          }
          cbn -[αinv].
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              exact (from_eq_cat_of_setcategory
                       (!(functor_comp G₂ (pr1 (Hβ y)) (# F (# P₁ g)))
                        @ maponpaths
                            (λ q, # G₂ q)
                            (!(nat_trans_ax (nat_z_iso_inv (β ,, Hβ)) _ _ g))
                       @ functor_comp G₂ _ _)
                       (pr2 (# P₂ f))).
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            apply functor_comp.
          }
          etrans.
          {
            apply maponpaths_2.
            do 2 (refine (assoc _ _ _ @ _) ; apply maponpaths_2).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (((_ @ eq_in_set_fiber (functor_comp G₁ _ _) _) @ _) @ _)).
          }
          do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     _
                     (_ @ total_set_category_pb_ump_1_mor_eq g)).
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply setcategory_refl_idtoiso.
            }
            apply id_right.
          }
          apply maponpaths_2.
          apply setcategory_eq_idtoiso.
    Qed.

    Definition total_set_category_pb_ump_1_mor
      : C₀ ⟶ total_setcategory_of_set_functor G₁.
    Proof.
      use make_functor.
      - exact total_set_category_pb_ump_1_mor_data.
      - exact total_set_category_pb_ump_1_mor_is_functor.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr1
      : total_set_category_pb_ump_1_mor ∙ pr1_total_category_of_set_functor G₁
        ⟹
        P₁.
    Proof.
      use make_nat_trans.
      - exact (λ _, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr1_is_nat_z_iso
      : is_nat_z_iso total_set_category_pb_ump_1_mor_pr1.
    Proof.
      intro x.
      apply is_z_isomorphism_identity.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr2_eq
               (x : C₀)
      : pr1 (# G₂ (β x))
          (pr1 (pr1 α (P₁ x))
             ((pr11 (αinv (P₁ x)))
                ((pr11 (# G₂ (pr1 (Hβ x))))
                   (pr2 (P₂ x)))))
        =
        pr2 (P₂ x).
    Proof.
      etrans.
      {
        apply maponpaths.
        apply α_iso_α_inv.
      }
      etrans.
      {
        exact (maponpaths
                 (λ z, pr11 z (pr2 (P₂ x)))
                 (!(functor_comp G₂ (pr1 (Hβ x)) (β x)))).
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        exact (z_iso_after_z_iso_inv (_ ,, Hβ x)).
      }
      cbn.
      etrans.
      {
        exact (maponpaths
                 (λ z, pr11 z (pr2 (P₂ x)))
                 (functor_id G₂ _)).
      }
      cbn.
      apply idpath.
    Qed.

    Definition total_set_category_pb_ump_1_mor_pr2_data
      : nat_trans_data
          (total_set_category_pb_ump_1_mor ∙ functor_total_category_of_set_functor F α)
          P₂.
    Proof.
      refine (λ x, β x ,, _).
      refine (idtoiso _).
      apply total_set_category_pb_ump_1_mor_pr2_eq.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr2_is_nat_trans
      : is_nat_trans
          _ _
          total_set_category_pb_ump_1_mor_pr2_data.
    Proof.
      intros x y f.
      use eq_mor_category_of_set_functor.
      - apply (nat_trans_ax β).
      - cbn -[αinv].
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (functor_comp _ _ _ @ _).
                etrans.
                {
                  apply maponpaths_2.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (α (P₁ y))).
                }
                etrans.
                {
                  apply maponpaths.
                  apply α_iso_α_inv_on_mor.
                }
                refine (assoc _ _ _ @ _).
                apply maponpaths_2.
                refine (assoc _ _ _ @ _).
                apply maponpaths_2.
                refine (!_).
                apply (pr1_idtoiso_concat
                         (maponpaths
                            (pr11 (α (P₁ y)))
                            (total_set_category_pb_ump_1_mor_eq f))).
              }
              refine (assoc _ _ _ @ _).
              apply maponpaths_2.
              refine (assoc _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (maponpaths
                          (pr11 (α (P₁ y)))
                          (total_set_category_pb_ump_1_mor_eq f) @ _)).
            }
            refine (functor_comp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (β y))).
            }
            apply maponpaths_2.
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₂ (β y))).
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp G₂ _ _) _)).
        }
        do 2 refine (assoc' _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (total_set_category_pb_ump_1_mor_pr2_eq y)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (from_eq_cat_of_setcategory
                   ((!functor_comp G₂ (pr1 (Hβ y)) (β y))
                    @ maponpaths
                        (λ z, # G₂ z)
                        (z_iso_after_z_iso_inv (_ ,, Hβ y))
                    @ functor_id G₂ _)
                   (pr2 (# P₂ f))).
        }
        etrans.
        {
          apply maponpaths.
          do 2 refine (assoc' _ _ _ @ _).
          do 2 apply maponpaths.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (_ @ total_set_category_pb_ump_1_mor_pr2_eq y)).
        }
        do 2 refine (assoc _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp G₂ _ _) _ @ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply setcategory_refl_idtoiso.
        }
        refine (id_right _ @ _).
        refine (_ @ assoc' _ _ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (# P₂ f)))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (eq_in_set_fiber (functor_comp G₂ _ _) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G₂ _ _) _ @ _)).
        }
        apply setcategory_eq_idtoiso.
    Qed.

    Definition total_set_category_pb_ump_1_mor_pr2
      : total_set_category_pb_ump_1_mor ∙ functor_total_category_of_set_functor F α
        ⟹
        P₂.
    Proof.
      use make_nat_trans.
      - exact total_set_category_pb_ump_1_mor_pr2_data.
      - exact total_set_category_pb_ump_1_mor_pr2_is_nat_trans.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr2_is_nat_z_iso_eq
               (x : C₀)
      : pr1 (# G₂ (pr1 (Hβ x))) (pr2 (P₂ x))
        =
        pr1 (pr1 α (P₁ x))
          ((pr11 (αinv (P₁ x)))
             ((pr11 (# G₂ (pr1 (Hβ x)))) (pr2 (P₂ x)))).
    Proof.
      refine (!_).
      apply α_iso_α_inv.
    Qed.

    Definition total_set_category_pb_ump_1_mor_pr2_is_nat_z_iso
      : is_nat_z_iso total_set_category_pb_ump_1_mor_pr2.
    Proof.
      intro x.
      use is_z_iso_total_setcategory_of_set_functor.
      - exact (Hβ x).
      - exact (idtoiso (total_set_category_pb_ump_1_mor_pr2_is_nat_z_iso_eq x)).
      - abstract
          (cbn ;
           etrans ;
           [ apply maponpaths_2 ;
             refine (!_) ;
             apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ x))))
           | ] ;
           etrans ;
           [ refine (!_) ;
             apply (pr1_idtoiso_concat
                      _
                      (total_set_category_pb_ump_1_mor_pr2_is_nat_z_iso_eq x))
           | ] ;
           apply setcategory_eq_idtoiso).
      - abstract
          (cbn ;
           etrans ;
           [ apply maponpaths_2 ;
             refine (!_) ;
             apply (pr1_maponpaths_idtoiso (# G₂ (β x)))
           | ] ;
           etrans ;
           [ refine (!_) ;
             apply (pr1_idtoiso_concat
                      _
                      (total_set_category_pb_ump_1_mor_pr2_eq x))
           | ] ;
           apply setcategory_eq_idtoiso).
    Defined.
  End PbMor.

  Section PbCell.
    Context {C₀ : setcategory}
            {φ₁ φ₂ : pr1 C₀ ⟶ total_setcategory_of_set_functor G₁}
            (δ₁ : φ₁ ∙ pr1_total_category_of_set_functor G₁
                  ⟹
                  φ₂ ∙ pr1_total_category_of_set_functor G₁)
            (δ₂ : φ₁ ∙ functor_total_category_of_set_functor F α
                  ⟹
                  φ₂ ∙ functor_total_category_of_set_functor F α)
            (q : ∏ (x : C₀), pr1 (δ₂ x) = # F (δ₁ x)).

    Definition total_set_category_pb_ump_2_unique
      : isaprop
          (∑ (γ : φ₁ ⟹ φ₂),
            post_whisker γ (pr1_total_category_of_set_functor G₁) = δ₁
            ×
            post_whisker γ (functor_total_category_of_set_functor F α) = δ₂).
    Proof.
      use invproofirrelevance.
      intros ζ ξ.
      use subtypePath.
      {
        intro.
        use isapropdirprod ; apply isaset_nat_trans ; apply homset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use eq_mor_category_of_set_functor.
      - exact (nat_trans_eq_pointwise (pr12 ζ) x @ !(nat_trans_eq_pointwise (pr12 ξ) x)).
      - assert (p := maponpaths
                       (λ z, #(pr1 (αinv (pr1 (φ₂ x)))) z)
                       (eq_mor_category_of_set_functor_pr2
                          (nat_trans_eq_pointwise (pr22 ζ) x
                           @ !(nat_trans_eq_pointwise (pr22 ξ) x)))).
        cbn -[αinv] in p.
        rewrite !(functor_comp (αinv (pr1 (φ₂ x)))) in p.
        rewrite !α_inv_α_iso_on_mor in p.
        (*
        simple refine (_ @ maponpaths (λ z, idtoiso TODO · z · idtoiso TODO) p @ _).
         *)
        apply TODO.
    Qed.

    Definition total_set_category_pb_ump_2_cell_data
      : nat_trans_data φ₁ φ₂.
    Proof.
      refine (λ x, δ₁ x ,, _).
      refine (idtoiso _ · # (pr1 (αinv (pr1 (φ₂ x)))) (pr2 (δ₂ x)) · idtoiso _).
      - abstract
          (rewrite q ;
           cbn -[αinv] ;
           pose (maponpaths (λ z, pr11 z (pr2 (φ₁ x))) (nat_trans_ax α _ _ (δ₁ x))) as p ;
           cbn in p ;
           refine (!_) ;
           etrans ;
             [ apply maponpaths ;
               exact (!p)
             | ] ;
           apply α_inv_α_iso).
      - abstract
          (apply α_inv_α_iso).
    Defined.

    Definition total_set_category_pb_ump_2_cell_is_nat_trans
      : is_nat_trans φ₁ φ₂ total_set_category_pb_ump_2_cell_data.
    Proof.
      intros x y f.
      use eq_mor_category_of_set_functor.
      - exact (nat_trans_ax δ₁ _ _ f).
      - cbn -[αinv].
        refine (!_).
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G₁ _ _) _)).
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            apply functor_comp.
          }
          rewrite !assoc.
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₁ (pr1 (# φ₂ f)))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (_ @ eq_in_set_fiber (functor_comp G₁ _ _) _)).
        }


        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (from_eq_cat_of_setcategory
                   (!(nat_trans_ax αinv _ _ (pr1 (# φ₂ f))))
                   (pr2 (δ₂ x))).
        }
        cbn -[αinv].

        pose (maponpaths
                (λ z, # (pr1 (αinv (pr1 (φ₂ y)))) z)
                (eq_mor_category_of_set_functor_pr2
                   (nat_trans_ax δ₂ _ _ f)))
          as p.
    Admitted.

    Definition total_set_category_pb_ump_2_cell
      : φ₁ ⟹ φ₂.
    Proof.
      use make_nat_trans.
      - exact total_set_category_pb_ump_2_cell_data.
      - exact total_set_category_pb_ump_2_cell_is_nat_trans.
    Defined.

    Definition total_set_category_pb_ump_2_pr1
      : post_whisker
          total_set_category_pb_ump_2_cell
          (pr1_total_category_of_set_functor G₁)
        =
        δ₁.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    Qed.

    Definition total_set_category_pb_ump_2_pr2
      : post_whisker
          total_set_category_pb_ump_2_cell
          (functor_total_category_of_set_functor F α)
        =
        δ₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use eq_mor_category_of_set_functor.
      - cbn.
        exact (!(q x)).
      - cbn -[αinv].
        etrans.
        {
          apply maponpaths.
          refine (functor_comp _ _ _ @ _).
          apply maponpaths_2.
          refine (functor_comp _ _ _ @ _).
          apply maponpaths.
          apply α_iso_α_inv_on_mor.
        }
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (α (pr1 (φ₂ x)))).
          }
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (α (pr1 (φ₂ x)))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (functor_total_category_of_set_functor_eq
                        F α
                        (total_set_category_pb_ump_2_cell_data x))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (functor_total_category_of_set_functor_eq
                      F α
                      (total_set_category_pb_ump_2_cell_data x) @ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply setcategory_refl_idtoiso.
        }
        refine (id_right _ @ _).
        apply maponpaths_2.
        apply setcategory_eq_idtoiso.
    Qed.
  End PbCell.
End PullbackFromTotal.
