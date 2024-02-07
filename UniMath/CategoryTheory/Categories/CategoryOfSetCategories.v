(******************************************************************************************

 The category of strict categories

 Strict categories are the categories in which the type of objects forms a set. As such,
 the type of functors between them is a set as well, and this allows us to construct a
 category whose objects are strict categories and whose morphisms are functors. We also
 show that this category is univalent.

 For the proof of univalence, we reuse the result that identity of categories is equivalent
 to isomorphisms of categories. The main work lies in showing that isomorpisms in the
 category of strict categories are the same as isomorphisms of categories. This makes use
 of some infrastructure regarding isomorphisms.

 One technical detail that occurs in the proof of univalence, lies in the fact that we
 define [path_setcategory_help_fun] and [path_setcategory_help_fun_alt] and that we show
 they are equal in [path_setcategory_help_fun_eq]. The function [path_setcategory_help_fun]
 is more useful computationally in [is_univalent_cat_of_setcategory], but
 [path_setcategory_help_fun_alt] simplifies the construction of the equivalence in
 [path_setcategory].

 Contents
 1. The category of strict categories
 2. Isomorphisms of strict categories
 3. The univalence of the category of strict categories

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.

Local Open Scope cat.

(** * 1. The category of strict categories *)
Definition precat_ob_mor_of_setcategory
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact setcategory.
  - exact (λ C₁ C₂, C₁ ⟶ C₂).
Defined.

Definition precat_data_of_setcategory
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact precat_ob_mor_of_setcategory.
  - exact (λ C, functor_identity _).
  - exact (λ C₁ C₂ C₃ F G, F ∙ G).
Defined.

Definition is_precategory_of_setcategory
  : is_precategory precat_data_of_setcategory.
Proof.
  use make_is_precategory_one_assoc.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
Qed.

Definition precat_of_setcategory
  : precategory.
Proof.
  use make_precategory.
  - exact precat_data_of_setcategory.
  - exact is_precategory_of_setcategory.
Defined.

Definition has_homsets_cat_of_setcategory
  : has_homsets precat_of_setcategory.
Proof.
  intros C₁ C₂.
  use functor_isaset.
  - apply homset_property.
  - apply C₂.
Qed.

Definition cat_of_setcategory
  : category.
Proof.
  use make_category.
  - exact precat_of_setcategory.
  - exact has_homsets_cat_of_setcategory.
Defined.

(** * 2. Isomorphisms of strict categories *)
Section CatIsoWeqIso.
  Context {C D : setcategory}
          (F : C ⟶ D).

  Section ToIso.
    Context (HF : is_catiso F).

    Let F_iso : catiso C D := F ,, HF.

    Definition is_cat_iso_to_is_z_isomorphism_inv_data
      : functor_data D C.
    Proof.
      use make_functor_data.
      - exact (catiso_inv_ob F_iso).
      - exact (λ x y f, catiso_inv_mor F_iso f).
    Defined.

    Proposition is_cat_iso_to_is_z_isomorphism_inv_laws
      : is_functor is_cat_iso_to_is_z_isomorphism_inv_data.
    Proof.
      split.
      - intro x ; cbn -[catiso_inv_mor].
        use catiso_inv_mor_eq ; cbn -[catiso_inv_mor].
        rewrite functor_id.
        rewrite id_right.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat
                   (!(catiso_catiso_inv_ob F_iso x))).
        }
        rewrite pathsinv0l.
        apply idpath.
      - intros x y z f g ; cbn -[catiso_inv_mor].
        use catiso_inv_mor_eq ; cbn -[catiso_inv_mor].
        rewrite functor_comp.
        rewrite !(catiso_catiso_inv_mor F_iso).
        refine (!_).
        etrans.
        {
          rewrite !assoc.
          etrans.
          {
            do 6 apply maponpaths_2.
            refine (!_).
            apply (pr1_idtoiso_concat
                     (!(catiso_catiso_inv_ob F_iso x))).
          }
          rewrite pathsinv0l.
          cbn.
          rewrite id_left.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            do 3 apply maponpaths_2.
            refine (!_).
            apply (pr1_idtoiso_concat
                     (!(catiso_catiso_inv_ob F_iso y))).
          }
          rewrite pathsinv0l.
          cbn.
          rewrite id_left.
          rewrite !assoc'.
          apply maponpaths.
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (!(catiso_catiso_inv_ob F_iso z))).
          }
          rewrite pathsinv0l.
          apply idpath.
        }
        cbn.
        rewrite id_right.
        apply idpath.
    Qed.

    Definition is_cat_iso_to_is_z_isomorphism_inv
      : D ⟶ C.
    Proof.
      use make_functor.
      - exact is_cat_iso_to_is_z_isomorphism_inv_data.
      - exact is_cat_iso_to_is_z_isomorphism_inv_laws.
    Defined.

    Proposition is_cat_iso_to_is_z_isomorphism_laws
      : @is_inverse_in_precat cat_of_setcategory
           C D
           F
           is_cat_iso_to_is_z_isomorphism_inv.
    Proof.
      split.
      - use functor_eq ; [ apply homset_property | ].
        use functor_data_eq_alt.
        + intros x ; cbn.
          apply homotinvweqweq.
        + intros x y f ; cbn -[catiso_inv_mor].
          rewrite (catiso_inv_mor_cat_iso F_iso).
          rewrite !assoc'.
          apply maponpaths.
          refine (_ @ id_right _).
          apply maponpaths.
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (!(catiso_inv_ob_catiso F_iso y))).
          }
          rewrite pathsinv0l.
          apply idpath.
      - use functor_eq ; [ apply homset_property | ].
        use functor_data_eq_alt.
        + intros x ; cbn.
          exact (homotweqinvweq (catiso_ob_weq F_iso) x).
        + intros x y f ; cbn -[catiso_inv_mor].
          rewrite (catiso_catiso_inv_mor F_iso).
          rewrite !assoc'.
          apply maponpaths.
          refine (_ @ id_right _).
          apply maponpaths.
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (!(catiso_catiso_inv_ob F_iso y))).
          }
          rewrite pathsinv0l.
          apply idpath.
    Qed.

    Definition is_cat_iso_to_is_z_isomorphism
      : @is_z_isomorphism cat_of_setcategory C D F.
    Proof.
      use make_is_z_isomorphism.
      - exact is_cat_iso_to_is_z_isomorphism_inv.
      - exact is_cat_iso_to_is_z_isomorphism_laws.
    Defined.
  End ToIso.

  Section FromIso.
    Context (HF : @is_z_isomorphism cat_of_setcategory C D F).

    Let F_iso : @z_iso cat_of_setcategory C D := F ,, HF.

    Let G : D ⟶ C := inv_from_z_iso F_iso.

    Lemma is_z_isomorphism_to_is_cat_iso_eq_l
          (x : C)
      : G(F x) = x.
    Proof.
      exact (path_functor_ob (z_iso_inv_after_z_iso F_iso) x).
    Defined.

    Lemma is_z_isomorphism_to_is_cat_iso_eq_r
          (y : D)
      : F(G y) = y.
    Proof.
      exact (path_functor_ob (z_iso_after_z_iso_inv F_iso) y).
    Defined.

    Definition is_z_isomorphism_to_is_cat_iso
      : is_catiso F.
    Proof.
      split.
      - intros x y.
        use isweq_iso.
        + exact (λ f,
                 idtoiso (!(is_z_isomorphism_to_is_cat_iso_eq_l _))
                 · #G f
                 · idtoiso (is_z_isomorphism_to_is_cat_iso_eq_l _)).
        + intro f.
          cbn.
          rewrite !assoc'.
          unfold is_z_isomorphism_to_is_cat_iso_eq_l.
          etrans.
          {
            apply maponpaths.
            exact (path_functor_mor (z_iso_inv_after_z_iso F_iso) f).
          }
          cbn.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (!(pr1_idtoiso_concat
                       (!(path_functor_ob (z_iso_inv_after_z_iso F_iso) x))
                       (path_functor_ob (z_iso_inv_after_z_iso F_iso) x))).
          }
          rewrite pathsinv0l.
          apply id_left.
        + intro f.
          refine (_ @ path_functor_mor_alt (z_iso_after_z_iso_inv F_iso) f).
          cbn.
          rewrite !functor_comp.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso F).
          }
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply (pr1_maponpaths_idtoiso F).
          }
          use setcategory_eq_idtoiso_comp.
      - use isweq_iso.
        + exact (λ y, G y).
        + exact is_z_isomorphism_to_is_cat_iso_eq_l.
        + exact is_z_isomorphism_to_is_cat_iso_eq_r.
    Qed.
  End FromIso.
End CatIsoWeqIso.

Definition is_catiso_weq_is_z_isomorphism
           {C D : setcategory}
           (F : C ⟶ D)
  : is_catiso F ≃ @is_z_isomorphism cat_of_setcategory C D F.
Proof.
  use weqimplimpl.
  - exact (is_cat_iso_to_is_z_isomorphism F).
  - exact (is_z_isomorphism_to_is_cat_iso F).
  - apply isaprop_is_catiso.
  - apply isaprop_is_z_isomorphism.
Defined.

(** * 3. The univalence of the category of strict categories *)
Definition path_setcategory_help_fun
           {C D : setcategory}
           (p : C = D)
  : category_from_setcategory C = category_from_setcategory D.
Proof.
  induction p.
  apply idpath.
Defined.

Definition path_setcategory_help_fun_alt
           {C D : setcategory}
           (p : C = D)
  : category_from_setcategory C = category_from_setcategory D.
Proof.
  use total2_paths_f.
  - exact (base_paths _ _ p).
  - apply isaprop_has_homsets.
Defined.

Proposition path_setcategory_help_fun_eq
            {C D : setcategory}
            (p : C = D)
  : path_setcategory_help_fun p = path_setcategory_help_fun_alt p.
Proof.
  induction p.
  refine (!_).
  refine (_ @ total2_fiber_paths _).
  unfold path_setcategory_help_fun_alt.
  apply maponpaths.
  apply isasetaprop.
  apply isaprop_has_homsets.
Qed.

Definition path_setcategory
           (C D : setcategory)
  : C = D
    ≃
    category_from_setcategory C = category_from_setcategory D.
Proof.
  use weq_iso.
  - exact path_setcategory_help_fun.
  - intro p.
    use total2_paths_f.
    + exact (base_paths _ _ p).
    + apply isaprop_is_setcategory.
  - abstract
      (intro p ;
       induction p ;
       rewrite path_setcategory_help_fun_eq ;
       unfold path_setcategory_help_fun_alt ;
       rewrite base_total2_paths ;
       refine (_ @ total2_fiber_paths _) ;
       apply maponpaths ;
       apply isasetaprop ;
       apply isaprop_is_setcategory).
  - abstract
      (intro p ;
       induction C as [ C HC ] ;
       induction D as [ D HD ] ;
       rewrite path_setcategory_help_fun_eq ;
       unfold path_setcategory_help_fun_alt ;
       rewrite base_total2_paths ;
       refine (_ @ total2_fiber_paths _) ;
       apply maponpaths ;
       apply isasetaprop ;
       apply isaprop_has_homsets).
Defined.

Proposition is_univalent_cat_of_setcategory
  : is_univalent cat_of_setcategory.
Proof.
  intros C D.
  use weqhomot.
  - exact (weqfibtototal _ _ is_catiso_weq_is_z_isomorphism
           ∘ catiso_is_path_cat _ _
           ∘ path_setcategory _ _)%weq.
  - intro p.
    induction p.
    use z_iso_eq.
    use subtypePath.
    {
      intro.
      apply isaprop_is_functor.
      apply homset_property.
    }
    apply idpath.
Qed.

Definition univalent_cat_of_setcategory
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact cat_of_setcategory.
  - exact is_univalent_cat_of_setcategory.
Defined.
