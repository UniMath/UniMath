From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.WeakEquivalences.
Require Import UniMath.CategoryTheory.DaggerCategories.Examples.Fullsub.

Local Open Scope cat.

Section ImageFactorization.

  Context {C D : category}
          {dagC : dagger C}
          {dagD : dagger D}
          {F : functor C D}
          (dagF : is_dagger_functor dagC dagD F).

  Definition is_in_dagger_img_functor (d : D)
    : hProp
    := ∃ c : C, unitary dagD (F c) d.

  Let P := (λ d : D, is_in_dagger_img_functor d).

  Definition full_dagger_img
    : category
    := full_sub_category D P.

  (*
     This definition is currently 'standalone' in this file (or however you say that it doesn't have any impact on the rest of this file.
     However, this I have already added this for future work when trying to compare multiple (whatever) factorization systems on DAG.
   *)
  Definition full_dagger_img_to_full_img
    : functor (full_sub_category D P) (full_sub_category D (λ d : D, is_in_img_functor F d)).
  Proof.
    use full_sub_category_functor.
    - exact (functor_identity D).
    - intros d in_dag_im.
      use (factor_through_squash_hProp _ _ in_dag_im).
      clear in_dag_im ; intro in_dag_im.
      apply hinhpr.
      exists (pr1 in_dag_im).
      exact (make_z_iso _ _ (pr22 in_dag_im)).
  Defined.

  Definition full_img_dagger
    : dagger full_dagger_img
    := full_sub_dagger dagD P.

  Definition full_dagger_img_functor_obj
    : ob C -> full_dagger_img.
  Proof.
    intro c.
    exists (F c).
    intros a b.
    apply b.
    exists c.
    apply unitary_id.
  Defined.

  Definition full_dagger_img_functor_data
    : functor_data C full_dagger_img.
  Proof.
    exists full_dagger_img_functor_obj.
    exact (λ a b f, #F f ,, tt).
  Defined.

  Lemma is_functor_full_dagger_img
    : is_functor full_dagger_img_functor_data.
  Proof.
    split.
    - intro ; apply subtypePath.
      { intro; apply isapropunit. }
      apply functor_id.
    - intro ; intros ; apply subtypePath.
      { intro ; apply isapropunit. }
      apply functor_comp.
  Qed.

  Definition functor_full_dagger_img
    : functor C full_dagger_img
    := _ ,, is_functor_full_dagger_img.

  Definition functor_full_img_is_dagger_functor
    : is_dagger_functor dagC full_img_dagger functor_full_dagger_img.
  Proof.
    intro ; intros ; use subtypePath ; [intro ; apply isapropunit | ].
    apply dagF.
  Qed.

  Lemma functor_full_img_is_unitarily_eso
    : is_unitarily_eso functor_full_img_is_dagger_functor.
  Proof.
    intro d.
    use (factor_through_squash_hProp _ _ (pr2 d)).
    intro c.
    apply hinhpr.
    exists (pr1 c).
    exists (pr12 c ,, tt).
    split ; (use subtypePath ; [intro ; apply isapropunit |]) ; apply (pr2 c).
  Qed.

  Definition factorization_full_dagger_inclusion_equal
    :  functor_full_dagger_img ∙ sub_precategory_inclusion D (full_sub_precategory P) = F.
  Proof.
    apply (functor_eq  _ _ (pr2 D)).
    apply idpath.
  Defined.

  Definition dagger_functor_dagger_img_factorization
    : ∑ (I : category) (dagI : dagger I)
        (F0 : functor C I) (F1 : functor I D)
        (dagF0 : is_dagger_functor dagC dagI F0)
        (dagF1 : is_dagger_functor dagI dagD F1),
      is_unitarily_eso dagF0
                       × fully_faithful F1
                       × functor_composite F0 F1 = F.
  Proof.
    exists full_dagger_img.
    exists full_img_dagger.
    exists functor_full_dagger_img.
    exists (sub_precategory_inclusion D (full_sub_precategory P)).
    exists functor_full_img_is_dagger_functor.
    exists (inclusion_is_dagger_functor _ _).
    exists functor_full_img_is_unitarily_eso.
    exists (fully_faithful_sub_precategory_inclusion _ _).
    apply factorization_full_dagger_inclusion_equal.
  Defined.

End ImageFactorization.
