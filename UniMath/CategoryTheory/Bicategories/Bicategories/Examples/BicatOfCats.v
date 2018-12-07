(* ******************************************************************************* *)
(** * Bicategory of 1-categories

    Benedikt Ahrens, Marco Maggesi

    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.

Local Open Scope cat.

Definition cat_prebicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact category.
  - exact (λ C D, functor C D).
  - exact (λ _ _ F G, nat_trans F G).
  - exact (λ C, functor_identity C).
  - exact (λ _ _ _ F G, functor_composite F G).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ α β, nat_trans_comp _ _ _ α β).
  - exact (λ _ _ _ F _ _ α, pre_whisker F α).
  - exact (λ _ _ _ _ _ H α, post_whisker α H).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
Defined.

Definition cat_prebicat_laws : prebicat_laws cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_right.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply assoc.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply functor_id.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_comp i). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (nat_trans_ax y ). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_id g). apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    repeat rewrite id_left. apply functor_id.
Qed.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_cats : isaset_cells prebicat_of_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_cats : bicat
  := (prebicat_of_cats,, isaset_cells_prebicat_of_cats).

Definition is_invertible_2cell_to_is_nat_iso
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_invertible_2cell η → is_nat_iso η.
Proof.
  intros Hη X.
  use is_iso_qinv.
  - apply (Hη^-1).
  - split ; cbn.
    + exact (nat_trans_eq_pointwise (vcomp_rinv Hη) X).
    + exact (nat_trans_eq_pointwise (vcomp_lid Hη) X).
Defined.

Definition invertible_2cell_to_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : invertible_2cell F G → nat_iso F G.
Proof.
  intros η.
  use mk_nat_iso.
  - exact (cell_from_invertible_2cell η).
  - apply is_invertible_2cell_to_is_nat_iso.
    apply η.
Defined.

Definition is_nat_iso_to_is_invertible_2cell
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_nat_iso η → is_invertible_2cell η.
Proof.
  intros Hη.
  use tpair.
  - apply (nat_iso_inv (η ,, Hη)).
  - split.
    + apply nat_trans_eq.
      { apply D. }
      intros X ; cbn.
      exact (iso_inv_after_iso (pr1 η X ,, _)).
    + apply nat_trans_eq.
      { apply D. }
      intros X ; cbn.
      exact (iso_after_iso_inv (pr1 η X ,, _)).
Defined.

Definition nat_iso_to_invertible_2cell
           {C D : bicat_of_cats}
           (F G : C --> D)
  : nat_iso F G → invertible_2cell F G.
Proof.
  intros η.
  use tpair.
  - apply η.
  - apply is_nat_iso_to_is_invertible_2cell.
    apply η.
Defined.

Definition invertible_2cell_is_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : invertible_2cell F G ≃ nat_iso F G.
Proof.
  use weqpair.
  - exact (invertible_2cell_to_nat_iso F G).
  - use isweq_iso.
    + exact (nat_iso_to_invertible_2cell F G).
    + intros X.
      use subtypeEquality.
      * intro.
        apply isaprop_is_invertible_2cell.
      * reflexivity.
    + intros X.
      use subtypeEquality.
      * intro.
        apply impred.
        intro.
        apply isaprop_is_iso.
      * reflexivity.
Defined.

Definition adj_equiv_to_equiv_cat
           {C D : bicat_of_cats}
           (F : C --> D)
  : left_adjoint_equivalence F → adj_equivalence_of_precats F.
Proof.
  intros A.
  use mk_adj_equivalence_of_precats.
  - exact (left_adjoint_right_adjoint A).
  - exact (left_adjoint_unit A).
  - exact (left_adjoint_counit A).
  - split.
    + intro X.
      cbn.
      pose (nat_trans_eq_pointwise (internal_triangle1 A) X) as p.
      cbn in p.
      rewrite !id_left, !id_right in p.
      exact p.
    + intro X.
      cbn.
      pose (nat_trans_eq_pointwise (internal_triangle2 A) X) as p.
      cbn in p.
      rewrite !id_left, !id_right in p.
      exact p.
  - split.
    + intro X.
      apply (invertible_2cell_to_nat_iso _ _ (left_equivalence_unit_iso A)).
    + intro X.
      apply (invertible_2cell_to_nat_iso _ _ (left_equivalence_counit_iso A)).
Defined.

Definition equiv_cat_to_adj_equiv
           {C D : bicat_of_cats}
           (F : C --> D)
  : adj_equivalence_of_precats F → left_adjoint_equivalence F.
Proof.
  intros A.
  use tpair.
  - use tpair.
    + apply A.
    + split ; cbn.
      * exact (pr1(pr1(pr2(pr1 A)))).
      * exact (pr2(pr1(pr2(pr1 A)))).
  - split ; split.
    + apply nat_trans_eq.
      { apply D. }
      intro X ; cbn.
      rewrite id_left, !id_right.
      apply (pr2(pr2(pr1 A))).
    + apply nat_trans_eq.
      { apply C. }
      intro X ; cbn.
      rewrite id_left, !id_right.
      apply (pr2(pr2(pr1 A))).
    + apply is_nat_iso_to_is_invertible_2cell.
      intro X.
      apply (pr2 A).
    + apply is_nat_iso_to_is_invertible_2cell.
      intro X.
      apply (pr2 A).
Defined.

Definition adj_equiv_is_equiv_cat
           {C D : bicat_of_cats}
           (F : C --> D)
  : left_adjoint_equivalence F ≃ adj_equivalence_of_precats F.
Proof.
  use weqpair.
  - exact (adj_equiv_to_equiv_cat F).
  - use isweq_iso.
    + exact (equiv_cat_to_adj_equiv F).
    + intros A.
      use subtypeEquality.
      * intro.
        do 2 apply isapropdirprod.
        ** apply bicat_of_cats.
        ** apply bicat_of_cats.
        ** apply isaprop_is_invertible_2cell.
        ** apply isaprop_is_invertible_2cell.
      * reflexivity.
    + intros A.
      use subtypeEquality.
      * intro.
        apply isapropdirprod ; apply impred ; intro ; apply isaprop_is_iso.
      * use total2_paths_b.
        ** reflexivity.
        ** use subtypeEquality.
           *** intro ; simpl.
               apply isaprop_form_adjunction.
           *** reflexivity.
Defined.