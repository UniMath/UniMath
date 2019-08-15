(* ******************************************************************************* *)
(** * Yoneda Lemma
    Niccolo Veltri, Niels van der Weide
    June 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Yoneda.
Require Import UniMath.Bicategories.PseudoFunctors.Representable.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Opaque psfunctor.

Section YonedaLemma.
  Context {B : bicat}.
  Variable (B_is_univalent_2_1 : is_univalent_2_1 B)
           (F : psfunctor (op1_bicat B) bicat_of_cats)
           (X : B).

  (** First, we construct a functor from the yoneda to the presheaf *)
  Definition yoneda_to_presheaf_data_ob
    : pstrans (representable B_is_univalent_2_1 X) F → pr1 (F X).
  Proof.
    intro τ.
    pose (τ X) as f; cbn in f.
    exact (f (identity X)).
  Defined.

  Definition yoneda_to_presheaf_data_mor
             (η₁ η₂ : pstrans (representable B_is_univalent_2_1 X) F)
             (m : modification η₁ η₂)
    : yoneda_to_presheaf_data_ob η₁ --> yoneda_to_presheaf_data_ob η₂.
  Proof.
    pose (m X) as n; cbn in n.
    exact (n (identity X)).
  Defined.

  Definition yoneda_to_presheaf_data
    : functor_data
        (univ_hom
           (psfunctor_bicat_is_univalent_2_1
              (op1_bicat B) bicat_of_cats
              univalent_cat_is_univalent_2_1)
           (y B_is_univalent_2_1 X) F)
        (F X : univalent_category).
  Proof.
    use make_functor_data.
    - exact yoneda_to_presheaf_data_ob.
    - exact yoneda_to_presheaf_data_mor.
  Defined.

  Definition yoneda_to_presheaf_is_functor
    : is_functor yoneda_to_presheaf_data.
  Proof.
    split.
    - intro η ; cbn.
      apply idpath.
    - intros η₁ η₂ η₃ f g ; cbn.
      apply idpath.
  Qed.


  Definition yoneda_to_presheaf
    : bicat_of_cats
        ⟦ univ_hom
            (psfunctor_bicat_is_univalent_2_1
               _ _ univalent_cat_is_univalent_2_1)
            (y B_is_univalent_2_1 X) F
          , F X ⟧.
  Proof.
    use make_functor.
    - exact yoneda_to_presheaf_data.
    - exact yoneda_to_presheaf_is_functor.
  Defined.

  (** Next, we construct a functor in the opposite direction *)
  Section PresheafToYonedaOb.
    Variable (x : (F X : univalent_category)).

    Definition presheaf_to_yoneda_ob_pstrans_functor_ob
               (Y : op1_bicat B)
      : B ⟦ Y , X ⟧ → pr1 (F Y)
      := λ f, (#F f : _ ⟶ _) x.

    Definition presheaf_to_yoneda_ob_pstrans_functor_mor
               (Y : op1_bicat B)
               (f g : B ⟦ Y , X ⟧)
               (α : f ==> g)
      : (presheaf_to_yoneda_ob_pstrans_functor_ob Y f)
          -->
          presheaf_to_yoneda_ob_pstrans_functor_ob Y g
      := (##F α : nat_trans _ _) x.

    Definition presheaf_to_yoneda_ob_pstrans_functor_data
               (Y : op1_bicat B)
      : functor_data (@hom B Y X) (pr1 (F Y)).
    Proof.
      use make_functor_data.
      - exact (presheaf_to_yoneda_ob_pstrans_functor_ob Y).
      - exact (presheaf_to_yoneda_ob_pstrans_functor_mor Y).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_functor
               (Y : op1_bicat B)
      : is_functor (presheaf_to_yoneda_ob_pstrans_functor_data Y).
    Proof.
      split.
      - intro f ; cbn.
        unfold presheaf_to_yoneda_ob_pstrans_functor_mor ;
        unfold presheaf_to_yoneda_ob_pstrans_functor_ob.
        exact (nat_trans_eq_pointwise (psfunctor_id2 F f) x).
      - intros f₁ f₂ f₃ α₁ α₂ ; cbn.
        unfold presheaf_to_yoneda_ob_pstrans_functor_mor.
        exact (nat_trans_eq_pointwise (psfunctor_vcomp F α₁ α₂) x).
    Qed.

    Definition presheaf_to_yoneda_ob_pstrans_functor
               (Y : op1_bicat B)
      : bicat_of_cats ⟦ @univ_hom B B_is_univalent_2_1 Y X , F Y ⟧.
    Proof.
      use make_functor.
      - exact (presheaf_to_yoneda_ob_pstrans_functor_data Y).
      - exact (presheaf_to_yoneda_ob_pstrans_is_functor Y).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_nat_trans_data
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : nat_trans_data
          (presheaf_to_yoneda_ob_pstrans_functor Y₁ · # F f : _ ⟶ _)
          (#(y B_is_univalent_2_1 X : psfunctor _ _) f
            · presheaf_to_yoneda_ob_pstrans_functor Y₂ : _ ⟶ _).
    Proof.
      intros g ; cbn in *.
      unfold presheaf_to_yoneda_ob_pstrans_functor_ob.
      pose (psfunctor_comp F g f : _ ==> _) as p ; cbn in p.
      exact (p x).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_nat_trans
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : is_nat_trans _ _ (presheaf_to_yoneda_ob_pstrans_nat_trans_data Y₁ Y₂ f).
    Proof.
      intros g₁ g₂ α ; cbn in *.
      unfold presheaf_to_yoneda_ob_pstrans_functor_mor ;
      unfold presheaf_to_yoneda_ob_pstrans_nat_trans_data.
      pose (psfunctor_rwhisker F f α) as p.
      pose (nat_trans_eq_pointwise p x) as q.
      exact (!q).
    Qed.

    Definition presheaf_to_yoneda_ob_pstrans_nat_trans
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : (presheaf_to_yoneda_ob_pstrans_functor Y₁ · # F f)
          ==>
          #(y B_is_univalent_2_1 X : psfunctor _ _) f
          · presheaf_to_yoneda_ob_pstrans_functor Y₂.
    Proof.
      use make_nat_trans.
      - exact (presheaf_to_yoneda_ob_pstrans_nat_trans_data Y₁ Y₂ f).
      - exact (presheaf_to_yoneda_ob_pstrans_is_nat_trans Y₁ Y₂ f).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_nat_iso
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : is_nat_iso (presheaf_to_yoneda_ob_pstrans_nat_trans Y₁ Y₂ f).
    Proof.
      intro g ; cbn in g.
      unfold presheaf_to_yoneda_ob_pstrans_nat_trans.
      simpl.
      unfold presheaf_to_yoneda_ob_pstrans_nat_trans_data.
      pose (is_invertible_2cell_to_is_nat_iso (psfunctor_comp F g f)) as i.
      apply i.
      exact (psfunctor_comp F g f).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_data
      : pstrans_data ((y B_is_univalent_2_1) X) F.
    Proof.
      pose x.
      use make_pstrans_data.
      - exact presheaf_to_yoneda_ob_pstrans_functor.
      - intros Y₁ Y₂ f.
        use make_invertible_2cell.
        + exact (presheaf_to_yoneda_ob_pstrans_nat_trans Y₁ Y₂ f).
        + apply is_nat_iso_to_is_invertible_2cell.
          exact (presheaf_to_yoneda_ob_pstrans_is_nat_iso Y₁ Y₂ f).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_pstrans
      : is_pstrans presheaf_to_yoneda_ob_pstrans_data.
    Proof.
      repeat split.
      - intros Y₁ Y₂ g₁ g₂ α.
        apply nat_trans_eq.
        { apply homset_property. }
        intro h ; cbn in *.
        unfold presheaf_to_yoneda_ob_pstrans_functor_ob,
               presheaf_to_yoneda_ob_pstrans_functor_mor,
               presheaf_to_yoneda_ob_pstrans_nat_trans_data.
        pose (psfunctor_lwhisker F h α).
        pose (nat_trans_eq_pointwise p x) as q.
        exact (!q).
      - intros Y.
        apply nat_trans_eq.
        { apply homset_property. }
        intro h ; cbn in *.
        unfold presheaf_to_yoneda_ob_pstrans_functor_ob,
               presheaf_to_yoneda_ob_pstrans_functor_mor,
               presheaf_to_yoneda_ob_pstrans_nat_trans_data.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            apply id_left.
          }
          etrans.
          {
            apply id_left.
          }
          exact (nat_trans_eq_pointwise (psfunctor_rinvunitor F h) x).
        }
        cbn -[psfunctor_id psfunctor_comp].
        apply maponpaths_2.
        apply id_left.
      - intros Y₁ Y₂ Y₃ g₁ g₂.
        apply nat_trans_eq.
        { apply homset_property. }
        intro h ; cbn in *.
        unfold presheaf_to_yoneda_ob_pstrans_functor_ob,
               presheaf_to_yoneda_ob_pstrans_functor_mor,
               presheaf_to_yoneda_ob_pstrans_nat_trans_data.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            etrans.
            { apply id_right. }
            apply maponpaths_2.
            etrans.
            { apply id_right. }
            apply id_left.
          }
          exact (nat_trans_eq_pointwise (psfunctor_rassociator F h g₁ g₂) x).
        }
        simpl.
        etrans.
        {
          apply maponpaths_2.
          apply id_left.
        }
        reflexivity.
    Qed.

    Definition presheaf_to_yoneda_ob
      : pstrans (y B_is_univalent_2_1 X) F.
    Proof.
      use make_pstrans.
      - exact presheaf_to_yoneda_ob_pstrans_data.
      - exact presheaf_to_yoneda_ob_pstrans_is_pstrans.
    Defined.
  End PresheafToYonedaOb.

  Section PresheafToYonedaMor.
    Variable (a b : (F X : univalent_category))
             (f : a --> b).

    Definition presheaf_to_yoneda_mor_modification_nat_trans_data
               (Y : op1_bicat B)
      : nat_trans_data
          ((presheaf_to_yoneda_ob a) Y : _ ⟶ _)
          ((presheaf_to_yoneda_ob b) Y : _ ⟶ _)
      := λ h, #(#F h : _ ⟶ _) f.

    Definition presheaf_to_yoneda_mor_modification_is_nat_trans
               (Y : op1_bicat B)
      : is_nat_trans
          _ _
          (presheaf_to_yoneda_mor_modification_nat_trans_data Y).
    Proof.
      intros h₁ h₂ α ; cbn in *.
      unfold presheaf_to_yoneda_ob_pstrans_functor_mor,
             presheaf_to_yoneda_mor_modification_nat_trans_data.
      pose (pr2 (##F α : _ ⟹ _)) as p.
      exact (!(p a b f)).
    Qed.

    Definition presheaf_to_yoneda_mor_modification_data
      : modification_data (presheaf_to_yoneda_ob a) (presheaf_to_yoneda_ob b).
    Proof.
      intros Y.
      use make_nat_trans.
      - exact (presheaf_to_yoneda_mor_modification_nat_trans_data Y).
      - exact (presheaf_to_yoneda_mor_modification_is_nat_trans Y).
    Defined.

    Definition presheaf_to_yoneda_mor_is_modification
      : is_modification presheaf_to_yoneda_mor_modification_data.
    Proof.
      intros Y₁ Y₂ g.
      apply nat_trans_eq.
      { apply homset_property. }
      intros h ; cbn in *.
      unfold presheaf_to_yoneda_ob_pstrans_nat_trans_data,
             presheaf_to_yoneda_mor_modification_nat_trans_data.
      pose (pr21 (psfunctor_comp F h g)) as p.
      exact (!(p a b f)).
    Qed.

    Definition presheaf_to_yoneda_mor_modification
      : modification (presheaf_to_yoneda_ob a) (presheaf_to_yoneda_ob b).
    Proof.
      use make_modification.
      - exact presheaf_to_yoneda_mor_modification_data.
      - exact presheaf_to_yoneda_mor_is_modification.
    Defined.
  End PresheafToYonedaMor.

  Definition presheaf_to_yoneda_data
    : functor_data
        (F X : univalent_category)
        (univ_hom
           (psfunctor_bicat_is_univalent_2_1
              (op1_bicat B) bicat_of_cats
              univalent_cat_is_univalent_2_1) ((y B_is_univalent_2_1) X) F).
  Proof.
    use make_functor_data.
    - exact presheaf_to_yoneda_ob.
    - exact presheaf_to_yoneda_mor_modification.
  Defined.

  Definition presheaf_to_yoneda_is_functor
    : is_functor presheaf_to_yoneda_data.
  Proof.
    split.
    - intros z.
      apply modification_eq.
      intros Z.
      apply nat_trans_eq.
      { apply homset_property. }
      intros f.
      cbn in *.
      unfold  presheaf_to_yoneda_mor_modification_nat_trans_data,
              presheaf_to_yoneda_ob_pstrans_functor_ob.
      apply functor_id.
    - intros z₁ z₂ z₃ f₁ f₂.
      apply modification_eq.
      intros Z.
      apply nat_trans_eq.
      { apply homset_property. }
      intros f.
      cbn in *.
      unfold  presheaf_to_yoneda_mor_modification_nat_trans_data,
              presheaf_to_yoneda_ob_pstrans_functor_ob.
      apply functor_comp.
  Qed.

  Definition presheaf_to_yoneda
    : bicat_of_cats
        ⟦ F X ,
          univ_hom
            (psfunctor_bicat_is_univalent_2_1
               _ _ univalent_cat_is_univalent_2_1)
            (y B_is_univalent_2_1 X) F ⟧.
  Proof.
    use make_functor.
    - exact presheaf_to_yoneda_data.
    - exact presheaf_to_yoneda_is_functor.
  Defined.

  Definition yoneda_unit_component_mod_component_nat_component
             (η : pstrans (representable B_is_univalent_2_1 X) F)
             (Z : op1_bicat B)
             (f : B ⟦ Z , X ⟧)
    : pr1 (F Z)
        ⟦ (η Z : _ ⟶ _) f ,
          (# F f : _ ⟶ _) ((η X : _ ⟶ _) (id₁ X)) ⟧
    := #(η Z : _ ⟶ _) (rinvunitor f)
        · pr1 ((psnaturality_of η f)^-1) (id₁ X).

  Definition yoneda_unit_component_mod_component_is_nat_trans
             (η : pstrans (representable B_is_univalent_2_1 X) F)
             (Z : op1_bicat B)
             (f₁ f₂ : B ⟦ Z , X ⟧)
             (α : f₁ ==> f₂)
    : # (η Z : _ ⟶ _) α
        · yoneda_unit_component_mod_component_nat_component η Z f₂
      =
      (yoneda_unit_component_mod_component_nat_component η Z f₁)
        · (## F α : _ ⟹ _) ((η X : _ ⟶ _) (id₁ X)).
  Proof.
    cbn ; unfold yoneda_unit_component_mod_component_nat_component.
    pose (nat_trans_eq_pointwise (psnaturality_inv_natural η _ _ _ _ α) (id₁ X)).
    cbn in p.
    refine (!_).
    etrans.
    {
      refine (!(assoc _ _ _) @ _).
      apply maponpaths.
      exact (nat_trans_eq_pointwise (psnaturality_inv_natural η _ _ _ _ α) (id₁ X)).
    }
    cbn.
    refine (assoc _ _ _ @ _ @ !(assoc _ _ _)).
    apply maponpaths_2.
    refine (!(functor_comp _ _ _) @ _ @ functor_comp _ _ _).
    apply maponpaths.
    refine (!_).
    refine (rinvunitor_natural _ @ _).
    apply maponpaths.
    refine (!_).
    apply rwhisker_hcomp.
  Qed.

  Definition yoneda_unit_component_mod_component_nat
             (η : pstrans (representable B_is_univalent_2_1 X) F)
    : modification_data
        ((functor_identity (hom_data (representable B_is_univalent_2_1 X) F)) η)
        ((yoneda_to_presheaf ∙ presheaf_to_yoneda) η).
  Proof.
    intro Z.
    use make_nat_trans.
    - exact (yoneda_unit_component_mod_component_nat_component η Z).
    - exact (yoneda_unit_component_mod_component_is_nat_trans η Z).
  Defined.

  Definition yoneda_unit_component_is_modification
             (η : pstrans (representable B_is_univalent_2_1 X) F)
    : is_modification (yoneda_unit_component_mod_component_nat η).
  Proof.
    intros Z₁ Z₂ f.
    apply nat_trans_eq.
    { apply homset_property. }
    intro g ; cbn in g.
    cbn.
    unfold yoneda_unit_component_mod_component_nat_component, yoneda_to_presheaf_data_ob,
    presheaf_to_yoneda_ob_pstrans_nat_trans_data.
    cbn in f.
    etrans.
    {
      do 2 apply maponpaths.
      exact (nat_trans_eq_pointwise (pstrans_inv_comp_alt η g f) (id₁ X)).
    }
    cbn.
    rewrite !id_right.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply functor_comp.
    }
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        apply id2_right.
      }
      refine (!(assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply functor_comp.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply rinvunitor_triangle.
      }
      cbn.
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply lassociator_rassociator.
      }
      apply id2_right.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (pr21 (psnaturality_of η f) g (g · id₁ X) (rinvunitor g)).
    }
    cbn.
    etrans.
    {
      refine (!(assoc _ _ _) @ _).
      apply maponpaths.
      exact (nat_trans_eq_pointwise (vcomp_rinv (psnaturality_of η f)) (g · id₁ X)).
    }
    apply id_right.
  Qed.

  Definition yoneda_unit_component_mod
             (η : pstrans (representable B_is_univalent_2_1 X) F)
    : modification
        (functor_identity (hom_data (representable B_is_univalent_2_1 X) F) η)
        ((yoneda_to_presheaf ∙ presheaf_to_yoneda) η).
  Proof.
    use make_modification.
    - exact (yoneda_unit_component_mod_component_nat η).
    - exact (yoneda_unit_component_is_modification η).
  Defined.

  Definition yoneda_unit_is_nat_trans
    : is_nat_trans
        (functor_identity (hom_data (representable B_is_univalent_2_1 X) F))
        (yoneda_to_presheaf ∙ presheaf_to_yoneda)
        yoneda_unit_component_mod.
  Proof.
    intros η₁ η₂ m.
    apply modification_eq.
    intros Z.
    apply nat_trans_eq.
    { apply homset_property. }
    intros g ; cbn in g.
    cbn.
    unfold yoneda_unit_component_mod_component_nat_component, yoneda_to_presheaf_data_ob,
    presheaf_to_yoneda_mor_modification_nat_trans_data,
    yoneda_to_presheaf_data_mor.
    refine (!_).
    etrans.
    {
      rewrite <- assoc.
      apply maponpaths.
      exact (!(nat_trans_eq_pointwise (mod_inv_naturality_of m X Z g) (id₁ X))).
    }
    simpl.
    rewrite !assoc.
    apply maponpaths_2.
    exact (pr2 ((m : modification _ _) Z) _ _ (rinvunitor g)).
  Qed.

  Definition yoneda_unit
    : functor_identity _ ⟹ yoneda_to_presheaf ∙ presheaf_to_yoneda.
  Proof.
    use make_nat_trans.
    - exact yoneda_unit_component_mod.
    - exact yoneda_unit_is_nat_trans.
  Defined.

  Definition yoneda_unit_is_inverses
             (g : pstrans (representable B_is_univalent_2_1 X) F)
             (Z : B)
             (Y : Z --> X)
    :  is_inverse_in_precat
         (# (g Z : _ ⟶ _) (rinvunitor Y) · pr1 ((psnaturality_of g Y) ^-1) (id₁ X))
         ((pr11 (psnaturality_of g Y)) (id₁ X) · # (g Z : _ ⟶ _) (runitor Y)).
  Proof.
    split.
    - rewrite <- !assoc.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          rewrite assoc.
          apply maponpaths_2.
          exact (nat_trans_eq_pointwise (vcomp_lid (psnaturality_of g Y)) (id₁ X)).
        }
        apply id_left.
      }
      refine (!(functor_comp _ _ _) @ _ @ functor_id (g Z) _).
      apply maponpaths.
      exact (rinvunitor_runitor Y).
    - rewrite <- !assoc.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          rewrite assoc.
          apply maponpaths_2.
          refine (!(functor_comp (g Z) _ _) @ _ @ functor_id (g Z) _).
          apply maponpaths.
          apply runitor_rinvunitor.
        }
        apply id_left.
      }
      exact (nat_trans_eq_pointwise (vcomp_rinv (psnaturality_of g Y)) (id₁ X)).
  Qed.

  Definition yoneda_unit_iso
             (g : pstrans (representable B_is_univalent_2_1 X) F)
             (Z : B)
             (Y : Z --> X)
    : is_iso (# (g Z : _ ⟶ _) (rinvunitor Y) · pr1 ((psnaturality_of g Y) ^-1) (id₁ X)).
  Proof.
    use is_iso_qinv.
    - exact (pr11 (psnaturality_of g Y) (id₁ X) · #(g Z : _ ⟶ _) (runitor Y)).
    - exact (yoneda_unit_is_inverses g Z Y).
  Defined.

  Definition yoneda_counit_component
             (Z : pr1 (F X))
    : pr1 (F X) ⟦ (# F (id₁ X) : _ ⟶ _) Z, Z ⟧
    := pr1 ((psfunctor_id F X)^-1) Z.

  Definition yoneda_counit_is_natural
    : is_nat_trans
        _
        (functor_identity _)
        yoneda_counit_component.
  Proof.
    intros Z₁ Z₂ h ; cbn.
    unfold yoneda_counit_component.
    pose (pr2 ((psfunctor_id F X)^-1) _ _ h) as p.
    exact p.
  Qed.

  Definition yoneda_counit
    : presheaf_to_yoneda ∙ yoneda_to_presheaf ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact yoneda_counit_component.
    - exact yoneda_counit_is_natural.
  Defined.

  Definition bicategorical_yoneda_lemma
    : left_adjoint_equivalence yoneda_to_presheaf.
  Proof.
    apply equiv_to_isadjequiv.
    use tpair.
    - use tpair.
      + exact presheaf_to_yoneda.
      + split.
        * exact yoneda_unit.
        * exact yoneda_counit.
    - split.
      + cbn.
        apply is_nat_iso_to_is_invertible_2cell.
        intro g.
        apply is_inv2cell_to_is_iso.
        apply make_is_invertible_modification.
        intro Z.
        apply is_nat_iso_to_is_invertible_2cell.
        intros Y.
        exact (yoneda_unit_iso g Z Y).
      + apply is_nat_iso_to_is_invertible_2cell.
        intros Z ; cbn.
        unfold yoneda_counit_component.
        use is_iso_qinv.
        * exact (pr1 (pr1 (psfunctor_id F X)) Z).
        * split.
          ** abstract (exact (nat_trans_eq_pointwise
                                (vcomp_lid (psfunctor_id F X)) Z)).
          ** abstract (exact (nat_trans_eq_pointwise
                                (vcomp_rinv (psfunctor_id F X)) Z)).
  Defined.

  Definition bicategorical_yoneda_lemma_inv
    : left_adjoint_equivalence presheaf_to_yoneda
    := inv_adjequiv (_ ,, bicategorical_yoneda_lemma).
End YonedaLemma.

Section YonedaLocalEquivalence.
  Context {B : bicat}.
  Variable (B_is_univalent_2_1 : is_univalent_2_1 B)
           (X Y : B).

  Definition yoneda_to_presheaf_representable_component_mod_component_nat
             (f : X --> Y)
             (Z : B)
             (g : Z --> X)
    : g · f ==> g · f
    := id₂ (g · f).

  Definition yoneda_to_presheaf_representable_component_mod_is_nat_trans
             (f : X --> Y)
             (Z : B)
    : is_nat_trans
        (representable1 B_is_univalent_2_1 f Z : _ ⟶ _)
        (presheaf_to_yoneda_ob
           B_is_univalent_2_1
           (representable B_is_univalent_2_1 Y)
           X f Z
         : _ ⟶ _)
        (yoneda_to_presheaf_representable_component_mod_component_nat f Z).
  Proof.
    intros h₁ h₂ α.
    cbn in *.
    unfold yoneda_to_presheaf_representable_component_mod_component_nat.
    rewrite id2_left,id2_right.
    apply idpath.
  Qed.

  Definition yoneda_to_presheaf_representable_component_mod_component
             (f : X --> Y)
    : modification_data
        (representable1 B_is_univalent_2_1 f)
        (presheaf_to_yoneda_ob
           B_is_univalent_2_1
           (representable B_is_univalent_2_1 Y) X f).
  Proof.
    intros Z.
    use make_nat_trans.
    - exact (yoneda_to_presheaf_representable_component_mod_component_nat f Z).
    - exact (yoneda_to_presheaf_representable_component_mod_is_nat_trans f Z).
  Defined.

  Definition yoneda_to_presheaf_representable_is_modification
             (f : X --> Y)
    : is_modification (yoneda_to_presheaf_representable_component_mod_component f).
  Proof.
    intros Z₁ Z₂ h.
    apply nat_trans_eq.
    { apply homset_property. }
    intros g.
    cbn in *.
    unfold yoneda_to_presheaf_representable_component_mod_component_nat.
    rewrite id2_right, lwhisker_id2, id2_left.
    apply idpath.
  Qed.

  Definition yoneda_to_presheaf_representable_component_mod
             (f : X --> Y)
    : modification
        (Fmor (y B_is_univalent_2_1) X Y f)
        ((presheaf_to_yoneda
            B_is_univalent_2_1
            (representable B_is_univalent_2_1 Y)
            X
          : _ ⟶ _) f).
  Proof.
    use make_modification.
    - exact (yoneda_to_presheaf_representable_component_mod_component f).
    - exact (yoneda_to_presheaf_representable_is_modification f).
  Defined.

  Definition yoneda_to_presheaf_representable_is_natural
    : is_nat_trans
        (Fmor_data (y B_is_univalent_2_1) X Y)
        _
        yoneda_to_presheaf_representable_component_mod.
  Proof.
    intros g₁ g₂ α.
    apply modification_eq.
    intros Z.
    apply nat_trans_eq.
    { apply homset_property. }
    intros h.
    cbn in *.
    unfold yoneda_to_presheaf_representable_component_mod_component_nat.
    rewrite id2_right, id2_left.
    apply idpath.
  Qed.

  Definition yoneda_to_presheaf_representable
    : (Fmor_univ  (y B_is_univalent_2_1) X Y _ _)
        ⟹
        (presheaf_to_yoneda
           B_is_univalent_2_1
           (representable B_is_univalent_2_1 Y)
           X
         : _⟶ _).
  Proof.
    use make_nat_trans.
    - exact yoneda_to_presheaf_representable_component_mod.
    - exact yoneda_to_presheaf_representable_is_natural.
  Defined.

  Definition yoneda_to_presheaf_representable_is_iso
    : @is_invertible_2cell
        bicat_of_cats
        _ _
        (Fmor_univ (y B_is_univalent_2_1) X Y _ _ : _ ⟶ _)
        _ (yoneda_to_presheaf_representable).
  Proof.
    apply is_nat_iso_to_is_invertible_2cell.
    intro g.
    apply is_inv2cell_to_is_iso.
    apply make_is_invertible_modification.
    intro Z.
    apply is_nat_iso_to_is_invertible_2cell.
    intros h.
    cbn in *.
    unfold yoneda_to_presheaf_representable_component_mod_component_nat.
    apply is_inv2cell_to_is_iso.
    is_iso.
  Defined.

  Definition yoneda_mor_is_equivalence
    : @left_adjoint_equivalence
        bicat_of_cats
        _ _
        (Fmor_univ
           (y B_is_univalent_2_1)
           X Y
           B_is_univalent_2_1
           (psfunctor_bicat_is_univalent_2_1
              (op1_bicat B) _
              univalent_cat_is_univalent_2_1)).
  Proof.
    apply equiv_to_isadjequiv.
    exact (@iso_equiv
            bicat_of_cats
            _
            _
            _
            (presheaf_to_yoneda
               B_is_univalent_2_1
               (representable B_is_univalent_2_1 Y)
               X
             : _⟶ _)
            (bicategorical_yoneda_lemma_inv B_is_univalent_2_1 _ _)
            _
            yoneda_to_presheaf_representable_is_iso).
  Defined.
End YonedaLocalEquivalence.
