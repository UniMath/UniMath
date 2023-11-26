(******************************************************************************************

 The displayed category of strict 2-sided displayed categories

 In this file, we define the displayed category of strict 2-sided displayed categories over
 the category of strict categories. The objects over a strict category `C` are strict
 2-sided displayed categories over `C` and `C`, and the morphisms over a functor `F` are
 2-sided displayed functors over `F` and `F`.

 Contents
 1. The data of the displayed category of 2-sided displayed categories
 2. Transport lemmas for this displayed category
 3. The laws
 4. The displayed category of strict 2-sided displayed categories
 5. The proof that it is univalent

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.DispFunctorPair.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.

Local Open Scope cat.

(** * 1. The data of the displayed category of 2-sided displayed categories *)
Definition disp_cat_ob_mor_of_strict_twosided_disp_cat
  : disp_cat_ob_mor cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : setcategory), strict_twosided_disp_cat C C).
  - exact (λ (C₁ C₂ : setcategory) D₁ D₂ (F : C₁ ⟶ C₂),
           twosided_disp_functor F F D₁ D₂).
Defined.

Definition disp_cat_id_comp_of_strict_twosided_disp_cat
  : disp_cat_id_comp
      cat_of_setcategory
      disp_cat_ob_mor_of_strict_twosided_disp_cat.
Proof.
  split.
  - exact (λ (C : setcategory) (D : strict_twosided_disp_cat C C),
           twosided_disp_functor_identity D).
  - exact (λ (C₁ C₂ C₃ : setcategory)
             (F : C₁ ⟶ C₂)
             (G : C₂ ⟶ C₃)
             (D₁ : strict_twosided_disp_cat C₁ C₁)
             (D₂ : strict_twosided_disp_cat C₂ C₂)
             (D₃ : strict_twosided_disp_cat C₃ C₃)
             (FF : twosided_disp_functor F F D₁ D₂)
             (GG : twosided_disp_functor G G D₂ D₃),
           comp_twosided_disp_functor FF GG).
Defined.

Definition disp_cat_data_of_strict_twosided_disp_cat
  : disp_cat_data cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_strict_twosided_disp_cat.
  - exact disp_cat_id_comp_of_strict_twosided_disp_cat.
Defined.

(** * 2. Transport lemmas for this displayed category *)
Proposition transportb_disp_cat_of_strict_twosided_disp_cat_ob_help
            {C₁ C₂ : category}
            (D₁ : twosided_disp_cat C₁ C₁)
            (D₂ : twosided_disp_cat C₂ C₂)
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x y : C₁}
            (xy : D₁ x y)
  : (transportb
       (λ H, twosided_disp_functor H H D₁ D₂)
       p
       GG)
      x
      y
      xy
    =
    transportb_disp_ob2
      (path_functor_ob p _)
      (path_functor_ob p _)
      (GG x y xy).
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_ob
            {C₁ C₂ : setcategory}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            (FD : functor_data C₁ C₂)
            (HF₁ HF₂ : is_functor FD)
            (F := make_functor FD HF₁)
            (G := make_functor FD HF₂)
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x y : C₁}
            (xy : D₁ x y)
  : (transportb
       (λ H, twosided_disp_functor H H D₁ D₂)
       p
       GG)
      x
      y
      xy
    =
    GG x y xy.
Proof.
  etrans.
  {
    apply transportb_disp_cat_of_strict_twosided_disp_cat_ob_help.
  }
  assert (path_functor_ob p x = idpath _) as r₁.
  {
    apply isaset_ob.
  }
  assert (path_functor_ob p y = idpath _) as r₂.
  {
    apply isaset_ob.
  }
  rewrite r₁, r₂.
  cbn.
  apply idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor_path
            {C₁ C₂ : setcategory}
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            {x₁ x₂ : C₁}
            (f : x₁ --> x₂)
  : idtoiso (idpath (F x₁))
    · idtoiso (path_functor_ob p x₁)
    · # G f
    · idtoiso (! path_functor_ob p x₂)
    · idtoiso (idpath (F x₂))
    =
    # F f.
Proof.
  induction p ; cbn.
  rewrite !id_left.
  rewrite !id_right.
  apply idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor_help
            {C₁ C₂ : setcategory}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x₁ x₂ y₁ y₂ : C₁}
            {f : x₁ --> x₂}
            {g : y₁ --> y₂}
            {xy₁ : D₁ x₁ y₁}
            {xy₂ : D₁ x₂ y₂}
            (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 (transportb
          (λ H, twosided_disp_functor H H D₁ D₂)
          p
          GG)
      fg
    =
    transportf_disp_mor2
      (transportb_disp_cat_of_strict_twosided_disp_cat_mor_path p f)
      (transportb_disp_cat_of_strict_twosided_disp_cat_mor_path p g)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (transportb_disp_cat_of_strict_twosided_disp_cat_ob_help D₁ D₂ p GG xy₁)
       ;;2 transportb_disp_ob2_mor _ _ _
       ;;2 #2 GG fg
       ;;2 transportb_disp_ob2_inv _ _ _
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (!transportb_disp_cat_of_strict_twosided_disp_cat_ob_help D₁ D₂ p GG xy₂)).
Proof.
  induction p ; cbn.
  rewrite !(id_two_disp_left (D := D₂)).
  rewrite !(id_two_disp_right (D := D₂)).
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite !(id_two_disp_left (D := D₂)).
  unfold transportb_disp_mor2.
  rewrite !transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor
            {C₁ C₂ : setcategory}
            {D₁ : strict_twosided_disp_cat C₁ C₁}
            {D₂ : strict_twosided_disp_cat C₂ C₂}
            (FD : functor_data C₁ C₂)
            (HF₁ HF₂ : is_functor FD)
            (F := make_functor FD HF₁)
            (G := make_functor FD HF₂)
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x₁ x₂ y₁ y₂ : C₁}
            {f : x₁ --> x₂}
            {g : y₁ --> y₂}
            {xy₁ : D₁ x₁ y₁}
            {xy₂ : D₁ x₂ y₂}
            (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 (transportb
          (λ H, twosided_disp_functor H H D₁ D₂)
          p
          GG)
       fg
    =
    transportf_disp_mor2
      (id_right _ @ id_left _)
      (id_right _ @ id_left _)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (transportb_disp_cat_of_strict_twosided_disp_cat_ob F HF₁ HF₂ p GG xy₁)
       ;;2 #2 GG fg
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob F HF₁ HF₂ p GG xy₂))).
Proof.
  rewrite transportb_disp_cat_of_strict_twosided_disp_cat_mor_help.
  unfold transportb_disp_ob2_mor, transportb_disp_ob2_inv.
  etrans.
  {
    apply maponpaths.
    do 3 apply maponpaths_2.
    apply idtoiso_twosided_disp_concat_strict.
  }
  unfold transportb_disp_mor2.
  rewrite !two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    apply idtoiso_twosided_disp_concat_strict.
  }
  unfold transportb_disp_mor2.
  rewrite !two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idtoiso_twosided_disp_triple_concat.
Qed.

Local Arguments idtoiso_twosided_disp {_ _ _ _ _ _ _ _ _ _ _ _}.

(** * 3. The laws *)
Proposition disp_cat_axioms_of_strict_twosided_disp_cat
  : disp_cat_axioms
      cat_of_setcategory
      disp_cat_data_of_strict_twosided_disp_cat.
Proof.
  repeat split.
  - cbn ; intros C₁ C₂ F D₁ D₂ FF.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob _ _ _ _ _ _)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg ; cbn -[idtoiso_twosided_disp].
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply transportb_disp_cat_of_strict_twosided_disp_cat_mor.
      }
      cbn -[idtoiso_twosided_disp].
      rewrite two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - cbn ; intros C₁ C₂ F D₁ D₂ FF.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob
                 F _ _
                 (@id_right cat_of_setcategory _ _ F)
                 FF
                 xy)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg ; cbn -[idtoiso_twosided_disp].
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (id_right (C := cat_of_setcategory) F)).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - cbn ; intros C₁ C₂ C₃ C₄ F G H D₁ D₂ D₃ D₄ FF GG HH.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob
                 _ _ _
                 (@assoc cat_of_setcategory _ _ _ _ F G H)
                 (comp_twosided_disp_functor (comp_twosided_disp_functor FF GG) HH)
                 xy)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (assoc (C := cat_of_setcategory) F G H)).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - intros.
    apply isaset_twosided_disp_functor.
Qed.

(** * 4. The displayed category of strict 2-sided displayed categories *)
Definition disp_cat_of_strict_twosided_disp_cat
  : disp_cat cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_strict_twosided_disp_cat.
  - exact disp_cat_axioms_of_strict_twosided_disp_cat.
Defined.

Definition cat_of_strict_twosided_disp_cat
  : category
  := total_category disp_cat_of_strict_twosided_disp_cat.

(** * 5. The proof that it is univalent *)
Section StrictTwosidedDispCatIso.
  Context {C : setcategory}
          {D₁ D₂ : strict_twosided_disp_cat C C}
          (F : disp_functor
                 (functor_identity _)
                 (twosided_disp_cat_to_disp_cat C C D₁)
                 (twosided_disp_cat_to_disp_cat C C D₂)).

  Proposition is_z_iso_disp_strict_twosided_disp_cat_to_ff
              (HF : is_z_iso_disp
                      (D := disp_cat_of_strict_twosided_disp_cat)
                      (@identity_z_iso cat_of_setcategory C)
                      (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)))
    : disp_functor_ff F.
  Proof.
    intros x y xx yy f.
  Admitted.

  Proposition is_z_iso_disp_strict_twosided_disp_cat_to_ob_weq
              (HF : is_z_iso_disp
                      (D := disp_cat_of_strict_twosided_disp_cat)
                      (@identity_z_iso cat_of_setcategory C)
                      (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)))
              (x : C × C)
    : isweq (F x).
  Proof.
  Admitted.

  Proposition to_is_z_iso_disp_strict_twosided_disp_cat
              (HF_ff : disp_functor_ff F)
              (HF_weq : ∏ (x : C × C), isweq (F x))
    : is_z_iso_disp
        (D := disp_cat_of_strict_twosided_disp_cat)
        (@identity_z_iso cat_of_setcategory C)
        (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)).
  Proof.
  Admitted.

  Proposition is_z_iso_disp_strict_twosided_disp_cat_weq
    : (∏ (x : C × C), isweq (F x)) × disp_functor_ff F
      ≃
      is_z_iso_disp
        (D := disp_cat_of_strict_twosided_disp_cat)
        (@identity_z_iso cat_of_setcategory C)
        (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)).
  Proof.
    use weqimplimpl.
    - intros HF.
      induction HF as [ HF_weq HF_ff ].
      exact (to_is_z_iso_disp_strict_twosided_disp_cat HF_ff HF_weq).
    - intros HF.
      split.
      + exact (is_z_iso_disp_strict_twosided_disp_cat_to_ob_weq HF).
      + exact (is_z_iso_disp_strict_twosided_disp_cat_to_ff HF).
    - use isapropdirprod.
      + use impred ; intro.
        apply isapropisweq.
      + apply isaprop_disp_functor_ff.
    - apply isaprop_is_z_iso_disp.
  Qed.
End StrictTwosidedDispCatIso.

Proposition is_univalent_disp_disp_cat_of_strict_twosided_disp_cat
  : is_univalent_disp disp_cat_of_strict_twosided_disp_cat.
Proof.
  use is_univalent_disp_from_fibers.
  intros C D₁ D₂.
  cbn in C, D₁, D₂.
  use weqhomot.
  - refine (_ ∘ path_sigma_hprop _ _ _ (isaprop_is_strict_twosided_disp_cat _))%weq.
    refine (_ ∘ make_weq _ (isweqmaponpaths (two_sided_disp_cat_weq_disp_cat C C) D₁ D₂))%weq.
    refine (_ ∘ disp_cat_eq _ _)%weq.
    use weqtotal2.
    + exact (invweq
               (two_sided_disp_functor_weq_disp_functor
                  (functor_identity C)
                  (functor_identity C) D₁ D₂)
             ∘ disp_functor_over_pair_weq _ _)%weq.
    + intro F.
      apply is_z_iso_disp_strict_twosided_disp_cat_weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_twosided_disp_functor_laws.
    }
    apply idpath.
Qed.

Proposition is_univalent_cat_of_strict_twosided_disp_cat
  : is_univalent cat_of_strict_twosided_disp_cat.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_cat_of_setcategory.
  - exact is_univalent_disp_disp_cat_of_strict_twosided_disp_cat.
Qed.
