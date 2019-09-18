(* ******************************************************************************* *)
(** * Bicategory of strict categories

    Benedikt Ahrens, Marco Maggesi

    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Definition strict_cat_prebicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact setcategory.
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

Definition strict_cat_prebicat_laws : prebicat_laws strict_cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq; try apply C₅.
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition prebicat_of_strict_cats : prebicat := _ ,, strict_cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_strict_cats : isaset_cells prebicat_of_strict_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_strict_cats : bicat
  := (prebicat_of_strict_cats,, isaset_cells_prebicat_of_strict_cats).

Definition idtoiso_2_1_strict_cat_help
           {c d : bicat_of_strict_cats}
           {f : functor_data (pr1 c) (pr1 d)}
           {Hf Hf' : is_functor f}
           (p : Hf = Hf')
           (x : pr1 c)
  : pr11 (@idtoiso_2_1
            bicat_of_strict_cats
            _ _
            _ _
            (maponpaths (λ z, f ,, z) p))
         x
    =
    id₁ (f x).
Proof.
  induction p.
  apply idpath.
Qed.

Definition idtoiso_2_1_strict_cat
           {c d : bicat_of_strict_cats}
           {f g : functor (pr1 c) (pr1 d)}
           (p : pr1 f = pr1 g)
           (x : pr1 c)
  : pr11 (@idtoiso_2_1
            bicat_of_strict_cats
            _ _
            f g
            (functor_eq
               _ _
               (isaset_mor d)
               f g
               p))
         x
    =
    idtoiso (maponpaths (λ q, pr1 q x) p).
Proof.
  induction f as [f Hf].
  induction g as [g Hg].
  simpl in *.
  induction p.
  apply idtoiso_2_1_strict_cat_help.
Qed.

Definition bicat_of_strict_cats_is_strict_bicat
  : is_strict_bicat bicat_of_strict_cats.
Proof.
  use make_is_strict_bicat.
  - intros c d.
    repeat use isaset_total2.
    + apply funspace_isaset.
      apply d.
    + intro f ; simpl.
      repeat (use impred_isaset ; intro).
      apply (isaset_mor d).
    + intro.
      apply isasetaprop.
      apply isaprop_is_functor.
      apply d.
  - repeat use tpair.
    + intros c d f.
      use functor_eq.
      { apply d. }
      apply idpath.
    + intros c d f.
      use functor_eq.
      { apply d. }
      apply idpath.
    + intros a b c d f g h.
      use functor_eq.
      { apply d. }
      apply idpath.
    + intros c d f.
      use nat_trans_eq.
      { apply d. }
      intro x.
      etrans.
      {
        apply idtoiso_2_1_strict_cat.
      }
      apply idpath.
    + intros c d f.
      use nat_trans_eq.
      { apply d. }
      intro x.
      etrans.
      {
        apply idtoiso_2_1_strict_cat.
      }
      apply idpath.
    + intros a b c d f g h.
      use nat_trans_eq.
      { apply d. }
      intro x.
      etrans.
      {
        apply idtoiso_2_1_strict_cat.
      }
      apply idpath.
Qed.

Definition two_cat_of_strict_cats
  : strict_bicat.
Proof.
  use tpair.
  - exact bicat_of_strict_cats.
  - exact bicat_of_strict_cats_is_strict_bicat.
Defined.
