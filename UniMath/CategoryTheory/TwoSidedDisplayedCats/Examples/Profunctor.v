(**********************************************************************************

 Every profunctor gives rise to a discrete two-sided fibration

 Contents
 1. Definition
 2. Univalence and discreteness
 3. The two-sided fibration

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Section ProfunctorToTwosidedDispCat.
  Context {C₁ C₂ : category}
          (P : profunctor C₁ C₂).

  (**
   1. Definition
   *)
  Definition profunctor_to_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, P x y).
    - exact (λ x₁ x₂ y₁ y₂ z₁ z₂ f g, rmap P g z₁ = lmap P f z₂).
  Defined.

  Definition profunctor_to_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp profunctor_to_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn -[lmap rmap].
      rewrite lmap_id, rmap_id.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂ ; cbn -[lmap rmap] in *.
      rewrite lmap_comp, rmap_comp.
      rewrite fg₁.
      rewrite rmap_lmap.
      rewrite fg₂.
      apply idpath.
  Qed.

  Definition profunctor_to_twosided_disp_cat_data
    : twosided_disp_cat_data C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact profunctor_to_twosided_disp_cat_ob_mor.
    - exact profunctor_to_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_profunctor_to_twosided_mor
             {x₁ x₂ : C₁}
             (f : x₁ --> x₂)
             {y₁ y₂ : C₂}
             (g : y₁ --> y₂)
             (xy₁ : profunctor_to_twosided_disp_cat_data y₁ x₁)
             (xy₂ : profunctor_to_twosided_disp_cat_data y₂ x₂)
             (fg fg' : xy₁ -->[ g ][ f ] xy₂)
    : fg = fg'.
  Proof.
    apply (P y₁ x₂).
  Qed.

  Definition profunctor_to_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms profunctor_to_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_profunctor_to_twosided_mor).
    apply isasetaprop.
    use invproofirrelevance.
    intro ; intro.
    apply isaprop_profunctor_to_twosided_mor.
  Qed.

  Definition profunctor_to_twosided_disp_cat
    : twosided_disp_cat C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact profunctor_to_twosided_disp_cat_data.
    - exact profunctor_to_twosided_disp_cat_axioms.
  Defined.

  (**
   2. Univalence and discreteness
   *)
  Definition univalent_profunctor_to_twosided_disp_cat
    : is_univalent_twosided_disp_cat profunctor_to_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p q xy₁ xy₂.
    induction p ; induction q.
    use isweqimplimpl.
    - cbn.
      intro z.
      pose (p := pr1 z) ; cbn -[lmap rmap] in p.
      rewrite lmap_id, rmap_id in p.
      exact p.
    - apply (P x₁ y₁).
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intro ; intros.
        apply isaprop_profunctor_to_twosided_mor.
  Qed.

  Definition discrete_profunctor_to_twosided_disp_cat
    : discrete_twosided_disp_cat profunctor_to_twosided_disp_cat.
  Proof.
    use make_discrete_twosided_disp_cat.
    repeat split.
    - intro ; intros.
      apply isaprop_profunctor_to_twosided_mor.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g Hf Hg p ; cbn -[lmap rmap] in *.
      pose (q := maponpaths (rmap P (inv_from_z_iso (g,, Hg))) p).
      cbn -[rmap lmap].
      rewrite <- rmap_comp in q.
      assert (xy₁
              =
              rmap P (inv_from_z_iso (g,, Hg)) (lmap P f xy₂)) as r.
      {
        refine (_ @ q).
        refine (!(rmap_id P xy₁) @ _).
        apply maponpaths_2.
        exact (!(z_iso_inv_after_z_iso (_ ,, Hg))).
      }
      rewrite r.
      rewrite rmap_lmap.
      rewrite <- lmap_comp.
      refine (!(lmap_id P _) @ _).
      apply maponpaths_2.
      exact (!(z_iso_after_z_iso_inv (_ ,, Hf))).
    - exact univalent_profunctor_to_twosided_disp_cat.
  Qed.

  (**
   3. The two-sided fibration
   *)
  Definition profunctor_to_discrete_twosided_fibration
    : discrete_twosided_fibration C₂ C₁.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact profunctor_to_twosided_disp_cat.
    - exact discrete_profunctor_to_twosided_disp_cat.
    - intros x₁ x₂ y xy₂ f.
      simple refine (_ ,, _ ,, _).
      + exact (lmap P f xy₂).
      + abstract
          (cbn -[lmap rmap] ;
           rewrite rmap_id ;
           apply idpath).
      + abstract
          (cbn ;
           intro ; intros ; cbn -[lmap rmap] in * ;
           rewrite id_right in fg' ;
           rewrite fg' ;
           rewrite lmap_comp ;
           apply idpath).
    - intros y x₁ x₂ xy₂ f.
      simple refine (_ ,, _ ,, _).
      + exact (rmap P f xy₂).
      + abstract
          (cbn -[lmap rmap] ;
           rewrite lmap_id ;
           apply idpath).
      + abstract
          (cbn ;
           intro ; intros ; cbn -[lmap rmap] in * ;
           rewrite id_left in fg' ;
           rewrite <- fg' ;
           rewrite rmap_comp ;
           apply idpath).
  Defined.
End ProfunctorToTwosidedDispCat.
