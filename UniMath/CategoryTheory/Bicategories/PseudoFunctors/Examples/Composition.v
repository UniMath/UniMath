(**
Composition of lax functors and pseudo functors.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Local Open Scope cat.
Local Open Scope bicategory_scope.

Section FunctorComposition.
  Context {C D E : bicat}.
  Variable (G : laxfunctor D E) (F : laxfunctor C D).

  Definition lax_comp_d : laxfunctor_data C E.
  Proof.
    use build_laxfunctor_data.
    - exact (λ X, G(F X)).
    - exact (λ _ _ f, #G(#F f)).
    - exact (λ _ _ _ _ α, ##G(##F α)).
    - exact (λ a, laxfunctor_id G (F a) • ##G (laxfunctor_id F a)).
    - exact (λ _ _ _ f g, laxfunctor_comp G (#F f) (#F g) • ##G (laxfunctor_comp F f g)).
  Defined.

  Definition comp_is_lax : laxfunctor_laws lax_comp_d.
  Proof.
    repeat split.
    - intros a b f ; cbn in *.
      rewrite !laxfunctor_id2.
      reflexivity.
    - intros a b f g h α β ; cbn in *.
      rewrite !laxfunctor_vcomp.
      reflexivity.
    - intros a b f ; cbn in *.
      rewrite !laxfunctor_lunitor.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite !laxfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- laxfunctor_rwhisker.
      reflexivity.
    - intros a b f ; cbn.
      rewrite !laxfunctor_runitor.
      rewrite <- lwhisker_vcomp.
      rewrite !laxfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- laxfunctor_lwhisker.
      reflexivity.
    - intros a b c d f g h ; cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- laxfunctor_vcomp.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite <- laxfunctor_lwhisker.
      rewrite !vassocl.
      rewrite <- !laxfunctor_vcomp.
      rewrite !vassocr.
      rewrite laxfunctor_lassociator.
      rewrite !laxfunctor_vcomp.
      rewrite !vassocl.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite laxfunctor_lassociator.
      rewrite !vassocl.
      apply (maponpaths (λ z, _ • z)).
      rewrite laxfunctor_rwhisker.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocl.
      rewrite <- laxfunctor_vcomp.
      rewrite !laxfunctor_lwhisker.
      rewrite !vassocr.
      rewrite <- (laxfunctor_lwhisker G).
      rewrite laxfunctor_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocl.
      rewrite <- laxfunctor_vcomp.
      rewrite !laxfunctor_rwhisker.
      rewrite !vassocr.
      rewrite <- (laxfunctor_rwhisker G).
      rewrite laxfunctor_vcomp.
      rewrite !vassocr.
      reflexivity.
  Qed.

  Definition lax_comp : laxfunctor C E
    := (_ ,, comp_is_lax).
End FunctorComposition.

Definition ps_comp
           {C D E : bicat}
           (G : psfunctor D E) (F : psfunctor C D)
  : psfunctor C E.
Proof.
  refine (lax_comp G F ,, _).
  split.
  - intros a ; cbn.
    is_iso.
    + exact (psfunctor_id G (F a)).
    + exact (laxfunctor_is_iso G (psfunctor_id F a)).
  - intros a b c f g ; cbn.
    is_iso.
    + exact (psfunctor_comp G (#F f) (#F g)).
    + exact (laxfunctor_is_iso G (psfunctor_comp F f g)).
Defined.