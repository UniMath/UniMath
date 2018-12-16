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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Local Open Scope cat.
Local Open Scope bicategory_scope.

Section FunctorComposition.
  Context {C D E : bicat}.
  Variable (G : psfunctor D E) (F : psfunctor C D).

  Definition ps_comp_d : psfunctor_data C E.
  Proof.
    use mk_psfunctor_data.
    - exact (λ X, G(F X)).
    - exact (λ _ _ f, #G(#F f)).
    - exact (λ _ _ _ _ α, ##G(##F α)).
    - exact (λ a, psfunctor_id G (F a) • ##G (psfunctor_id F a)).
    - exact (λ _ _ _ f g, psfunctor_comp G (#F f) (#F g) • ##G (psfunctor_comp F f g)).
  Defined.

  Definition comp_is_ps : psfunctor_laws ps_comp_d.
  Proof.
    repeat split.
    - intros a b f ; cbn in *.
      rewrite !psfunctor_id2.
      reflexivity.
    - intros a b f g h α β ; cbn in *.
      rewrite !psfunctor_vcomp.
      reflexivity.
    - intros a b f ; cbn in *.
      rewrite !psfunctor_lunitor.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite !psfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- psfunctor_rwhisker.
      reflexivity.
    - intros a b f ; cbn.
      rewrite !psfunctor_runitor.
      rewrite <- lwhisker_vcomp.
      rewrite !psfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- psfunctor_lwhisker.
      reflexivity.
    - intros a b c d f g h ; cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- psfunctor_vcomp.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite <- psfunctor_lwhisker.
      rewrite !vassocl.
      rewrite <- !psfunctor_vcomp.
      rewrite !vassocr.
      pose @psfunctor_lassociator as p.
      cbn in p.
      rewrite p ; clear p.
      rewrite !psfunctor_vcomp.
      rewrite !vassocl.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite psfunctor_lassociator.
      rewrite !vassocl.
      apply (maponpaths (λ z, _ • z)).
      rewrite psfunctor_rwhisker.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocl.
      rewrite <- psfunctor_vcomp.
      rewrite !psfunctor_lwhisker.
      rewrite !vassocr.
      pose (@psfunctor_lwhisker _ _ G) as p.
      cbn in p ; rewrite <- p ; clear p.
      rewrite psfunctor_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocl.
      rewrite <- psfunctor_vcomp.
      rewrite !psfunctor_rwhisker.
      rewrite !vassocr.
      pose (@psfunctor_rwhisker _ _ G) as p.
      cbn in p ; rewrite <- p ; clear p.
      rewrite psfunctor_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a ; cbn.
      is_iso.
      + exact (psfunctor_id G (F a)).
      + exact (psfunctor_is_iso G (psfunctor_id F a)).
    - intros a b c f g ; cbn.
      is_iso.
      + exact (psfunctor_comp G (#F f) (#F g)).
      + exact (psfunctor_is_iso G (psfunctor_comp F f g)).
  Qed.

  Definition ps_comp : psfunctor C E
    := (_ ,, comp_is_ps).
End FunctorComposition.