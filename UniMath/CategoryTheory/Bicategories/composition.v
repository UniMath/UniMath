Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.

Section FunctorComposition.
  Context {C D E : bicat}.
  Variable (G : laxfunctor D E) (F : laxfunctor C D).

  Definition lax_comp_d : laxfunctor_data C E.
  Proof.
    use build_laxfunctor_data.
    - exact (λ X, G(F X)).
    - exact (λ _ _ f, #G(#F f)).
    - exact (λ _ _ _ _ α, ##G(##F α)).
    - exact (λ a, laxfunctor_id G (F a) o ##G (laxfunctor_id F a)).
    - exact (λ _ _ _ f g, laxfunctor_comp G (#F f) (#F g) o ##G (laxfunctor_comp F f g)).
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
      rewrite !laxfunctor_vcomp.
      rewrite laxfunctor_lunitor.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite laxfunctor_rwhisker.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      reflexivity.
    - intros a b f ; cbn.
      rewrite !laxfunctor_runitor.
      rewrite !laxfunctor_vcomp.
      rewrite laxfunctor_runitor.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite laxfunctor_lwhisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      reflexivity.
    - intros a b c d f g h ; cbn.
      rewrite !vassocr.
      rewrite !vassocl.
      rewrite <- rwhisker_vcomp.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite <- laxfunctor_rwhisker.
      rewrite !vassocr.
      rewrite <- !laxfunctor_vcomp.
      rewrite laxfunctor_lassociator.
      rewrite !laxfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite laxfunctor_lassociator.
      rewrite !vassocr.
      rewrite laxfunctor_lwhisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocr.
      rewrite <- laxfunctor_vcomp.
      rewrite !laxfunctor_lwhisker.
      rewrite !vassocl.
      rewrite <- (laxfunctor_lwhisker G).
      rewrite laxfunctor_vcomp.
      rewrite !vassocr.
      reflexivity.
    - intros a b c f g₁ g₂ α ; cbn.
      rewrite !vassocr.
      rewrite <- laxfunctor_vcomp.
      rewrite !laxfunctor_rwhisker.
      rewrite !vassocl.
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
    + exact (laxfunctor_is_iso G (psfunctor_id F a)).
    + exact (psfunctor_id G (F a)).
  - intros a b c f g ; cbn.
    is_iso.
    + exact (laxfunctor_is_iso G (psfunctor_comp F f g)).
    + exact (psfunctor_comp G (#F f) (#F g)).
Defined.