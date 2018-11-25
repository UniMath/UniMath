(**
The identity pseudo functor on a bicategoy.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.

Section IdentityFunctor.
  Variable (C : bicat).

  Definition id_functor_d : laxfunctor_data C C.
  Proof.
    use build_laxfunctor_data.
    - exact (λ x, x).
    - exact (λ _ _ x, x).
    - exact (λ _ _ _ _ x, x).
    - exact (λ x, id2 _).
    - exact (λ _ _ _ _ _, id2 _).
  Defined.

  Definition id_functor_laws : laxfunctor_laws id_functor_d.
  Proof.
    repeat split.
    - intros a b f ; cbn in *.
      rewrite id2_rwhisker.
      rewrite !id2_left.
      reflexivity.
    - intros a b f ; cbn in *.
      rewrite lwhisker_id2.
      rewrite !id2_left.
      reflexivity.
    - intros a b c d f g h ; cbn in *.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      reflexivity.
    - intros a b c f g h α ; cbn in *.
      rewrite !id2_left, !id2_right.
      reflexivity.
    - intros a b c f g h α ; cbn in *.
      rewrite !id2_left, !id2_right.
      reflexivity.
  Qed.

  Definition lax_id_functor : laxfunctor C C
    := (_ ,, id_functor_laws).

  Definition lax_id_functor_is_pseudo
    : is_pseudofunctor lax_id_functor.
  Proof.
    split ; intros ; cbn ; is_iso.
  Defined.

  Definition ps_id_functor : psfunctor C C
    := (_ ,, lax_id_functor_is_pseudo).
End IdentityFunctor.