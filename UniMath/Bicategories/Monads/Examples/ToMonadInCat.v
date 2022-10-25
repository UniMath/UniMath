(**********************************************************************

 Every monad induces a monad on the hom-categories

 Given a bicategory `B`, a monad `m` in `B`, and an object `x`,
 then we get a monad on `hom x (pr1 m)`.

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

Section MonadToCatMonad.
  Context {B : bicat}
          (m : mnd B)
          (x : B).

  Definition mnd_to_functor
    : hom x (pr1 m) ⟶ hom x (pr1 m)
    := post_comp x (endo_of_mnd m).

  Definition mnd_to_cat_mu
    : mnd_to_functor ∙ mnd_to_functor ⟹ mnd_to_functor.
  Proof.
    use make_nat_trans.
    - exact (λ f, rassociator _ _ _ • (f ◃ mult_of_mnd m)).
    - abstract
        (intros f g α ; cbn ;
         rewrite !vassocr ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition mnd_to_cat_unit
    : functor_identity _ ⟹ mnd_to_functor.
  Proof.
    use make_nat_trans.
    - exact (λ f, rinvunitor _ • (f ◃ unit_of_mnd m)).
    - abstract
        (intros f g α ; cbn ;
         rewrite !vassocr ;
         rewrite rinvunitor_natural ;
         rewrite <- rwhisker_hcomp ;
         rewrite !vassocl ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition mnd_to_cat_Monad_data
    : Monad_data (hom x (pr1 m)).
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact mnd_to_functor.
    - exact mnd_to_cat_mu.
    - exact mnd_to_cat_unit.
  Defined.

  Definition mnd_to_cat_Monad_laws
    : Monad_laws mnd_to_cat_Monad_data.
  Proof.
    repeat split ; intro f ; cbn.
    - rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      refine (_ @ lwhisker_id2 _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (mnd_unit_right m).
    - rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      refine (_ @ lwhisker_id2 _ _).
      apply maponpaths.
      rewrite !vassocr.
      exact (mnd_unit_left m).
    - rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        apply idpath.
      }
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite inverse_pentagon_7.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      refine (!_).
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      exact (mnd_mult_assoc m).
  Qed.

  Definition mnd_to_cat_Monad
    : Monad (hom x (pr1 m)).
  Proof.
    simple refine (_ ,, _).
    - exact mnd_to_cat_Monad_data.
    - exact mnd_to_cat_Monad_laws.
  Defined.
End MonadToCatMonad.
