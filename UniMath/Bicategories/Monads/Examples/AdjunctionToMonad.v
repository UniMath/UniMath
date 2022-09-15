(*************************************************************************

 Every adjunction gives rise to a monad

 In arbitrary bicategories, every adjunction gives rise to a monad

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

Section MonadFromAdjunction.
  Context {B : bicat}
          {x y : B}
          (l : adjunction x y).

  Let r : y --> x := left_adjoint_right_adjoint l.
  Let η : id₁ _ ==> l · r := left_adjoint_unit l.
  Let ε : r · l ==> id₁ _ := left_adjoint_counit l.

  Let f : x --> x := l · r.
  Let monad_η : id₁ _ ==> f := η.
  Let monad_μ : f · f ==> f
    := rassociator _ _ _
       • (_ ◃ lassociator _ _ _)
       • (_ ◃ (ε ▹ _))
       • (_ ◃ lunitor _).

  Local Lemma mnd_from_adjunction_η_left
    : (linvunitor f • (monad_η ▹ f)) • monad_μ = id₂ _.
  Proof.
    pose (p₁ := internal_triangle1 l).
    unfold monad_η, monad_μ, f.
    cbn -[η ε] ; cbn -[η ε] in p₁.
    rewrite !vassocl.
    rewrite !vassocl in p₁.
    refine (_ @ id2_rwhisker _ _).
    rewrite <- p₁.
    rewrite <- !rwhisker_vcomp.
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- rassociator_rassociator.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite lwhisker_vcomp.
    rewrite rassociator_lassociator.
    rewrite lwhisker_id2.
    rewrite id2_left.
    rewrite !vassocr.
    rewrite rwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    apply maponpaths.
    rewrite lunitor_lwhisker.
    apply idpath.
  Qed.

  Local Lemma mnd_from_adjunction_η_right
    : (rinvunitor f • (f ◃ monad_η)) • monad_μ = id₂ _.
  Proof.
    pose (p₁ := internal_triangle1 l).
    pose (p₂ := internal_triangle2 l).
    unfold monad_η, monad_μ, f.
    cbn -[η ε] ; cbn -[η ε] in p₁, p₂.
    rewrite !vassocl.
    rewrite !vassocl in p₂.
    refine (_ @ lwhisker_id2 _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!p₂).
    }
    rewrite <- !lwhisker_vcomp.
    rewrite <- rinvunitor_triangle.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite lassociator_rassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Local Lemma mnd_from_adjunction_assoc
    : (rassociator f f f • (f ◃ monad_μ)) • monad_μ
      =
      (monad_μ ▹ f) • monad_μ.
  Proof.
    unfold monad_μ.
    rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        etrans.
        {
          apply inverse_pentagon_4.
        }
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        apply lwhisker_lwhisker.
      }
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      apply idpath.
    }
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocl.
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply lwhisker_vcomp.
      }
      rewrite vcomp_lunitor.
      refine (lwhisker_vcomp _ _ _ @ _).
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      apply idpath.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        refine (!_).
        apply rwhisker_lwhisker_rassociator.
      }
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      refine (!_).
      apply rwhisker_lwhisker_rassociator.
    }
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      apply idpath.
    }
    rewrite !lunitor_assoc.
    rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp, <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    refine (!_).
    rewrite !vassocl.
    etrans.
    {
      do 6 apply maponpaths.
      rewrite !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite <- rwhisker_rwhisker.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite lwhisker_vcomp.
    rewrite pentagon_6.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 3 apply maponpaths_2.
        apply inverse_pentagon_7.
      }
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite <- rwhisker_lwhisker_rassociator.
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      rewrite <- lassociator_lassociator.
      rewrite <- !lwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    refine (_ @ !(rassociator_rassociator _ _ _ _)).
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_lwhisker_rassociator.
      }
      rewrite !vassocl.
      apply maponpaths.
      apply lwhisker_lwhisker_rassociator.
    }
    rewrite !vassocr.
    refine (_ @ id2_left _).
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    rewrite <- lwhisker_id2.
    apply maponpaths.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite lwhisker_id2.
      apply id2_left.
    }
    apply rassociator_lassociator.
  Qed.

  Definition mnd_from_adjunction
    : mnd B.
  Proof.
    use make_mnd.
    - use make_mnd_data.
      + exact x.
      + exact f.
      + exact monad_η.
      + exact monad_μ.
    - refine (_ ,, _ ,, _).
      + exact mnd_from_adjunction_η_left.
      + exact mnd_from_adjunction_η_right.
      + exact mnd_from_adjunction_assoc.
  Defined.
End MonadFromAdjunction.
