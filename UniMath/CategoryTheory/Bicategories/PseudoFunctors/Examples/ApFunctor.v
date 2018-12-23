(**
Given a map between two functors, we get a pseudofunctor between their fundamental bigroupoids.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.TwoType.

Section ApFunctor.
  Context {X Y : UU}
          (HX : isofhlevel 4 X)
          (HY : isofhlevel 4 Y).
  Variable (f : X → Y).

  Definition ap_functor_data
    : psfunctor_data (fundamental_bigroupoid X HX) (fundamental_bigroupoid Y HY).
  Proof.
    use mk_psfunctor_data.
    - exact f.
    - exact (λ _ _, maponpaths f).
    - exact (λ _ _ _ _ s, maponpaths (maponpaths f) s).
    - exact (λ x, idpath (idpath (f x))).
    - exact (λ _ _ _ p q, !(maponpathscomp0 f p q)).
  Defined.

  Definition ap_functor_laws
    : psfunctor_laws ap_functor_data.
  Proof.
    repeat split.
    - intros x y p₁ p₂ p₃ s₁ s₂ ; cbn in *.
      exact (maponpathscomp0 (maponpaths f) s₁ s₂).
    - intros x y p ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros x y p ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros w x y z p q r ; cbn in *.
      induction p, q, r ; cbn.
      reflexivity.
    - intros x y z p q₁ q₂ s ; cbn in *.
      induction s ; cbn.
      exact (pathscomp0rid _).
    - intros x y z p₁ p₂ q s ; cbn in *.
      induction s ; cbn.
      exact (pathscomp0rid _).
  Qed.

  Definition ps_ap_functor
    : psfunctor (fundamental_bigroupoid X HX) (fundamental_bigroupoid Y HY).
  Proof.
    use mk_psfunctor.
    - exact ap_functor_data.
    - exact ap_functor_laws.
    - split.
      + intros a.
        exact (fundamental_groupoid_2cell_iso Y HY (idpath(idpath (f a)))).
      + intros a b c p q.
        exact (fundamental_groupoid_2cell_iso Y HY (!(maponpathscomp0 f p q))).
  Defined.
End ApFunctor.