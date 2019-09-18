(**
A homotopy between homotopy gives rise to a modification
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Core.Examples.TwoType.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.ApFunctor.
Require Import UniMath.Bicategories.Transformations.Examples.ApTransformation.

Local Open Scope cat.

Definition homothomotsec_natural
           {X Y : UU}
           {f g : X → Y}
           {e₁ e₂ : f ~ g}
           (h : e₁ ~ e₂)
           {x y : X}
           (p : x = y)
  : homotsec_natural e₁ p
    @ maponpaths (λ s : f y = g y, maponpaths f p @ s) (h y)
    =
    maponpaths (λ s : f x = g x, s @ maponpaths g p) (h x)
    @ homotsec_natural e₂ p.
Proof.
  induction p ; cbn.
  induction (h x).
  apply pathscomp0rid.
Defined.

Section ApModification.
  Context {X Y : UU}
          (HX : isofhlevel 4 X)
          (HY : isofhlevel 4 Y)
          {f g : X → Y}
          {e₁ e₂ : f ~ g}
          (h : e₁ ~ e₂).

  Definition ap_modification_data
    : modification_data
        (ap_pstrans HX HY e₁)
        (ap_pstrans HX HY e₂)
    := h.

  Definition ap_modification_is_modification
    : is_modification ap_modification_data.
  Proof.
    intros x y p.
    exact (homothomotsec_natural h p).
  Qed.

  Definition ap_modification
    : modification
        (ap_pstrans HX HY e₁)
        (ap_pstrans HX HY e₂).
  Proof.
    use make_modification.
    - exact ap_modification_data.
    - exact ap_modification_is_modification.
  Defined.
End ApModification.
