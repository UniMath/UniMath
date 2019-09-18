(**
Each homotopy between functions give rise to a pseudotransformation
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
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Core.Examples.TwoType.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.ApFunctor.

Local Open Scope cat.

Definition homotsec_natural
           {X Y : UU}
           {f g : X → Y}
           (e : f ~ g)
           {x y : X}
           (p : x = y)
  : e x @ maponpaths g p = maponpaths f p @ e y.
Proof.
  induction p.
  apply pathscomp0rid.
Defined.

Definition homotsec_natural_natural
           {X Y : UU}
           {f g : X → Y}
           (e : f ~ g)
           {x y : X}
           {p q : x = y}
           (h : p = q)
  : maponpaths
      (λ s : g x = g y, e x @ s)
      (maponpaths (maponpaths g) h)
    @ homotsec_natural e q
    =
    homotsec_natural e p
    @ maponpaths (λ s : f x = f y, s @ e y) (maponpaths (maponpaths f) h).
Proof.
  induction h.
  exact (!(pathscomp0rid _)).
Defined.

Section ApTrans.
  Context {X Y : UU}
          (HX : isofhlevel 4 X)
          (HY : isofhlevel 4 Y)
          {f g : X → Y}
          (e : f ~ g).

  Definition ap_pstrans_data
    : pstrans_data
        (ps_ap_functor HX HY f)
        (ps_ap_functor HX HY g).
  Proof.
    use make_pstrans_data.
    - exact e.
    - intros x y p.
      use make_invertible_2cell.
      + exact (homotsec_natural e p).
      + apply fundamental_groupoid_2cell_iso.
  Defined.

  Definition ap_pstrans_laws
    : is_pstrans ap_pstrans_data.
  Proof.
    repeat split.
    - simpl ; intros x y p q h ; cbn.
      exact (homotsec_natural_natural e h).
    - simpl ; intro x ; cbn.
      exact (!(pathscomp0rid _ @ pathscomp0rid _)).
    - simpl ; intros x y z p q ; cbn.
      induction p, q.
      cbn.
      induction (e x).
      apply idpath.
  Qed.

  Definition ap_pstrans
    : pstrans
        (ps_ap_functor HX HY f)
        (ps_ap_functor HX HY g).
  Proof.
    use make_pstrans.
    - exact ap_pstrans_data.
    - exact ap_pstrans_laws.
  Defined.
End ApTrans.
