(*******************************************************************************************

 Fully faithful displayed functors

 In this file, we collect properties of fully faithful displayed functors.

 Contents
 1. Fully faithful displayed functors reflect isomorphisms

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. Fully faithful displayed functors reflect isomorphisms *)
Section DispFunctorReflectIso.
  Context {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (FF : disp_functor F D₁ D₂)
          (HFF : disp_functor_ff FF)
          {x y : C₁}
          {f : z_iso x y}
          {xx : D₁ x}
          {yy : D₁ y}
          (Fff : z_iso_disp
                  (functor_on_z_iso F f)
                  (FF x xx)
                  (FF y yy)).

  Let ff : xx -->[ f ] yy
    := disp_functor_ff_inv FF HFF Fff.
  Let gg : yy -->[ inv_from_z_iso f] xx
    := disp_functor_ff_inv FF HFF (inv_mor_disp_from_z_iso Fff).

  Lemma disp_functor_ff_reflect_disp_iso_left
    : gg ;; ff
      =
      transportb (mor_disp yy yy) (z_iso_after_z_iso_inv f) (id_disp yy).
  Proof.
    unfold ff, gg.
    rewrite <- disp_functor_ff_inv_compose.
    etrans.
    {
      do 2 apply maponpaths.
      exact (z_iso_disp_after_inv_mor Fff).
    }
    unfold transportb.
    rewrite <- (disp_functor_ff_inv_identity FF HFF).
    rewrite <- disp_functor_ff_inv_transportf.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Lemma disp_functor_ff_reflect_disp_iso_right
    : ff ;; gg
      =
      transportb (mor_disp xx xx) (z_iso_inv_after_z_iso f) (id_disp xx).
  Proof.
    unfold ff, gg.
    rewrite <- disp_functor_ff_inv_compose.
    etrans.
    {
      do 2 apply maponpaths.
      exact (inv_mor_after_z_iso_disp Fff).
    }
    unfold transportb.
    rewrite <- (disp_functor_ff_inv_identity FF HFF).
    rewrite <- disp_functor_ff_inv_transportf.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition disp_functor_ff_reflect_disp_iso
    : z_iso_disp f xx yy.
  Proof.
    use make_z_iso_disp.
    - exact ff.
    - simple refine (_ ,, _ ,, _).
      + exact gg.
      + exact disp_functor_ff_reflect_disp_iso_left.
      + exact disp_functor_ff_reflect_disp_iso_right.
  Defined.
End DispFunctorReflectIso.
