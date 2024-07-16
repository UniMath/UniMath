(**************************************************************************************

 The inclusion of monomorphisms into morphisms

 We construct the displayed functor over the identity from the displayed category of
 monomorphisms to the displayed category of morphisms, and we instantiate it to obtain
 fiber functors. We also show that an object in the slice category lies in the slice
 category of monomorphisms if an only if the map to the terminal object is a monomorphism
 as well.

 Content
 1. The displayed functor
 2. The fiber functor
 3. From the slice category to the slice category of monomorphisms

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The displayed functor *)
Definition mono_cod_to_cod
           (C : category)
  : disp_functor
      (functor_identity C)
      (disp_mono_codomain C)
      (disp_codomain C)
  := sigma_disp_pr _.

(** * 2. The fiber functor *)
Definition mono_cod_to_cod_fib
           {C : category}
           (x : C)
  : (C /m x) ⟶ (C / x)
  := fiber_functor (mono_cod_to_cod C) x.

Proposition mono_cod_fiber_functor_on_mor
            {C : category}
            (HC : Pullbacks C)
            {x y : C}
            (f : x --> y)
            {zg₁ zg₂ : C /m y}
            (gp : zg₁ --> zg₂)
  : #(mono_cod_pb HC f) gp
    =
    (#(cod_pb HC f) (#(mono_cod_to_cod_fib _) gp) ,, tt).
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  rewrite cod_fiber_functor_on_mor.
  use (MorphismsIntoPullbackEqual
         (isPullback_Pullback (HC y (pr11 zg₂) x (pr21 zg₂) f))) ; cbn.
  - rewrite !PullbackArrow_PullbackPr1.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (HC y (pr11 zg₂) x (pr21 zg₂) f)).
    }
    rewrite transportf_mono_cod_disp.
    cbn.
    apply idpath.
  - rewrite !PullbackArrow_PullbackPr2.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (HC y (pr11 zg₂) x (pr21 zg₂) f)).
    }
    apply id_right.
Qed.

(** * 3. From the slice category to the slice category of monomorphisms *)
Section MonicSlice.
  Context {C : category}
          {y : C}
          (xf : C / y)
          (T : Terminal (C / y)).

    Let T' : Terminal (C / y) := codomain_fib_terminal y.
    Let x : C := cod_dom xf .
    Let f  : x --> y := cod_mor xf.

    Let fm := @make_cod_fib_mor _ _ xf T' f (id_right _).

    Proposition to_monic_slice_from_terminal
                (H : isMonic (TerminalArrow T xf))
      : isMonic (cod_mor xf).
    Proof.
      intros w g h p.
      simple refine (maponpaths pr1 (H (cod_fib_comp f (make_cod_fib_ob g)) (_ ,, _) (_ ,, _) _)).
      + cbn.
        rewrite id_right.
        apply idpath.
      + cbn.
        rewrite id_right.
        exact (!p).
      + apply TerminalArrowEq.
    Qed.

    Proposition from_monic_slice_to_terminal
                (H : isMonic (cod_mor xf))
      : isMonic (TerminalArrow T xf).
    Proof.
      intros xg φ ψ p.
      use eq_mor_cod_fib.
      use H.
      use (cancel_z_iso _ _ (functor_on_z_iso (slice_dom _) (z_iso_Terminals T' T))).
      pose (maponpaths dom_mor p) as q.
      rewrite !comp_in_cod_fib in q.
      assert (TerminalArrow T xf
              =
              fm · TerminalArrow T T') as r.
      {
        apply TerminalArrowEq.
      }
      rewrite r in q ; clear r.
      rewrite !comp_in_cod_fib in q.
      rewrite !assoc'.
      exact q.
    Qed.

    Definition monic_slice_equiv_terminal
      : isMonic (cod_mor xf)
        ≃
        isMonic (TerminalArrow T xf).
    Proof.
      use weqimplimpl.
      - apply from_monic_slice_to_terminal.
      - apply to_monic_slice_from_terminal.
      - apply isapropisMonic.
      - apply isapropisMonic.
    Qed.
End MonicSlice.
