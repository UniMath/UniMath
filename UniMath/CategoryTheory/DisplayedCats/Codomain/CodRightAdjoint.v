(**************************************************************************************

 Dependent products in a locally cartesian closed category

 Every locally cartesian closed category supports dependent products. The existence of
 the desired adjoints follows by definition of locally cartesian closed, so the only
 work lies in verifying the Beck-Chevalley condition. This follows from a more general
 fact, which allows us to conclude the Beck-Chevalley condition for right adjoints from
 the Beck-Chevalley condition of left adjoints.

 Contents
 1. The Beck-Chevalley condition
 2. Dependent products in a locally cartesian closed category

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.

Local Open Scope cat.

Section DependentProductsCodomain.
  Context {C : category}
          {PB : Pullbacks C}
          (HC : is_locally_cartesian_closed PB).

  Let HD : cleaving (disp_codomain C)
    := disp_codomain_cleaving PB.

  (** * 1. The Beck-Chevalley condition *)
  Proposition cod_right_beck_chevalley
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (H : isPullback p)
    : right_beck_chevalley HD f g h k p (HC x w f) (HC z y h).
  Proof.
    use right_from_left_beck_chevalley.
    - apply is_right_adjoint_cod_fiber_functor.
    - apply is_right_adjoint_cod_fiber_functor.
    - use cod_left_beck_chevalley.
      apply is_symmetric_isPullback.
      exact H.
  Defined.

  Definition lccc_exp_fib_subst
             {Γ Δ : C}
             (s : Γ --> Δ)
             (πA : C/Δ)
             (πB : C/cod_dom πA)
    : z_iso
        (cod_pb PB s (lccc_exp_fib HC πA πB))
        (lccc_exp_fib
           HC
           (cod_pb PB s πA)
           (cod_pb PB (PullbackPr1 _) πB))
    := _
       ,,
       cod_right_beck_chevalley
         _ _ _ _ _
         (isPullback_Pullback (PB _ _ _ (cod_mor πA) s))
         πB.

  (** * 2. Dependent products in a locally cartesian closed category *)
  Definition cod_dependent_products
    : has_dependent_products HD.
  Proof.
    simple refine (_ ,, _).
    - apply HC.
    - exact @cod_right_beck_chevalley.
  Defined.
End DependentProductsCodomain.
