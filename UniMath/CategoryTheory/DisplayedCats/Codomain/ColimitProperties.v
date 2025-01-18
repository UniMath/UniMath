(***************************************************************************************

 Properties of colimits in the slice

 We verify some properties of binary coproducts and initial objects in the slice. More
 precisely, we give conditions for when we have a strict initial object in the slice
 category, and when we have disjoint and stable coproducts in the slice category.

 Contents
 1. Strict initial objects in the slice category
 2. Disjoint binary coproducts in the slice
 3. Stable binary coproducts in the slice

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.IteratedSlice.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.

Local Open Scope cat.

Section ASlice.
  Context {C : category}
          (x : C).

  (** * 1. Strict initial objects in the slice category *)
  Definition is_strict_initial_cod_fib
             (I : Initial C)
             (HI : is_strict_initial I)
    : is_strict_initial (initial_cod_fib x I).
  Proof.
    intros y f.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    apply HI.
  Qed.

  Definition strict_initial_cod_fib
             (I : strict_initial_object C)
    : strict_initial_object (C/x).
  Proof.
    use make_strict_initial.
    - exact (initial_cod_fib x I).
    - apply is_strict_initial_cod_fib.
      exact (is_strict_initial_strict_initial I).
  Defined.

  (** * 2. Disjoint binary coproducts in the slice *)
  Definition disjoint_bincoproducts_cod_fib
             (I : Initial C)
             (BC : BinCoproducts C)
             (H : disjoint_bincoproducts BC I)
    : disjoint_bincoproducts
        (bincoproducts_cod_fib x BC)
        (initial_cod_fib x I).
  Proof.
    repeat split.
    - use is_monic_cod_fib.
      apply H.
    - use is_monic_cod_fib.
      apply H.
    - use to_is_pullback_slice.
      + abstract
          (rewrite <- !comp_in_cod_fib ;
           apply maponpaths ;
           apply InitialArrowEq).
      + apply H.
  Qed.

  (** * 3. Stable binary coproducts in the slice *)
  Definition stable_bincoproducts_cod_fib
             (BC : BinCoproducts C)
             (HC : Pullbacks C)
             (H : stable_bincoproducts BC)
    : stable_bincoproducts (bincoproducts_cod_fib x BC).
  Proof.
    use stable_bincoproducts_from_pb_preserves_bincoproduct.
    - use codomain_fiberwise_pullbacks.
      exact HC.
    - intros f g p.
      use preserves_bincoproduct_cod_pb_iterated.
      exact (pb_preserves_bincoproduct_from_stable_bincoproducts BC HC H (dom_mor p)).
  Qed.
End ASlice.

(** * 4. Preservation of colimits by the arrow functor *)
Definition preserves_initial_fiber_functor_disp_codomain
           {C₁ C₂ : category}
           (I : Initial C₁)
           {F : C₁ ⟶ C₂}
           (HF : preserves_initial F)
           (x : C₁)
  : preserves_initial (fiber_functor (disp_codomain_functor F) x).
Proof.
  use preserves_initial_if_preserves_chosen.
  {
    exact (initial_cod_fib x I).
  }
  unfold preserves_chosen_initial.
  use to_initial_slice.
  apply HF.
  exact (pr2 I).
Qed.

Definition preserves_bincoproducts_fiber_functor_disp_codomain
           {C₁ C₂ : category}
           (BC : BinCoproducts C₁)
           {F : C₁ ⟶ C₂}
           (HF : preserves_bincoproduct F)
           (x : C₁)
  : preserves_bincoproduct (fiber_functor (disp_codomain_functor F) x).
Proof.
  use preserves_bincoproduct_if_preserves_chosen.
  {
    exact (bincoproducts_cod_fib x BC).
  }
  intros f g.
  use to_bincoproduct_slice.
  use (isBinCoproduct_eq_arrow
         _ _
         (HF _ _ _ _ _ (isBinCoproduct_BinCoproduct _ (BC (cod_dom f) (cod_dom g))))).
  - rewrite disp_codomain_fiber_functor_mor.
    apply idpath.
  - rewrite disp_codomain_fiber_functor_mor.
    apply idpath.
Qed.
