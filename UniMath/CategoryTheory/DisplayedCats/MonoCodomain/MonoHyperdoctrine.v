Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.Inclusion.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodRightAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.FirstOrderHyperdoctrine.

Local Open Scope cat.

Section HyperdoctrineSubobjects.
  Context {C : univalent_category}
          (T : Terminal C)
          {PB : Pullbacks C}
          (I : Initial C)
          (HI : is_strict_initial I)
          (BC : BinCoproducts C)
          (HBC : stable_bincoproducts BC)
          (HC : is_locally_cartesian_closed PB)
          (HC' : is_regular_category C).

  Let BP : BinProducts C := BinProductsFromPullbacks PB T.

  Definition subobject_hyperdoctrine
    : hyperdoctrine.
  Proof.
    use make_hyperdoctrine.
    - exact C.
    - exact (disp_mono_codomain C).
    - exact T.
    - exact BP.
    - exact (mono_cod_disp_cleaving PB).
    - apply locally_propositional_mono_cod_disp_cat.
    - apply disp_univalent_disp_mono_codomain.
  Defined.

  Definition subobject_first_order_hyperdoctrine
    : first_order_hyperdoctrine.
  Proof.
    use make_first_order_hyperdoctrine.
    - exact subobject_hyperdoctrine.
    - apply mono_codomain_fiberwise_terminal.
    - exact (mono_codomain_fiberwise_initial PB I HI).
    - apply mono_codomain_fiberwise_binproducts.
    - exact (mono_codomain_fiberwise_bincoproducts PB BC HBC HC').
    - exact (fiberwise_exponentials_mono_cod HC HC').
    - exact (has_dependent_products_mono_cod HC HC').
    - exact (mono_codomain_has_dependent_sums HC' PB).
  Defined.
End HyperdoctrineSubobjects.
