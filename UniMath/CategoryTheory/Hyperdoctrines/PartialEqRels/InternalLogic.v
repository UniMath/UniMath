(*********************************************************************************************

 The first-order hyperdoctrine of partial setoids

 Every first-order hyperdoctrine gives rise to the category of partial setoids in that
 first-order hyperdoctrine. The category of partial setoids enjoys many properties, and these
 allow us to interpret first-order predicate logic via partial setoids using monomorphisms. In
 this file, we construct an equivalent first-order hyperdoctrine that uses a simpler
 characterization of monomorphisms, namely as formulas in the original hyperdoctrine that
 satisfy some extra properties. This allows us to work with the internal logic in the same way
 as we use subsets.

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Truth.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Falsity.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Conjunction.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Disjunction.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Implication.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Existential.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Universal.

Local Open Scope cat.
Local Open Scope hd.

Definition per_subobject_hyperdoctrine
           (H : first_order_hyperdoctrine)
  : hyperdoctrine.
Proof.
  use make_hyperdoctrine.
  - exact (category_of_partial_setoids H).
  - exact (disp_cat_per_subobject H).
  - exact (terminal_partial_setoid H).
  - exact (binproducts_partial_setoid H).
  - exact (disp_cat_per_subobject_cleaving H).
  - apply locally_prop_disp_cat_per_subobject.
  - apply is_univalent_disp_cat_per_subobject.
Defined.

Definition per_subobject_first_order_hyperdoctrine
           (H : first_order_hyperdoctrine)
  : first_order_hyperdoctrine.
Proof.
  use make_first_order_hyperdoctrine.
  - exact (per_subobject_hyperdoctrine H).
  - apply fiberwise_terminal_per_subobject.
  - apply fiberwise_initial_per_subobject.
  - apply fiberwise_binproducts_per_subobject.
  - apply fiberwise_bincoproducts_per_subobject.
  - apply fiberwise_exponentials_per_subobject.
  - apply dependent_products_per_subobject.
  - apply dependent_sums_per_subobject.
Defined.
