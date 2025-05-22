(******************************************************************************************

 Exponentials of partial setoids

 In this file we put together all the necessary statements that show that the category of
 partial setoids has exponentials.

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialEval.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialLam.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialEqs.

Local Open Scope cat.
Local Open Scope hd.

Definition exponentials_partial_setoid
           (H : tripos)
  : Exponentials (binproducts_partial_setoid H).
Proof.
  intros X.
  apply right_adjoint_weq_coreflections.
  intro Y.
  use make_coreflection'.
  - exact (exp_partial_setoid X Y).
  - exact (eval_partial_setoid X Y).
  - intro φ.
    use make_coreflection_arrow.
    + exact (lam_partial_setoid (coreflection_data_arrow φ)).
    + exact (lam_partial_setoid_comm (coreflection_data_arrow φ)).
    + exact (lam_partial_setoid_unique (coreflection_data_arrow φ)).
Defined.
