(******************************************************************************************

 Exponentials of partial setoids

 In this file we put together all the necessary statements that show that the category of
 partial setoids has exponentials.

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
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
  use left_adjoint_from_partial.
  - exact (λ Y, exp_partial_setoid X Y).
  - exact (λ Y, eval_partial_setoid X Y).
  - intros Y Z φ.
    use make_iscontr.
    + simple refine (_ ,, _).
      * exact (lam_partial_setoid φ).
      * exact (lam_partial_setoid_comm φ).
    + abstract
        (intros ψ ;
         induction ψ as [ ψ p ] ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
         exact (lam_partial_setoid_unique φ ψ p)).
Defined.
