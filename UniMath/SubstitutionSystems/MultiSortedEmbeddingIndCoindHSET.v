(** the embedding of generated inductive syntax into coinductive syntax is a morphism of Sigma-monoids

    this is only exemplified for [HSET] as base category

author: Ralph Matthes 2023
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.

Local Open Scope cat.

Section A.

  Context (sort : UU) (Hsort : isofhlevel 3 sort) (*(Hsort_set : isaset sort)*) (sig : MultiSortedSig sort).

  (* Let Hsort := hlevelntosn 2 _ Hsort_set. *)

  Let θHSET := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
                 TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET sig.

  Local Definition Initialσind := InitialSigmaMonoidOfMultiSortedSig_CAT sort Hsort HSET TerminalHSET InitialHSET
                                    BinProductsHSET BinCoproductsHSET (fun s s' => ProductsHSET (s=s')) CoproductsHSET
                                    (EsortToSet2 sort Hsort) (ColimsHSET_of_shape nat_graph) sig.

  Local Definition σind : SigmaMonoid θHSET := pr1 Initialσind.

  Let sortToSet : category := [path_pregroupoid sort Hsort, HSET].

  Local Definition Tind : [sortToSet, sortToSet] := SigmaMonoid_carrier θHSET σind.

  Local Definition σcoind : SigmaMonoid θHSET
    := coindSigmaMonoidOfMultiSortedSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET sig is_univalent_HSET.

  Local Definition Tcoind : [sortToSet, sortToSet] := pr1 σcoind.

  Local Definition ind_into_coind : SigmaMonoid θHSET ⟦σind, σcoind⟧ := InitialArrow Initialσind σcoind.

(* TODO: spell out the constituents *)

End A.
