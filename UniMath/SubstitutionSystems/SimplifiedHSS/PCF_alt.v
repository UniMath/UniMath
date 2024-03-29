(**

Syntax of PCF as a multisorted binding signature.

Written by: Anders Mörtberg, 2021

version for simplified notion of HSS by Ralph Matthes (2022, 2023)
the file is identical to the homonymous file in the parent directory, except for importing files from the present directory

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.STLC_alt.

Local Open Scope cat.

Section pcf.

(** We assume a set of types with bool, nat and function types *)
Context (type : hSet) (Bool Nat : type) (arr : type → type → type).

Let Htype : isofhlevel 3 type := MultiSortedBindingSig.PCF_Hsort type.
Let typeToSet : category := SortIndexing.sortToSet type Htype.
Let typeToSet2 : category := SortIndexing.sortToSet2 type Htype.

Local Definition BCtypeToSet : BinCoproducts typeToSet := SortIndexing.BCsortToSet type Htype.

Local Notation "'Id'" := (functor_identity _).

Let PCF_Sig : MultiSortedSig type := PCF_Sig type Bool Nat arr.

Definition PCF_Signature : Signature typeToSet _ _ :=
  MultiSortedSigToSignatureSet type Htype PCF_Sig.

Definition PCF_Functor : functor typeToSet2 typeToSet2 :=
  Id_H _ BCtypeToSet PCF_Signature.

Lemma PCF_Functor_Initial : Initial (FunctorAlg PCF_Functor).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + intros; apply ProductsHSET.
  + apply Exponentials_functor_HSET.
  + apply ColimsHSET_of_shape.
Defined.

Definition PCF_Monad : Monad typeToSet :=
  MultiSortedSigToMonadSet type Htype PCF_Sig.

(** Extract the constructors from the initial algebra *)
Definition PCF_M : typeToSet2 :=
  alg_carrier _ (InitialObject PCF_Functor_Initial).

Let PCF_M_mor : typeToSet2⟦PCF_Functor PCF_M,PCF_M⟧ :=
  alg_map _ (InitialObject PCF_Functor_Initial).

Let PCF_M_alg : algebra_ob PCF_Functor :=
  InitialObject PCF_Functor_Initial.

(** The variables *)
Definition var_map : typeToSet2⟦Id,PCF_M⟧ := η PCF_M_alg.

(* We can also extract the other constructors *)

End pcf.
