(**

This file contains the final step in the formalization of multisorted binding signatures:

- Construction of a monad on Set/sort from a multisorted signature
  ([MultiSortedSigToMonad])


Written by: Anders Mörtberg, 2016. The formalization follows a note
written by Benedikt Ahrens and Ralph Matthes, and is also inspired by
discussions with them and Vladimir Voevodsky.

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Slice.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted.

Local Open Scope cat.

Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_cat C X).

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Context (sort : hSet).

Local Definition HSET_over_sort : category.
Proof.
exists (HSET / sort).
now apply has_homsets_slice_precat.
Defined.

(** * Construction of a monad from a multisorted signature *)
Section monad.

Let Id_H := Id_H (HSET / sort) (BinCoproducts_HSET_slice sort).

(* ** Construction of initial algebra for a signature with strength on Set / sort *)
Definition SignatureInitialAlgebraSetSort
  (H : Signature HSET_over_sort HSET_over_sort HSET_over_sort) (Hs : is_omega_cocont H) :
  Initial (FunctorAlg (Id_H H)).
Proof.
use colimAlgInitial.
- apply Initial_functor_precat, Initial_slice_precat, InitialHSET.
- apply (is_omega_cocont_Id_H), Hs.
- apply ColimsFunctorCategory_of_shape, slice_precat_colims_of_shape,
        ColimsHSET_of_shape.
Defined.

Let HSS := @hss_category _ (BinCoproducts_HSET_slice sort).

(* ** Multisorted signature to a HSS *)
Definition MultiSortedSigToHSS (sig : MultiSortedSig sort) :
  HSS (MultiSortedSigToSignature sort sig).
Proof.
apply SignatureToHSS.
+ apply Initial_slice_precat, InitialHSET.
+ apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
+ apply is_omega_cocont_MultiSortedSigToSignature.
  apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

(* The above HSS is initial *)
Definition MultiSortedSigToHSSisInitial (sig : MultiSortedSig sort) :
  isInitial _ (MultiSortedSigToHSS sig).
Proof.
now unfold MultiSortedSigToHSS, SignatureToHSS; destruct InitialHSS.
Qed.

(** ** Function from multisorted binding signatures to monads *)
Definition MultiSortedSigToMonad (sig : MultiSortedSig sort) : Monad (HSET / sort).
Proof.
use Monad_from_hss.
- apply BinCoproducts_HSET_slice.
- apply (MultiSortedSigToSignature sort sig).
- apply MultiSortedSigToHSS.
Defined.

End monad.

End MBindingSig.
