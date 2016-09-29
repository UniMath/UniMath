(**

Definition of multisorted binding signatures.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section DiscreteCategory.

Variable (A : UU).

Definition DiscretePrecategory : precategory.
Proof.
use tpair.
- use tpair.
use tpair.
apply A.
simpl.
intros a b.
apply (a = b).
use tpair.
simpl.
intro a; apply idpath.
simpl.
intros a b c h1 h2.
apply (pathscomp0 h1 h2).
- split. split; trivial.
simpl.
intros a b f.
apply pathscomp0rid.
simpl.
intros.
apply path_assoc.
Defined.

Lemma has_homsets_DiscretePrecategory (H : isofhlevel 3 A) : has_homsets DiscretePrecategory.
Proof.
simpl.
unfold has_homsets.
intros.
simpl in *.
unfold isaset in *.
intros h1 h2.
unfold isaprop.
simpl.
apply H.
Defined.

End DiscreteCategory.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variable sort : UU.

Let Dsort := DiscretePrecategory sort.

Let C := [Dsort,HSET,has_homsets_HSET].



End MBindingSig.
