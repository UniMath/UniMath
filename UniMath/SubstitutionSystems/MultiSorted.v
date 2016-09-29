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

Definition DiscPrecat_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_DiscPrecat_data : is_precategory DiscPrecat_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition DiscPrecat : precategory :=
  (DiscPrecat_data,,is_precategory_DiscPrecat_data).

Lemma has_homsets_DiscPrecat (H : isofhlevel 3 A) : has_homsets DiscPrecat.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

End DiscreteCategory.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variable sort : UU.

Let sort_cat : precategory := DiscPrecat sort.
Let sortToHSET : precategory := [sort_cat,HSET,has_homsets_HSET].

Definition MSig (s : sort) : UU :=
  Σ (I : sort -> UU), I s → list (list sort × sort).

Definition indices {s : sort} (M : MSig s) : sort → UU := pr1 M.

Definition args {s : sort} (M : MSig s) : indices M s → list (list sort × sort) := pr2 M.


Local Notation "'1'" := (TerminalHSET).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsHSET a b)) (at level 50).
Local Notation "a ⊛ b" := (BinProductObject _ (BinProductsHSET a b)) (at level 60).

Definition option (eq : isdeceq sort) : sort -> sortToHSET -> sortToHSET.
Proof.
intros s f.
mkpair.
- mkpair.
  + intro t.
    induction (eq s t) as [H|H].
    * apply (pr1 f t ⊕ 1). (* TODO: Add coercion to make this look like sort -> Set *)
    * apply (pr1 f t).
  + now intros t1 t2 [].
- abstract (split; [ now intros ? | now intros ? ? ? [] [] ]). (* UGH *)
Defined.

Definition option_list (eq : isdeceq sort) : list sort -> sortToHSET -> sortToHSET.
Admitted.

Definition endo_fun (a : list sort × sort) (X : functor sortToHSET sortToHSET) : functor sortToHSET HSET.
Admitted.

Definition endo_funs (xs : list (list sort × sort)) (X : functor sortToHSET sortToHSET) : functor sortToHSET HSET.
Admitted.

Definition MSigToFunctor {s : sort} (M : MSig s) : functor sortToHSET sortToHSET.
Admitted.

End MBindingSig.
