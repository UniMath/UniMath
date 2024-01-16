From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(** * Category of [hSet]s

Started by: Benedikt Ahrens, Chris Kapulkin, Mike Shulman

January 2013

Extended by: Anders Mörtberg (October 2015)

*)

(** ** Contents:

- Category [HSET] of [hSet]s ([hset_category])
- Some particular HSETs
- Hom functors

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.HLevels.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

(** ** Category HSET of [hSet]s ([hset_category]) *)
Section HSET_precategory.

  Definition hset_precategory_ob_mor : precategory_ob_mor :=
    make_precategory_ob_mor
      hSet
      (λ A B : hSet, A -> B).

Definition hset_precategory_data : precategory_data :=
  make_precategory_data hset_precategory_ob_mor (fun (A:hSet) (x : A) => x)
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
Proof.
repeat split.
Qed.

Definition hset_precategory : precategory :=
  tpair _ _ is_precategory_hset_precategory_data.

Local Notation "'HSET'" := hset_precategory : cat.

Lemma has_homsets_HSET : has_homsets HSET.
Proof.
intros a b; apply isaset_set_fun_space.
Qed.

(*
  Canonical Structure hset_precategory. :-)
 *)

Definition hset_category : category := (HSET ,, has_homsets_HSET).

End HSET_precategory.

Notation "'HSET'" := hset_category : cat.
Notation "'SET'" := hset_category : cat.

(** ** Some particular HSETs *)

Definition emptyHSET : HSET.
Proof.
  exists empty.
  abstract (apply isasetempty).
Defined.

Definition unitHSET : HSET.
Proof.
  exists unit.
  abstract (apply isasetunit).
Defined.

Definition natHSET : HSET.
Proof.
  exists nat.
  abstract (apply isasetnat).
Defined.

(*Definition of HomFunctor for categories, analagous definition for precategories is in ../Type/Core*)
Section HomSetFunctors.

Context {C : category}.

Definition homSet_functor_data :
  functor_data (category_binproduct (C^op) C) hset_category.
Proof.
  use make_functor_data.
  + intros pair.
    induction pair as (p1, p2).
    use make_hSet.
    - exact (C ⟦ p1, p2 ⟧).
    - use (homset_property C).
  + intros x y fg h.
    induction fg as (fg1, fg2).
    cbn in fg1.
    exact (fg1 · h · fg2).
Defined.

Lemma is_functor_homSet_functor_type : is_functor homSet_functor_data.
Proof.
  use make_dirprod.
  - intro; cbn.
    apply funextsec; intro.
    refine (id_right _ @ _).
    apply id_left.
  - repeat intro.
    apply funextsec; intro; cbn.
    do 3 rewrite assoc.
    reflexivity.
Defined.

Definition homSet_functor : functor (category_binproduct (C^op) C) hset_category :=
  make_functor _ is_functor_homSet_functor_type.

Context (c : C).

Definition cov_homSet_functor : functor C hset_category :=
  functor_fix_fst_arg (C^op) _ _ homSet_functor c.

Definition contra_homSet_functor : functor (C^op) hset_category :=
  functor_fix_snd_arg (C^op) _ _ homSet_functor c.

End HomSetFunctors.