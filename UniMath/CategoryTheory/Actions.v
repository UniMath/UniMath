(** Author: Langston Barrett (@siddharthist) *)
(** ** Actions *)
(** ** Contents
- Strutures on morphisms
 - Endomorphisms and the endomorphism monoid
 - Automorphisms and the automorphism group
 - The endomorphism ring in an additive category
- Actions
 - Monoid (group) actions
 - Ring  actions
 *)

(** TODO:
 1. Rephrase definitions, prove equivalences with the originals:
   - Modules as abelian groups with a ring  action
   - Group actions (Ktheory/GroupAction) as sets with a group action
 2. Category of actions
 3. Actions as functors, equivariant maps as natural transformations,
    categories of actions as functor categories. Prerequisites:
   - Groups as single object categories
   - Rings as single object categories
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.CategoryTheory.Categories.

(* For the endomorphism ring  *)
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

(* For the symmetric group *)
Require Import UniMath.CategoryTheory.categories.category_hset.

(* For the (re)definition of rings *)
Require Import UniMath.CategoryTheory.categories.abgrs.

Local Open Scope cat.

(** ** Structures on morphisms *)

(** *** Endomorphisms and the endomorphism monoid *)

(** Endomorphisms of X are arrows X --> X *)
Definition endomorphisms {C : precategory} (X : ob C) : UU := (X --> X).

(** When the hom-types of C are sets, we can form the endomorphism monoid *)
Definition endomorphism_monoid {C : category} (X : ob C) : monoid.
Proof.
  refine ((((X --> X,, pr2 C X X)),, compose),, _).
  split.
  - exact (fun x x' x'' => !(@assoc C _ _ _ _ x x' x'')).
  - refine (identity X,, _).
    split.
    * exact (@id_left C X X).
    * exact (@id_right C X X).
Defined.

(** *** Automorphisms and the automorphism group *)

(** The automorphism group is a submonoid of the endomorphism monoid *)

(** When the hom-types of C are sets, we can form the automorphism grp *)
Definition automorphism_grp {C : category} (X : ob C) : gr :=
  gr_invertible_elements (endomorphism_monoid X).

Example symmetric_grp (X : hSet) := @automorphism_grp hset_category X.

(** *** The endomorphism ring in an additive category *)

Definition endomorphism_rng {C : Additive}
           (_ : ob (categoryWithAbgrops_category C)) : rng.
Proof.
  (** The multiplication operation is composition, we reuse the proof
      from the endomorphism monoid. The addition operation is the addition
      on homsets, we extract this with to_binop *)
  pose (end_monoid := @endomorphism_monoid (categoryWithAbgrops_category C) X).
  refine ((pr1 (pr1 end_monoid),,
          dirprodpair (to_binop X X) (pr2 (pr1 end_monoid))),, _).

  split; split.
  (** We know by assumption on C that + is an abgrop.*)
  - exact (to_isabgrop _ _).
  (** We already proved this *)
  - exact (pr2 end_monoid).
  (** We know by assumption on C that pre- and post-composition
   *)
  - intros f g h.
    apply (to_premor_monoid C _ _ _ h).
  - intros f g h.
    apply (to_postmor_monoid C _ _ _ h).
Defined.

(** ** Actions *)

(** *** Monoid (group) actions *)

Definition monaction {C : category} (M : monoid) (X : ob C) :=
  monoidfun M (endomorphism_monoid X).

(** *** Ring actions *)

Definition rngaction {C : Additive} (R : rng) (X : ob C) :=
  rngfun R (endomorphism_rng X).