(** **********************************************************

Contents:

        - Definition of proto-monads [proto_monad]



Written by Benedikt Ahrens (started April 2017)
  following slides by Ralph Matthes
<<
  https://fpfm.github.io/Slides_Matthes.pdf
>>
************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Section fix_a_functor.

Variables C D : precategory.
Variable J : functor C D.

Definition proto_monad : UU
  := ∑ F : functor C D, nat_trans J F.

Coercion functor_from_proto_monad (Z : proto_monad) : functor _ _ := pr1 Z.
Definition proto_η (Z : proto_monad) : nat_trans J Z := pr2 Z.


Section proto_module.

Variable Z : proto_monad.
Variable E : precategory.

Definition mbind_op (X : functor C E) : UU
  := ∏ (c c' : C), D⟦J c, Z c'⟧ → E⟦X c, X c'⟧.

Definition η_mbind {X : functor C E} (R : mbind_op X) : UU
  := ∏ (c c' : C), R _ _ (proto_η Z c) = identity (X c) .

(** TODO: better have two separate equations here *)
Definition n_mbind {X : functor C E} (R : mbind_op X) : UU
  := ∏ (c1 c1' c2 c2' : C) (h1 : c1' --> c1) (h2 : c2 --> c2')
       (f : J c1 --> Z c2),
     #X h1 · R _ _ f · #X h2 = R _ _ (#J h1 · f · #Z h2).



Definition proto_module_data : UU
  := ∑ X : functor C E, mbind_op X.
Coercion functor_from_proto_module (Z : proto_module_data) : functor _ _ := pr1 Z.
Definition mbind (X : proto_module_data) {c c' : C} : _ → _  := pr2 X c c'.

Definition proto_module : UU
  := ∑ X : proto_module_data, η_mbind (pr2 X) × n_mbind (pr2 X).

End proto_module.


End fix_a_functor.
(* *)