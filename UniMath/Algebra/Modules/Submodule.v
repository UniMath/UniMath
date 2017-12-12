(** Authors Floris van Doorn, December 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Algebra.Modules.Core.

(** ** Contents
- Subobjects of modules
*)

Definition issubsetwithsmul {R : hSet} {M : hSet} (smul : R → M → M) (A : hsubtype M) : UU :=
∏ r m, A m → A (smul r m).

Definition issubmodule {R : rng} {M : module R} (A : hsubtype M) : UU :=
issubgr A × issubsetwithsmul (module_mult M) A.

Definition issubmodulepair {R : rng} {M : module R} {A : hsubtype M}
           (H1 : issubgr A) (H2 : issubsetwithsmul (module_mult M) A) : issubmodule A :=
dirprodpair H1 H2.
