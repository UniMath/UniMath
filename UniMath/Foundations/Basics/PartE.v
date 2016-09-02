(** * Univalent Basics, Part E

This file contains the results from the univalent basics that use more than one universe.
Since at the moment the universe discipline in the UniMath is enforced through human attention
and participation some questions concerning the universe management have been left unanswered.

For example, should there be one or many [ empty ] types?

In the context of UniMath-Coq these questions will become answered eventually in the process of the
development of the type system underlying Coq and its implementation.

Univalent Basics Parts A-D use strictly only one universe UU and types that a members of this universe.

This part of the Univalent Basics starts introducing concepts requiring more than one, usually two,
universes.

The analysis of how a particular system of universe management would affect UniMath should
start with this file. *)

(** ** Preamble *)

(** *** Settings *)

Unset Automatic Introduction.
(* The above line has to be removed for the file to compile with Coq8.2 *)


(** *** Imports *)

Require Export UniMath.Foundations.Basics.PartB.

(* end of "Preamble" *)

(** *** Homotopies between families and the total spaces *)

Definition famhomotfun {X : UU} {P Q : X -> UU}
           (h : P ~ Q) (xp : total2 P) : total2 Q.
Proof.
  intros.
  induction xp as [ x p ].
  split with x.
  induction (h x).
  apply p.
Defined.

Definition famhomothomothomot {X : UU} {P Q : X -> UU} (h1 h2 : P ~ Q)
           (H : h1 ~ h2) : famhomotfun h1 ~ famhomotfun h2.
Proof.
  intros.
  intro xp.
  induction xp as [x p].
  simpl.
  apply (maponpaths (fun q => tpair Q x q)).
  induction (H x).
  apply idpath.
Defined.

(* End of file *)