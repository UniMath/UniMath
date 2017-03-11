Require Export UniMath.Foundations.Preamble.
Require Export UniMath.Foundations.Resizing1.

(* this file is compiled with type-in-type *)

(* temporarily, for debugging: *)
Global Set Printing Universes.
Global Arguments paths : clear implicits.

Section A.

  Universe i j.

  Constraint i < j.             (* we impose this constraint so we don't resize a type needlessly *)

  Definition ResizeType (T : Type@{j}) : Type@{i}.
  (* Later we'll add hypotheses on T, analogous to those in the resizing axioms of Voevodsky.
     For example, that T is a proposition. *)
  Proof.
    exact T.
  Defined.

End A.

