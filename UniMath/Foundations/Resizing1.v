Require Export UniMath.Foundations.PartB.

Section SafeResizing.

  (** this file is not compiled with type-in-type *)

  (** In this section we put any type-safe definitions needed by Resizing.v, which
     is compiled with type-in-type. *)

  Universe i j.
  Constraint i < j.
  Set Printing Universes.
  Unset Printing Notations.

End SafeResizing.
