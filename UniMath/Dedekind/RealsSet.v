(** * Definition of abstract reals and non-negative reals *)
(** Catherine Lelay. Jan. 2016 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.ConstructiveStructures.

(** ** Morphism *)

Definition ismonoidmorphism {X Y : monoid} (f : X -> Y) :=
  f 0%addmonoid = 0%addmonoid × ∀ x y : X, f (x + y)%addmonoid = (f x + f y)%addmonoid.
Definition monoidmorphism (X Y : monoid) :=
  Σ (f : X -> Y), ismonoidmorphism f.


(** ** Archimedean set *)
