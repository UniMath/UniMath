(** ** Null homotopies, an aid for proving things about propositional truncation *)

Require Export UniMath.Foundations.PartD.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Notations.

Local Open Scope transport.

Definition nullHomotopyTo {X Y} (f:X->Y) (y:Y) := ∏ x:X, f x = y.
Definition NullHomotopyTo {X Y} (f:X->Y) := total2 (nullHomotopyTo f).
Definition NullHomotopyTo_center {X Y} (f:X->Y) : NullHomotopyTo f -> Y := pr1.
Definition NullHomotopyTo_path {X Y} {f:X->Y} (r:NullHomotopyTo f) := pr2 r.

Definition nullHomotopyFrom {X Y} (f:X->Y) (y:Y) := ∏ x:X, y = f x.
Definition NullHomotopyFrom {X Y} (f:X->Y) := total2 (nullHomotopyFrom f).
Definition NullHomotopyFrom_center {X Y} (f:X->Y) : NullHomotopyFrom f -> Y := pr1.
Definition NullHomotopyFrom_path {X Y} {f:X->Y} (r:NullHomotopyFrom f) := pr2 r.

Definition nullHomotopyTo_transport {X Y} {f:X->Y} {y:Y} (h : nullHomotopyTo f y)
           {y':Y} (p:y = y') (x:X) : (p # h) x = h x @ p.
Proof.
  intros. induction p. apply pathsinv0. apply pathscomp0rid.
Defined.

Lemma isaset_NullHomotopyTo {X Y} (i:isaset Y) (f:X->Y) : isaset (NullHomotopyTo f).
Proof.
  intros. apply (isofhleveltotal2 2).
  { apply i. }
  intros y. apply impred; intros x. apply isasetaprop. apply i.
Defined.

Lemma isaprop_nullHomotopyTo {X Y} (is:isaset Y) (f:X->Y) (y:Y) :
  isaprop (nullHomotopyTo f y).
Proof.
  apply impred; intros x. apply is.
Defined.

Lemma isaprop_NullHomotopyTo {X} {Y} (is:isaset Y) (f:X->Y) :
  ∥ X ∥ -> isaprop (NullHomotopyTo f).
Proof.
  apply factor_through_squash.
  apply isapropisaprop.
  intros x. apply invproofirrelevance. intros [r i] [s j].
  apply subtypePairEquality.
  - intros n. apply (isaprop_nullHomotopyTo is).
  - exact (!i x @ j x).
Defined.

(* We can get a map from '∥ X ∥' to any type 'Y' provided paths
   are given that allow us to map first into a cone in 'Y'.  *)

Definition cone_squash_map {X Y} (f:X->Y) (y:Y) :
  nullHomotopyTo f y -> ∥ X ∥ -> Y.
Proof.
  intros e h. exact (point_from (h (paths_to_prop y) (λ x, f x,,e x))).
Defined.

Goal ∏ X Y (y:Y) (f:X->Y) (e:∏ m:X, f m = y),
       f = cone_squash_map f y e ∘ squash_element.
Proof.
  reflexivity.
Qed.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/MoreFoundations/NullHomotopies.vo"
End:
*)
