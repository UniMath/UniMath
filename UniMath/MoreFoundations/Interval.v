(** * A construction of the interval using propositional truncation *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.NullHomotopies.
Require Import UniMath.MoreFoundations.Notations.

Definition interval := ∥ bool ∥.
Definition left := hinhpr true : interval.
Definition right := hinhpr false : interval.
Definition interval_path : left = right := squash_path true false.
Definition interval_map {Y} {y y':Y} : y = y' -> interval -> Y.
Proof.
  intros e. set (f := λ t:bool, if t then y else y').
  refine (cone_squash_map f (f false) _).
  intros v. induction v.
  { exact e. }
  { reflexivity. }
Defined.

Goal ∏ Y {y y':Y} (e : y = y'), interval_map e left = y.
   reflexivity.
Qed.

Goal ∏ Y {y y':Y} (e : y = y'), interval_map e right = y'.
   reflexivity.
Qed.

(** ** An easy proof of functional extensionality for sections using the interval, which is derived
       from formal properlties of propositional truncation, but notice that propositional truncation
       uses functional extensionality for functions, already. *)

Definition funextsec2 X (Y:X->Type) (f g:∏ x,Y x) :
           (∏ x, f x = g x) -> f = g.
Proof.
  intros e. exact (maponpaths (λ h x, interval_map (e x) h) interval_path).
Defined.
