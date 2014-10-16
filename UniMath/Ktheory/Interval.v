(** * A construction of the interval using propositional truncation *)

Require Import Ktheory.Utilities.

Definition interval := squash bool.
Definition left := hinhpr _ true : interval.
Definition right := hinhpr _ false : interval.
Definition interval_path : left = right := squash_path true false.
Definition interval_map {Y} {y y':Y} : y = y' -> interval -> Y.
Proof. intros ? ? ? e. set (f := fun t:bool => if t then y else y').
       refine (cone_squash_map f (f false) _).
       intros v. induction v. { exact e. } { reflexivity. } Defined.

(** ** An easy proof of functional extensionality for sections using the interval *)

Definition funextsec2 X (Y:X->Type) (f g:forall x,Y x) :
           (forall x, f x = g x) -> f = g.
Proof. intros ? ? ? ? e.
       exact (maponpaths (fun h x => interval_map (e x) h) interval_path).
Defined.
