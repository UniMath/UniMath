(** * Prime Numbers *)
(** ** Contents
- Definition of Prime Numbers
- Univalence for Primes
*)

Require Import UniMath.MoreFoundations.All.

(** ** Primes *)

(** *** Basic definitions *)

Definition pr : UU := total2 (λ X : setwithbinop, isgrop (@op X)).

Definition make_pr :

Definition 
