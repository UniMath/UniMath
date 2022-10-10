(** * Additional theorems about fields *)

Require Export UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Lemma isapropmultinvpair :
  ∏ (X : rig) (x : X), isaprop (multinvpair X x).
Proof.
  intros X x.
  apply isapropinvpair.
Qed.

(** ** Projections for [fld] *)

Section fld_proj.

Context {X : fld}.

Definition zero_fld : X := 0%ring.
Definition one_fld : X := 1%ring.
Definition plus_fld (x y : X) : X := (x + y)%ring.
Definition opp_fld (x : X) : X := (- x)%ring.
Definition minus_fld (x y : X) : X := (x - y)%ring.
Definition mult_fld (x y : X) : X := (x * y)%ring.
Definition inv_fld (x : X) : X.
Proof.
  apply sumofmaps with (3 := fldchoice x) ; intro x'.
  - exact (pr1 x').
  - exact x.
Defined.
Definition div_fld (x y : X) : X := mult_fld x (inv_fld y).

End fld_proj.

(** ** [fld] and the other structures *)

Section fld_struct.

Context (X : fld).

Definition fld_to_gr1 : gr :=
  abgrtogr (pr1fld X).

Definition fld_to_monoid1 : monoid :=
  grtomonoid fld_to_gr1.

Definition fld_to_monoid2 : monoid :=
  ringmultmonoid (pr1fld X).

End fld_struct.
