(** * Additional theorems about fields *)

Require Export UniMath.Algebra.Domains_and_Fields.

Lemma isapropmultinvpair :
  ∏ (X : rig) (x : X), isaprop (multinvpair X x).
Proof.
  intros X x.
  apply isapropinvpair.
Qed.

(** ** Projections for [fld] *)

Section fld_proj.

Context {X : fld}.

Definition zero_fld : X := 0%rng.
Definition one_fld : X := 1%rng.
Definition plus_fld (x y : X) : X := (x + y)%rng.
Definition opp_fld (x : X) : X := (- x)%rng.
Definition minus_fld (x y : X) : X := (x - y)%rng.
Definition mult_fld (x y : X) : X := (x * y)%rng.
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
  rngmultmonoid (pr1fld X).

End fld_struct.
