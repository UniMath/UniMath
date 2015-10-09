(** * Additional theorems about fields *)

Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

(** ** [fld] and the other structures *)

Section fld_struct.

Context (X : fld).

Definition fld_to_addmonoid : monoid :=
  grtomonoid (rngaddabgr (pr1fld X)).

Definition fld_to_multmonoid : monoid :=
  rngmultmonoid (pr1fld X).

End fld_struct.
