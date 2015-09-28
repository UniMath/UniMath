(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.hlevel2.hq.

Opaque hq.

Open Scope hq_scope.

(** ** Non-negative ratrional numbers *)

Definition hnnq := total2 (hqleh 0).

Definition hnnq_to_hq (r : hnnq) : hq := pr1 r.
Coercion hnnq_to_hq : hnnq >-> pr1hSet.
Definition hq_to_hnnq (r : hq) (Hr : hqleh 0 r) : hnnq :=
  tpair (fun x : hq => hqleh 0 x) r Hr.

Lemma isincl_hnnq_to_hq : isincl hnnq_to_hq. 
Proof. 
  apply (isinclpr1 (fun x : hq => hqleh 0 x) (fun x : hq => isapropneg (hqgth 0 x))).
Qed.
Definition hnnqset : hSet := 
  hSetpair _ (isasetsubset hnnq_to_hq isasethq isincl_hnnq_to_hq).

(** ** Equality and order on [ hnnq ] *)

(** *** Equality *)

Definition hnnqeq ( x y : hnnq ) : hProp := 
  hqeq x y.
Lemma isdecrelhnnqeq : isdecrel hnnqeq.
Proof.
  intros (r1,H1) (r2,H2).
  apply isdecrelhqeq.
Qed.
Definition hnnqdeceq : decrel hnnq :=
  tpair _ hnnqeq isdecrelhnnqeq.

Definition hnnqbooleq := decreltobrel hnnqdeceq.

Definition hnnqneq ( x y : hnnq ) : hProp := hProppair ( neg (hnnqeq  x y ) ) ( isapropneg _  )  .
Definition isdecrelhnnqneq : isdecrel hnnqneq  := isdecnegrel _ isdecrelhnnqeq . 
Definition hnnqdecneq : decrel hnnq := decrelpair isdecrelhnnqneq . 

Definition hnnqboolneq := decreltobrel hnnqdecneq . 

Close Scope hq_scope.

(* End of the file hnnq.v *)
