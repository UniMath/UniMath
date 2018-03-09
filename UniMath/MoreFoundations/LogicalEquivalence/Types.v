(** * Logical equivalence for general types*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.

(** ** Contents

- Direct products
- Coproducts
*)

(** A weak equivalence ([weq]) induces a logical equivalence ([logeq]) *)
Lemma weq_to_logeq {P Q : UU} : (P ≃ Q) → (P <-> Q).
Proof.
  intros w.
  split.
  - apply w.
  - apply invmap, w.
Defined.

(** Two empty types are logically equivalent *)
Lemma logeq_if_both_false (P Q : UU) : ¬P -> ¬Q -> (P <-> Q).
Proof.
  intros; apply weq_to_logeq; apply weqempty; assumption.
Defined.

(** Two inhabited types are logically equivalent *)
Lemma logeq_if_both_true (P Q : UU) : P -> Q -> (P <-> Q).
Proof.
  intros p q.
  split.
  - intros; exact q.
  - intros; exact p.
Defined.

(** ** Direct products *)

(** Associativity of direct products *)
Lemma logeq_assoc_dirprod {P Q R : UU} : (P × Q) × R <-> P × (Q × R).
Proof.
  apply weq_to_logeq, weqdirprodasstor.
Defined.

(** Commutativity of direct products *)
Lemma logeq_comm_dirprod {P Q : UU} : P × Q <-> Q × P.
Proof.
  apply weq_to_logeq, weqdirprodcomm.
Defined.

(** Projections from products with [unit] *)
Lemma logeq_dirprod_unit_l {P : UU} : unit × P <-> P.
Proof.
  apply weq_to_logeq.
  intermediate_weq (P × unit).
  - apply weqdirprodcomm.
  - apply invweq, weqtodirprodwithunit.
Defined.

(** Projections from products with [unit] *)
Lemma logeq_dirprod_unit_r {P : UU} : P × unit <-> P.
Proof.
  apply weq_to_logeq.
  apply invweq, weqtodirprodwithunit.
Defined.

(** ** Coproducts *)

(** Associativity of coproducts *)
Lemma logeq_assoc_coprod {P Q R : UU} : (P ⨿ Q) ⨿ R <-> P ⨿ (Q ⨿ R).
Proof.
  apply weq_to_logeq, weqcoprodasstor.
Defined.

(** Absorbtion of coproducts *)
Lemma logeq_dirprod_with_coprod {P Q : UU} : P × (P ⨿ Q) <-> P.
Proof.
  use dirprodpair.
  - exact pr1.
  - intros p; exact (dirprodpair p (inl p)).
Defined.

(** Coproduct with [empty]  *)
Lemma logeq_coprod_empty {P : UU} : ∅ ⨿ P <-> P.
Proof.
  apply weq_to_logeq, weq_coprod_empty.
Defined.
