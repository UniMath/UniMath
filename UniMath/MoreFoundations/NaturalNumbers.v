(** * Natural numbers

Author: Langston Barrett (@siddharthist)

Some definitions are derived from Coq.ZArith.Znumtheory.
*)

(** ** Contents
- Primality
  - Greatest common divisors ([gcd])
  - Relative primality ([rel_prime])
  - Primality ([is_prime])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.

(** ** Primality *)

(** *** Greatest common divisors ([gcd]) *)

(** First definition: the remainder when dividing m by n is 0. *)
Definition natdivides (n m : nat) : hProp.
Proof.
  use hProppair.
  - exact (natrem m n = 0).
  - apply isasetnat.
Defined.

(** Alternative definition: there exists some p such that n * p = m. *)
Definition natdivides' (n m : nat) : hProp.
Proof.
  use hProppair.
  - exact (n ≠ 0 → ∑ p, n * p = m).
  - apply impred; intros neq0.
    apply invproofirrelevance; intros p p'.
    apply subtypeEquality'; [|apply isasetnat].
    apply (natdivremunique n (pr1 p) 0 (pr1 p') 0).
    + apply natneq0to0lth; assumption.
    + apply natneq0to0lth; assumption.
    + refine (_ @ !natplusl0 _).
      refine (natplusl0 _ @ _).
      refine (natmultcomm _ _ @ _).
      refine (_ @ !natmultcomm _ _).
      refine (pr2 p @ _).
      exact (!pr2 p').
Defined.

Notation "n | m" := (natdivides n m) (at level 50) : nat.

Local Open Scope nat.

(** Note that due to the definition of [natdivmod], 0 divides everything. *)
Lemma natdivides_0 (n : nat) : 0 | n.
Proof.
  destruct n; reflexivity.
Defined.

Lemma natdivides_1 (n : nat) : 1 | n.
Proof.
  destruct n; reflexivity.
Defined.

(** The two definitions are equivalent. *)
Lemma if_divides_then_factor {n m : nat} : n ≠ 0 → (n | m) → m = (m / n) * n.
  intros neq0 ?.
  refine (natdivremrule m n neq0 @ _).
  refine (_ @ natplusl0 _).
  apply (maponpaths (λ z, z + (m / n) * n)).
  assumption.
Defined.

Corollary natdivides_to_natdivides' {n m : nat} : natdivides n m → natdivides' n m.
  intros divs.
  exists (m / n).
  refine (natmultcomm _ _ @ _).
  apply pathsinv0.
  apply if_divides_then_factor; assumption.
Defined.

Definition is_nat_gcd (n m g : nat) : hProp.
Proof.
  use hProppair.
  - exact ((g | n) × (g | m) × (∏ x : nat, (x | n) -> (x | m) -> x ≤ g)).
  - apply isapropdirprod.
    + apply isasetnat.
    + apply isapropdirprod.
      * apply isasetnat.
      * do 3 (apply impred; intro).
        apply propproperty.
Defined.

Definition mk_is_nat_gcd {n m : nat} (g : nat) :
  (g | n) → (g | m) → (∏ x : nat, (x | n) -> (x | m) -> x ≤ g) → is_nat_gcd n m g :=
  λ gn gm f, dirprodpair gn (dirprodpair gm f).

(** [nat_gcd] and accessor functions. *)
Definition nat_gcd (n m : nat) : UU := ∑ g : nat, is_nat_gcd n m g.
Definition mk_nat_gcd {n m} : ∏ (g : nat), is_nat_gcd n m g -> nat_gcd n m := tpair _.
Definition nat_gcd_num {n m} (g : nat_gcd n m) : nat := pr1 g.
Definition nat_gcd_div_n {n m} (g : nat_gcd n m) : (nat_gcd_num g) | n := dirprod_pr1 (pr2 g).
Definition nat_gcd_div_m {n m} (g : nat_gcd n m) : (nat_gcd_num g) | m :=
  dirprod_pr1 (dirprod_pr2 (pr2 g)).
Definition nat_gcd_ge_divisors {n m} (g : nat_gcd n m) :
  ∏ x : nat, (x | n) -> (x | m) -> x ≤ nat_gcd_num g :=
  dirprod_pr2 (dirprod_pr2 (pr2 g)).

(** There is at most one [nat_gcd]. *)
Lemma isaprop_nat_gcd {n m : nat} : isaprop (nat_gcd n m).
Proof.
  apply invproofirrelevance.
  intros g g'.
  apply subtypeEquality'.
  - apply isantisymmnatleh.
    + apply nat_gcd_ge_divisors; [apply nat_gcd_div_n|apply nat_gcd_div_m].
    + apply nat_gcd_ge_divisors; [apply nat_gcd_div_n|apply nat_gcd_div_m].
  - apply propproperty.
Defined.

(** "The nat_gcd of n and m is g", i.e. every nat_gcd of n and m is equal to g. *)
Definition nat_gcd_is (n m g : nat) : hProp.
Proof.
  use hProppair.
  - exact (∏ gc : nat_gcd n m, nat_gcd_num gc = g).
  - apply impred; intro; apply isasetnat.
Defined.

(** [nat_gcd] is symmetric *)
Local Lemma nat_gcd_sym_lemma {n m : nat} (g : nat) : is_nat_gcd n m g -> is_nat_gcd m n g.
Proof.
  intros isg; use mk_is_nat_gcd.
  - apply (nat_gcd_div_m (mk_nat_gcd g isg)).
  - apply (nat_gcd_div_n (mk_nat_gcd g isg)).
  - intro x.
    apply flip.
    apply (nat_gcd_ge_divisors (mk_nat_gcd g isg)).
Defined.

Lemma nat_gcd_sym {n m : nat} (g : nat) : is_nat_gcd n m g ≃ is_nat_gcd m n g.
Proof.
  apply weqimplimpl.
  - apply nat_gcd_sym_lemma.
  - apply nat_gcd_sym_lemma.
  - apply propproperty.
  - apply propproperty.
Defined.

(** [nat_gcd] with 0 and 1. *)

Lemma nat_gcd_0 : ∏ (n : nat), nat_gcd_is n 0 1.
Abort.

Lemma nat_gcd_1 : ∏ (n : nat), nat_gcd_is n 1 1.
Abort.

(** *** Relative primality ([rel_prime]) *)

(** Two numbers are relatively prime if their [nat_gcd] is 1. *)
Definition rel_prime (n : nat) (m : nat) : hProp.
Proof.
  use hProppair.
  - exact (∏ g : nat_gcd n m, nat_gcd_num g = 1).
  - apply impred; intro; apply isasetnat.
Defined.

(** Relative primality is symmetric *)

(** *** Primality ([natprime]) *)

(** A number is prime if it is relatively prime with every number less than it. *)
Definition natprime (n : nat) : hProp.
Proof.
  use hProppair.
  - exact (1 < n × (∏ m, m < n -> rel_prime n m)).
  - apply isapropdirprod.
    + apply propproperty.
    + do 2 (apply impred; intro).
      apply propproperty.
Defined.

(** It would be great to prove
    <<
    Lemma prime_2 : prime 2.
    >>
    For this, it seems one needs that nat_gcd(n, 0) = 1 and nat_gcd(n, 1) = 1.
 *)
Lemma prime_2 : natprime 2.
Abort.
