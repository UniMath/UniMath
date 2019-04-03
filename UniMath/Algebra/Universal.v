(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

(** Basic definitions *)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: UU), names → Arity.

Definition names: Signature -> UU := pr1.

Definition arity: ∏ (sigma: Signature), names sigma → Arity := pr2.

Definition make_signature_from_vector {n: nat} (v: Vector nat n): Signature.
  unfold Signature.
  exists (stn n).
  exact (el v).
Defined.

Definition Algebra (sigma: Signature): UU :=
  ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity sigma nm) → support.

Definition support {sigma: Signature}: Algebra sigma → hSet := pr1.

Definition dom {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  Vector (support a) (arity sigma nm).

Definition op {sigma: Signature} {m: Algebra sigma}:
  ∏ (nm: names sigma), (dom nm) → support m := pr2 m.

(** Examples of signatures and models *)

Local Open Scope stn.

Definition nat_signature := make_signature_from_vector (vcons 0 (vcons 1 vnil)).

Definition nat_zero: names nat_signature := (●0).

Definition nat_succ: names nat_signature := (●1).

Definition bool_signature := make_signature_from_vector (vcons 0 (vcons 1 (vcons  1 (vcons 2 vnil)))).

Definition bool_false: names bool_signature  := (●0).
Definition bool_true: names bool_signature  := (●1).
Definition bool_not: names bool_signature  := (●2).
Definition bool_and: names bool_signature  := (●3).

Definition nat_algebra: Algebra nat_signature.
  unfold Algebra.
  exists natset.
  intro.
  cbn in nm.
  induction nm as [n proofn].
  induction n.
  cbn.
  exact (λ _, 0).
  induction n.
  cbn.
  exact (λ x, S(pr1 x)).
  exact (fromempty (nopathsfalsetotrue proofn)).
Defined.

(**** Algebra homomorphism *)

Section Homomorphisms.

  Context { sigma: Signature }.

  Definition is_hom {a1 a2: Algebra sigma} (f: support a1 → support a2): UU :=
     ∏ (nm: names sigma) (x: dom nm), (f (op nm x) = (op nm (vector_map f x))).

  Definition hom (a1 a2: Algebra sigma) :=  ∑ (f: support a1 → support a2), is_hom f.

  Notation "m1 |-> m2" := (hom m1 m2) (at level 80, right associativity).

  Definition hom_to_fun {a1 a2: Algebra sigma} (h: a1 |-> a2): (support a1) -> (support a2) := pr1 h.

  Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 |-> a2) (h2: a2 |-> a3) : a1 |-> a3.
    exists (funcomp (hom_to_fun h1) (hom_to_fun h2)).
    unfold is_hom.
    intros.
    induction h1 as [f1 ishomf1].
    induction h2 as [f2 ishomf2].
    cbn.
    rewrite vector_map_comp.
    rewrite ishomf1.
    rewrite ishomf2.
    reflexivity.
  Defined.

  Lemma is_hom_idfun {a: Algebra sigma}: is_hom (idfun (support a)).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_idfun {a: Algebra sigma}: a |-> a.
    exists (idfun (support a)).
    exact (is_hom_idfun).
  Defined.

  Definition term_length (l: list (names sigma)): nat.
    induction l as [n v].
    induction n as [  | m h].
    - exact 0.
    - set (rest := h (tl v)).
      exact (S(rest - (arity sigma (hd v)))).
  Defined.

  Definition term_is_wf (l: list (names sigma)): UU := term_length l = 1.

  Definition term_algebra_support := ∑ l: list (names sigma), term_is_wf l.

(*
  Definition isaset_term_algebra_support: isaset term_algebra_support.
    apply isaset_total2.
    apply isofhlevellist.

  Definition term_algebra: Algebra sigma.
   use tpair
   
*)

End Homomorphisms.


  Local Notation "[]" := nil (at level 0, format "[]").
  Local Infix "::" := cons.

  Eval compute in term_length (nat_succ :: nat_zero :: nil).
  Eval compute in term_length nil.
  Eval compute in term_length (nat_zero :: nat_zero :: nil).

