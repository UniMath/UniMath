(** * Groups as universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Groups.

Open Scope stn.

Definition group_signature: signature
  := make_signature_simple
       (vcons 2                       (* multiplication *)
              (vcons 0                (* identity *)
                     (vcons 1         (* inverse *)
                            vnil))).

Local Definition group_mul_op: names group_signature := ●0.
Local Definition group_id_op: names group_signature := ●2.
Local Definition group_inv_op: names group_signature := ●2.

Section GroupAlgebra.

  Variable G: gr.

  Let arg1 {i: nat} (p: Vector G (1 + i)): G := el p (●0).
  Let arg2 {i} (p: Vector G (2 + i)): G := el p (●1).

  Definition group_ops (nm : names group_signature)
    : Vector G (arity nm) → G.
  Proof.
    induction nm as (i,ilt).
    induction i as [|i _].
    { exact (λ p, op (arg1 p) (arg2 p)). }
    induction i as [|i _].
    { exact (λ _, unel G). }
    induction i as [|i _].
    { exact (λ p, grinv G (arg1 p)). }
    exact (fromempty (nopathsfalsetotrue ilt)).
  Defined.

  Definition group_algebra : algebra group_signature
    := make_algebra G group_ops.

End GroupAlgebra.

Definition group_mul := build_term_curried group_mul_op.
Definition group_id  := build_term_curried group_id_op.
Definition group_inv := build_term_curried group_inv_op.
