(***** Universal Algebra: the group-terms algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Groups.

Open Scope stn.

Definition group_signature: signature
  := make_signature_simple
       (vcons 2          (* multiplication *)
       (vcons 0          (* identity *)
       (vcons 1          (* inverse *)
     vnil))).

Local Definition group_mul_op: names group_signature := ●0.
Local Definition group_id_op: names group_signature := ●2.
Local Definition group_inv_op: names group_signature := ●2.

Section Group_Algebra.

  Variable G : gr.

  Let arg1 {i} (p: Vector G (1 + i)) : G := el p (●0).
  Let arg2 {i} (p: Vector G (2 + i)) : G := el p (●1).

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

End Group_Algebra.

Definition group_mul := iter_build_term group_mul_op.
Definition group_id  := iter_build_term group_id_op.
Definition group_inv := iter_build_term group_inv_op.
