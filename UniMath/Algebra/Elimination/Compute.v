Require Import UniMath.Algebra.Elimination.Elimination.
Require Import UniMath.Algebra.Elimination.RowOps.

Require Import UniMath.Algebra.Matrix.

Require Import UniMath.RealNumbers.Prelim.

(** Observing/testing the extent that it is
    possible to compute some of the Elimination material.

    Primary author: Daniel @Skantz (September 2022) *)

(** This section tests just the matrix/vector operations, avoiding use of the ring operations as far as possible. *)
Section Tests_1.

  Context (R : rig).
  Context (NCR : natcommrig).
  Context (F : fld).

  Let v1 := (append_vec empty_vec 2).
  Let v2 := (append_vec empty_vec 3).

  Let eval1 := Eval compute in firstValue (@pointwise nat _ mul v1 v2).

  Local Lemma eq1 : eval1 = 6. Proof. apply idpath. Defined.

  Let v3 := (append_vec (append_vec empty_vec 2) 3).
  Let v4 := (append_vec (append_vec empty_vec 3) 4).

  Let eval2 := Eval compute in firstValue (@pointwise nat _ mul v1 v2).

  Local Lemma eq2 : eval2 = 6. Proof. apply idpath. Defined.

  Let eval3 := Eval compute in stnsum (@pointwise nat _ mul v3 v4).

  Local Lemma eq3 : eval3 = 18. Proof. apply idpath. Defined.

  Let e1 := (@nattorig natcommrig 2).
  Let e2 := (@nattorig natcommrig 3).

  Let v5 := (append_vec (append_vec empty_vec e1) e1).
  Let v6 := (append_vec (append_vec empty_vec e2) e2).

  Let m1 := append_vec (row_vec v5) v6.

  (* dot product of [2, 2], [3, 3] *)
  Let eval4 :=
      Eval compute
        in ((iterop_fun (@rigunel2 natcommrig) op1 (pointwise _ op2 v5 v6))).
  (* 12 *)

  Local Lemma eq4 : eval4 = 12. Proof. apply idpath. Defined.

  (* matrix product : [2, 2] [2, 2] = [10, 10]
                      [3, 3] [3, 3]   [15, 15] *)

  (* Computing entry (1, 1) : *)
  Let eval5 :=
      Eval compute in firstValue (firstValue (@matrix_mult _ _ _ m1 _ m1)).

  Local Lemma eq5 : eval5 = 10. Proof. apply idpath. Defined.

  Let eval6 := Eval cbn in
    (@matrix_mult _ _ _ (@identity_matrix natcommrig 10)
      _ (@identity_matrix natcommrig 10)).

  Local Lemma eq6 : firstValue (firstValue eval6) = (@nattorig natcommrig 1).
  Proof. apply idpath. Defined.

  (* Switch : [1, 0] -> [0, 1]
              [0, 1]    [1, 0]*)

  Let eval7 := @gauss_switch_row _ 2 2 (0,, (natgthsnn 0)) (1,, (natgthsnn _)) (@identity_matrix R 2).

  Local Lemma eq7 : (firstValue (firstValue eval7)) = (@rigunel1 R).
  Proof. apply idpath. Defined.

  Local Lemma eq8 : (firstValue (lastValue eval7)) = (@rigunel2 R).
  Proof. apply idpath. Defined.

End Tests_1.

Section Tests_2.
(** This section tests computation in the integers [hz] and rationals [hq] *)

    Context {R: rig}.
    Context {F: fld}.

    (* Very slow *)
    (* Eval cbn in (1 + 1 + 1 + 1 + 1)%hz. *)

    Let v3 := (append_vec empty_vec (1 + 1)%hz).
    Let v4 := (append_vec empty_vec (1 + 1)%hq).

    (* Let eval6 := Eval cbn in (op2 (1 + 1) (1 + 1))%hz. *)
    (* rigtoringop2int natcommrig (make_dirprod 2 0) (make_dirprod 2 0)) *)

    (* < 1 second, not computing. *)
    (* Eval cbn in (firstValue (@pointwise hz _ op2 v3 v3)).
    (* rigtoringop2int _ (make_dirprod 2 0) (make_dirprod 2 0) *) *)

    (* < 1 second, not computing. *)
    (* Eval cbn in
        firstValue (firstValue (@matrix_mult hz _ _ (row_vec v3) _ (col_vec v3))). *)

    (* A minute - and not computing *)
    (* Let eval6 := Eval cbn in
        ((@gaussian_elimination hq _ _ (row_vec v3))). *)

End Tests_2.
