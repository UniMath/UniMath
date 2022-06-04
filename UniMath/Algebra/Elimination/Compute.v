Require Import UniMath.Combinatorics.VectorsTests.
Require Import UniMath.Algebra.Elimination.Elimination.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Matrix.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.RealNumbers.Prelim.


Section Tests_1.

  Context (R : rig).
  Context (NCR : natcommrig).

  Let v1 := (append_vec empty_vec 2).
  Let v2 := (append_vec empty_vec 3).

  Eval compute in firstValue (@pointwise nat _ mul v1 v2).

  Let v3 := (append_vec (append_vec empty_vec 2) 3).
  Let v4 := (append_vec (append_vec empty_vec 3) 4).

  Eval compute in firstValue (@pointwise nat _ mul v1 v2).

  Eval compute in stnsum (@pointwise nat _ mul v3 v4).
  (* 18 *)

  Let e1 := (@nattorig natcommrig 2).
  Let e2 := (@nattorig natcommrig 3).

  Let v5 := (append_vec (append_vec empty_vec e1) e1).
  Let v6 := (append_vec (append_vec empty_vec e2) e2).

  Let m1 := append_vec (row_vec v5) v6.

  (* sum [2, 2] ^ [3, 3] *)
  Eval compute in ((iterop_fun (@rigunel2 natcommrig) op1 (pointwise _ op2 v5 v6))).
  (* 12 *)

  (* [2, 2] [2, 2] = [10, 10]
     [3, 3] [3, 3]   [15, 15] *)
  Eval compute in (firstValue (@matrix_mult _ _ _ m1 _ m1)).
  (* Does not compute, or at least not display, well *)

  (* Computing entry (1, 1) : 10 *)
  Eval compute in firstValue (firstValue (@matrix_mult _ _ _ m1 _ m1)).
  (* 10 *)

End Tests_1.

Section Tests_2.

    Context {R: rig}.
    Context {F: fld}.
    Context {nat' : natcommrig}.

    (* Very slow *)
    (* Eval cbn in (1 + 1 + 1 + 1 + 1)%hz. *)

    Eval cbn in (1 + 0)%hq.

    Let v3 := (append_vec empty_vec (1 + 1)%hz).
    Let v4 := (append_vec empty_vec (1 + 1)%hz).

    Eval cbn in (op2 (1 + 1) (1 + 1))%hz.
    (* rigtoringop2int natcommrig (make_dirprod 2 0) (make_dirprod 2 0)) *)

    Eval cbn in (firstValue (@pointwise hz _ op2 v3 v3)).
    (* rigtoringop2int _ (make_dirprod 2 0) (make_dirprod 2 0) *)
    Eval cbn in
        firstValue (firstValue (@matrix_mult hz _ _ (row_vec v3) _ (col_vec v4))).

End Tests_2.