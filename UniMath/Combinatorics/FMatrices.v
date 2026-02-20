(** * Finite sequences

Matrices defined in March 2018 by Langston Barrett (@siddharthist).
 *)

(** ** Contents

  Matrices

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FVectors.

(** ** Matrices *)

Local Open Scope stn.

(** An m × n matrix is an m-length vector of n-length vectors (rows).
<<
        <--- n --->
      | [ * * * * ]
      m [ * * * * ]
      | [ * * * * ]
>>
    Since [Vector]s are encoded as functions ⟦n⟧ → X, a matrix is a function (of
    two arguments). Thus, the (i, j)-entry of a matrix Mat is simply Mat i j.
 *)
Definition Matrix (X : UU) (m n : nat) : UU := Vector (Vector X n) m.

(** The transpose is obtained by flipping the arguments. *)
Definition transpose {X : UU} {n m : nat} (mat : Matrix X m n) : Matrix X n m :=
  flip mat.

Definition row {X : UU} {m n : nat} (mat : Matrix X m n) : ⟦ m ⟧ → Vector X n := mat.

Definition col {X : UU} {m n : nat} (mat : Matrix X m n) : ⟦ n ⟧ → Vector X m := transpose mat.

Definition row_vec {X : UU} {n : nat} (vec : Vector X n) : Matrix X 1 n :=
  λ i j, vec j.

Definition col_vec {X : UU} {n : nat} (vec : Vector X n) : Matrix X n 1 :=
  λ i j, vec i.

(** hlevel of matrices *)
Lemma matrix_hlevel (X : UU) (n m : nat) {o : nat} (ism : isofhlevel o X) :
  isofhlevel o (Matrix X n m).
Proof.
  do 2 apply vector_hlevel; assumption.
Defined.

(** Constant matrix *)
Definition const_matrix {X : UU} {n m : nat} (x : X) : Matrix X n m :=
  const_vec (const_vec x).

(** Every type is equivalent to 1 × 1 matrices on that type. *)
Lemma weq_matrix_1_1 {X : UU} : X ≃ Matrix X 1 1.
  intermediate_weq (Vector X 1); apply weq_vector_1.
Defined.
