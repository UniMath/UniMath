(** * Matrices

Operations on vectors and matrices.

Author: Langston Barrett (@siddharthist) (March 2018)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.RigsAndRings.

(** ** Contents

 - Vectors
   - Standard conditions on one binary operation
   - Standard conditions on a pair of binary operations
   - Structures
 - Matrices
   - Standard conditions on one binary operation
   - Structures
   - Matrix rig
*)

(** ** Vectors *)

Definition pointwise {X : UU} (n : nat) (op : binop X) : binop (Vector X n) :=
  λ v1 v2 i, op (v1 i) (v2 i).

(** *** Standard conditions on one binary operation *)

(** Most features of binary operations (associativity, unity, etc) carry over to
    pointwise operations. *)
Section OneOp.
  Context {X : UU} {n : nat} {op : binop X}.

  Definition pointwise_assoc (assocax : isassoc op) : isassoc (pointwise n op).
  Proof.
    intros ? ? ?; apply funextfun; intro; apply assocax.
  Defined.

  Definition pointwise_lunit (lun : X) (lunax : islunit op lun) :
    islunit (pointwise n op) (const_vec lun).
  Proof.
    intros ?; apply funextfun; intro; apply lunax.
  Defined.

  Definition pointwise_runit (run : X) (runax : isrunit op run) :
    isrunit (pointwise n op) (const_vec run).
  Proof.
    intros ?; apply funextfun; intro; apply runax.
  Defined.

  Definition pointwise_unit (un : X) (unax : isunit op un) :
    isunit (pointwise n op) (const_vec un).
  Proof.
    use isunitpair.
    - apply pointwise_lunit; exact (pr1 unax).
    - apply pointwise_runit; exact (pr2 unax).
  Defined.

  Definition pointwise_comm (commax : iscomm op) : iscomm (pointwise n op).
  Proof.
    intros ? ?; apply funextfun; intro; apply commax.
  Defined.

  Definition pointwise_monoidop (monoidax : ismonoidop op) :
    ismonoidop (pointwise n op).
  Proof.
    use mk_ismonoidop.
    - apply pointwise_assoc, assocax_is; assumption.
    - use isunitalpair.
      + apply (const_vec (unel_is monoidax)).
      + apply pointwise_unit, unax_is.
  Defined.

  Definition pointwise_abmonoidop (abmonoidax : isabmonoidop op) :
    isabmonoidop (pointwise n op).
  Proof.
    use mk_isabmonoidop.
    - apply pointwise_monoidop; exact (pr1isabmonoidop _ _ abmonoidax).
    - apply pointwise_comm; exact (pr2 abmonoidax).
  Defined.

End OneOp.

(** *** Standard conditions on a pair of binary operations *)

Section TwoOps.
  Context {X : UU} {n : nat} {op : binop X} {op' : binop X}.

  Definition pointwise_ldistr (isldistrax : isldistr op op') :
    isldistr (pointwise n op) (pointwise n op').
  Proof.
    intros ? ? ?; apply funextfun; intro; apply isldistrax.
  Defined.

  Definition pointwise_rdistr (isrdistrax : isrdistr op op') :
    isrdistr (pointwise n op) (pointwise n op').
  Proof.
    intros ? ? ?; apply funextfun; intro; apply isrdistrax.
  Defined.

  Definition pointwise_distr (isdistrax : isdistr op op') :
    isdistr (pointwise n op) (pointwise n op').
  Proof.
    use dirprodpair.
    - apply pointwise_ldistr; apply (dirprod_pr1 isdistrax).
    - apply pointwise_rdistr; apply (dirprod_pr2 isdistrax).
  Defined.

End TwoOps.

(** *** Structures *)

Section Structures.

  Definition pointwise_hSet (X : hSet) (n : nat) : hSet.
  Proof.
    use hSetpair.
    - exact (Vector X n).
    - change isaset with (isofhlevel 2).
      apply vector_hlevel, setproperty.
  Defined.

  Definition pointwise_setwithbinop (X : setwithbinop) (n : nat) : setwithbinop.
  Proof.
    use setwithbinoppair.
    - apply pointwise_hSet; [exact X|assumption].
    - exact (pointwise n op).
  Defined.

  Definition pointwise_setwith2binop (X : setwith2binop) (n : nat) : setwith2binop.
  Proof.
    use setwith2binoppair.
    - apply pointwise_hSet; [exact X|assumption].
    - split.
      + exact (pointwise n op1).
      + exact (pointwise n op2).
  Defined.

  Definition pointwise_monoid (X : monoid) (n : nat) : monoid.
  Proof.
    use monoidpair.
    - apply pointwise_setwithbinop; [exact X|assumption].
    - apply pointwise_monoidop; exact (pr2 X).
  Defined.

  Definition pointwise_abmonoid (X : abmonoid) (n : nat) : abmonoid.
  Proof.
    use abmonoidpair.
    - apply pointwise_setwithbinop; [exact X|assumption].
    - apply pointwise_abmonoidop; exact (pr2 X).
  Defined.

End Structures.

(** ** Matrices *)

Definition entrywise {X : UU} (n m : nat) (op : binop X) : binop (Matrix X n m) :=
  λ mat1 mat2 i, pointwise _ op (mat1 i) (mat2 i).

(** *** Standard conditions on one binary operation *)

Section OneOpMat.
  Context {X : UU} {n m : nat} {op : binop X}.

  Definition entrywise_assoc (assocax : isassoc op) : isassoc (entrywise n m op).
  Proof.
    intros ? ? ?; apply funextfun; intro; apply pointwise_assoc, assocax.
  Defined.

  Definition entrywise_lunit (lun : X) (lunax : islunit op lun) :
    islunit (entrywise n m op) (const_matrix lun).
  Proof.
    intros ?; apply funextfun; intro; apply pointwise_lunit, lunax.
  Defined.

  Definition entrywise_runit (run : X) (runax : isrunit op run) :
    isrunit (entrywise n m op) (const_matrix run).
  Proof.
    intros ?; apply funextfun; intro; apply pointwise_runit, runax.
  Defined.

  Definition entrywise_unit (un : X) (unax : isunit op un) :
    isunit (entrywise n m op) (const_matrix un).
  Proof.
    use isunitpair.
    - apply entrywise_lunit; exact (pr1 unax).
    - apply entrywise_runit; exact (pr2 unax).
  Defined.

  Definition entrywise_comm (commax : iscomm op) : iscomm (entrywise n m op).
  Proof.
    intros ? ?; apply funextfun; intro; apply pointwise_comm, commax.
  Defined.

  Definition entrywise_monoidop (monoidax : ismonoidop op) :
    ismonoidop (entrywise n m op).
  Proof.
    use mk_ismonoidop.
    - apply entrywise_assoc, assocax_is; assumption.
    - use isunitalpair.
      + apply (const_matrix (unel_is monoidax)).
      + apply entrywise_unit, unax_is.
  Defined.

  Definition entrywise_abmonoidop (abmonoidax : isabmonoidop op) :
    isabmonoidop (entrywise n m op).
  Proof.
    use mk_isabmonoidop.
    - apply entrywise_monoidop; exact (pr1isabmonoidop _ _ abmonoidax).
    - apply entrywise_comm; exact (pr2 abmonoidax).
  Defined.

End OneOpMat.

(** It is uncommon to consider two entrywise binary operations on matrices,
    so we don't derive "standard conditions on a pair of binar operations"
    for matrices. *)

(** *** Structures *)

(** *** Matrix rig *)

Section MatrixMult.

  Context {R : rig}.

  (** Summation and pointwise multiplication *)
  Local Notation Σ := (iterop_fun rigunel1 op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (** If A is m × n (so B is n × p),
      <<
        AB(i, j) = A(i, 1) * B(1, j) + A(i, 2) * B(2, j) + ⋯ + A(i, n) * B(n, j)
      >>
      The order of the arguments allows currying the first matrix.
  *)
  Definition matrix_mult {m n : nat} (mat1 : Matrix R m n)
                         {p : nat} (mat2 : Matrix R n p) : (Matrix R m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  Lemma identity_matrix {n : nat} : (Matrix R n n).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
    - exact (rigunel2). (* The multiplicative identity *)
    - exact (rigunel1). (* The additive identity *)
  Defined.

End MatrixMult.

Local Notation Σ := (iterop_fun rigunel1 op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).
Local Notation "A ** B" := (matrix_mult A B) (at level 80).

(** The following is based on "The magnitude of metric spaces" by Tom Leinster
    (arXiv:1012.5857v3). *)
Section Weighting.

  Context {R : rig}.

  (** Definition 1.1.1 in arXiv:1012.5857v3 *)
  Definition weighting {m n : nat} (mat : Matrix R m n) : UU :=
    ∑ vec : Vector R n, (mat ** (col_vec vec)) = col_vec (const_vec (1%rig)).

  Definition coweighting {m n : nat} (mat : Matrix R m n) : UU :=
    ∑ vec : Vector R m, ((row_vec vec) ** mat) = row_vec (const_vec (1%rig)).

  Lemma matrix_mult_vectors {n : nat} (vec1 vec2 : Vector R n) :
    ((row_vec vec1) ** (col_vec vec2)) = weq_matrix_1_1 (Σ (vec1 ^ vec2)).
  Proof.
    apply funextfun; intro i; apply funextfun; intro j; reflexivity.
  Defined.

  (** Multiplying a column vector by the identity row vector is the same as
      taking the sum of its entries. *)
  Local Lemma sum_entries1 {n : nat} (vec : Vector R n) :
    weq_matrix_1_1 (Σ vec) = ((row_vec (const_vec (1%rig))) ** (col_vec vec)).
  Proof.
    refine (_ @ !matrix_mult_vectors _ _).
    do 2 apply maponpaths.
    apply pathsinv0.
    refine (pointwise_lunit 1%rig _ vec).
    apply riglunax2.
  Defined.

  Local Lemma sum_entries2 {n : nat} (vec : Vector R n) :
      weq_matrix_1_1 (Σ vec) = (row_vec vec ** col_vec (const_vec 1%rig)).
  Proof.
    refine (_ @ !matrix_mult_vectors _ _).
    do 2 apply maponpaths.
    apply pathsinv0.
    refine (pointwise_runit 1%rig _ vec).
    apply rigrunax2.
  Defined.

  (** TODO: prove this so that the below isn't hypothetical *)
  Definition matrix_mult_assoc_statement : UU :=
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q),
    ((mat1 ** mat2) ** mat3) = (mat1 ** (mat2 ** mat3)).

  (** Lemma 1.1.2 in arXiv:1012.5857v3 *)
  Lemma weighting_coweighting_sum {m n : nat} (mat : Matrix R m n)
        (wei : weighting mat) (cowei : coweighting mat)
        (assocax : matrix_mult_assoc_statement) :
    Σ (pr1 wei) = Σ (pr1 cowei).
  Proof.
    apply (invmaponpathsweq weq_matrix_1_1).
    intermediate_path ((row_vec (const_vec (1%rig))) ** (col_vec (pr1 wei))).
    - apply sum_entries1.
    - refine (!maponpaths (λ z, z ** _) (pr2 cowei) @ _).
      refine (assocax _ _ _ _ _ _ _ @ _).
      refine (maponpaths (λ z, _ ** z) (pr2 wei) @ _).
      apply pathsinv0, sum_entries2 .
  Defined.

  (** Definition 1.1.3 in arXiv:1012.5857v3 *)
  Definition has_magnitude {n m : nat} (mat : Matrix R m n) : UU :=
    (weighting mat) × (coweighting mat).

  Definition magnitude {n m : nat} (m : Matrix R m n) (has : has_magnitude m) : R :=
    Σ (pr1 (dirprod_pr1 has)).

End Weighting.
