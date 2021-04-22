(** * Matrices

Operations on vectors and matrices.

Author: Langston Barrett (@siddharthist) (March 2018)
*)

Require Import UniMath.Combinatorics.StandardFiniteSets.

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
    intros ? ? ?.
    apply funextfun.
    intro.
    apply assocax.
  Defined.

  Definition pointwise_lunit (lun : X) (lunax : islunit op lun) :
    islunit (pointwise n op) (const_vec lun).
  Proof.
    intros ?.
    apply funextfun.
    intro.
    apply lunax.
  Defined.

  Definition pointwise_runit (run : X) (runax : isrunit op run) :
    isrunit (pointwise n op) (const_vec run).
  Proof.
    intros ?; apply funextfun; intro; apply runax.
  Defined.

  Definition pointwise_unit (un : X) (unax : isunit op un) :
    isunit (pointwise n op) (const_vec un).
  Proof.
    use make_isunit.
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
    use make_ismonoidop.
    - apply pointwise_assoc, assocax_is; assumption.
    - use make_isunital.
      + apply (const_vec (unel_is monoidax)).
      + apply pointwise_unit, unax_is.
  Defined.

  Definition pointwise_abmonoidop (abmonoidax : isabmonoidop op) :
    isabmonoidop (pointwise n op).
  Proof.
    use make_isabmonoidop.
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
    intros ? ? ?.
    apply funextfun.
    intro.
    apply isldistrax.
  Defined.

  Definition pointwise_rdistr (isrdistrax : isrdistr op op') :
    isrdistr (pointwise n op) (pointwise n op').
  Proof.
    intros ? ? ?; apply funextfun; intro; apply isrdistrax.
  Defined.

  Definition pointwise_distr (isdistrax : isdistr op op') :
    isdistr (pointwise n op) (pointwise n op').
  Proof.
    use make_dirprod.
    - apply pointwise_ldistr; apply (dirprod_pr1 isdistrax).
    - apply pointwise_rdistr; apply (dirprod_pr2 isdistrax).
  Defined.

End TwoOps.

(** *** Structures *)

Section Structures.

  Definition pointwise_hSet (X : hSet) (n : nat) : hSet.
  Proof.
    use make_hSet.
    - exact (Vector X n).
    - change isaset with (isofhlevel 2).
      apply vector_hlevel, setproperty.
  Defined.

  Definition pointwise_setwithbinop (X : setwithbinop) (n : nat) : setwithbinop.
  Proof.
    use make_setwithbinop.
    - apply pointwise_hSet; [exact X|assumption].
    - exact (pointwise n op).
  Defined.

  Definition pointwise_setwith2binop (X : setwith2binop) (n : nat) : setwith2binop.
  Proof.
    use make_setwith2binop.
    - apply pointwise_hSet; [exact X|assumption].
    - split.
      + exact (pointwise n op1).
      + exact (pointwise n op2).
  Defined.

  Definition pointwise_monoid (X : monoid) (n : nat) : monoid.
  Proof.
    use make_monoid.
    - apply pointwise_setwithbinop; [exact X|assumption].
    - apply pointwise_monoidop; exact (pr2 X).
  Defined.

  Definition pointwise_abmonoid (X : abmonoid) (n : nat) : abmonoid.
  Proof.
    use make_abmonoid.
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
    intros ? ? ?.
    apply funextfun.
    intro.
    apply pointwise_assoc, assocax.
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
    use make_isunit.
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
    use make_ismonoidop.
    - apply entrywise_assoc, assocax_is; assumption.
    - use make_isunital.
      + apply (const_matrix (unel_is monoidax)).
      + apply entrywise_unit, unax_is.
  Defined.

  Definition entrywise_abmonoidop (abmonoidax : isabmonoidop op) :
    isabmonoidop (entrywise n m op).
  Proof.
    use make_isabmonoidop.
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



Section Toys.

  Context {R : rig}.

  Definition matrix_equal
  {n m : nat}  (mat1 mat2: Matrix R m n) : UU
  :=  ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn),
      (mat1 i) j = (mat2 i) j.

  Definition vector_equal
  {n : nat}  (vec1 vec2: Vector R n) : UU
  :=  ∏ (i : ⟦ n ⟧%stn),
      vec1 i = vec2 i.

  Definition sum_rows
  {m n : nat}
  (mat : Matrix R m n): Vector R m
  :=  λ (i : (⟦ m ⟧)%stn),
      Σ (row mat i).

  Definition sum_cols
  {m n : nat}
  (mat : Matrix R m n): Vector R n
  := λ (i : (⟦ n ⟧)%stn),
     Σ (col mat i).

  Definition is_square
  {m n: nat} (_ : Matrix R m n) : UU := m = n.

  (* TODO: make this definition more similar to matrix_mult? *)
  Definition matrix_add
  {m n : nat}
  (mat1 : Matrix R m n)
  (mat2 : Matrix R m n)
  : (Matrix R m n) :=
    λ i j,
      op1 ((row mat1 i) j) ((row mat2 i) j).

  Lemma matrix_add_comm:
  ∏ {m n : nat} (mat1 : Matrix R m n)
                (mat2 : Matrix R m n),
  matrix_add mat1 mat2 = matrix_add mat2 mat1.
  Proof.
    intros.   apply funextfun.
    intros i. apply funextfun.
    intros j. apply rigcomm1.
  Defined.

  Lemma matrix_add_assoc:
  ∏ {m n : nat} (mat1 : Matrix R m n)
  (mat2 : Matrix R m n) (mat3 : Matrix R m n),
    matrix_add (matrix_add mat1 mat2) mat3
  = matrix_add mat1 (matrix_add mat2 mat3).
  Proof.
    intros.   apply funextfun.
    intros i. apply funextfun.
    intros j. apply rigassoc1.
  Defined.

  Definition scalar_lmult_vec
  (s : R)
  {n : nat} (vec: Vector R n)
  := (const_vec s) ^ vec.

  Definition scalar_rmult_vec
  (s : R)
  {n : nat} (vec: Vector R n)
  := vec ^ (const_vec s).

  Lemma zero_function_sums_to_zero:
    ∏ (n : nat)
      (f : (⟦ n ⟧)%stn -> R),
    (λ i : (⟦ n ⟧)%stn, f i) = const_vec 0%rig ->
    (Σ (λ i : (⟦ n ⟧)%stn, f i) ) = 0%rig.
  Proof.
    intros n f X.
    rewrite X.
    unfold const_vec.
    induction n.
    - reflexivity.
    - intros. rewrite iterop_fun_step.
      + rewrite rigrunax1.
        unfold "∘".
        rewrite -> IHn with ((λ _ : (⟦ n ⟧)%stn, 0%rig)).
        reflexivity.
        reflexivity.
      + apply riglunax1.
  Defined.

  Lemma sum_is_ldistr :
    ∏ (n : nat) (vec : Vector R n) (s : R),
    op2 s (Σ vec) =  Σ ((λ _ : (⟦ n ⟧)%stn, s ) ^ vec).
  Proof.
    intros. induction n.
    - change (Σ vec) with (@rigunel1 R).
      rewrite zero_function_sums_to_zero.
      + apply rigmultx0.
      + apply funextfun; intros i.
        destruct (weqstn0toempty i).
    - rewrite iterop_fun_step.  2: {apply riglunax1. }
      rewrite rigldistr.
      rewrite -> IHn.
      rewrite -> replace_dni_last.
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite -> replace_dni_last.
      apply idpath.
  Defined.

  Lemma sum_is_rdistr:
    ∏ (n : nat) (vec : Vector R n) (s : R),
    op2 (Σ vec) s =  Σ (vec ^ (λ _ : (⟦ n ⟧)%stn, s )).
  Proof.
    intros. induction n.
    - assert (x : ( Σ vec ) = 0%rig).
      + apply idpath.
      + rewrite x. apply rigmult0x.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite rigrdistr.
      rewrite -> IHn.
      rewrite -> replace_dni_last.
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite -> replace_dni_last.
      apply idpath.
  Defined.

  Lemma zero_function_sums_to_zero':
    ∏ (n : nat) (f : (⟦ n ⟧)%stn -> R),
    (λ i : (⟦ n ⟧)%stn, f i) = const_vec 0%rig ->
    (Σ (λ i : (⟦ n ⟧)%stn, f i) ) = 0%rig.
  Proof.
    intros n f f_eq.
    rewrite f_eq.
    unfold const_vec.
    induction n.
    - reflexivity.
    - intros.
      rewrite iterop_fun_step. 2 : {apply riglunax1. }
      rewrite rigrunax1.
      unfold "∘".
      rewrite -> IHn with ((λ _ : (⟦ n ⟧)%stn, 0%rig)).
      + reflexivity.
      + reflexivity.
  Defined.

  Lemma eqlen_sums_mergeable :
    ∏ (n : nat) (f1 f2 : (⟦ n ⟧)%stn -> R),
    op1 (Σ (λ i: (⟦ n ⟧)%stn, f1 i))  (Σ (λ i : (⟦ n ⟧)%stn, f2 i))
    = Σ (λ i: (⟦ n ⟧)%stn, op1 (f1 i) (f2 i)).
  Proof.
    intros.
    induction n.
    - assert ( sum0 : Σ (λ i : (⟦ 0 ⟧)%stn, f1 i) = 0%rig). {reflexivity. }
      assert ( sum0': Σ (λ i : (⟦ 0 ⟧)%stn, f2 i) = 0%rig). {reflexivity. }
      rewrite sum0. rewrite sum0'.
      apply riglunax1.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite <- rigassoc1.
      do 3 rewrite -> rigcomm1.
      rewrite <- (rigcomm1 _ (f1 lastelement)).
      rewrite rigassoc1.
      rewrite IHn.
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite <- rigassoc1.
      rewrite rigcomm1.
      rewrite (rigcomm1 R (f2 lastelement)  (f1 lastelement)).
      reflexivity.
  Defined.

  Lemma interchange_sums :
    ∏ (m n : nat)
      (f : (⟦ n ⟧)%stn ->  (⟦ m ⟧)%stn -> R),
    Σ (λ i: (⟦ m ⟧)%stn, Σ (λ j : (⟦ n ⟧)%stn, f j i) )
    = Σ (λ j: (⟦ n ⟧)%stn, Σ (λ i : (⟦ m ⟧)%stn, f j i)).
  Proof.
    intros. induction n. induction m.
    { reflexivity. }
    assert (x :
        (Σ (λ i : (⟦ 0 ⟧)%stn, Σ ((λ j : (⟦ _ ⟧)%stn, f i j) ))) = 0%rig).
    { reflexivity. }
    - change (Σ (λ i : (⟦ 0 ⟧)%stn, Σ ((λ j : (⟦ _ ⟧)%stn, f i j) )))
        with (@rigunel1 R).
      apply zero_function_sums_to_zero.
      reflexivity.
    - rewrite -> iterop_fun_step. 2: { apply riglunax1. }
      unfold  "∘".
      rewrite <- IHn.
      rewrite eqlen_sums_mergeable.
      apply maponpaths, funextfun. intros i.
      rewrite -> iterop_fun_step. 2: { apply riglunax1. }
      reflexivity.
  Defined.

  Lemma matrix_mult_assoc :
    ∏ {m n : nat} (mat1 : Matrix R m n)
      {p : nat} (mat2 : Matrix R n p)
      {q : nat} (mat3 : Matrix R p q),
    ((mat1 ** mat2) ** mat3) = (mat1 ** (mat2 ** mat3)).
  Proof.
    intros.
    unfold matrix_mult.
    apply funextfun. intro i.
    apply funextfun. intro j.
    etrans.
    2: { symmetry.
         apply maponpaths, funextfun. intros k.
         apply sum_is_ldistr. }
    etrans.
      { apply maponpaths. apply funextfun. intros k.
        apply sum_is_rdistr. }
    rewrite interchange_sums.
    apply maponpaths, funextfun; intros k.
    apply maponpaths, funextfun; intros l.
    apply rigassoc2.
  Defined.

  Local Notation "A ++' B" := (matrix_add A B) (at level 80).

  (* Can we prove this one easier using the lemmas for scalars ? *)
  Lemma eqlen_vec_sums_mergeable :
    ∏ (n : nat) (vec1 vec2 : Vector R n),
     (Σ (λ i : (⟦ n ⟧)%stn, (op1 (vec1 i)  (vec2 i))))
  =  (op1 (Σ (λ i : (⟦ n ⟧)%stn, (vec1 i)))  (Σ ( λ i : (⟦ n ⟧)%stn, vec2 i))).
  Proof.
    intros.
    induction n.
    - rewrite zero_function_sums_to_zero.
      + rewrite riglunax1. apply idpath.
      + apply funextfun; intros i.
        apply fromempty; use weqstn0toempty.
        assumption.
    - do 3 try rewrite iterop_fun_step; try apply riglunax1.
      do 3 unfold "∘"; rewrite replace_dni_last.
      + do 2 rewrite <- rigassoc1;
        do 2 rewrite <- (rigcomm1 _ (vec2 lastelement)).
        do 2 rewrite <- (rigcomm1 _ (vec1 lastelement)).
        rewrite <- rigassoc1.
        rewrite IHn.
        do 2 rewrite rigassoc1.
        reflexivity.
  Defined.

  (* TODO: We are unfolding the matrix multiplication excessively.
           Can we restate this better without unfolding rows, cols ... ?*)
  Lemma matrix_mult_ldistr :
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R n p),
    ((mat1 ** (mat2 ++' mat3))) = ((mat1 ** mat2) ++' (mat1 ** mat3)).
  Proof.
    intros.
    unfold "**". unfold "++'". unfold row. unfold col.
    unfold transpose.  unfold pointwise. unfold flip.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {
      apply maponpaths. apply funextfun. intros k.
      rewrite rigldistr.
      reflexivity.
    }
    apply eqlen_vec_sums_mergeable.
  Defined.

  (*TODO again, many unfolds ...*)
  Lemma matrix_mult_rdistr :
    ∏ (m n p: nat) (mat1 : Matrix R n p)
      (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q),
    ((mat1 ++' mat2) ** mat3) = ((mat1 ** mat3) ++' (mat2 ** mat3)).
  Proof.
    intros.
    unfold "**". unfold "++'". unfold row. unfold col.
    unfold transpose.  unfold pointwise. unfold flip.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {
      apply maponpaths. apply funextfun. intros k.
      rewrite rigrdistr.
      reflexivity.
    }
    apply eqlen_vec_sums_mergeable.
  Defined.

End Toys.
