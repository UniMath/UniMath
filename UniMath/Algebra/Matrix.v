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

  (*
  Lemma inverse {n : nat} : (Matrix R n n).
  Proof.
    intros i j.
    trivial.
  Defined.
  *)

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

  (*
  Lemma helper : 
   {m : nat} {p : nat} {q : nat} :  m -> p -> q ->  R ->  Matrix R m q.
  Proof.
  reflexivity.
  Admitted.
  *)
(*((⟦ m ⟧)%stn) → ((⟦ q ⟧)%stn) → ((⟦ p ⟧)%stn) → R*)


Section Toys.

  Context {R : rig}.

  Definition matrix_equal
  {n m : nat} 
  (mat1 mat2: Matrix R m n) : UU :=
  ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn),
  (mat1 i) j = (mat2 i) j.  
   
  Definition vector_equal
  {n : nat} 
  (vec1 vec2: Vector R n) : UU :=
  ∏ (i : ⟦ n ⟧%stn),
  vec1 i = vec2 i.  
   
  
  (* Start easy *)
  Lemma pointwise_matrix_flip_eq:
    ∏ (m n : nat) (mat : Matrix R m n)
    (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn),
    (col mat j) i = (row mat i) j.
  Proof.
    reflexivity.
  Defined.
  
  (*
  Definition matrix_mult {m n : nat} (mat1 : Matrix R m n)
                         {p : nat} (mat2 : Matrix R n p) : (Matrix R m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).  
  *)

  Definition sum_rows
  {m n : nat}
  (mat : Matrix R m n)
  : Vector R m :=
   λ (i : (⟦ m ⟧)%stn),
    Σ (row mat i). 
 
  Definition sum_cols
  {m n : nat}
  (mat : Matrix R m n)
  : Vector R n :=
   λ (i : (⟦ n ⟧)%stn),
    Σ (col mat i). 

  (*We want a function Vector R n -> Matrix R n 1
  This is col_vec / row_vec from finite sequences*)

  (*Matrix R m n -> Vector R 1 *)
  Definition sum_cols_then_rows 
  {m n : nat}
  (mat : Matrix R m n)
  : Vector R 1 :=
   sum_rows (row_vec (sum_cols mat)). 


  Definition sum_rows_then_cols
  {m n : nat}
  (mat : Matrix R m n)
  : Vector R 1 :=
   sum_cols (col_vec (sum_rows mat)). 



  (* Σ
  (row (λ (i0 : (⟦ m ⟧)%stn) (j0 : (⟦ p ⟧)%stn), Σ (row mat1 i0 ^ col mat2 j0)) i
   ^ col mat3 j) =
Σ
  (row mat1 i
   ^ col (λ (i0 : (⟦ n ⟧)%stn) (j0 : (⟦ q ⟧)%stn), Σ (row mat2 i0 ^ col mat3 j0)) j)
 *)
  
  
  (* Could be generalized to all sets with commutative (+),
     under some restrictions *) 
  (*
  Lemma ring_sum_interchange : 
    ∏ (X : R),  (Σ X * 
    ( Σ Y)) = (Σ Y * ( Σ X)).
  *)
  
  Definition is_square 
    {m n: nat} (_ : Matrix R m n) : UU := m = n.


  Lemma matrix_sum_order_eq :
  ∏ (m n : nat)
  (mat : Matrix R m n),
  (sum_cols_then_rows mat
  = sum_rows_then_cols mat).
  Proof.
  intros.
  unfold sum_cols_then_rows.
  unfold sum_rows_then_cols.
  unfold sum_rows. unfold sum_cols.
  unfold row_vec. unfold col_vec.
  unfold col. unfold row.
  unfold transpose.
  unfold flip.
  Admitted. 


  Search pr1hSet.
  About pr1hSet.
  Search "pr1hSet".
  Definition matrix_add
  {m n : nat}
  (mat1 : Matrix R m n)
  (mat2 : Matrix R m n)
  : (Matrix R m n) :=
    λ i j,
      op1 ((row mat1 i) j) ((row mat2 i) j).



    
  Lemma matrix_add_comm:
      ∏ (m n : nat) (mat1 : Matrix R m n)
      (mat2 : Matrix R m n),
      matrix_add mat1 mat2 = matrix_add mat2 mat1.
  Proof.
  intros.
  apply funextfun.
  intros i.
  apply funextfun.
  intros j.
  (*
  unfold matrix_add.
  unfold row. unfold col.
  *)
  apply rigcomm1.
  Defined.

  Lemma matrix_add_assoc:
      ∏ (m n : nat) (mat1 : Matrix R m n)
      (mat2 : Matrix R m n) (mat3 : Matrix R m n),
      matrix_add (matrix_add mat1 mat2) mat3
      = matrix_add mat1 (matrix_add mat2 mat3).
  Proof.
  intros.
  apply funextfun.
  intros i.
  apply funextfun.
  intros j.
  apply rigassoc1.
  Defined.
  
  (* We don't have additive inverses in rigs (but matrices do)? *)
  (*
  Definition matrix_add_inverse 
  {m n : nat) (mat1 : Matrix R m n) := *)

  Definition matrix_add_id
  {m n : nat} (mat1 : Matrix R m n) :=
  λ (i : (⟦ m ⟧)%stn) (j : (⟦ n ⟧)%stn), rigunel1 .

  (* Include additive identity *)
  
  (* How do we phrase something exists ?*)
  
  (* Additive inverse *)
  
  

  (* Also, right/left distributivity,
     Scalar multiplication,
     Transpose ... *)
  
  About Vector.
  Search Vector.

  (* Definition Vector (X : UU) (n : nat) : UU := stn n -> X. *)
  (* Definition Matrix (X : UU) (m n : nat) : UU := Vector (Vector X n) m. *)
  (* Local Notation Σ := (iterop_fun rigunel1 op1). *)
  Print iterop_fun.
  Print nat_rect.

(*
LHS
sum l=1 -> p   sum k -> n  (a_il o b_lk) o c_kj
RHS
sum l=1 -> n   sum k -> p  a_il  o (b_lk o c_kj)
*)

(* re write *)


  Check ((pointwise _ op2)).


  (* Σ
  (row (λ (i0 : (⟦ m ⟧)%stn) (j0 : (⟦ p ⟧)%stn), Σ (row mat1 i0 ^ col mat2 j0)) i
   ^ col mat3 j) =
Σ
  (row mat1 i
   ^ col (λ (i0 : (⟦ n ⟧)%stn) (j0 : (⟦ q ⟧)%stn), Σ (row mat2 i0 ^ col mat3 j0)) j)

  *)
  
  Definition scalar_lmult_vec
  (s : R)
  {n : nat} (vec: Vector R n) :=
  (const_vec s) ^ vec.

  Definition scalar_rmult_vec
  (s : R)
  {n : nat} (vec: Vector R n) :=
  vec ^ (const_vec s).

  Lemma distr_through_sum_ :
  ∏ (n : nat)
    (vec : Vector R n)
    (s : R),
    op2 s (Σ vec) =  Σ (scalar_lmult_vec s vec).
  Proof.
    intros.
    unfold scalar_lmult_vec.
    unfold pointwise.
  Admitted.
  (*
  Lemma distr_through_sum_fun:
  ∏ (n : nat)
    (vec : Vector R n)
    (s : R),
    op2 s (Σ vec) =  Σ (scalar_lmult_vec s vec).
  *)
  Lemma interchange_sums :
  ∏ (m n : nat)
    (i : (⟦ m ⟧)%stn)
    (j : (⟦ n ⟧)%stn)
    (f1 : (⟦ n ⟧)%stn -> R)
    (f2 : (⟦ m ⟧)%stn -> R),
    Σ (λ i : (⟦ n ⟧)%stn, op2 (f1 i)  (Σ (λ j : (⟦ m ⟧)%stn, f2 j)))
  = Σ (λ j : (⟦ m ⟧)%stn, op2 (f2 j) (( Σ (λ i : (⟦ n ⟧)%stn, f1 i)))).
  Proof.
  intros.
  Admitted.
  
  Lemma distr_through_sum :
  ∏ (n : nat)
    (i : (⟦ n ⟧)%stn)
    (vec : Vector R n)
    (s : R),
     op2 s (Σ (λ i : (⟦ n ⟧)%stn,    (vec i)))
  =      Σ (λ i : (⟦ n ⟧)%stn, op2 s (vec i)).
  Proof.
  intros.
  Admitted.

  Lemma distr_through_sum_2 :
  ∏ (n : nat)
    (i : (⟦ n ⟧)%stn)
    (vec : Vector R n)
    (vec2 : Vector R n)
    (s : R),
     op2 s (Σ (λ i : (⟦ n ⟧)%stn,    op2 (vec i) (vec2 i)))
  =      Σ (λ i : (⟦ n ⟧)%stn, op2 s (op2 (vec i) (vec2 i))).
  Proof.
  intros.
  Admitted.

  Lemma distr_through_sum_explicit:
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q)
      (i : (⟦ m ⟧)%stn)
      (i0 : (⟦ n ⟧)%stn)
      (j : (⟦ q ⟧)%stn),
  op2 (mat1 i i0) (Σ (λ i1 : (⟦ p ⟧)%stn, op2 (mat2 i0 i1)  (mat3 i1 j))) =
    Σ (λ i1 : (⟦ p ⟧)%stn, op2 (mat1 i i0) ( op2 (mat2 i0 i1) (mat3 i1 j))).
  Proof.
  intros.
  apply distr_through_sum_2.
  (* ______________________________________(1/1)
    (⟦ p ⟧)%stn      *)
  Admitted.
  

  
  Lemma exact_ : 
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q)
      (i : (⟦ m ⟧)%stn)
      (j : (⟦ q ⟧)%stn),
  (Σ (λ i0 : (⟦ n ⟧)%stn, (((mat1 i i0) * (Σ (λ i1 : (⟦ p ⟧)%stn, ((mat2 i0 i1) * (mat3 i1 j)))))%ring)))
  =
  (Σ (λ i0 : (⟦ n ⟧)%stn, (((Σ (λ i1 : (⟦ p ⟧)%stn, (mat1 i i0) *  ((mat2 i0 i1) * (mat3 i1 j)))))%ring))).
  Proof.
  intros.
  Admitted.

  Lemma exact_2 : 
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q)
      (i : (⟦ m ⟧)%stn)
      (j : (⟦ q ⟧)%stn),
  Σ (λ i0 : (⟦ p ⟧)%stn, (Σ (λ i1 : (⟦ n ⟧)%stn, mat1 i i1 * mat2 i1 i0) * mat3 i0 j)%ring)
  =
  Σ (λ i0 : (⟦ p ⟧)%stn, (Σ (λ i1 : (⟦ n ⟧)%stn, (mat1 i i1 * mat2 i1 i0) * mat3 i0 j))%ring).
  Proof.
  intros.
  Admitted.




  Lemma interchange_sums_ :
  ∏ (m n : nat)
  (f : (⟦ n ⟧)%stn ->  (⟦ m ⟧)%stn -> R),   (* really a matrix by definition *)
  Σ (λ i: (⟦ m ⟧)%stn, Σ (λ j : (⟦ n ⟧)%stn, f j i) )
= Σ (λ j: (⟦ n ⟧)%stn, Σ (λ i : (⟦ m ⟧)%stn, (flip f) i j)  ).
  Proof.
  intros.
  (*
  apply flip.
  rewrite funextfun.
  apply rigcomm1.
  *)
  Admitted.

  (*
  Lemma uncurry_sum : 
  ∏ (m n : nat)
  (f : (⟦ n ⟧)%stn ->  (⟦ m ⟧)%stn -> R),   (* really a matrix by definition *)
    Σ (λ i: (⟦ m ⟧)%stn, Σ (λ j : (⟦ n ⟧)%stn, f j i) )
  = Σ ( Σ ( λ i: (⟦ m ⟧)%stn, λ j: (⟦ n ⟧)%stn, f i j)).
  Proof.
  intros.
  Admitted.
  *)

  Notation "x * y" := (op2 x y) : rig_scope.

  Lemma funeq_implies_sumeq :
  ∏ (n:nat) (f1 f2: (⟦ n ⟧)%stn -> R),
    (f1 = f1) -> (Σ f1) = (Σ f2).
  Proof.
  intros.
  Admitted.
    

  Lemma matrix_mult_assocc : 

    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q),
    ((mat1 ** mat2) ** mat3) = (mat1 ** (mat2 ** mat3)).
  Proof.
  intros.
  unfold matrix_mult.
  change (mat1 ** mat2) with (mat1 ** mat2).
  apply funextfun.
  intro i.
  apply funextfun.
  intro j.
  unfold row. unfold col. unfold transpose. (*unfold flip.*)
  unfold pointwise.
  unfold flip.
  rewrite -> exact_.
  rewrite -> exact_2.
  rewrite interchange_sums_.
  unfold flip.
  set (mat1fun := (λ x y, mat1 x y)). simpl in mat1fun.
  set (mat2fun := (λ x y, mat2 x y)). simpl in mat2fun.
  set (mat3fun := (λ x y, mat3 x y)). simpl in mat3fun.
  apply funeq_implies_sumeq.
  apply funextfun.
  intros k.
  apply funeq_implies_sumeq.
  apply funextfun.
  intros l.
  reflexivity.
  Defined.  

  Local Notation "A ++' B" := (matrix_add A B) (at level 80).

  Lemma sum_distr : 
    ∏ (n : nat) (vec1 vec2 : Vector R n),
     (Σ (λ i : (⟦ n ⟧)%stn, (op1 (vec1 i)  (vec2 i))))
  =  (op1 (Σ (λ i : (⟦ n ⟧)%stn, (vec1 i)))  (Σ ( λ i : (⟦ n ⟧)%stn, vec2 i))).
  Proof.
  intros.
  Admitted.


  Lemma matrix_mult_ldistr : 
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R n p),
    ((mat1 ** (mat2 ++' mat3))) = ((mat1 ** mat2) ++' (mat1 ** mat3)).
  Proof.
  intros.
  unfold "**".
  unfold matrix_add.
  unfold row. unfold col. unfold flip. unfold transpose.
  unfold pointwise. unfold flip.
  apply funextfun.
  intros i.
  apply funextfun.
  intros j.
  set (mat1fun := λ i0 : (⟦ n ⟧)%stn, mat1 i i0).
  set (mat2fun := λ i0 : (⟦ n ⟧)%stn, (mat2 i0) j).
  set (mat3fun := λ i0 : (⟦ n ⟧)%stn, (mat3 i0) j).
  assert (distr: (λ i0 : (⟦ n ⟧)%stn, (mat1fun i0 * (mat2 i0 j + mat3 i0 j))%ring)
               = (λ i0 : (⟦ n ⟧)%stn, op1 (op2 (mat1fun i0) (mat2 i0 j)) (op2 (mat1fun i0) (mat3 i0 j)))%ring).
  + apply funextfun.
    intros k.
    apply rigldistr.
  + rewrite distr.
    rewrite  sum_distr.
    reflexivity.
  Defined.

  Lemma matrix_mult_rdistr : 
    ∏ (m n p: nat) (mat1 : Matrix R n p)
      (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q),
    ((mat1 ++' mat2) ** mat3) = ((mat1 ** mat3) ++' (mat2 ** mat3)).
  Proof.
  intros.
  unfold "**".
  unfold matrix_add. unfold row. unfold col. unfold flip. unfold transpose.
  unfold pointwise. unfold flip.
  apply funextfun.
  intros i.
  apply funextfun.
  intros j.
  assert (distr: (λ i0 : (⟦ p ⟧)%stn, (op1 (mat1 i i0)  (mat2 i i0)) * mat3 i0 j)%ring
               = (λ i0 : (⟦ p ⟧)%stn,  op1 (op2 (mat1 i i0) (mat3 i0 j))
                                           (op2 (mat2 i i0) (mat3 i0 j)))%ring).
  + apply funextfun.
    intros k.
    rewrite rigrdistr.
    reflexivity.
  + rewrite -> distr.
    rewrite sum_distr.
    reflexivity.
  Defined.

  (* *)
  Search "iterop".
  Local Notation Π := (iterop_fun identity_matrix matrix_mult).

  Definition nth_pow_mat
    {m n : nat} (mat : Matrix R m n)
    (pow : nat) := Π (λ _ : (⟦ pow ⟧)%stn, mat). 
End Toys.
