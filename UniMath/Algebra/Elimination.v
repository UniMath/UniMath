(** * Matrices

Gaussian Elimination over integers.

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.NumberSystems.RationalNumbers.

Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.Combinatorics.Vectors.

Local Definition R := pr1hSet natcommrig.

Section Gauss.
  (* Gaussian elimination over the field of rationals *)

  Local Definition F := pr1hSet hq.


  Definition gauss_add_row {m n : nat} (mat : Matrix F m n)
    (s : F) (r1 r2 : ⟦ m ⟧%stn) : (Matrix F m n).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (op1 (mat r1 j)  (op2 s (mat r2 j))). (* Target row *)
    - exact (mat r1 j). (* Regular row (ID)*)
  Defined.


  (* Is stating this as a Lemma more in the style of other UniMath work?*)
  Local Definition identity_matrix {n : nat} : (Matrix F n n).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
    - exact 1%hq.
    - exact 0%hq.
  Defined.


  (* Need again to restate several definitions to use the identity on rationals*)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Local Definition matrix_mult {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  (* Can be defined inductively, directly, too.*)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  :=
    gauss_add_row (identity_matrix) s r1 r2.

  Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) (s : F) : Matrix F m n :=
    (make_add_row_matrix r1 r2 s ) **  mat.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
             (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  Definition gauss_switch_row {m n : nat} (mat : Matrix F m n)
             (r1 r2 : ⟦ m ⟧%stn) : Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  (*  This might be a non-trivial property to prove, especially in the current double induction-based formalization.*)
  Definition test_row_switch_statement {m n : nat} (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) := (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.


  (* Do we need to redefine this ? *)
  Definition max_hq (a b : hq) : hq.
    induction (hqgthorleh a b).
    - exact a.
    - exact b.
  Defined.

  Definition max_hq_one_arg (a : hq) : hq -> hq := max_hq a.

  (* This should exist somewhere *)
  Definition tl' { n : nat }  (vec: Vector F n) : Vector F (n - 1).
    induction (natgtb n 0).
     assert  ( b: (n - 1 <= n)). { apply (natlehtolehm1 n n). apply isreflnatleh. }
    + exact (λ i : (⟦ n - 1 ⟧%stn), vec (stnmtostnn (n - 1) n b i)).
    + exact (λ i : (⟦ n - 1 ⟧%stn), 0%hq). (* Zero length vector with placeholder *)
  Defined.


  (* We can generalize this to just ordered sets *)
  (*Definition max_hq_index (e : F)  (i : nat) (e' : F) (i' : nat) : hq × nat.*)
  Definition max_hq_index { n : nat } (ei ei' : hq × ⟦ n ⟧%stn) : hq × ⟦ n ⟧%stn.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact ei.
    - exact ei'.
  Defined.

  Definition max_hq_index_one_arg { n : nat } (ei : hq × ⟦ n ⟧%stn) : (hq × ⟦ n ⟧%stn) -> (hq × ⟦ n ⟧%stn)
    := max_hq_index ei.


  (* These are very specific and could be better without the general definition form, or we
     could write these as local definitions *)
  Definition max_argmax_stnhq {n : nat} (vec : Vector F n) (pn : n > 0) : hq × (⟦ n ⟧)%stn.
      (*:=  (foldleft (0%hq ,, 0) (max_hq_index_one_arg) (λ i : (⟦ n ⟧%stn), (vec i) ,, (stntonat _ i))).*)
  Proof.
    set (max_and_idx := (foldleft (0%hq,,(0%nat,,pn)) max_hq_index (λ i : (⟦ n ⟧%stn), (vec i) ,, i))).
    exact (max_and_idx).
  Defined.

  (* To be refactored *)
  Local Definition truncate_pr1 { n : nat } ( f : ⟦ n ⟧%stn → hq) ( k : ⟦ n ⟧%stn ) : ( ⟦ n ⟧%stn → hq).
  Proof.
    intros.
    induction (natgtb X k).
    - exact (f X).
    - exact (f k).
  Defined.

  Definition select_pivot_row {m n : nat} (mat : Matrix F m n) ( k : ⟦ m ⟧%stn ) (pm : m > 0) (pn : n > 0) : ⟦ m ⟧%stn
    := pr2 (max_argmax_stnhq (truncate_pr1  ( λ i : (⟦ m ⟧%stn),  pr1 (max_argmax_stnhq ( ( mat) i) pn)) k ) pm).

  (* Helper Lemma. Possibly unecessary. *)
  Local Definition opt_matrix_op {n : nat} (b : bool) (mat : Matrix F n n) (f : Matrix F n n -> Matrix F n n) : Matrix F n n.
  Proof.
    induction b.
    - exact (f mat).
    - exact mat.
  Defined.

  (* We can probably assert at this point that m and n are > 0, as the base cases can be handled by caller *)
  (* Performed k times . *)
  Definition gauss_step { m : nat } { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) (pm : m > 0) (pn : n > 0) : Matrix F n n × ⟦ n ⟧%stn.
  Proof.
    set (ik := (select_pivot_row mat k pn pn)).
    use tpair. 2: {exact ik. }
    intros i j.
    induction (natlthorgeh i k) as [LT | GTH]. {exact ((mat i j)). }
    set (mat' := gauss_switch_row mat k ik).
    set (mat'' := gauss_scalar_mult_row mat' ((- 1%hq)%hq * (hqmultinv ( mat' k k )))%hq i%nat).
    induction (natgtb j k).
    - exact (((mat'' i j) + (mat'' i k) * (mat k j))%hq).
    - exact (mat'' i j).
  Defined.

  (* k  : 1 -> n - 1 *)
  Definition vec_row_ops_step { n : nat } (k pivot_ik: ⟦ n ⟧%stn)  (mat : Matrix F n n) (vec : Matrix F n 1) : Matrix F n 1.
  Proof.
  intros i.
  induction (natlthorgeh i k). 2 : {exact (vec i). }
  set (vec' := gauss_switch_row vec pivot_ik k).
  assert (pr2stn1 : 0 < 1). { reflexivity. }
  set ( j := make_stn 1 0 pr2stn1).
  exact ( weq_vector_1 ((((vec' i) j) + ((vec' k) j) * (mat i k))%hq)).  (* Would like to verify this construction works*)
  Defined.

  (* The backwards substitution step is done backwards . *)
  (*
  Definition back_sub_step { n : nat }  (vec : Matrix F n 1) : Matrix F n 1.
  Proof.
  intros i.
  induction (natlehchoice i (n - 1)) as [LT | GTH].
  + exact ((vec i) - ∑
  +
  Defined.
  *)

  (* 3 steps :
     Partial pivoting on A.
     Row operations on B.
     Back substitution on B. *)

  Definition gaussian_elimination { m n : nat } (mat : Matrix F n n) (vec : Matrix F 1 n) (pn : n > 0) : Matrix F n n × Matrix F 1 n.
  Proof.
    exact (mat,, vec). (* Placeholder *)
  Defined.


  (* TODO : this one has reversed, incorrect induction steps ... *)
  Definition make_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix F (S n) (S n)) : Matrix F n n.
  Proof.
    intros i' j'.
    assert (bound_n : n <= (S n)). { exact (natlehnsn n). }
    assert (bound_sn : (S n) <= (S n)). { change ((S n) <= (S n)) with (n <= n). apply isreflnatleh. }
    assert (bound_si : (S i') < (S n)). {exact (pr2 i'). }
    assert (bound_sj : (S j') < (S n)). {exact (pr2 j'). }
    set (stn_si := make_stn (S n) (S i') bound_si).
    set (stn_sj := make_stn (S n) (S j') bound_sj).
    induction (natgtb i'  (i - 1)).
    - induction (natgtb j' (j - 1)).
      + exact (mat (stnmtostnn n (S n) (natlehnsn n) i') (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat ((stnmtostnn n (S n) (natlehnsn n) i')) stn_sj).
    - induction (natgtb j' (j - 1)).
      + exact (mat stn_si  (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat stn_si stn_sj).
  Defined.

  (* TODO: need to figure out the recursive step ! *)
  (*
  Definition determinant { n : nat} (mat : Matrix F n n) : F.
  Proof.
    intros.
    set (exp_row := 0).
    induction (natgtb n 1).
    - induction (nat_eq_or_neq n 2).
      assert (x :  0 < n). {rewrite a. reflexivity.}.
      assert (x' : 1 < n). {rewrite a. reflexivity.}.
      set (stn_0 := make_stn n 0 x).
      set (stn_1 := make_stn n 1 x').
      + exact ((mat stn_0 stn_0) * (mat stn_1 stn_1) - (mat stn_0 stn_1) * (mat stn_1 stn_0))%hq.
      + set (cof := 1). (* TODO : this is a dummy for (-1)^(i + j) *)
        exact (Σ (λ j : (⟦ n ⟧%stn), cof * mat ( exp_row j) (determinant ( make_minor i j mat)))).  (* TODO *)
    - induction (nat_eq_or_neq n 0).
      + exact 0%hq.
      + assert (x :  0 < n). {apply natneq0togth0. assumption.}
        set (stn_0 := make_stn n 0 x).
        exact (mat stn_0 stn_0).
  Defined.
  *)

End Gauss.






Section SmithNF.
 (* Generalized elimination over the ring of integers *)

(* Such code might go intro Matrix.v *)
Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
  ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i != (stntonat _ j)) -> (mat i j) = 0%rig.

(*
Definition divisibility_over_diagonal {m n : nat} (mat : Matrix R m n) := *)


End SmithNF.
