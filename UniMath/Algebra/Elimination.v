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

Require Import UniMath.Foundations.NaturalNumbers.

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

  (* These could really be m x n ...*)
  Definition make_scalar_mult_row_matrix { n : nat}
    (s : F) (r : ⟦ n ⟧%stn): Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r).
    + exact ((gauss_scalar_mult_row identity_matrix s r) r).
    + exact (identity_matrix r).
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

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (identity_matrix r2).
    - induction (stn_eq_or_neq i r2).
      + exact (identity_matrix r1).
      + exact (identity_matrix i).
  Defined.



  (*  This might be a non-trivial property to prove, especially in the current double induction-based formalization.*)
  Definition test_row_switch_statement {m n : nat} (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
  Proof.
    use funextfun; intros i.
    use funextfun; intros j.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq i r1) as [ e_ir1 | ne_ir1 ]; simpl.
    - destruct (stn_eq_or_neq r2 r1) as [ e_r1r2 | ne_r1r2 ]; simpl.
      + destruct e_ir1, e_r1r2. apply idpath.
      + destruct (stn_eq_or_neq r2 r2) as [ ? | absurd ]; simpl.
        * destruct e_ir1. apply idpath.
        * set (H := isirrefl_natneq _ absurd). destruct H.
  Abort.

  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)

  Lemma matrix_scalar_mult_is_elementary_row_op {n : nat} (mat : Matrix F n n) (s : F) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    intros.
  Abort.

  (* Order of arguments should be standardized... *)
  Lemma matrix_row_mult_is_elementary_row_op {n : nat} (r1 r2 : ⟦ n ⟧%stn) (mat : Matrix F n n) (s : F) :
    ((make_add_row_matrix r1 r2 s) ** mat) = gauss_add_row mat s r1 r2.
  Proof.
    intros.
  Abort.

  Lemma matrix_switch_row_is_elementary_row_op {n : nat} (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) :
    gauss_switch_row mat r1 r2 = ((make_gauss_switch_row_matrix n r1 r2) ** mat).
  Proof.
    intros.
  Abort.



  (* The following three lemmata test the correctness of elementary row operations, i.e. they do not affect the solution set. *)

  Lemma eq_sol_invar_under_scalar_mult {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_scalar_mult_row_matrix s r) ** A ** x)  = ((make_scalar_mult_row_matrix s r) ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_add {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_add_row_matrix r1 r2 s) ** A ** x)  = ((make_add_row_matrix r1 r2 s)  ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_switch {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_gauss_switch_row_matrix n r1 r2) ** A ** x)  = ((make_gauss_switch_row_matrix n r1 r2) ** (transpose b)).
  Proof.
    intros.
  Abort.


  (* The following definitions set up helper functions on finite sets which are then used in formalizing Gaussian Elimination*)

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
    + exact (λ i : (⟦ n - 1 ⟧%stn), 0%hq). (* ? *)
  Defined.


  (* We can generalize this to just ordered sets *)
  Definition max_hq_index { n : nat } (ei ei' : hq × ⟦ n ⟧%stn) : hq × ⟦ n ⟧%stn.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact ei.
    - exact ei'.
  Defined.

  Definition max_hq_index_one_arg { n : nat } (ei : hq × ⟦ n ⟧%stn) : (hq × ⟦ n ⟧%stn) -> (hq × ⟦ n ⟧%stn)
    := max_hq_index ei.

  (* Some of the following lemmata are very specific and could be better without the general definition form, or we
     could write these as local definitions *)
  Definition max_argmax_stnhq {n : nat} (vec : Vector F n) (pn : n > 0) : hq × (⟦ n ⟧)%stn.
  Proof.
    set (max_and_idx := (foldleft (0%hq,,(0%nat,,pn)) max_hq_index (λ i : (⟦ n ⟧%stn), (vec i) ,, i))).
    exact (max_and_idx).
  Defined.

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

  Lemma stn_implies_nneq0 { n : nat } (i : ⟦ n ⟧%stn) : n ≠ 0.
  Proof.
    induction (natchoice0 n) as [T | F].
    - rewrite <- T in i.
      apply weqstn0toempty in i. apply fromempty. assumption.
    - change (0 < n) with (n > 0) in F.
      destruct n.
      + apply isirreflnatgth in F. apply fromempty. assumption.
      + apply natgthtoneq in F. reflexivity.
  Defined.

  Lemma stn_implies_ngt0 { n : nat} (i : ⟦ n ⟧%stn) : n > 0.
  Proof.
    exact (natneq0to0lth n (stn_implies_nneq0 i)).
  Defined.



  (* Stepwise Gaussian Elimination definitions *)

  (* We can probably assert at this point that m and n are > 0, as the base cases can be handled by caller *)
  (* Performed k times . *)
  (* We should be able to assert n, m > 0 wherever needed, by raa.*)
  Definition gauss_step  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n × ⟦ n ⟧%stn.
  Proof.
    assert (pn : (n > 0)). { exact (stn_implies_ngt0 k). }
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

  (* ( i,, i < n) to (i-1,, i-1 < n *)
  Definition decrement_stn { n : nat } ( i : (⟦ n ⟧)%stn ) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgtb (pr1 i) 0).
    (*- assert ( p : ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }*)
    - assert ( p :  ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }
      exact ((pr1 i) - 1,, p).
    - exact i.
  Defined.

  Definition decrement_stn_by_m { n : nat } ( i : (⟦ n ⟧)%stn ) (m : nat) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgehchoice m 0).
    - assert ( p :  ((pr1 i) - m) < n).
        {  unfold stn in i. set (p0 := pr2 i). assert (pr1 i < n).
           - exact (pr2 i).
           - assert ((pr1 i - m <= ( pr1 i))). {apply (natminuslehn ). }
              apply (natlehlthtrans (pr1 i - m) (pr1 i) ).
              + assumption.
              + assumption.
        }
      exact (pr1 i - m,, p).
    - exact i.
    - reflexivity.
  Defined.

  Local Definition mltntommin1ltn { n m : nat } (p : m < n) : (m - 1 < n).
  Proof.
    apply natlthtolthm1. assumption.
  Defined.

  Definition switch_vector_els { n : nat } (vec : Vector F n) (e1 e2 : ⟦ n ⟧%stn) : Vector F n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i e1).
    - exact (vec e2).
    - induction (stn_eq_or_neq i e2).
      + exact (vec e1).
      + exact (vec i).
  Defined.

  (* k  : 1 -> n - 1 *)
  Definition vec_row_ops_step { n : nat } (k pivot_ik: ⟦ n ⟧%stn)  (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    induction (natlthorgeh i k). 2 : {exact (vec i). }
    set (vec' := switch_vector_els vec pivot_ik k).
    assert (pr2stn1 : 0 < 1). { reflexivity. }
    set ( j := make_stn 1 0 pr2stn1).
    exact (  ((((vec' i)) + ((vec' k)) * (mat i k))%hq)).  (* Would like to verify this construction works*)
  Defined.

  (* Not really a clamp but setting every element at low indices to zero.  *)
  Local Definition clamp_f {n : nat} (f : ⟦ n ⟧%stn -> hq) (cutoff : ⟦ n ⟧%stn) : (⟦ n ⟧%stn -> hq).
    intros i.
    induction (natlthorgeh i cutoff) as [LT | GTH].
    - exact 0%hq.
    - exact (f i).
  Defined.

  (* This one especially needs to be checked for correctness (use of indices) *)
  Definition back_sub_step { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    induction (natlehchoice ((S (pr1 iter)) ) (n)) as [LT | GTH].
    - exact ((((vec i) - Σ (clamp_f vec i)) * (hqmultinv (mat i i)))%hq).
    - exact ((vec i) * (hqmultinv (mat i i)))%hq.
    - unfold stn in i.
      apply (pr2 iter).
  Defined.

  Definition zero_vector_hq (n : nat) : ⟦ n ⟧%stn -> hq :=
    λ i : ⟦ n ⟧%stn, 0%hq.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  (* This is not really a zero vector, it might be [0 1 2 3] ... Serves the purpose of a placeholder however. *)
  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros i.
    assumption.
  Defined.

  Definition set_stn_vector_el { n : nat } (vec : Vector (⟦ n ⟧%stn) n) (idx : ⟦ n ⟧%stn) (el : (⟦ n ⟧%stn)) : Vector (⟦ n ⟧%stn) n.
  Proof.
  intros i.
  induction (stn_eq_or_neq i idx).
  + exact el.
  + exact (vec i).
  Defined.


  (* Now, three fixpoint definitions for three subroutines.
     Partial pivoting on "A", defining b according to pivots on A,
     then back-substitution. *)
  Fixpoint gauss_iterate ( pr1i : nat ) { n : nat } ( current_idx : ⟦ n ⟧%stn) (start_idx : ⟦ n ⟧%stn ) (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n) {struct pr1i }: (Matrix F n n) × (Vector (⟦ n ⟧%stn) n) :=

  let current_idx := decrement_stn_by_m start_idx (n - pr1i)  in
  let idx_nat := pr1 current_idx in
  let proof   := pr2 current_idx in
  match pr1i with
  | 0 => mat,, pivots
  | S m =>
            let mat_vec_tup := ((gauss_step current_idx mat)) in
            let mat' := pr1 mat_vec_tup in
            let piv  := (pr2 mat_vec_tup) in
            let pivots' := set_stn_vector_el pivots current_idx piv in
            gauss_iterate m current_idx start_idx mat' pivots'
  end.

Fixpoint vec_ops_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
  let current_idx := decrement_stn_by_m start_idx (n - iter)  in
  match iter with
  | 0 => b
  | S m => vec_ops_iterate m start_idx (vec_row_ops_step current_idx (pivots current_idx) mat b) pivots mat
  end.


Fixpoint back_sub_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
  let current_idx := decrement_stn_by_m start_idx (n - iter)  in
  match iter with
  | 0 => b
  | S m => back_sub_iterate m start_idx ( back_sub_step current_idx mat b) pivots mat
  end.


  (* The main definition using above Fixpoints, which in turn use stepwise definitions.*)
  Definition gaussian_elimination { n : nat } (mat : Matrix F n n) (b : Vector F n) (pn : n > 0) : Matrix F n n × Vector F n.
  Proof.
    set (A_and_pivots := gauss_iterate n (0,,pn) (0,,pn) mat (zero_vector_stn n)).
    set (A  := pr1 A_and_pivots).
    set (pv := pr2 A_and_pivots).
    set (b'  := vec_ops_iterate 0 (0,,pn) b pv A).
    set (b'' := back_sub_iterate n (0,, pn) b' pv A).
    exact (A,, b').
  Defined.



  (* Some properties on the above procedure which we would like to prove. *)

  Definition is_upper_triangular { m n : nat } (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < j -> mat i j = 0%hq.

  Definition is_upper_triangular_to_k { m n : nat} ( k : nat ) (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < k -> i < j -> mat i j = 0%hq.


  Lemma gauss_step_clears_row  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    is_upper_triangular_to_k (pr1 k) (pr1 (gauss_step k mat)).
  Proof.
    intros.
  Abort.

  Lemma A_is_upper_triangular { n : nat} ( temp_proof_0_lt_n : 0 < n ) (mat : Matrix F n n) :
    is_upper_triangular (pr1 (gauss_iterate 0 (0,, temp_proof_0_lt_n) (0,, temp_proof_0_lt_n) mat (zero_vector_stn n))).
  Proof.
    intros.
  Abort.


  (* Reliance on pn, coercing matrices could be done away with. *)
  Lemma sol_is_invariant_under_gauss  {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n)  (pn : n > 0) (pn' : 1 > 0) :
    (A ** x) = (transpose b) -> ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** A ** x)  = ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** (transpose b)).
  Proof.
    intros.
  Abort.





  (* Determinants, minors, minor expansions ... *)

  (* TODO : Verify this is close to accurate ... *)
  Definition make_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix F (S n) (S n)) : Matrix F n n.
  Proof.
    intros i' j'.
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
  Definition determinant_step { n : nat} (mat : Matrix F (S n) (S n)) : (Matrix F n n) × F.
  Proof.
    set (exp_row := 0).
    use tpair.
    - (* Minors *)
      intros i j.
      (* Carefully do induction on S n, not n. *)
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
(*
          assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                    - apply natlthnsn.
                                    - apply (istransnatgth n 1 0).
                                      + apply
G.
                                      + reflexivity.
                                   }
*)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].
          * exact 1%hq.
          * assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                       - apply natlthnsn.
                                       - apply (istransnatgth n 1 0).
                                         + apply G.
                                         + reflexivity.
                                     }
            assert (x' : 1 < (S n)). {apply (istransnatgth (S n) n 1).
                                       - apply natlthnsn.
                                       - apply G. }
            assert (pexp : exp_row < S n). { reflexivity. }
            assert (psj : (pr1 j) < S n). {  apply natlthtolths. exact (pr2 j). }.
            set (stn_0 := make_stn (S n) 0 x ).
            set (stn_1 := make_stn (S n) 1 x').
            set (cof := 1%hq). (* TODO : this is a dummy for (-1)^(i + j) *)
            exact (Σ (λ j : (⟦ S n ⟧%stn), cof * (mat (exp_row,, pexp) (j)))%hq).
    - (* Scalar terms *)
      intros i j.
      set (exp_row := 0).
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].

    induction (natgtb n 1) as [T | F].
    - induction (nat_eq_or_neq n 2) as [T' | F'].
      assert (x :  0 < (S n)). {rewrite T'. reflexivity.}.
      assert (x' : 1 < (S n)). {rewrite T'. reflexivity.}.
      set (stn_0 := make_stn (S n) 0 x).
      set (stn_1 := make_stn (S n) 1 x').
      + exact (1%hq,, (mat stn_0 stn_0) * (mat stn_1 stn_1) - (mat stn_0 stn_1) * (mat stn_1 stn_0))%hq).
      + set (cof := 1). (* TODO : this is a dummy for (-1)^(i + j) *)
        exact (Σ (λ j : (⟦ n ⟧%stn), cof * mat ( exp_row j) (determinant ( make_minor i j mat)))).  (* TODO *)
    - induction (nat_eq_or_neq n 0).
      + exact 0%hq.
      + assert (x :  0 < n). {apply natneq0togth0. assumption.}
        set (stn_0 := make_stn n 0 x).
        exact (mat stn_0 stn_0).
  Defined.
  *)

  (*How do we produce either a smaller matrix or scalar value? *)
  (*
  Fixpoint determinant_iter {n : nat} (mat : Matrix F (S n) (S n)) := Matrix F n n.
  *)


End Gauss.





Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.

  (* Such code might go intro Matrix.v *)
  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i != (stntonat _ j)) -> (mat i j) = 0%rig.


  Definition nat_lt_minmn_to_stnm_stnn {m n : nat} (i : nat) (p : i < min m n) : ⟦ m ⟧%stn × ⟦ n ⟧%stn.
  Proof.
   (* unfold min in p. *)
    assert (i < n).
    (* cbn in p. *)
    induction (natgehchoice m n) as [MGT | NGE].
  Abort.

  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.


End SmithNF.
