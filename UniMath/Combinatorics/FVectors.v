(** * Finite sequences

Vectors defined in March 2018 by Langston Barrett (@siddharthist).
 *)

(** ** Contents

  Vectors

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

(** ** Vectors *)

(** A [Vector] of length n with values in X is an ordered n-tuple of elements of X,
    encoded here as a function ⟦n⟧ → X. *)
Definition Vector (X : UU) (n : nat) : UU := stn n -> X.

(** hlevel of vectors *)
Lemma vector_hlevel (X : UU) (n : nat) {m : nat} (ism : isofhlevel m X) :
  isofhlevel m (Vector X n).
Proof.
  apply impred; auto.
Defined.

(** Constant vector *)
Definition const_vec {X : UU} {n : nat} (x : X) : Vector X n := λ _, x.

(** The unique empty vector *)
Definition iscontr_vector_0 X : iscontr (Vector X 0).
Proof.
  intros. apply (@iscontrweqb _ (empty -> X)).
  - apply invweq. apply weqbfun. apply weqstn0toempty.
  - apply iscontrfunfromempty.
Defined.

Definition empty_vec {X : UU} : Vector X 0 := iscontrpr1 (iscontr_vector_0 X).

(** Every type is equivalent to vectors of length 1 on that type. *)
Lemma weq_vector_1 {X : UU} : X ≃ Vector X 1.
  intermediate_weq (unit → X).
  - apply invweq, weqfunfromunit.
  - apply weqbfun.
    exact weqstn1tounit.
Defined.

Section Append.

  Context {X : UU} {n : nat} (vec : Vector X n) (x : X).

  Definition append_vec : Vector X (S n).
  Proof.
    intros i.
    induction (natlehchoice4 (pr1 i) n (pr2 i)) as [c|d].
    - exact (vec (pr1 i,,c)).
    - exact x.
  Defined.

  Definition append_vec_compute_1 i : append_vec (dni lastelement i) = vec i.
  Proof.
    intros.
    induction i as [i b]; simpl.
    rewrite replace_dni_last.
    unfold append_vec; simpl.
    induction (natlehchoice4 i n (natlthtolths i n b)) as [p|p].
    - simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
    - simpl. destruct p. induction (isirreflnatlth i b).
  Defined.

  Definition append_vec_compute_2 : append_vec lastelement = x.
  Proof.
    intros; unfold append_vec; simpl.
    induction (natlehchoice4 n n (natgthsnn n)) as [a|a]; simpl.
    - contradicts a (isirreflnatlth n).
    - reflexivity.
  Defined.

End Append.

Lemma drop_and_append_vec {X n} (x : Vector X (S n)) :
  append_vec (x ∘ dni_lastelement) (x lastelement) = x.
Proof.
  intros.
  apply funextfun; intros [i b].
  simpl.
  induction (natlehchoice4 i n b) as [p|p].
  - simpl.
    unfold append_vec. simpl.
    induction (natlehchoice4 i n b) as [q|q].
    + simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
    + induction q. contradicts p (isirreflnatlth i).
  - induction p.
    unfold append_vec; simpl.
    induction (natlehchoice4 i i b) as [r|r].
    * simpl. apply maponpaths.
      apply isinjstntonat; simpl. reflexivity.
    * simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
Defined.

(** An induction principle for vectors: If a statement is true for the empty
    vector, and if it is true for vectors of length n it is also true for those
    of length S n, then it is true for all vectors.
 *)
Definition Vector_rect {X : UU} {P : ∏ n, Vector X n -> UU}
           (p0 : P 0 empty_vec)
           (ind : ∏ (n : nat) (vec : Vector X n) (x : X),
                  P n vec -> P (S n) (append_vec vec x))
           {n : nat} (vec : Vector X n) : P n vec.
Proof.
  intros.
  induction n as [|n IH].
  - refine (transportf (P 0) _ p0).
    apply proofirrelevancecontr, iscontr_vector_0.
  - exact (transportf (P _) (drop_and_append_vec vec)
                      (ind _ (vec ∘ dni_lastelement)
                             (vec lastelement)
                             (IH (vec ∘ dni_lastelement)))).
Defined.

Section Lemmas.

  Context {X : UU} {n : nat}.

  Definition vectorEquality {m : nat} (f : Vector X n) (g : Vector X m) (p : n = m) :
    (∏ i, f i = g (transportf stn p i))
    -> transportf (Vector X) p f = g.
  Proof.
    intro.
    induction p.
    apply funextfun.
    assumption.
  Defined.

  Definition tail (vecsn : Vector X (S n)) : Vector X n :=
    vecsn ∘ dni (0,, natgthsn0 n).

  (** It doesn't matter what the proofs are in the stn inputs. *)
  Definition vector_stn_proofirrelevance {vec : Vector X n}
            {i j : stn n} : (stntonat _ i = stntonat _ j) -> vec i = vec j.
  Proof.
    intro.
    apply maponpaths, isinjstntonat; assumption.
  Defined.
End Lemmas.
