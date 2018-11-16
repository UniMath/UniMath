(** * Finite sequences

Vectors and matrices defined in March 2018 by Langston Barrett (@siddharthist).
 *)

(** ** Contents

  - Vectors
  - Matrices
  - Sequences
    - Definitions
    - Lemmas

 *)

Require Export UniMath.Combinatorics.FiniteSets.
Require Export UniMath.Combinatorics.Lists.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Unset Automatic Introduction.

Local Open Scope transport.

(** ** Vectors *)

(** A [Vector] of length n with values in X is an ordered n-tuple of elements of X,
    encoded here as a function ⟦n⟧ → X. *)
Definition Vector (X : UU) (n : nat) : UU := stn n -> X.

(** hlevel of vectors *)
Lemma vector_hlevel (X : UU) (n : nat) {m : nat} (ism : isofhlevel m X) :
  isofhlevel m (Vector X n).
Proof.
  intros ? ? ? ?; apply impred; auto.
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
  intros X.
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
  - unfold funcomp; simpl.
    unfold append_vec. simpl.
    induction (natlehchoice4 i n b) as [q|q].
    + simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
    + induction q. contradicts p (isirreflnatlth i).
  - induction p.
    unfold append_vec; simpl.
    induction (natlehchoice4 i i b) as [r|r].
    * simpl. unfold funcomp; simpl. apply maponpaths.
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
    apply proofirrelevance, isapropifcontr, iscontr_vector_0.
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
    intros ? ? ? p ?.
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
    intros ? ? ? ?.
    apply maponpaths, isinjstntonat; assumption.
  Defined.
End Lemmas.

(** ** Matrices *)

Open Scope stn.

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
  intros ? ? ? ? ?; do 2 apply vector_hlevel; assumption.
Defined.

(** Constant matrix *)
Definition const_matrix {X : UU} {n m : nat} (x : X) : Matrix X n m :=
  const_vec (const_vec x).

(** Every type is equivalent to 1 × 1 matrices on that type. *)
Lemma weq_matrix_1_1 {X : UU} : X ≃ Matrix X 1 1.
  intros X; intermediate_weq (Vector X 1); apply weq_vector_1.
Defined.

(** ** Sequences *)

(** *** Definitions *)

(** A [Sequence] is a [Vector] of any length. *)
Definition Sequence (X : UU) := ∑ n, Vector X n.

Definition NonemptySequence (X:UU) := ∑ n, stn (S n) -> X.

Definition UnorderedSequence (X:UU) := ∑ I:FiniteSet, I -> X.

Definition length {X} : Sequence X -> nat := pr1.

Definition sequenceToFunction {X} (x:Sequence X) := pr2 x : stn (length x) -> X.

Coercion sequenceToFunction : Sequence >-> Funclass.

Definition unorderedSequenceToFunction {X} (x:UnorderedSequence X) := pr2 x : pr1 (pr1 x) -> X.

Coercion unorderedSequenceToFunction : UnorderedSequence >-> Funclass.

Definition sequenceToUnorderedSequence {X} : Sequence X -> UnorderedSequence X.
Proof.
  intros X x.
  exists (standardFiniteSet (length x)).
  exact x.
Defined.

Coercion sequenceToUnorderedSequence : Sequence >-> UnorderedSequence.

Definition length'{X} : NonemptySequence X -> nat := λ x, S(pr1 x).

Definition functionToSequence {X n} (f:stn n -> X) : Sequence X
  := (n,,f).

Definition functionToUnorderedSequence {X} {I : FiniteSet} (f:I -> X) : UnorderedSequence X := (I,,f).

Definition NonemptySequenceToFunction {X} (x:NonemptySequence X) := pr2 x : stn (length' x) -> X.

Coercion NonemptySequenceToFunction : NonemptySequence >-> Funclass.

Definition NonemptySequenceToSequence {X} (x:NonemptySequence X) := functionToSequence (NonemptySequenceToFunction x) : Sequence X.

Coercion NonemptySequenceToSequence : NonemptySequence >-> Sequence.

(** *** Lemmas *)

Definition composeSequence {X Y} (f:X->Y) : Sequence X -> Sequence Y := λ x, functionToSequence (f ∘ x).

Definition composeSequence' {X m n} (f:stn n -> X) (g:stn m -> stn n) : Sequence X
  := functionToSequence (f ∘ g).

Definition composeUnorderedSequence {X Y} (f:X->Y) : UnorderedSequence X -> UnorderedSequence Y
  := λ x, functionToUnorderedSequence(f ∘ x).

Definition weqListSequence {X} : list X ≃ Sequence X.
Proof.
  intros.
  apply weqfibtototal; intro n.
  apply weqlistfun.
Defined.

Definition transport_stn m n i (b:i<m) (p:m=n) :
  transportf stn p (i,,b) = (i,,transportf (λ m,i<m) p b).
Proof. intros. induction p. reflexivity. Defined.

Definition sequenceEquality2 {X} (f g:Sequence X) (p:length f=length g) :
  (∏ i, f i = g (transportf stn p i)) -> f = g.
Proof.
  intros ? ? ? ? e. induction f as [m f]. induction g as [n g]. simpl in p.
  apply (total2_paths2_f p). now apply vectorEquality.
Defined.

(** The following two lemmas are the key lemmas that allow to prove (transportational) equality of
 sequences whose lengths are not definitionally equal. In particular, these lemmas can be used in
the proofs of such results as associativity of concatenation of sequences and the right unity
axiom for the empty sequence. **)

Definition seq_key_eq_lemma {X :UU}( g g' : Sequence X)(e_len : length g = length g')
           (e_el : forall ( i : nat )(ltg : i < length g )(ltg' : i < length g' ),
               g (i ,, ltg) = g' (i ,, ltg')) : g=g'.
Proof.
  intros.
  induction g as [m g]; induction g' as [m' g']. simpl in e_len, e_el.
  intermediate_path (m' ,, transportf (λ i, stn i -> X) e_len g).
  - apply transportf_eq.
  - apply maponpaths.
    intermediate_path (g ∘ transportb stn e_len).
    + apply transportf_fun.
    + apply funextfun. intro x. induction x as [ i b ].
      simple refine (_ @ e_el _ _ _).
      * unfold funcomp.
        apply maponpaths.
        apply transport_stn.
Defined.

(** The following lemma requires in the assumption [ e_el ] only one comparison [ i < length g ]
 and one comparison [ i < length g' ] for each i instead of all such comparisons as in the
 original version [ seq_key_eq_lemma ] . **)

Definition seq_key_eq_lemma' {X :UU} (g g' : Sequence X) :
  length g = length g' ->
  (∏ i, ∑ ltg : i < length g, ∑ ltg' : i < length g',
                                        g (i ,, ltg) = g' (i ,, ltg')) ->
  g=g'.
Proof.
  intros ? ? ? k r.
  apply seq_key_eq_lemma.
  * assumption.
  * intros.
    induction (r i) as [ p [ q e ]].
    simple refine (_ @ e @ _).
    - now apply maponpaths, isinjstntonat.
    - now apply maponpaths, isinjstntonat.
Defined.

Notation fromstn0 := empty_vec.

Definition nil {X} : Sequence X.
Proof. intros. exact (0,, empty_vec). Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof. intros ? x y. exact (S (length x),, append_vec (pr2 x) y).
Defined.

Definition drop_and_append {X n} (x : stn (S n) -> X) :
  append (n,,x ∘ dni_lastelement) (x lastelement) = (S n,, x).
Proof.
  intros. apply pair_path_in2. apply drop_and_append_vec.
Defined.

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Definition nil_unique {X} (x : stn 0 -> X) : nil = (0,,x).
Proof.
  intros. unfold nil. apply maponpaths. apply isapropifcontr. apply iscontr_vector_0.
Defined.

Definition isaset_transportf {X : hSet} (P : X ->UU) {x : X} (e : x = x) (p : P x) :
  transportf P e p = p.
(* move upstream *)
Proof. intros ? ? ? ? ?.
       induction (pr1 ((setproperty _) _ _ (idpath _) e)).
       reflexivity.
Defined.

(* induction principle for contractible types, as a warmup *)

(* Three ways.  Use induction: *)

Definition iscontr_rect' X (i : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : ∏ x:X, P x.
Proof. intros. induction (pr1 (isapropifcontr i x0 x)). exact p0. Defined.

Definition iscontr_rect_compute' X (i : iscontr X) (x : X) (P : X ->UU) (p : P x) :
  iscontr_rect' X i x P p x = p.
Proof.
  intros.
  (* this step might be a problem in more complicated situations: *)
  unfold iscontr_rect'.
  induction (pr1 (isasetifcontr i x x (idpath _) (pr1 (isapropifcontr i x x)))).
  reflexivity.
Defined.

(* ... or use weqsecovercontr, but specializing x to pr1 i: *)

Definition iscontr_rect'' X (i : iscontr X) (P : X ->UU) (p0 : P (pr1 i)) : ∏ x:X, P x.
Proof. intros. exact (invmap (weqsecovercontr P i) p0 x). Defined.

Definition iscontr_rect_compute'' X (i : iscontr X) (P : X ->UU) (p : P(pr1 i)) :
  iscontr_rect'' X i P p (pr1 i) = p.
Proof. try reflexivity. intros. exact (homotweqinvweq (weqsecovercontr P i) p).
Defined.

(* .... or use transport explicitly: *)

Definition iscontr_adjointness X (is:iscontr X) (x:X) : pr1 (isapropifcontr is x x) = idpath x.
(* we call this adjointness, because if [unit] had η-reduction, then adjointness of
   the weq [unit ≃ X] would give it to us, in the case where x is [pr1 is] *)
Proof. intros. now apply isasetifcontr. Defined.

Definition iscontr_rect X (is : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : ∏ x:X, P x.
Proof. intros. exact (transportf P (pr1 (isapropifcontr is x0 x)) p0). Defined.

Definition iscontr_rect_compute X (is : iscontr X) (x : X) (P : X ->UU) (p : P x) :
  iscontr_rect X is x P p x = p.
Proof. intros. unfold iscontr_rect. now rewrite iscontr_adjointness. Defined.

Corollary weqsecovercontr':     (* reprove weqsecovercontr, move upstream *)
  ∏ (X:UU) (P:X->UU) (is:iscontr X), (∏ x:X, P x) ≃ P (pr1 is).
Proof.
  intros.
  set (x0 := pr1 is).
  set (secs := ∏ x : X, P x).
  set (fib  := P x0).
  set (destr := (λ f, f x0) : secs->fib).
  set (constr:= iscontr_rect X is x0 P : fib->secs).
  exists destr.
  apply (isweq_iso destr constr).
  - intros f. apply funextsec; intros x.
    unfold destr, constr.
    apply transport_section.
  - apply iscontr_rect_compute.
Defined.

(*  *)

Definition nil_length {X} (x : Sequence X) : length x = 0 <-> x = nil.
Proof.
  intros. split.
  - intro e. induction x as [n x]. simpl in e.
    induction (!e). apply pathsinv0. apply nil_unique.
  - intro h. induction (!h). reflexivity.
Defined.

Definition drop {X} (x:Sequence X) : length x != 0 -> Sequence X.
Proof.
  intros ? [n x] h.
  induction n as [|n].
  - simpl in h. contradicts h (idpath 0).
  - exact (n,,x ∘ dni_lastelement).
Defined.

Definition drop' {X} (x:Sequence X) : x != nil -> Sequence X.
Proof. intros ? ? h. exact (drop x (pr2 (logeqnegs (nil_length x)) h)). Defined.

Lemma append_and_drop_fun {X n} (x : stn n -> X) y :
  append_vec x y ∘ dni lastelement = x.
Proof.
  intros.
  apply funextsec; intros i.
  unfold funcomp.
  unfold append_vec.
  induction (natlehchoice4 (pr1 (dni lastelement i)) n (pr2 (dni lastelement i))) as [I|J].
  - simpl. apply maponpaths. apply subtypeEquality_prop. simpl. apply di_eq1. exact (stnlt i).
  - apply fromempty. simpl in J.
    assert (P : di n i = i).
    { apply di_eq1. exact (stnlt i). }
    induction (!P); clear P.
    induction i as [i r]. simpl in J. induction J.
    exact (isirreflnatlth _ r).
Defined.

Definition drop_and_append' {X n} (x : stn (S n) -> X) :
  append (drop (S n,,x) (negpathssx0 _)) (x lastelement) = (S n,, x).
Proof.
  intros. simpl. apply pair_path_in2. apply drop_and_append_vec.
Defined.

Definition disassembleSequence {X} : Sequence X -> coprod unit (X × Sequence X).
Proof.
  intros ? x.
  induction x as [n x].
  induction n as [|n].
  - exact (ii1 tt).
  - exact (ii2(x lastelement,,(n,,x ∘ dni_lastelement))).
Defined.

Definition assembleSequence {X} : coprod unit (X × Sequence X) -> Sequence X.
Proof.
  intros ? co.
  induction co as [t|p].
  - exact nil.
  - exact (append (pr2 p) (pr1 p)).
Defined.

Lemma assembleSequence_ii2 {X} (p : X × Sequence X) :
  assembleSequence (ii2 p) = append (pr2 p) (pr1 p).
Proof. reflexivity. Defined.

Theorem SequenceAssembly {X} : Sequence X ≃ unit ⨿ (X × Sequence X).
Proof.
  intros. exists disassembleSequence. apply (isweq_iso _ assembleSequence).
  { intros. induction x as [n x]. induction n as [|n].
    { apply nil_unique. }
    apply drop_and_append'. }
  intros co. induction co as [t|p].
  { unfold disassembleSequence; simpl. apply maponpaths.
    apply proofirrelevancecontr. apply iscontrunit. }
  induction p as [x y]. induction y as [n y].
  apply (maponpaths (@inr unit (X × Sequence X))).
  unfold append_vec, lastelement, funcomp; simpl.
  unfold append_vec. simpl.
  induction (natlehchoice4 n n (natgthsnn n)) as [e|e].
  { contradicts e (isirreflnatlth n). }
  simpl. apply maponpaths, maponpaths.
  apply funextfun; intro i. clear e. induction i as [i b].
  unfold funcomp, dni_lastelement; simpl.
  induction (natlehchoice4 i n (natlthtolths i n b)) as [d|d].
  { simpl. apply maponpaths. now apply isinjstntonat. }
  simpl. induction d; contradicts b (isirreflnatlth i).
Defined.


Definition Sequence_rect {X} {P : Sequence X ->UU}
           (p0 : P nil)
           (ind : ∏ (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof. intros. induction x as [n x]. induction n as [|n IH].
  - exact (transportf P (nil_unique x) p0).
  - exact (transportf P (drop_and_append x)
                      (ind (n,,x ∘ dni_lastelement)
                           (x lastelement)
                           (IH (x ∘ dni_lastelement)))).
Defined.

Lemma Sequence_rect_compute_nil {X} {P : Sequence X ->UU} (p0 : P nil)
      (ind : ∏ (s : Sequence X) (x : X), P s -> P (append s x)) :
  Sequence_rect p0 ind nil = p0.
Proof.
  intros.
  try reflexivity.
  unfold Sequence_rect; simpl.
  change p0 with (transportf P (idpath nil) p0) at 2.
  apply (maponpaths (λ e, transportf P e p0)).
  exact (maponpaths (maponpaths functionToSequence) (iscontr_adjointness _ _ _)).
Defined.

Lemma Sequence_rect_compute_cons
      {X} {P : Sequence X ->UU} (p0 : P nil)
      (ind : ∏ (s : Sequence X) (x : X), P s -> P (append s x))
      (p := Sequence_rect p0 ind) (x:X) (l:Sequence X) :
  p (append l x) = ind l x (p l).
Proof.
  intros.
  cbn.
  (* proof needed to complete induction for sequences *)
Abort.

Lemma append_length {X} (x:Sequence X) (y:X) :
  length (append x y) = S (length x).
Proof. intros. reflexivity. Defined.

Definition concatenate {X : UU} : binop (Sequence X)
  := λ x y, functionToSequence (concatenate' x y).

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof. intros. reflexivity. Defined.

Definition concatenate_0 {X} (s t:Sequence X) : length t = 0 -> concatenate s t = s.
Proof.
  induction s as [m s]. induction t as [n t].
  intro e; simpl in e. induction (!e).
  simple refine (sequenceEquality2 _ _ _ _).
  - simpl. apply natplusr0.
  - intro i; simpl in i. simpl.
    unfold concatenate'.
    rewrite weqfromcoprodofstn_invmap_r0.
    simpl.
    reflexivity.
Defined.

Definition concatenateStep {X : UU} (x : Sequence X) {n : nat} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ dni lastelement)) (y lastelement).
Proof.
  intros X m. induction m as [m l]. intros n y.
  use seq_key_eq_lemma.
  - cbn. apply natplusnsm.
  - intros i r s.
    unfold concatenate, concatenate', weqfromcoprodofstn_invmap; cbn.
    unfold append_vec, coprod_rect, funcomp; cbn.
    induction (natlthorgeh i m) as [H | H].
    + induction (natlehchoice4 i (m + n) s) as [H1 | H1].
      * reflexivity.
      * apply fromempty. induction (!H1); clear H1.
        set (tmp := natlehnplusnm m n).
        set (tmp2 := natlehlthtrans _ _ _ tmp H).
        exact (isirreflnatlth _ tmp2).
    + induction (natlehchoice4 i (m + n) s) as [I|J].
      * apply maponpaths, subtypeEquality_prop. rewrite replace_dni_last. reflexivity.
      * apply maponpaths, subtypeEquality_prop. simpl.
        induction (!J). rewrite natpluscomm. apply plusminusnmm.
Qed.

Definition flatten {X : UU} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? x. exists (stnsum (length ∘ x)). exact (flatten' (sequenceToFunction ∘ x)).
Defined.

Definition flattenUnorderedSequence {X : UU} : UnorderedSequence (UnorderedSequence X) -> UnorderedSequence X.
Proof.
  intros ? x.
  use tpair.
  - exact ((∑ i, pr1 (x i))%finset).
  - intros ij. exact (x (pr1 ij) (pr2 ij)). (* could also have used (uncurry (unorderedSequenceToFunction x)) here *)
Defined.

Definition flattenStep' {X n}
           (m : stn (S n) → nat)
           (x : ∏ i : stn (S n), stn (m i) → X)
           (m' := m ∘ dni lastelement)
           (x' := x ∘ dni lastelement) :
  flatten' x = concatenate' (flatten' x') (x lastelement).
Proof.
  intros.
  apply funextfun; intro i.
  unfold flatten'.
  unfold funcomp.
  rewrite 2 weqstnsum1_eq'.
  unfold StandardFiniteSets.weqstnsum_invmap at 1.
  unfold concatenate'.
  unfold nat_rect, coprod_rect, funcomp.
  change (weqfromcoprodofstn_invmap (stnsum (λ r : stn n, m (dni lastelement r))))
  with (weqfromcoprodofstn_invmap (stnsum m')) at 1 2.
  induction (weqfromcoprodofstn_invmap (stnsum m')) as [B|C].
  - reflexivity.
  - now induction C.            (* not needed with primitive projections *)
Defined.

Definition flattenStep {X} (x: NonemptySequence (Sequence X)) :
  flatten x = concatenate (flatten (composeSequence' x (dni lastelement))) (lastValue x).
Proof.
  intros.
  apply pair_path_in2.
  set (xlens := λ i, length(x i)).
  set (xvals := λ i, λ j:stn (xlens i), x i j).
  exact (flattenStep' xlens xvals).
Defined.

(* partitions *)

Definition partition' {X n} (f:stn n -> nat) (x:stn (stnsum f) -> X) : stn n -> Sequence X.
Proof. intros ? ? ? ? i. exists (f i). intro j. exact (x(inverse_lexicalEnumeration f (i,,j))).
Defined.

Definition partition {X n} (f:stn n -> nat) (x:stn (stnsum f) -> X) : Sequence (Sequence X).
Proof. intros. exists n. exact (partition' f x).
Defined.

Definition flatten_partition {X n} (f:stn n -> nat) (x:stn (stnsum f) -> X) :
  flatten (partition f x) ~ x.
Proof.
  intros. intro i.
  change (x (weqstnsum1 f (pr1 (invmap (weqstnsum1 f) i),, pr2 (invmap (weqstnsum1 f) i))) = x i).
  apply maponpaths. apply subtypeEquality_prop. now rewrite homotweqinvweq.
Defined.

(* associativity of "concatenate" *)

Definition isassoc_concatenate {X : UU} (x y z : Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros X x y z.
  use seq_key_eq_lemma.
  - cbn. apply natplusassoc.
  - intros i ltg ltg'. cbn. unfold concatenate'. unfold weqfromcoprodofstn_invmap. unfold coprod_rect. cbn.
    induction (natlthorgeh i (length x + length y)) as [H | H].
    + induction (natlthorgeh (stnpair (length x + length y) i H) (length x)) as [H1 | H1].
      * induction (natlthorgeh i (length x)) as [H2 | H2].
        -- apply maponpaths. apply isinjstntonat. apply idpath.
        -- apply fromempty. exact (natlthtonegnatgeh i (length x) H1 H2).
      * induction (natchoice0 (length y)) as [H2 | H2].
        -- apply fromempty. induction H2. induction (! (natplusr0 (length x))).
           apply (natlthtonegnatgeh i (length x) H H1).
        -- induction (natlthorgeh i (length x)) as [H3 | H3].
           ++ apply fromempty. apply (natlthtonegnatgeh i (length x) H3 H1).
           ++ induction (natchoice0 (length y + length z)) as [H4 | H4].
              ** apply fromempty. induction (! H4).
                 use (isirrefl_natneq (length y)).
                 use natlthtoneq.
                 use (natlehlthtrans (length y) (length y + length z) (length y) _ H2).
                 apply natlehnplusnm.
              ** cbn. induction (natlthorgeh (i - length x) (length y)) as [H5 | H5].
                 --- apply maponpaths. apply isinjstntonat. apply idpath.
                 --- apply fromempty.
                     use (natlthtonegnatgeh (i - (length x)) (length y)).
                     +++ set (tmp := natlthandminusl i (length x + length y) (length x) H
                                                     (natlthandplusm (length x) _ H2)).
                         rewrite (natpluscomm (length x) (length y)) in tmp.
                         rewrite plusminusnmm in tmp. exact tmp.
                     +++ exact H5.
    + induction (natchoice0 (length z)) as [H1 | H1].
      * apply fromempty. cbn in ltg. induction H1. rewrite natplusr0 in ltg.
        exact (natlthtonegnatgeh i (length x + length y) ltg H).
      * induction (natlthorgeh i (length x)) as [H2 | H2].
        -- apply fromempty.
           use (natlthtonegnatgeh i (length x) H2).
           use (istransnatgeh i (length x + length y) (length x) H).
           apply natgehplusnmn.
        -- induction (natchoice0 (length y + length z)) as [H3 | H3].
           ++ apply fromempty. cbn in ltg'. induction H3. rewrite natplusr0 in ltg'.
              exact (natlthtonegnatgeh i (length x) ltg' H2).
           ++ cbn. induction (natlthorgeh (i - length x) (length y)) as [H4 | H4].
              ** apply fromempty.
                 use (natlthtonegnatgeh i (length x + length y) _ H).
                 apply (natlthandplusr _ _ (length x)) in H4.
                 rewrite minusplusnmm in H4.
                 --- rewrite natpluscomm in H4. exact H4.
                 --- exact H2.
              ** apply maponpaths. apply isinjstntonat. cbn. apply (! (natminusminus _ _ _)).
Qed.

(** Reverse *)

Definition reverse {X : UU} (x : Sequence X) : Sequence X :=
  functionToSequence (fun i : (stn (length x)) => x (dualelement i)).

Lemma reversereverse {X : UU} (x : Sequence X) : reverse (reverse x) = x.
Proof.
  intros X x. induction x as [n x].
  apply pair_path_in2.
  apply funextfun; intro i.
  unfold reverse, dualelement, coprod_rect. cbn.
  induction (natchoice0 n) as [H | H].
  + apply fromempty. rewrite <- H in i. now apply negstn0.
  + cbn. apply maponpaths. apply isinjstntonat. apply minusminusmmn. apply natgthtogehm1. apply stnlt.
Qed.

Lemma reverse_index {X : UU} (x : Sequence X) (i : stn (length x)) :
  (reverse x) (dualelement i) = x i.
Proof.
  intros X x i. cbn. unfold dualelement, coprod_rect.
  set (e := natgthtogehm1 (length x) i (stnlt i)).
  induction (natchoice0 (length x)) as [H' | H'].
  - apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
  - apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
Qed.

Lemma reverse_index' {X : UU} (x : Sequence X) (i : stn (length x)) :
  (reverse x) i = x (dualelement i).
Proof.
  intros X x i. cbn. unfold dualelement, coprod_rect.
  induction (natchoice0 (length x)) as [H' | H'].
  - apply maponpaths. apply isinjstntonat. cbn. apply idpath.
  - apply maponpaths. apply isinjstntonat. cbn. apply idpath.
Qed.
