Require Export UniMath.Combinatorics.Lists.
Require Export UniMath.Combinatorics.FiniteSequences.
Require Export UniMath.Algebra.Monoids_and_Groups.
Require Export UniMath.Foundations.UnivalenceAxiom.
Unset Automatic Introduction.

(* move upstream *)

Local Arguments dni {_} _ _.

Local Arguments firstelement {_}. (* make non local *)

Local Arguments lastelement {_}. (* make non local *)

(* end of move upstream *)

Local Notation "[]" := Lists.nil (at level 0, format "[]").
Local Infix "::" := cons.

(** general associativity for binary operations on types *)

Section BinaryOperations.

  Context {X:UU} (unel:X) (op:binop X).

  (* we use an extra induction step in each of the following definitions so
     we don't end up with superfluous unel factors *)

  Definition iterop_list : list X -> X.
  Proof.
    intro k.
    simple refine (list_ind (λ _, X) _ _ k).
    - simpl. exact unel.
    - intros x m _.
      generalize x; clear x.
      simple refine (list_ind (λ _, X -> X) _ _ m).
      + simpl. intro x. exact x.
      + simpl. intros y _ z x. exact (op x (z y)).
  Defined.

  Definition iterop_fun {n} (x:stn n->X) : X.
  Proof.
    intros.
    induction n as [|n _].
    { exact unel. }
    { induction n as [|n I].
      { exact (x lastelement). }
      { exact (op (I (x ∘ dni lastelement)) (x lastelement)). }}
  Defined.

  Definition iterop_seq : Sequence X -> X.
  Proof.
    intros x.
    exact (iterop_fun x).
  Defined.

  (* now define products of products *)

  Definition iterop_list_list : list(list X) -> X.
  Proof.
    intros w.
    exact (iterop_list (map iterop_list w)).
  Defined.

  Definition iterop_fun_fun {n} {m:stn n -> nat} : (∏ i (j:stn (m i)), X) -> X.
  Proof.
    intros ? ? x.
    exact (iterop_fun (λ i, iterop_fun (x i))).
  Defined.

  Definition iterop_seq_seq : Sequence (Sequence X) -> X.
  Proof.
    intros x.
    exact (iterop_fun_fun (λ i j, x i j)).
  Defined.

  Definition isAssociative_list := ∏ (x:list (list X)), iterop_list (Lists.flatten x) = iterop_list_list x.

  Definition isAssociative_fun :=
    ∏ n (m:stn n -> nat) (x : ∏ i (j:stn (m i)), X), iterop_fun (StandardFiniteSets.flatten' x) = iterop_fun_fun x.

  Definition isAssociative_seq :=
    ∏ (x : Sequence (Sequence X)), iterop_seq (FiniteSequences.flatten x) = iterop_seq_seq x.

  Lemma assoc_fun_to_seq : isAssociative_fun -> isAssociative_seq.
  Proof.
    intros assoc x.
    exact (assoc _ _ (λ i j, x i j)).
  Defined.

  Lemma assoc_seq_to_fun : isAssociative_seq -> isAssociative_fun.
  Proof.
    intros assoc n m x.
    exact (assoc (functionToSequence (λ i, functionToSequence (x i)))).
  Defined.

  Definition iterop_list_step (runax : isrunit op unel) (x:X) (xs:list X) :
    iterop_list (x::xs) = op x (iterop_list xs).
  Proof.
    intros runax x xs.
    generalize x; clear x.
    apply (list_ind (λ xs, ∏ x : X, iterop_list (x :: xs) = op x (iterop_list xs))).
    { intro x. simpl. apply pathsinv0,runax. }
    intros y rest IH x.
    reflexivity.
  Defined.

  Definition iterop_fun_step' (lunax : islunit op unel) {m} (xs:stn m -> X) (x:X) :
    iterop_fun (append_fun xs x) = op (iterop_fun xs) x.
  Proof.
    intros lunax ? ? ?.
    unfold iterop_fun at 1.
    simpl.
    induction m as [|m _].
    - simpl. rewrite append_fun_compute_2. apply pathsinv0. apply lunax.
    - simpl. rewrite append_fun_compute_2.
      apply (maponpaths (λ y, op y x)). apply maponpaths.
      apply append_and_drop_fun.
  Defined.

  Definition iterop_fun_step (lunax : islunit op unel) {m} (x:stn(S m) -> X) :
    iterop_fun x = op (iterop_fun (x ∘ dni lastelement)) (x lastelement).
  Proof.
    intros.
    unfold iterop_fun at 1.
    simpl.
    induction m as [|m _].
    - simpl. apply pathsinv0, lunax.
    - simpl. reflexivity.
  Defined.

  Definition iterop_fun_append (lunax : islunit op unel) {m} (x:stn m -> X) (y:X) :
    iterop_fun (append_fun x y) = op (iterop_fun x) y.
  Proof.
    intros lunax. intros.
    rewrite (iterop_fun_step lunax).
    rewrite append_fun_compute_2.
    apply (maponpaths (λ x, op (iterop_fun x) y)).
    apply funextfun; intro i.
    unfold funcomp.
    rewrite append_fun_compute_1.
    reflexivity.
  Defined.

End BinaryOperations.

(** general associativity for addition in nat *)

Theorem nat_plus_associativity {n} {m:stn n->nat} (k:∏ (ij : ∑ i, stn (m i)), nat) :
  stnsum (λ i, stnsum (curry k i)) = stnsum (k ∘ lexicalEnumeration m).
Proof.
  intros. apply weqtoeqstn.
  intermediate_weq (∑ i, stn (stnsum (curry k i))).
  { apply invweq. apply weqstnsum1. }
  intermediate_weq (∑ i j, stn (curry k i j)).
  { apply weqfibtototal; intro i. apply invweq. apply weqstnsum1. }
  intermediate_weq (∑ ij, stn (k ij)).
  { exact (weqtotal2asstol (stn ∘ m) (stn ∘ k)). }
  intermediate_weq (∑ ij, stn (k (lexicalEnumeration m ij))).
  { apply (weqbandf (inverse_lexicalEnumeration m)). intro ij. apply eqweqmap.
    apply (maponpaths stn), (maponpaths k). apply pathsinv0, homotinvweqweq. }
  apply inverse_lexicalEnumeration.
Defined.

Corollary nat_plus_associativity' n (m:stn n->nat) (k:∏ i, stn (m i) -> nat) :
  stnsum (λ i, stnsum (k i)) = stnsum (uncurry k ∘ lexicalEnumeration m).
Proof. intros. exact (nat_plus_associativity (uncurry k)). Defined.

Lemma iterop_fun_nat {n:nat} (x:stn n->nat) : iterop_fun 0 Nat.add x = stnsum x.
Proof.
  intros. induction n as [|n I].
  - reflexivity.
  - induction n as [|n J].
    + reflexivity.
    + simple refine (iterop_fun_step 0 Nat.add natplusl0 _ @ _ @ ! stnsum_step _).
      apply (maponpaths (λ i, i + x lastelement)).
      rewrite replace_dni_last. apply I.
Defined.

Theorem associativityNat : isAssociative_fun 0 Nat.add.
Proof.
  intros n m x. unfold iterop_fun_fun. apply pathsinv0. rewrite 2 iterop_fun_nat.
  intermediate_path (stnsum (λ i : stn n, stnsum (x i))).
  - apply maponpaths. apply funextfun; intro. apply iterop_fun_nat.
  - now apply nat_plus_associativity'.
Defined.

(** general associativity for monoids *)

Local Open Scope multmonoid.

Definition iterop_list_mon {M:monoid} : list M -> M.
Proof.
  intros ? x.
  exact (iterop_list (unel M) (@op M) x).
Defined.

Definition iterop_seq_mon {M:monoid} : Sequence M -> M.
Proof.
  intros ? x.
  exact (iterop_seq (unel M) (@op M) x).
Defined.

Definition iterop_seq_seq_mon {M:monoid} : Sequence (Sequence M) -> M.
Proof.
  intros ? x.
  exact (iterop_seq_seq (unel M) (@op M) x).
Defined.

Definition iterop_list_list_mon {M:monoid} : list (list M) -> M.
Proof.
  intros ? x.
  exact (iterop_list_list (unel M) (@op M) x).
Defined.

(* some rewriting rules *)

Lemma iterop_seq_mon_len1 {M:monoid} (x : stn 1 -> M) :
  iterop_seq_mon (functionToSequence x) = x lastelement.
Proof.
  reflexivity.
Defined.

Definition iterop_seq_mon_step {M:monoid} {n} (x:stn (S n) -> M) :
  iterop_seq_mon (S n,,x) = iterop_seq_mon (n,,x ∘ dni lastelement) * x lastelement.
Proof.
  intros.
  induction n as [|n _].
  { apply pathsinv0, lunax. }
  reflexivity.
Defined.

Definition iterop_list_mon_step {M:monoid} (x:M) (xs:list M) :
  iterop_list_mon (x::xs) = x * iterop_list_mon xs.
Proof.
  intros M x xs.
  apply iterop_list_step.
  apply runax.
Defined.

Local Definition iterop_seq_mon_append {M:monoid} (x:Sequence M) (m:M) :
  iterop_seq_mon (append x m) = iterop_seq_mon x * m.
Proof.
   intros ? [n x] ?. unfold append. rewrite iterop_seq_mon_step.
   rewrite append_fun_compute_2.
   apply (maponpaths (λ a, a * m)).
   apply (maponpaths (λ x, iterop_seq_mon (n,,x))).
   apply funextfun; intros [i b]; simpl.
   unfold funcomp.
   now rewrite append_fun_compute_1.
Defined.

Local Definition iterop_seq_seq_mon_step {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  iterop_seq_seq_mon (S n,,x) = iterop_seq_seq_mon (n,,x ∘ dni lastelement) * iterop_seq_mon (x lastelement).
Proof.
  intros.
  induction n as [|n _].
  - simpl. apply pathsinv0,lunax.
  - reflexivity.
Defined.

Lemma iterop_seq_mon_homot {M:monoid} {n} (x y : stn n -> M) :
  x ~ y -> iterop_seq_mon(n,,x) = iterop_seq_mon(n,,y).
Proof.
  intros M n. induction n as [|n N].
  - reflexivity.
  - intros x y h. rewrite 2 iterop_seq_mon_step.
    apply two_arg_paths.
    + apply N. apply funhomot. exact h.
    + apply h.
Defined.

(** The general associativity theorem. *)

Theorem associativityOfProducts_list (M:monoid) : isAssociative_list (unel M) (@op M).
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros M. unfold isAssociative_list.
  apply list_ind.
  - simpl. reflexivity.
  - intros x xs I. simpl in I.
    rewrite Lists.flattenStep.
    unfold iterop_list_list_mon. unfold iterop_list_list. rewrite mapStep.
    rewrite (iterop_list_step _ _ (runax M)).
    intermediate_path (iterop_list 1 op x * iterop_list 1 op (Lists.flatten xs)).
    + generalize (Lists.flatten xs) as y; clear xs I; intro y.
      generalize x; clear x.
      apply list_ind.
      * cbn. apply pathsinv0, lunax.
      * intros x xs J. rewrite Lists.concatenateStep.
        rewrite 2 (iterop_list_step _ _ (runax M)).
        rewrite assocax. apply maponpaths. exact J.
    + apply maponpaths. exact I.
Defined.

Theorem associativityOfProducts_seq (M:monoid) : isAssociative_seq (unel M) (@op M).
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros M. unfold isAssociative_seq; intros. induction x as [n x].
  induction n as [|n IHn].
  { reflexivity. }
  change (flatten _) with (flatten ((n,,x): NonemptySequence _)).
  rewrite flattenStep.
  change (lastValue _) with (x lastelement).
  unfold iterop_seq_seq. simpl.
  unfold iterop_fun_fun.
  rewrite (iterop_fun_step _ _ (lunax M)).
  generalize (x lastelement) as z; intro z.
  unfold iterop_seq.
  induction z as [m z].
  induction m as [|m IHm].
  { simpl. rewrite runax.
    simple refine (_ @ IHn (x ∘ dni lastelement)).
    rewrite concatenate'_r0.
    now apply (two_arg_paths_b (natplusr0 (stnsum (length ∘ (x ∘ dni lastelement))))). }
  change (length (S m,, z)) with (S m). change (sequenceToFunction (S m,,z)) with z.
  rewrite (iterop_fun_step _ _ (lunax M)). rewrite concatenateStep.
  generalize (z lastelement) as w; intros.
  rewrite <- assocax. unfold append.
  Opaque iterop_fun. simpl. Transparent iterop_fun.
  rewrite (iterop_fun_append _ _ (lunax M)).
  apply (maponpaths (λ u, u*w)). simpl in IHm. apply IHm.
Defined.

Corollary associativityOfProducts' {M:monoid} {n} (f:stn n -> nat) (x:stn (stnsum f) -> M) :
  iterop_seq_mon (stnsum f,,x) = iterop_seq_seq_mon (partition f x).
Proof.
  intros. refine (_ @ associativityOfProducts_seq M (partition f x)).
  assert (L := flatten_partition f x). apply pathsinv0. exact (iterop_seq_mon_homot _ _ L).
Defined.

(** generalized commutativity *)

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Ltac change_lhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T a y) end.
Ltac change_rhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T x a) end.

Local Open Scope stn.

Lemma commutativityOfProducts_helper {M:abmonoid} {n} (x:stn (S n) -> M) (j:stn (S n)) :
  iterop_seq_mon (S n,,x) = iterop_seq_mon (n,,x ∘ dni j) * x j.
Proof.
  induction j as [j jlt].
  assert (jle := natlthsntoleh _ _ jlt).
  Local Open Scope transport.
  set (f := nil □ j □ S O □ n-j : stn 3 -> nat).
  assert (B : stnsum f = S n).
  { unfold stnsum, f; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc.
    rewrite (natpluscomm 1). rewrite <- natplusassoc.
    rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }
  set (r := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B) ) :
              stn (stnsum f) ≃ stn (S n)).
  set (x' := x ∘ r).
  intermediate_path (iterop_seq_mon (stnsum f,, x')).
  { induction B. apply iterop_seq_mon_homot. intros i. unfold x'.
    unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
  unfold iterop_seq_mon. unfold iterop_seq.
  refine (associativityOfProducts' f x' @ _).
  unfold partition.
  rewrite 3 iterop_seq_seq_mon_step.
  change (iterop_seq_seq_mon (0,,_)) with (unel M); rewrite lunax.
  unfold funcomp at 1 2.
  set (s0 := dni lastelement (dni lastelement (@lastelement 0))).
  unfold funcomp at 1.
  set (s1 := dni lastelement (@lastelement 1)).
  set (s2 := @lastelement 2).
  unfold partition'. unfold inverse_lexicalEnumeration.
  change (f s0) with j; change (f s1) with (S O); change (f s2) with (n-j).
  set (f' := nil □ j □ n-j : stn 2 -> nat).
  assert (B' : stnsum f' = n).
  { unfold stnsum, f'; simpl. repeat unfold append_fun; simpl.
    rewrite natpluscomm. now apply minusplusnmm. }
  set (r' := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B') ) :
              stn (stnsum f') ≃ stn n).
  set (x'' := x ∘ dni (j,, jlt) ∘ r').
  intermediate_path (iterop_seq_mon (stnsum f',, x'') * x (j,, jlt)).
  { assert (L := iterop_seq_mon_len1 (λ j0 : stn 1, x' ((weqstnsum1 f) (s1,, j0)))).
    unfold functionToSequence in L.
    rewrite L. rewrite assocax. refine (transportf (λ k, _*k=_) (commax _ _ _) _).
    rewrite <- assocax.
    apply two_arg_paths.
    { refine (_ @ !associativityOfProducts' f' x'').
      unfold partition.
      rewrite 2 iterop_seq_seq_mon_step.
      change (iterop_seq_seq_mon (0,,_)) with (unel M); rewrite lunax.
      apply two_arg_paths.
      { unfold funcomp. set (s0' := dni lastelement (@lastelement 0)).
        unfold partition'. change (f' s0') with j.
        apply iterop_seq_mon_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply subtypeEquality_prop.
        change_lhs (stntonat _ i).
        unfold dni. unfold di.
        unfold stntonat; rewrite rewrite_pr1_tpair.
        match goal with |- context [ match ?x with _ => _ end ]
                        => induction x as [c|c] end.
        { reflexivity. }
        { apply fromempty. assert (P := c : i ≥ j); clear c.
          exact (natlthtonegnatgeh _ _ (stnlt i) P). } }
      { unfold partition'. change (f' lastelement) with (n-j).
        apply iterop_seq_mon_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply subtypeEquality_prop. change_lhs (j+1+i). unfold dni, di.
        unfold stntonat; rewrite rewrite_pr1_tpair.
        match goal with |- context [ match ?x with _ => _ end ]
                        => induction x as [c|c] end.
        { apply fromempty. exact (negnatlthplusnmn j i c). }
        { change_rhs (1 + (j + i)). rewrite <- natplusassoc. rewrite (natpluscomm j 1).
          reflexivity. } } }
    unfold x'. unfold funcomp. apply maponpaths.
    apply subtypeEquality_prop. change (j+0 = j). apply natplusr0. }
  { apply (maponpaths (λ k, k * _)). induction (!B').
    change_rhs (iterop_seq_mon (n,, x ∘ dni (j,, jlt))).
    apply iterop_seq_mon_homot; intros i.
    unfold x''. unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
Qed.

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  iterop_seq_mon (n,,x) = iterop_seq_mon (n,,x∘f).
Proof.
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros. induction n as [|n IH].
  - reflexivity.
  - set (i := @lastelement n); set (i' := f i).
    rewrite (iterop_seq_mon_step (x ∘ f)).
    change ((x ∘ f) lastelement) with (x i').
    rewrite (commutativityOfProducts_helper x i').
    apply (maponpaths (λ k, k*_)).
    set (f' := weqoncompl_ne f i (stnneq i) (stnneq i') : stn_compl i ≃ stn_compl i').
    set (g := weqdnicompl i); set (g' := weqdnicompl i').
    apply pathsinv0.
    set (h := (invweq g' ∘ f' ∘ g)%weq).
    assert (L : x ∘ f ∘ dni lastelement ~ x ∘ dni i' ∘ h).
    { intro j. unfold funcomp. apply maponpaths.
      apply (invmaponpathsincl _ ( isinclstntonat _ ) _ _).
      unfold h. rewrite 2 weqcomp_to_funcomp_app. rewrite pr1_invweq.
      induction j as [j J]. unfold g, i, f', g', stntonat.
      rewrite <- (weqdnicompl_compute i').
      unfold pr1compl_ne.
      unfold funcomp.
      rewrite homotweqinvweq.
      rewrite (weqoncompl_ne_compute f i (stnneq i) (stnneq i') _).
      apply maponpaths, maponpaths.
      apply subtypeEquality_prop.
      unfold stntonat.
      now rewrite weqdnicompl_compute. }
    rewrite (IH (x ∘ dni i') h).
    now apply iterop_seq_mon_homot.
Defined.
