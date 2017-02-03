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

  Context {X:UU} (unit:X) (op:binop X).

  (* we use an extra induction step in each of the following definitions so
     we don't end up with superfluous unit factors *)

  Definition iterop_list : list X -> X.
  Proof.
    intro k.
    simple refine (list_ind (λ _, X) _ _ k).
    - simpl. exact unit.
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
    { exact unit. }
    { induction n as [|n I].
      { exact (x lastelement). }
      { exact (op (I (x ∘ dni_lastelement)) (x lastelement)). }}
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
    ∏ n (m:stn n -> nat) (x : ∏ i (j:stn (m i)), X), iterop_fun (FiniteSequences.flatten' x) = iterop_fun_fun x.

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

  Definition iterop_list_step (runax : isrunit op unit) (x:X) (xs:list X) :
    iterop_list (x::xs) = op x (iterop_list xs).
  Proof.
    intros runax x xs.
    generalize x; clear x.
    apply (list_ind (λ xs, ∏ x : X, iterop_list (x :: xs) = op x (iterop_list xs))).
    { intro x. simpl. apply pathsinv0,runax. }
    intros y rest IH x.
    reflexivity.
  Defined.

  Definition iterop_fun_step' (lunax : islunit op unit) {m} (xs:stn m -> X) (x:X) :
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

  Definition iterop_fun_step (lunax : islunit op unit) {m} (x:stn(S m) -> X) :
    iterop_fun x = op (iterop_fun (x ∘ dni_lastelement)) (x lastelement).
  Proof.
    intros.
    unfold iterop_fun at 1.
    simpl.
    induction m as [|m _].
    - simpl. apply pathsinv0, lunax.
    - simpl. reflexivity.
  Defined.

  Definition iterop_fun_append (lunax : islunit op unit) {m} (x:stn m -> X) (y:X) :
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

(** general associativity for nat *)

Lemma iterop_fun_nat {n:nat} (x:stn n->nat) : iterop_fun 0 Nat.add x = stnsum x.
Proof.
  intros.
  induction n as [|n I].
  - reflexivity.
  - induction n as [|n J].
    + reflexivity.
    + simple refine (iterop_fun_step 0 Nat.add natplusl0 _ @ _ @ ! stnsum_step _).
      apply (maponpaths (λ i, i + x lastelement)).
      rewrite replace_dni_last.
      apply I.
Defined.

Theorem associativityNat : isAssociative_fun 0 Nat.add.
Proof.
  intros n m x.
  unfold iterop_fun_fun.
  apply pathsinv0.
  rewrite 2 iterop_fun_nat.
  intermediate_path (stnsum (λ i : stn n, stnsum (x i))).
  - apply maponpaths.
    apply funextfun; intro.
    apply iterop_fun_nat.
  - simple refine (nat_plus_associativity' _ _ _ @ _).
    apply maponpaths.
    unfold flatten'.
    unfold lexicalEnumeration.
    apply (maponpaths ((λ f, uncurry x ∘ f)
                       : (stn (stnsum m) → ∑ i : stn n, stn (m i)) → stn (stnsum m) → nat )).
    change (invmap (weqstnsum1 m) = weqstnsum_invmap m).
    (* we need to construct weqstnsum1 with weqstnsum_invmap *)
Abort.

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

Definition iterop_seq_mon_step {M:monoid} {n} (x:stn (S n) -> M) :
  iterop_seq_mon (S n,,x) = iterop_seq_mon (n,,x ∘ dni_lastelement) * x lastelement.
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
  iterop_seq_seq_mon (S n,,x) = iterop_seq_seq_mon (n,,x ∘ dni_lastelement) * iterop_seq_mon (x lastelement).
Proof.
  intros.
  induction n as [|n _].
  - simpl. apply pathsinv0,lunax.
  - reflexivity.
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
    simple refine (_ @ IHn (x ∘ dni_lastelement)).
    rewrite concatenate'_r0.
    now apply (two_arg_paths_b _ _ _ _ _ (natplusr0 (stnsum (length ∘ (x ∘ dni_lastelement))))). }
  change (length (S m,, z)) with (S m). change (sequenceToFunction (S m,,z)) with z.
  rewrite (iterop_fun_step _ _ (lunax M)). rewrite concatenateStep.
  generalize (z lastelement) as w; intros.
  rewrite <- assocax. unfold append.
  Opaque iterop_fun. simpl. Transparent iterop_fun.
  rewrite (iterop_fun_append _ _ (lunax M)).
  apply (maponpaths (λ u, u*w)). simpl in IHm. apply IHm.
Defined.

(** commutativity *)

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  iterop_seq_mon (n,,x) = iterop_seq_mon (n,,x∘f).
Proof.
  (** This proof comes from % \cite[section 1.5, Theorem 2, page 9]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros.
  induction n as [|n IH].
  - reflexivity.
  - assert (specialcase : ∏ (y:stn _->M) (g : stn _ ≃ stn _), g lastelement = lastelement ->
        iterop_seq_mon (S n,, y) = iterop_seq_mon (S n,, y ∘ g)).
    { intros ? ? a. rewrite 2? iterop_seq_mon_step. change ((_ ∘ _) _) with (y (g lastelement)).
      rewrite a. apply (maponpaths (λ m, m * _)). change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_lastelement)).
      set (h := eqweqmap (maponpaths stn_compl a)).
      assert (pr1_h : ∏ i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. }
      set (wc := weqdnicompl n lastelement).
      set (g' := (invweq wc ∘ (h ∘ (weqoncompl_ne g lastelement (stnneq _) (stnneq _) ∘ wc))) %weq).
      intermediate_path (iterop_seq_mon (n,, y ∘ dni_lastelement ∘ g')).
      { apply IH. }
      { change ((_ ∘ _) ∘ _) with (y ∘ (dni_lastelement ∘ g')).
        apply maponpaths; apply maponpaths.
        apply (maponpaths (λ h i, y(h i))).
        apply funextfun; intros i.
        unfold funcomp. apply isinjstntonat. rewrite pr1_dni_lastelement. unfold g'.
        rewrite 3? weqcomp_to_funcomp_app. rewrite inv_weqdnicompl_compute_last. rewrite pr1_h.
        unfold pr1weq.
        unfold weqoncompl_ne.
        (* change (pr1 *)
        (*    (weqpair *)
        (*       (maponcomplweq_ne g lastelement  *)
        (*          (stnneq lastelement) (stnneq (pr1 g lastelement))) *)
        (*       (isweqmaponcompl_ne g lastelement *)
        (*          (stnneq lastelement) (stnneq (pr1 g lastelement)))) *)
        (*    (pr1 wc i)) *)
        (* with (maponcomplweq_ne g lastelement  *)
        (*                        (stnneq lastelement) (stnneq (pr1 g lastelement)) *)
        (*                        (pr1 wc i) *)
        (*      ). *)
        (* unfold wc. *)
        (* unfold weqdnicompl. *)

        (* induction (natlthorgeh j lastelement) as [t|t]. *)

        (* rewrite weqdnicompl_compute_last. *) (* rewrite pr1_dni_lastelement. *)
        (* reflexivity. *)
        admit.
      }}
    set (j := f lastelement).
    induction j as [j jlt].
    assert (jle := natlthsntoleh _ _ jlt).
    Local Open Scope nat.
    set (m := nil □ j □ 1 □ n-j).
    set (m' := nil □ j □ n-j □ 1).
    set (sw := (nil □ ●0 □ ●2 □ ●1 : Sequence (stn 3)) % stn).
    assert (B : stnsum m = S n).
    { unfold stnsum; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc. rewrite (natpluscomm 1). rewrite <- natplusassoc.
      rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }
    assert (B' : stnsum m' = S n).
    { unfold stnsum; simpl. rewrite natplusassoc. rewrite (natpluscomm _ 1). rewrite <- natplusassoc. apply B. }
    assert (C : m' ∘ sw ~ m).
    { intro i. change (pr1 sw) with 3 in i.
      induction i as [i b]. inductive_reflexivity i b. }
    assert (isweqsw : isweq sw).
    { refine (gradth sw sw _ _); ( intros [i b]; inductive_reflexivity i b). }
    set (w := weqstnsum1 m). rewrite B in w. change (pr1 m) with 3 in w.
    set (w' := weqstnsum1 m'). rewrite B' in w'. change (pr1 m') with 3 in w'.

(*
    induction (isdeceqstn (S n) (f lastelement) lastelement) as [p|p].
    + now apply specialcase.
    +
*)

Abort.
