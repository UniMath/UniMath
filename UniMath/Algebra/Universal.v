(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.

Section Basic.

  Definition Arity: UU := nat.

  Definition Signature: UU := ∑ (names: hSet), names → Arity.

  Definition names (sigma: Signature): hSet := pr1 sigma.

  Definition arity {sigma: Signature} (nm: names sigma): Arity := pr2 sigma nm.

  Definition mksignature {n: nat} (v: Vector nat n): Signature := (stnset n ,, el v).

  Definition Algebra (sigma: Signature): UU
    := ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

  Coercion support {sigma: Signature} (a: Algebra sigma): hSet := pr1 a.

  Definition dom {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
    := Vector (support a) (arity nm).

  Definition cod {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
    := support a.

  Definition op {sigma: Signature} (a: Algebra sigma) (nm: names sigma): (dom a nm) → (cod a nm)
    := pr2 a nm.

  Definition mkalgebra {sigma : Signature} (support : hSet)
             (ops: ∏ nm: names sigma, Vector support (arity nm) → support) : Algebra sigma
    := (support ,, ops).

End Basic.

Section Homomorphisms.

  Context { sigma: Signature }.

  Definition is_hom {a1 a2: Algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition hom (a1 a2: Algebra sigma): UU :=  ∑ (f: a1 → a2), is_hom f.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {a1 a2: Algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2proof {a1 a2: Algebra sigma} (f: a1 ↦ a2): is_hom f := pr2 f.

  Definition mkhom {a1 a2: Algebra sigma} (f: a1 → a2) (f_is_hom: is_hom f)
    : a1 ↦ a2 := f ,, f_is_hom.

  Theorem ishom_isaprop {a1 a2: Algebra sigma} (f: a1 → a2): isaprop (is_hom f).
  Proof.
    unfold is_hom.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply (setproperty a2).
  Defined.

  Theorem hom_isaset (a1 a2: Algebra sigma): isaset (hom a1 a2).
  Proof.
    unfold hom.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      apply isasetaprop.
      apply ishom_isaprop.
  Defined.

  Local Lemma idfun_is_hom (a: Algebra sigma): is_hom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_id (a: Algebra sigma): a ↦ a := mkhom (idfun a) (idfun_is_hom a).

  Local Lemma comp_is_hom  {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): is_hom (h2 ∘ h1).
  Proof.
    red.
    intros.
    induction h1 as [f1 ishomf1].
    induction h2 as [f2 ishomf2].
    cbn.
    rewrite vector_map_comp.
    rewrite ishomf1.
    rewrite ishomf2.
    reflexivity.
  Defined.

  Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
    := mkhom (h2 ∘ h1) (comp_is_hom h1 h2).

End Homomorphisms.

Declare Scope hom_scope.

Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity): hom_scope.

Delimit Scope hom_scope with hom.

Local Open Scope hom.

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mkalgebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

  Local Lemma is_hom_terminalhom {a: Algebra sigma}
    : @is_hom sigma a terminal_algebra tounit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition terminal_hom (a : Algebra sigma): hom a terminal_algebra
    := @mkhom sigma a terminal_algebra tounit is_hom_terminalhom.

  Theorem terminal_hom_unicity (a: Algebra sigma) (f: hom a terminal_algebra): f = terminal_hom a.
  Proof.
    use total2_paths2_f.
    - apply iscontrfuntounit.
    - apply proofirrelevance.
      apply ishom_isaprop.
  Defined.

End TerminalAlgebra.

Section Natlemmas.

  Local Lemma nat_movminusleft {a b c: nat}: c ≤ b → a = b - c  → a + c = b.
  Proof.
    intros hp1 hp2.
    apply (maponpaths  (λ n: nat, n + c)) in hp2.
    rewrite minusplusnmm in hp2 ; assumption.
  Defined.

  Local Lemma nat_movplusright {a b c: nat}: a + c = b → a = b - c.
  Proof.
    intros hp.
    apply (maponpaths (λ n: nat, n - c)) in hp.
    rewrite plusminusnmm in hp.
    assumption.
  Defined.

  Local Lemma natleh_plusright {n1 n2 m: nat}: n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    apply (istransnatleh(m:=n2)).
    - assumption.
    - apply natlehnplusnm.
  Defined.

  Local Lemma natleh_minusplus {n1 n2 n3: nat}: n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.
  Proof.
    intros.
    apply nat_movplusright.
    rewrite natplusassoc.
    rewrite (natpluscomm n2 n3).
    rewrite <- natplusassoc.
    rewrite minusplusnmm.
    - reflexivity.
    - assumption.
  Defined.

End Natlemmas.

(** ** Status of a stack machine. *)

Section Status.

  Context {sigma: Signature}.

  (**
    A status is either a natural number, representing the number of terms in the stack,
    or an error.
  **)

  Definition Status: UU := nat ⨿ unit.

  Definition statusok (n: nat): Status := ii1 n.

  Definition statuserror: Status := ii2 tt.

  Lemma Status_isaset: isaset Status.
  Proof.
    apply isasetcoprod.
    - apply isasetnat.
    - apply isasetunit.
  Defined.

  (** Computes the effect, on status, of pushing a function symbol on the top of a stack **)

  Definition status_cons (nm: names sigma) (status: Status): Status.
  Proof.
    induction status as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (statusok ( S(n - arity nm) ) ).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_cons_statusok_f {nm: names sigma} {n: nat} (p: arity nm ≤ n):
    status_cons nm (statusok n) = statusok (S (n - arity nm)).
  Proof.
    cbn [status_cons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) n) as [ok | error] ; cbn.
    - apply idpath.
    - contradiction.
  Defined.

  Lemma status_cons_statusok_fr {nm: names sigma} {n m: nat}:
    status_cons nm (statusok n) = statusok m → arity nm ≤ n × m = S(n - arity nm).
  Proof.
    intro scons.
    cbn [status_cons statusok coprod_rect] in scons.
    induction (isdecrelnatleh (arity nm) n) as [ok | error] ; cbn in scons.
    - apply ii1_injectivity in scons.
      exact (ok ,, ! scons).
    - apply negpathsii2ii1 in scons.
      contradiction.
  Defined.

  Local Lemma status_cons_arith {n1 n2 n3: nat}: n3 ≤ n2 → n1 = S (n2 - n3) → n2 = n1 + n3 -1.
  Proof.
    intros hp valn1.
    rewrite valn1.
    change (S (n2 - n3)) with (1 + (n2 - n3)).
    rewrite natplusassoc.
    rewrite minusplusnmm.
    - rewrite natpluscomm.
      rewrite plusminusnmm.
      apply idpath.
    - assumption.
  Defined.

  Lemma status_cons_statusok_r {nm: names sigma} {status: Status} {m: nat}:
    status_cons nm status = statusok m → m > 0 × status = statusok (m + arity nm - 1).
  Proof.
    intro hp.
    induction status as [n | noerror].
    - apply status_cons_statusok_fr in hp.
      induction hp as [aritynm valm].
      split.
      + rewrite valm.
        apply natgthsn0.
      + apply (maponpaths inl).
        apply status_cons_arith ; assumption.
    - apply negpathsii2ii1 in hp.
      contradiction.
  Defined.

  Lemma status_cons_noerror_r {nm: names sigma} {status: Status}:
    status_cons nm status != statuserror → ∑ n: nat, arity nm ≤ n × status = statusok n.
  Proof.
    intro noerror.
    induction status.
    - cbn [status_cons statusok coprod_rect] in noerror.
      induction (isdecrelnatleh (arity nm) a) as [ok | error].
      + exists a.
        exact (ok ,, idpath _).
      + contradiction.
    - contradiction.
  Defined.

  (** Computes the effect, on status, of concatenating two sequences of function symbols. **)

  Definition status_concatenate (status1 status2: Status): Status.
  Proof.
    induction status2 as [len_s2 | error2].
    - induction status1 as [len_s1 | error1].
      + exact (statusok (len_s1 + len_s2)).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_concatenate_statuscons {nm: names sigma} {status1 status2: Status}:
    (status_cons nm status1 != statuserror) →
    status_concatenate (status_cons nm status1) status2
    = status_cons nm (status_concatenate status1 status2).
  Proof.
    induction status1 as [a1 | error1].
    2: contradiction.
    induction status2 as [a2 | error2].
    2: reflexivity.
    intro noerror.
    cbn [status_cons coprod_rect] in noerror.
    cbn [status_concatenate status_cons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) a1) as [ok1 | error1] ; cbn in noerror.
    - induction (isdecrelnatleh (arity nm) (a1+a2)) as [ok2 | error2]; cbn.
      + apply maponpaths.
        apply (maponpaths S).
        apply natleh_minusplus.
        assumption.
      + apply fromempty.
        apply error2.
        apply natleh_plusright.
        assumption.
    - contradiction.
  Defined.

End Status.

Section OpList.

  Context {sigma: Signature}.

  (**
    Computes the status of a sequence of function symbols. The sequence should be thought of
    as a stack. A stack will be formally defined as a non-erratic list of function symbols.
   **)

  Definition list2status (l: list (names sigma)): Status := foldr status_cons (statusok 0) l.

  Lemma list2status_cons {nm: names sigma} {l: list (names sigma)}:
    list2status (cons nm l) = status_cons nm (list2status l).
  Proof.
    reflexivity.
  Defined.

  Lemma list2status_zero {l: list (names sigma)}: list2status l = statusok 0 → l = nil.
  Proof.
    intro proof.
    induction l as [len v].
    induction len.
    - induction v.
      reflexivity.
    - apply status_cons_statusok_r in proof.
      induction proof as [contr _].
      apply isirreflnatgth in contr.
      contradiction.
  Defined.

  Lemma list2status_positive {l: list (names sigma)} {n: nat}:
    list2status l = statusok (S n) →
    ∑ (lentail: nat) (v: Vector (names sigma) (S lentail)), l = (S lentail,, v).
  Proof.
    intro proof.
    induction l as [len v].
    induction len.
    - induction v.
      apply ii1_injectivity in proof.
      apply negpaths0sx in proof.
      contradiction.
    - exists len.
      exists v.
      apply idpath.
  Defined.

  Lemma list2status_concatenate {l1 l2: list (names sigma)}:
    list2status l1 != statuserror →
    list2status (concatenate l1 l2) = status_concatenate (list2status l1) (list2status l2).
  Proof.
    apply (list_ind (λ s, list2status s != statuserror →
                          list2status (concatenate s l2) =
                          status_concatenate (list2status s) (list2status l2))).
    - intros.
      change (concatenate nil l2) with (l2).
      induction (list2status l2) as [okl2 | badl2].
      + reflexivity.
      + induction badl2.
        reflexivity.
    - intros nm l1tail IH noerror.
      rewrite list2status_cons.
      rewrite status_concatenate_statuscons by (assumption).
      rewrite <- IH.
      + reflexivity.
      + intro error.
        rewrite list2status_cons in noerror.
        rewrite error in noerror.
        contradiction.
  Defined.

  (** Split a stack in a stack of up to n terms and a stack of the remaining terms **)

  Definition extract_list (l: list (names sigma)) (n: nat):
    list (names sigma) × list (names sigma).
  Proof.
    revert l n.
    apply (list_ind (λ l: list (names sigma),
                          ∏ (n : nat), list (names sigma) × list (names sigma))).
    - intros.
      exact (nil,, nil).
    - intros x xs IH n.
      induction n.
      + exact (nil,, (cons x xs)).
      + set (resind := IH (n + arity x)).
        exact (cons x (pr1 resind) ,, pr2 resind).
  Defined.

  Lemma extract_list_zero {l: list (names sigma)}: extract_list l 0 = nil,, l.
  Proof.
    apply (list_ind (λ l: list (names sigma), extract_list l 0 = nil,, l)).
    - reflexivity.
    - reflexivity.
  Defined.

  Lemma extract_list_cons {x: names sigma} {xs: list (names sigma)} {n: nat}:
    extract_list (cons x xs) (S n) =
    cons x (pr1 (extract_list xs (n + arity x))) ,,
         (pr2 (extract_list xs (n + arity x))).
  Proof.
    reflexivity.
  Defined.

  Lemma extract_list_concatenate1 (l: list (names sigma)) (n: nat)
    : concatenate (pr1 (extract_list l n)) (pr2 (extract_list l n)) = l.
  Proof.
    revert l n.
    apply (list_ind (λ l : list (names sigma), ∏ (n: nat),
      concatenate (pr1 (extract_list l n)) (pr2 (extract_list l n)) = l)).
    - intros.
      reflexivity.
    - intros x xs HPxs n.
      induction n.
      + reflexivity.
      + rewrite extract_list_cons.
        cbn - [concatenate].
        rewrite concatenateStep.
        rewrite (HPxs (n + arity x)).
        reflexivity.
  Defined.

  Local Lemma extract_list_arith1 {n1 n2 n3: nat}: S n1 ≤ n2 → n1 + n3 ≤ n2 + n3 - 1.
  Proof.
    intro nlehm.
    apply (natlehandplusr  _ _  n3) in nlehm.
    apply (natgehandminusl _ _  1) in nlehm.
    change (S n1) with (1 + n1) in nlehm.
    rewrite natplusassoc in nlehm.
    rewrite (natpluscomm 1 (n1 + n3)) in nlehm.
    rewrite plusminusnmm in nlehm.
    assumption.
  Defined.

  Lemma extract_list_success (l: list (names sigma)) {m: nat} (n: nat):
    list2status l = statusok m → n ≤ m  →
                    list2status (pr1 (extract_list l n)) = statusok n ×
                    list2status (pr2 (extract_list l n)) = statusok (m - n).
  Proof.
    revert l m n.
    apply (list_ind (λ l : list (names sigma), ∏ (m n: nat),
        list2status l = statusok m → n ≤ m  →
        list2status (pr1 (extract_list l n)) = statusok n ×
        list2status (pr2 (extract_list l n)) = statusok (m - n))).
    - intros m n proofnil nlehm.
      cbn.
      apply ii1_injectivity in proofnil.
      rewrite <- proofnil in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      repeat split.
    - intros x xs HPind m n proofxxs nlehm.
      induction n.
      + change (extract_list (cons x xs) 0) with (make_dirprod (nil(A:=names sigma)) (cons x xs)).
        rewrite natminuseqn.
        repeat split.
        assumption.
      + clear IHn.
        rewrite extract_list_cons.
        cbn - [list2status].
        rewrite list2status_cons in proofxxs.
        apply status_cons_statusok_r in proofxxs.
        induction proofxxs as [ _ proofxxs].
        eapply extract_list_arith1 in nlehm.
        induction (HPind (m + arity x - 1) (n + arity x) proofxxs nlehm) as [ind1 ind2].
        split.
        * rewrite list2status_cons.
          rewrite ind1.
          rewrite status_cons_statusok_f.
          -- apply (maponpaths statusok).
             rewrite plusminusnmm.
             apply idpath.
          -- rewrite natpluscomm.
             apply natleh_plusright.
             apply isreflnatleh.
        * rewrite ind2.
          apply (maponpaths statusok).
          rewrite NaturalNumbers.natminusminus.
          rewrite <- natplusassoc.
          rewrite (natpluscomm (1+n) (arity x)).
          rewrite <- NaturalNumbers.natminusminus.
          rewrite plusminusnmm.
          apply idpath.
  Defined.

  Lemma extract_list_norest {l: list (names sigma)} {n: nat}
    : list2status l = statusok n →  extract_list l n = l ,, nil.
  Proof.
    intro proofl.
    set (H1 := extract_list_success l n proofl (isreflnatleh n)).
    set (concat := extract_list_concatenate1 l n).
    induction H1 as [first second].
    rewrite minuseq0' in second.
    apply list2status_zero in second.
    rewrite second in concat.
    rewrite concatenate_nil in concat.
    apply dirprodeq ; assumption.
  Defined.

  Local Lemma extract_list_arith2 {n1 n2: nat}: S n1 + n2 - 1 = n1 + n2.
  Proof.
    change (S n1) with (1 + n1).
    rewrite natplusassoc.
    rewrite (natpluscomm 1 (n1 + n2)).
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Lemma extract_list_concatenate2 (l1 l2: list (names sigma)) {n1: nat} (n: nat)
    : list2status l1 = statusok n1 → n ≤ n1 →
        extract_list (concatenate l1 l2) n =
          pr1 (extract_list l1 n) ,, concatenate (pr2 (extract_list l1 n)) l2.
  Proof.
    revert l1 n1 n.
    apply (list_ind (λ l1 : list (names sigma), ∏ (n1 n: nat),
           list2status l1 = statusok n1 → n ≤ n1 → extract_list (concatenate l1 l2) n =
              pr1 (extract_list l1 n) ,, concatenate (pr2 (extract_list l1 n)) l2)).
    - intros n1 n proofl1 nlehn1.
      apply ii1_injectivity in proofl1.
      rewrite <- proofl1 in *.
      apply natleh0tois0 in nlehn1.
      rewrite nlehn1.
      cbn - [extract_list].
      rewrite extract_list_zero.
      reflexivity.
    - intros x xs HPind n1 n proofl1 nlehn1.
      rewrite concatenateStep.
      induction n.
      + reflexivity.
      + rewrite list2status_cons in proofl1.
        apply status_cons_statusok_r in proofl1.
        induction proofl1 as [_ proofxs].
        assert (newnok: S n + arity x - 1 ≤ n1 + arity x - 1).
        {
          apply natgehandminusl, natlehandplusr.
          assumption.
        }
        set (ind := HPind (n1 + arity x - 1) (S n + arity x - 1) proofxs newnok).
        rewrite extract_list_arith2 in ind.
        do 2 rewrite extract_list_cons.
        apply pathsdirprod.
        * apply (maponpaths (λ xs, cons x xs)).
          apply (maponpaths pr1) in ind.
          assumption.
        * apply (maponpaths dirprod_pr2) in ind.
          assumption.
  Defined.

End OpList.

Section Term.

  Definition Stack (sigma: Signature) (n: nat)
    : UU := ∑ s: list (names sigma), list2status s = statusok n.

  Definition mkstack {sigma: Signature} {n: nat} (s: list (names sigma))
             (proofs: list2status s = statusok n)
    : Stack sigma n := s ,, proofs.

  Coercion stack2list {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list (names sigma) := pr1 s.

  Definition stack2proof {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list2status s = statusok n := pr2 s.

  Definition Term (sigma: Signature): UU := Stack sigma 1.

  Coercion term2list {sigma: Signature} (t: Term sigma): list (names sigma) := pr1 t.

  Definition term2proof {sigma: Signature} (t: Term sigma)
    : list2status t = statusok 1 := pr2 t.

  Lemma Stack_isaset (sigma: Signature) (n: nat): isaset (Stack sigma n).
  Proof.
    apply isaset_total2.
    - apply isofhlevellist.
      exact (setproperty (names sigma)).
    - intros.
      apply isasetaprop.
      apply Status_isaset.
  Defined.

  Definition Term_hset (sigma : Signature): hSet
    := make_hSet (Term sigma) (Stack_isaset sigma 1).

  Context {sigma: Signature}.

  Lemma stack_extens {n: nat} {s1 s2 : Stack sigma n} (p : stack2list s1 = stack2list s2)
    : s1 = s2.
  Proof.
    apply subtypePath.
    2: exact p.
    intros s.
    apply Status_isaset.
  Defined.

  Definition stack_nil (sigma: Signature): Stack sigma 0 := stnpr nil.

  Lemma stack_isnil (s: Stack sigma 0): s = stack_nil sigma.
  Proof.
    induction s as [l proof].
    apply stack_extens.
    apply list2status_zero.
    assumption.
  Defined.

  Local Lemma is_stack_concatenate  {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : list2status (concatenate s1 s2) = statusok (n1 + n2).
  Proof.
    change (statusok (n1 + n2)) with (status_concatenate (statusok n1) (statusok n2)).
    rewrite <- (stack2proof s1).
    rewrite <- (stack2proof s2).
    apply list2status_concatenate.
    rewrite (stack2proof s1).
    apply negpathsii1ii2.
  Defined.

  Definition stack_concatenate {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : Stack sigma (n1 + n2) := mkstack (concatenate s1 s2) (is_stack_concatenate s1 s2).

  Lemma stack2list_stackconcatenate {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : stack2list (stack_concatenate s1 s2) = concatenate (stack2list s1) (stack2list s2).
  Proof.
    reflexivity.
  Defined.

  Definition terms2stack {n: nat} (vec: Vector (Term sigma) n): Stack sigma n.
  Proof.
    induction n.
    - exact (stack_nil sigma).
    - exact (stack_concatenate (hd vec) (IHn (tl vec))).
  Defined.

  Lemma terms2stack_vcons {n: nat} {v: Vector (Term sigma) n} {t: Term sigma} :
    terms2stack (vcons t v) = stack_concatenate t (terms2stack v).
  Proof.
    reflexivity.
  Defined.

  Lemma is_mkterm_term (nm: names sigma) (vec: Vector (Term sigma) (arity nm)):
    list2status (cons nm (terms2stack vec)) = statusok 1.
  Proof.
    rewrite list2status_cons.
    rewrite (stack2proof (terms2stack vec)).
    rewrite status_cons_statusok_f.
    - rewrite minuseq0'.
      apply idpath.
    - apply isreflnatleh.
  Defined.

  Definition mkterm (nm: names sigma) (vec: Vector (Term sigma) (arity nm)): Term sigma
    := mkstack (cons nm (terms2stack vec)) (is_mkterm_term nm vec).

  (** Principal operation of a term (i.e., the head of the underling list). *)

  Definition princop (t: Term sigma): names sigma.
  Proof.
    induction t as [l proof].
    induction (list2status_positive proof) as [len [v _]].
    exact (hd v).
  Defined.

  Local Definition extract_term {n: nat} (s: Stack sigma (S n))
    : Term sigma ×  Stack sigma n.
  Proof.
    set (rest := extract_list_success s 1 (stack2proof s) (natleh0n n)).
    induction rest as [fproof sproof].
    split.
    - exact (mkstack (pr1 (extract_list s 1)) fproof).
    - change (S n - 1) with (1 + n - 1) in sproof.
      rewrite natpluscomm in sproof.
      rewrite plusminusnmm in sproof.
      exact (mkstack (pr2 (extract_list s 1)) sproof).
  Defined.

  Definition stack_first {n: nat} (s: Stack sigma (S n)): Term sigma
    := pr1 (extract_term s).

  Definition stack_rest {n: nat} (s: Stack sigma (S n)): Stack sigma n
    := pr2 (extract_term s).

  Lemma stack_concatenate_normalize1 {n: nat} (s: Stack sigma (S n))
    : stack_concatenate (stack_first s) (stack_rest s) = s.
  Proof.
    apply stack_extens.
    apply (extract_list_concatenate1 s 1).
  Defined.

  Lemma stack_concatenate_normalize2 (t: Term sigma) {n2: nat} (s2: Stack sigma n2)
    : stack_first (stack_concatenate t s2) = stack_first t.
  Proof.
    apply stack_extens.
    cbn - [extract_list].
    set (res := extract_list_concatenate2 t s2 1 (stack2proof t) (natleh0n 0)).
    apply (maponpaths pr1) in res.
    assumption.
  Defined.

  Lemma stack_concatenate_normalize3 (t: Term sigma) {n2: nat} (s2: Stack sigma n2)
    : stack_rest (stack_concatenate t s2) = s2.
  Proof.
    apply stack_extens.
    cbn - [extract_list].
    set (res := extract_list_concatenate2 t s2 1 (stack2proof t) (natleh0n 0)).
    apply (maponpaths dirprod_pr2) in res.
    cbn - [extract_list] in res.
    apply pathsinv0 in res.
    rewrite extract_list_norest in res.
    - apply pathsinv0 in res.
      assumption.
    - exact (stack2proof t).
  Defined.
  
  Lemma stack_first_term {t: Term sigma}: stack_first t = t.
  Proof.
    apply stack_extens.
    cbn.
    rewrite extract_list_norest.
    - reflexivity.
    - exact (stack2proof t).
  Defined.

  Definition stack2terms {n: nat} (s: Stack sigma n): Vector (Term sigma) n.
  Proof.
    induction n.
    - exact vnil.
    - exact (vcons (stack_first s) (IHn (stack_rest s))).
  Defined.

  Lemma stack2terms_concatenate {t: Term sigma} {n: nat} (s2: Stack sigma n):
    stack2terms (stack_concatenate t s2) = vcons t (stack2terms s2).
  Proof.
    change (stack2terms (stack_concatenate t s2))
      with (vcons (stack_first (stack_concatenate t s2))
                  (stack2terms (stack_rest (stack_concatenate t s2)))).
    rewrite stack_concatenate_normalize2.
    rewrite stack_concatenate_normalize3.
    rewrite stack_first_term.
    apply idpath.
  Defined.

  Definition subterms (t: Term sigma): Vector (Term sigma) (arity (princop t)).
  Proof.
    induction t as [l proof].
    unfold princop.
    induction (list2status_positive proof) as [lentail [v ldef]].
    rewrite ldef in proof.
    change (S lentail ,, v) with (cons (hd v) (lentail ,, (tl v))) in proof.
    rewrite list2status_cons in proof.
    apply status_cons_statusok_r in proof.
    induction proof as [_ proof].
    rewrite natpluscomm in proof.
    rewrite plusminusnmm in proof.
    exact (stack2terms (mkstack (lentail,, tl v) proof)).
  Defined.

  Lemma terms2stack2terms {n: nat} (s: Stack sigma n): terms2stack (stack2terms s) = s.
  Proof.
    induction n.
    - rewrite stack_isnil.
      apply idpath.
    - rewrite <- (stack_concatenate_normalize1 s).
      simpl.
      rewrite stack_concatenate_normalize2.
      rewrite stack_concatenate_normalize3.
      rewrite stack_first_term.
      apply maponpaths.
      apply (IHn (stack_rest s)).
  Defined.
  
End Term.

Section TermInduction.

  Context {sigma: Signature}.
  
  (** Some lemmatas on length of lists **)

  Local Lemma length_cons {A: UU} (x: A) (xs: list A):
    length (cons x xs) = S(length xs).
  Proof.
    reflexivity.
  Defined.

  Local Lemma length_concatenate (l1: list (names sigma)) (l2: list (names sigma)) :
    length (concatenate l1 l2) = length l1 + length l2.
  Proof.
    induction l1 as [len1 vec1].
    induction len1.
    - induction vec1.
      reflexivity.
    - change (S (length (concatenate (len1,, tl vec1) l2)) = S (len1 + length l2)).
      apply maponpaths.
      apply (IHlen1 (tl vec1)).
  Defined.

  Local Lemma length_terms2stack {n: nat} (s: Vector (Term sigma) n):
    ∏ i:  ⟦ n ⟧, length (el s i) ≤ length (terms2stack s).
  Proof.
    induction n.
    - intro i.
      apply fromempty.
      apply negstn0 in i.
      assumption.
    - change (S n) with (1 + n) in *.
      induction i as [i iproof].
      induction i.
      + change s with (vcons (hd s) (tl s)).
        rewrite terms2stack_vcons.
        change (el s (0,, iproof)) with (hd s).
        rewrite stack2list_stackconcatenate.
        rewrite length_concatenate.
        apply natleh_plusright.
        apply isreflnatleh.
      + set (ind := IHn (tl s) (i,, iproof)).
        rewrite <- drop_el in ind.
        change  (drop (el s) (i,, iproof)) with (el s (S i,, iproof)) in ind.
        assert (length (terms2stack (tl s)) ≤  length (terms2stack s)).
        {
          change s with (vcons (hd s) (tl s)).
          rewrite terms2stack_vcons.
          change  (tl (vcons (hd s) (tl s))) with (tl s).
          rewrite stack2list_stackconcatenate.
          rewrite length_concatenate.
          rewrite natpluscomm.
          apply natleh_plusright.
          apply isreflnatleh.
        }
        apply (istransnatleh(m:=length (terms2stack (tl s)))).
        * assumption.
        * assumption.
  Defined.

  Lemma term_ind_len
    (P: Term sigma → UU)
    (HPind : ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i : ⟦ arity nm ⟧), P (el vterm i)) → P (mkterm nm vterm) )
  :
    ∏ (n vlen: nat) (vlehn: vlen ≤ n) (v: Vector (names sigma) vlen)
      (lp: list2status (vlen ,, v) = statusok 1), P (mkstack (vlen ,, v) lp).
  Proof.
    induction n.
    - intros.
      apply fromempty.
      apply natleh0tois0 in vlehn.
      generalize v lp.
      clear v lp.
      rewrite vlehn.
      intros.
      induction v.
      apply ii1_injectivity in lp.
      apply negpaths0sx in lp.
      assumption.
    - intros.
      induction (isdeceqnat vlen (S n)) as [vlenlehn | vleneqsn].
      + generalize v lp.
        rewrite vlenlehn.
        clear v lp.
        intros v lp.
        pose (l := lp).
        change (S n,, v) with (cons (hd v) (n ,, tl v)) in l.
        rewrite list2status_cons in l.
        apply status_cons_statusok_r in l.
        induction l as [_ l].
        rewrite natpluscomm in l.
        rewrite plusminusnmm in l.
        set (terms := stack2terms (mkstack (n ,, tl v) l)).
        assert (struct: mkstack (S n ,, v) lp = mkterm (hd v) terms).
        * unfold mkterm, is_mkterm_term, terms.
          rewrite terms2stack2terms.
          apply stack_extens.
          reflexivity.
        * rewrite struct.
          assert (prevterms: ∏ i: ⟦ arity (hd v) ⟧, P (el terms i)).
          {
            intro i.
            set (sizei := length_terms2stack terms i).
            change  (length (terms2stack terms))
              with (length (terms2stack (stack2terms (mkstack (n,, tl v) l)))) in sizei.
            rewrite terms2stack2terms in sizei.
            change (length (mkstack (n,, tl v) l)) with n in sizei.
            induction (el terms i) as [[leni veci] proofi].
            change (length (term2list ((leni,, veci),, proofi))) with leni in sizei.
            exact (IHn leni sizei  veci proofi).
          }
          exact (HPind (hd v) terms prevterms).
      + induction (natlehchoice _ _ vlehn) as [vlenlehn | vleneqn].
        * apply natlthsntoleh in vlenlehn.
          exact (IHn vlen vlenlehn v lp).
        * contradiction.
  Defined.

  Theorem term_ind
    (P: Term sigma → UU)
    (HPind: ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (mkterm nm vterm) )
    : (∏ t: Term sigma, P t).
  Proof.
    intro t.
    induction t as [[lent vect] prooft].
    exact (term_ind_len P HPind lent lent (isreflnatleh _) vect prooft).
  Defined.

  (**  TODO: is it possible to change definition of term_ind so that this lemma may be
   proved by reflexivity? **)

  Lemma term_ind_destruct (nm: names sigma) (v: Vector (Term sigma) (arity nm)):
    ∏ (P: Term sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (mkterm nm vterm)),
    term_ind P Ind (mkterm nm v) = Ind nm v (λ i:  ⟦ arity nm ⟧, term_ind P Ind (el v i)).
  Proof.
    intros.
  Abort.

  (** TODO: change term_ind so that this definition computes. **)

  Definition depth (t: Term sigma): nat
    := term_ind ( λ t: Term sigma, nat)
                ( λ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm))
                    (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) )
                t.

  Lemma depth_step (t: Term sigma) (nm : names sigma) (args : Vector (Term sigma) (arity nm))
     (levels : Vector nat (arity nm)) :
     depth (mkterm nm args) = 1 + vector_foldr max 0 levels.
  Proof.
    unfold depth.
    unfold term_ind.
  Abort.

End TermInduction.

Section TermAlgebra.

  Definition term_algebra (sigma: Signature): Algebra sigma
    := mkalgebra (Term_hset sigma) mkterm.

  (** TODO

  Definition initial_hom {sigma: Signature} (a: Algebra sigma): term_algebra sigma ↦ a.

  Definition initial_hom_unicity {sigma: Signature} (a: Algebra sigma) (f: hom term_algebra a)
     : f = initial_hom a.

  **)

End TermAlgebra.
