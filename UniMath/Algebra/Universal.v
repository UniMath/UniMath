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

  Local Notation "a1 ↦ a2" := (hom a1 a2)  (at level 80, right associativity).

  Definition hom2fun {a1 a2: Algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2proof {a1 a2: Algebra sigma} (f: a1 ↦ a2): is_hom f := pr2 f.

  Definition mkhom {a1 a2: Algebra sigma} (f: a1 → a2) (f_is_hom: is_hom f)
    : a1 ↦ a2 := f ,, f_is_hom.

  Theorem hom_isaset (a1 a2: Algebra sigma): isaset (hom a1 a2).
  Proof.
    unfold hom.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      unfold is_hom.
      apply impred_isaset.
      intros.
      apply impred_isaset.
      intros.
      apply isasetaprop.
      apply (setproperty a2).
  Defined.

  Local Lemma idfun_is_hom (a: Algebra sigma): is_hom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_id (a: Algebra sigma): a ↦ a := mkhom (idfun a) (idfun_is_hom a).

  Local Lemma comp_is_hom  {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): is_hom (funcomp h1 h2).
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
    := mkhom (funcomp h1 h2) (comp_is_hom h1 h2).

End Homomorphisms.

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mkalgebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

  Local Lemma is_hom_terminalhom {a: Algebra sigma}: is_hom(a2 := terminal_algebra) (λ x: a, tt).
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition terminal_hom (a : Algebra sigma): hom a terminal_algebra
    :=  mkhom(a2 := terminal_algebra) (λ _: a, tt) is_hom_terminalhom.

  Theorem terminal_hom_unicity (a: Algebra sigma) (f: hom a terminal_algebra): f = terminal_hom a.
  Proof.
    eapply total2_paths2_f.
    Unshelve.
    2: apply iscontrfuntounit.
    assert (isprop: ∏ (f: support a → support terminal_algebra), isaprop (is_hom f)).
    - intro.
      apply isapropifcontr.
      unfold is_hom.
      apply impred_iscontr.
      intros.
      apply impred_iscontr.
      intros.
      apply iscontrpathsinunit.
    - apply isprop.
  Defined.

End TerminalAlgebra.

Section Natlemmas.

  Local Lemma nat_movesubleft {a b c: nat}: c ≤ b → a = b - c  → a + c = b.
  Proof.
    intros hp1 hp2.
    apply (maponpaths  (λ n: nat, n + c)) in hp2.
    rewrite minusplusnmm in hp2 ; assumption.
  Defined.

  Local Lemma nat_movaddleft {a b c: nat}: a = b + c → a - c = b.
  Proof.
    intros hp.
    apply (maponpaths (λ n: nat, n - c)) in hp.
    rewrite plusminusnmm in hp.
    assumption.
  Defined.

  Local Lemma natleh_add { n1 n2 m: nat }: n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    apply (istransnatleh(m:=n2)).
    - assumption.
    - apply natlehnplusnm.
  Defined.

  (** Forward chaining variant
  Lemma natleh_add { n1 n2 m: nat }: n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    set (H := natlehnplusnm n2 m).
    exact (istransnatleh X H).
  Defined.
  **)

  Local Lemma natleh_adddiff {n1 n2 n3: nat}: n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.
  Proof.
    intros.
    apply nat_movesubleft.
    - rewrite natpluscomm.
      rewrite <- natplusminusle.
      + apply natlehnplusnm.
      + assumption.
    - rewrite NaturalNumbers.natminusminus.
      replace (n3 + n2) with (n2 + n3) by (rewrite natpluscomm; reflexivity).
      rewrite <- NaturalNumbers.natminusminus.
      rewrite plusminusnmm.
      reflexivity.
  Defined.

  Local Lemma nat_notgeh1 {n: nat}: ¬ (n ≥ 1) → n = 0.
  Proof.
    intro n_gte_1.
    induction n.
    - apply idpath.
    - apply fromempty.
      apply n_gte_1.
      apply natgthtogehsn.
      apply natgthsn0.
  Defined.

  Local Lemma nat_notgeh1_inv {n: nat}: n != 0 → n ≥ 1.
  Proof.
    intros.
    apply natgthtogehsn.
    apply natneq0togth0.
    apply nat_nopath_to_neq.
    assumption.
  Defined.

  (*** These axioms probably needs some additional hypotheses ***)

  Local Axiom natlehandminusl: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Local Axiom natlehandminusr: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Local Axiom natdiff0: ∏ a b: nat, 0 = a - b → b ≥ a.

  Local Axiom natdiffasymm: ∏ a b: nat, a ≤ b → a ≥ b → a=b.

  Local Axiom nat_ax: ∏ a b c: nat, a = S (b - c) → b = a + c -1.

  Local Axiom nat_ax3: ∏ a b c : nat, a + b - 1 - (c + b - 1) = a-c.

End Natlemmas.

Section Status.

  Context {sigma: Signature}.

  Definition Status: UU := nat ⨿ unit.

  Definition statusok (n: nat): Status := ii1 n.

  Definition statuserror: Status := ii2 tt.

  Lemma Status_isaset: isaset Status.
  Proof.
    apply isasetcoprod.
    - apply isasetnat.
    - apply isasetunit.
  Defined.

  Definition status_cons (nm: names sigma) (status: Status): Status.
  Proof.
    induction status as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (statusok ( S(n - arity nm) ) ).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_cons_statusok_cases (nm: names sigma) (n: nat):
    (arity nm ≤ n × status_cons nm (statusok n) = statusok (S(n - arity nm)))
      ⨿ (¬ (arity nm ≤ n) × status_cons nm (statusok n) = statuserror).
  Proof.
    cbn [status_cons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) n) as [ok | error].
    - left.
      exact (ok ,, idpath _).
    - right.
      exact (error ,, idpath _).
  Defined.

  Lemma status_cons_statusok_f {nm: names sigma} {n: nat} (p: arity nm ≤ n):
    status_cons nm (statusok n) = statusok (S (n - arity nm)).
  Proof.
    induction (status_cons_statusok_cases nm n) as [ [aritynm ok] | [aritynm error] ].
    - rewrite ok.
      apply idpath.
    - apply fromempty.
      apply aritynm.
      assumption.
  Defined.

  Lemma status_cons_statusok_fr {nm: names sigma} {n m: nat}:
    status_cons nm (statusok n) = statusok m → arity nm ≤ n × m = S(n - arity nm).
  Proof.
    intro scons.
    induction (status_cons_statusok_cases nm n) as [ [aritynm ok] | [aritynm error] ].
    - rewrite scons in ok.
      apply ii1_injectivity in ok.
      exact (aritynm ,, ok).
    - rewrite scons in error.
      apply negpathsii1ii2 in error.
      contradiction.
  Defined.

  Lemma status_cons_arith {n1 n2 n3: nat}: n3 ≤ n2 → n1 = S (n2 - n3) → n2 = n1 + n3 -1.
  Proof.
    intros hp valn1.
    change (S (n2 - n3)) with (1 + (n2 - n3)) in valn1.
    rewrite natplusminusle in valn1.
    - apply nat_movesubleft in valn1.
      + replace (1+n2) with (n2+1) in valn1 by (rewrite natpluscomm; reflexivity).
        apply nat_movaddleft in valn1.
        apply pathsinv0.
        assumption.
      + rewrite natpluscomm.
        apply natleh_add.
        assumption.
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
    - induction (status_cons_statusok_cases nm a) as [ [aritynm ok] | [aritynm error] ].
      + exists a.
        exact (aritynm ,, idpath _).
      + contradiction.
    - contradiction.
  Defined.

  Lemma status_cons_noerror2_r {nm: names sigma} {status: Status}:
    status_cons nm status != statuserror → status != statuserror.
  Proof.
    apply negf.
    intro status_err.
    rewrite status_err.
    reflexivity.
  Defined.

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
    change inl with statusok.
    induction (status_cons_statusok_cases nm a1) as [ [aritynm ok] | [aritynm error] ].
    - rewrite ok.
      cbn [status_concatenate statusok coprod_rect].
      induction (status_cons_statusok_cases nm (a1+a2)) as [ [aritynm2 ok2] | [aritynm2 error2] ].
      + rewrite ok2.
        apply maponpaths.
        apply (maponpaths S).
        apply natleh_adddiff.
        assumption.
      + apply fromempty.
        apply aritynm2.
        apply natleh_add.
        assumption.
    - contradiction.
  Defined.

End Status.

Section Stack.

  Definition list2status {sigma: Signature} (l: list (names sigma)): Status
    := foldr status_cons (statusok 0) l.

  Definition Stack (sigma: Signature) (n: nat)
    : UU := ∑ s: list (names sigma), list2status s = statusok n.

  Lemma Stack_isaset (sigma: Signature) (n: nat): isaset (Stack sigma n).
  Proof.
    apply isaset_total2.
    - apply isofhlevellist.
      exact (pr2 (names sigma)).
    - intros.
      apply isasetaprop.
      apply Status_isaset.
  Defined.

  Definition mkstack {sigma: Signature} {n: nat} (s: list (names sigma))
             (proofs: list2status s = statusok n)
    : Stack sigma n := s ,, proofs.

  Coercion stack2list {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list (names sigma) := pr1 s.

  Definition stack2proof {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list2status s = statusok n := pr2 s.

  Definition stack_nil (sigma: Signature): Stack sigma 0 := stnpr nil.

  Lemma stack_extens {sigma : Signature} {n: nat} {s1 s2 : Stack sigma n}
        (p : stack2list s1 = stack2list s2)
    : s1 = s2.
  Proof.
    apply subtypePath.
    2: exact p.
    intros s.
    apply Status_isaset.
  Defined.

  Definition Term (sigma: Signature): UU := Stack sigma 1.

  Coercion term2list {sigma: Signature} (t: Term sigma): list (names sigma) := pr1 t.

  Definition Term_hset (sigma : Signature): hSet := make_hSet (Term sigma) (Stack_isaset sigma 1).

End Stack.

Section StackOps.

  Context {sigma: Signature}.

  Lemma list2status_cons {nm: names sigma} {l: list (names sigma)}:
    list2status (cons nm l) = status_cons nm (list2status l).
  Proof.
    reflexivity.
  Defined.

  Lemma stack_zero (s: Stack sigma 0): s = stack_nil sigma.
  Proof.
    induction s as [[len vec] proof].
    induction len.
    - induction vec.
      apply stack_extens.
      reflexivity.
    - apply fromempty.
      change (S len,, vec) with (cons (hd vec) (len ,, tl vec)) in proof.
      rewrite list2status_cons in proof.
      apply status_cons_statusok_r in proof.
      apply pr1 in proof.
      apply isirreflnatgth in proof.
      assumption.
  Defined.

  Lemma stack_positive {n: nat} (s: Stack sigma (S n)):
    ∑ (lentail: nat) (v: Vector (names sigma) (S lentail)),
    stack2list s = cons (hd v) (lentail ,, tl v).
  Proof.
    induction s as [[len vec] s_is_stack].
    induction len.
    - induction vec.
      apply fromempty.
      apply ii1_injectivity in s_is_stack.
      apply negpaths0sx in s_is_stack.
      assumption.
    - exists len.
      exists vec.
      apply idpath.
  Defined.

  Definition stack_hd {n: nat} (s: Stack sigma (S n)): names sigma.
  Proof.
    set (s_struct := stack_positive s).
    induction s_struct as [lentail [v _]].
    exact (hd v).
  Defined.

  Lemma list2status_concatenate {l1 l2: list (names sigma)}:
    list2status l1 != statuserror →
    status_concatenate (list2status l1) (list2status l2) = list2status (concatenate l1 l2).
  Proof.
    apply (list_ind (λ s, list2status s != statuserror →
                          status_concatenate (list2status s) (list2status l2)
                          = list2status (concatenate s l2))).
    - intros.
      change (list2status (concatenate nil l2)) with (list2status l2).
      induction (list2status l2) as [okl2 | badl2].
      + reflexivity.
      + induction badl2.
        reflexivity.
    - intros nm l1tail IH noerror.
      rewrite list2status_cons.
      rewrite status_concatenate_statuscons by (assumption).
      rewrite IH.
      + rewrite <- list2status_cons.
        reflexivity.
      + apply (status_cons_noerror2_r(nm:=nm)).
        assumption.
  Defined.

  Lemma list2status_concatenate2 {l1 l2: list (names sigma)} {n1 n2: nat}
        (proof1: list2status l1 = statusok n1) (proof2: list2status l2 = statusok n2)
    : list2status (concatenate l1 l2) = statusok (n1 + n2).
  Proof.
    apply pathsinv0.
    change (statusok (n1 + n2)) with (status_concatenate (statusok n1) (statusok n2)).
    rewrite <- proof1.
    rewrite <- proof2.
    apply list2status_concatenate.
    intro l1error.
    rewrite proof1 in l1error.
    apply negpathsii1ii2 in l1error.
    assumption.
  Defined.

  Local Lemma is_stack_concatenate  {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : list2status (concatenate s1 s2) = statusok ( n1 + n2 ).
  Proof.
    rewrite <- list2status_concatenate.
    - rewrite (stack2proof s1).
      rewrite (stack2proof s2).
      reflexivity.
    - rewrite (stack2proof s1).
      apply negpathsii1ii2.
  Defined.

  Definition stack_concatenate {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : Stack sigma (n1 + n2) := mkstack (concatenate s1 s2) (is_stack_concatenate s1 s2).

End StackOps.

Section Term.

  Context {sigma: Signature}.

  Definition terms2stack_list {n: nat} (vec: Vector (list (names sigma)) n): list (names sigma)
    := vector_foldr concatenate nil vec.

  Lemma terms2stack_list_vcons {l: list (names sigma)} {n: nat} {v: Vector (list (names sigma)) n}:
    terms2stack_list (vcons l v) = concatenate l (terms2stack_list v).
  Proof.
    reflexivity.
  Defined.

  Definition terms2stack {n: nat} (vec: Vector (Term sigma) n): Stack sigma n.
  Proof.
    exists (terms2stack_list (vector_map stack2list vec)).
    induction n.
    - reflexivity.
    - simpl.
      rewrite (list2status_concatenate2(n1:= 1)(n2:=n)).
      * reflexivity.
      * exact (stack2proof (hd vec)).
      * exact (IHn (tl vec)).
  Defined.

  Lemma terms2stack_vcons {t: Term sigma} {n: nat} {v: Vector (Term sigma) n}:
    terms2stack (vcons t v) = stack_concatenate t (terms2stack v).
  Proof.
    apply stack_extens.
    simpl.
    reflexivity.
  Defined.

  Definition term_op_list (nm: names sigma) {n: nat} (vec: Vector (list (names sigma)) n)
    : list (names sigma) := cons nm (terms2stack_list vec).

  Definition term_op (nm: names sigma) (vec: Vector (Term sigma) (arity nm)): Term sigma.
  Proof.
    exists (cons nm (terms2stack vec)).
    change (terms2stack_list (vector_map stack2list vec)) with (stack2list (terms2stack vec)).
    rewrite list2status_cons.
    rewrite (stack2proof (terms2stack vec)).
    rewrite status_cons_statusok_f.
    - rewrite minuseq0'.
      apply idpath.
    - apply isreflnatleh.
  Defined.

  Definition princ_op (t: Term sigma): names sigma := stack_hd t.

  Definition extract_substack_list (l: list (names sigma)) (n: nat):
    list (names sigma) × list (names sigma).
  Proof.
    apply (list_ind (λ l: list (names sigma),
                         ∏ (n : nat), list (names sigma) × list (names sigma))).
    - clear n.
      intros.
      exact (nil ,, nil).
    - clear n.
      intros x xs HPind n.
      induction n.
      + exact (nil ,, (cons x xs)).
      + set (resind := HPind (n + arity x)).
        exact (cons x (pr1 resind) ,, pr2 resind).
    - exact l.
    - exact n.
  Defined.

  Lemma extract_substack_list_zero (l: list (names sigma)):
    extract_substack_list l 0 = nil,, l.
  Proof.
    apply (list_ind (λ l: list (names sigma), extract_substack_list l 0 = nil,, l)).
    - reflexivity.
    - reflexivity.
  Defined.

  Lemma extract_substack_list_cons {x: names sigma} {xs: list (names sigma)} {n: nat}:
    extract_substack_list (cons x xs) (S n) =
    cons x (pr1 (extract_substack_list xs (n + arity x))) ,,
         (pr2 (extract_substack_list xs (n + arity x))).
  Proof.
    reflexivity.
  Defined.

  Lemma extract_substack_list_arith1 {n1 n2: nat}: S n1 + n2 - 1 = n1 + n2.
  Proof.
    change (S n1) with (1+n1).
    rewrite natplusassoc.
    rewrite (natpluscomm 1 (n1 + n2)).
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Lemma extract_substack_list_norest (l: list (names sigma)) {n: nat}
    :  list2status l = statusok n →  extract_substack_list l n = l ,, nil.
  Proof.
    generalize l n.
    apply (list_ind (λ l: list (names sigma),
                          ∏ (n : nat),  list2status l = statusok n →
                                        extract_substack_list l n = l,, nil)).
    - clear l n.
      intros n proofl.
      cbn in proofl.
      apply ii1_injectivity in proofl.
      rewrite <- proofl.
      reflexivity.
    - clear l n.
      intros x xs HPind n proofxxs.
      rewrite list2status_cons in proofxxs.
      apply status_cons_statusok_r in proofxxs.
      induction proofxxs as [nbound proofxs].
      induction n.
      + apply isirreflnatgth in nbound.
        contradiction.
      + rewrite extract_substack_list_cons.
        rewrite extract_substack_list_arith1 in proofxs.
        set (ind := HPind (n + arity x) proofxs).
        rewrite ind.
        reflexivity.
  Defined.

  Lemma extract_substack_list_concatenate (l1: list (names sigma)) {n1: nat}
        (l2: list (names sigma)) (n: nat)
    :  list2status l1 = statusok n1 → n ≤ n1 →
       extract_substack_list (concatenate l1 l2) n =
       (pr1 (extract_substack_list l1 n)) ,,
                                          concatenate (pr2 (extract_substack_list l1 n)) l2.
  Proof.
    generalize l1 n1 n.
    apply (list_ind (λ l1 : list (names sigma),
                     ∏ (n1 n: nat),
                     list2status l1 = statusok n1 → n ≤ n1
                     → extract_substack_list (concatenate l1 l2) n =
                       pr1 (extract_substack_list l1 n),,
                           concatenate (pr2 (extract_substack_list l1 n)) l2)).
    - clear l1 n1 n.
      intros n1 n proofl1 nlehn1.
      cbn in proofl1.
      apply ii1_injectivity in proofl1.
      rewrite <- proofl1 in *.
      apply natleh0tois0 in nlehn1.
      rewrite nlehn1.
      simpl.
      rewrite extract_substack_list_zero.
      reflexivity.
    - clear l1 n1 n.
      intros x xs HPind n1 n proofl1 nlehn1.
      change (concatenate (cons x xs) l2) with (cons x (concatenate xs l2)).
      induction n.
      + rewrite extract_substack_list_zero.
        reflexivity.
      + rewrite list2status_cons in proofl1.
        apply status_cons_statusok_r in proofl1.
        induction proofl1 as [n1gt0 proofxs].
        assert (newnok: S n + arity x - 1 ≤ n1 + arity x - 1).
        {
          apply natlehandminusl, natlehandplusr.
          assumption.
        }
        set (ind := HPind (n1 + arity x - 1) (S n + arity x - 1) proofxs newnok).
        assert (X: S n + arity x - 1 = n + arity x).
        {
          change (S n) with (1+n).
          rewrite natplusassoc.
          rewrite (natpluscomm 1 (n+arity x)).
          rewrite plusminusnmm.
          apply idpath.
        }
        rewrite X in ind.
        do 2 rewrite extract_substack_list_cons.
        apply pathsdirprod.
        * apply (maponpaths (λ xs, cons x xs)).
          apply (maponpaths pr1) in ind.
          cbn in ind.
          assumption.
        * apply (maponpaths dirprod_pr2) in ind.
          cbn in ind.
          assumption.
  Defined.

  Definition extract_sublist (l: list (names sigma)) (m n: nat):
    list2status l = statusok m → n ≤ m  →
    ∑ first second: list (names sigma),
                    list2status first = statusok n ×
                    list2status second = statusok (m - n) ×
                    concatenate first second = l.
  Proof.
    set (res := (extract_substack_list l n)).
    intros proofl nlehm.
    exists (pr1 res).
    exists (pr2 res).
    apply (list_ind (λ l : list (names sigma), ∏ (m n: nat),
        list2status l = statusok m → n ≤ m  →
        list2status (pr1 (extract_substack_list l n)) = statusok n ×
        list2status (pr2 (extract_substack_list l n)) = statusok (m - n) ×
        concatenate (pr1 (extract_substack_list l n)) (pr2 (extract_substack_list l n)) = l)).
    - clear l m n res proofl nlehm.
      intros m n proofnil nlehm.
      cbn.
      apply ii1_injectivity in proofnil.
      rewrite <- proofnil in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      repeat split.
    - clear l m n res proofl nlehm.
      intros x xs HPind m n proofxxs nlehm.
      induction n.
      + change (extract_substack_list (cons x xs) 0)
          with (make_dirprod (nil(A:=names sigma)) (cons x xs)).
        rewrite natminuseqn.
        repeat split.
        assumption.
      + clear IHn.
        change (extract_substack_list (cons x xs) (S n))
          with (make_dirprod (cons x (pr1 (extract_substack_list xs (n + arity x))))
                            (pr2 (extract_substack_list xs (n + arity x)))).
        simpl.
        rewrite list2status_cons in proofxxs.
        apply status_cons_statusok_r in proofxxs.
        apply dirprod_pr2 in proofxxs.
        assert (arityind: n + arity x ≤ m + arity x - 1).
        {
          apply (natlehandplusr  _ _  (arity x)) in nlehm.
          apply (natlehandminusl _ _  1) in nlehm.
          change (S n) with (1 + n) in nlehm.
          rewrite natplusassoc in nlehm.
          rewrite natpluscomm in nlehm.
          rewrite plusminusnmm in nlehm.
          assumption.
        }
        set (ind := HPind (m + arity x - 1) (n + arity x) proofxxs arityind).
        repeat split.
        * simpl.
          rewrite list2status_cons.
          rewrite (pr1 ind).
          rewrite status_cons_statusok_f.
          -- apply (maponpaths statusok).
             rewrite plusminusnmm.
             apply idpath.
          -- rewrite natpluscomm.
             apply natleh_add.
             apply isreflnatleh.
        * rewrite (pr1 (pr2 ind)).
          apply (maponpaths statusok).
          rewrite natminusminus.
          rewrite <- natplusassoc.
          rewrite (natpluscomm (1+n) (arity x)).
          rewrite <- natminusminus.
          rewrite plusminusnmm.
          apply idpath.
        * change (concatenate (cons x (pr1 (extract_substack_list xs (n + arity x))))
                              (pr2 (extract_substack_list xs (n + arity x))))
            with (cons x (concatenate (pr1 (extract_substack_list xs (n + arity x)))
                              (pr2 (extract_substack_list xs (n + arity x))))).
          rewrite (pr2 (pr2 ind)).
          apply idpath.
    - assumption.
    - assumption.
  Defined.

  Definition extract_substack {m: nat} (s: Stack sigma m) (n: nat):
    n ≤ m  → ∑ (first: Stack sigma n) (second: Stack sigma (m - n)),
    concatenate first second = s.
  Proof.
    intro n_leq_m.
    set (res := extract_sublist s m n (stack2proof s) n_leq_m).
    induction res as [fsupp [ssupp [fproof [sproof concproof]]]].
    exists (mkstack fsupp fproof).
    exists (mkstack ssupp sproof).
    assumption.
  Defined.

  Definition extract_term {n: nat} (s: Stack sigma (S n)):
    ∑ (term: Term sigma) (rest: Stack sigma n), stack_concatenate term rest = s.
  Proof.
    set (rest := extract_sublist s (S n) 1 (stack2proof s) (natleh0n n)).
    induction rest as [fsupp [ssupp [fproof [sproof conc]]]].
    exists (mkstack fsupp fproof).
    change (S n) with (1 + n) in sproof.
    rewrite natpluscomm in sproof.
    rewrite plusminusnmm in sproof.
    exists (mkstack ssupp sproof).
    apply stack_extens.
    assumption.
  Defined.

  Definition stack_first_list (l: list (names sigma)): list (names sigma)
    := dirprod_pr1 (extract_substack_list l 1).

  Definition stack_rest_list (l: list (names sigma)): list (names sigma)
    := dirprod_pr2 (extract_substack_list l 1).

  Definition stack_first {n: nat} (s: Stack sigma (S n)): Term sigma.
  Proof.
    set (res := extract_sublist s (S n) 1 (stack2proof s) (natleh0n n)).
    induction res as [first [second [prooff _]]].
    exists first.
    exact prooff.
  Defined.

  Definition stack_rest {n: nat} (s: Stack sigma (S n)): Stack sigma n.
  Proof.
    set (res := extract_sublist s (S n) 1 (stack2proof s) (natleh0n n)).
    induction res as [first [second [prooff [secondf _]]]].
    exists (second).
    rewrite secondf.
    apply (maponpaths statusok).
    change (S n) with (1 + n).
    rewrite natpluscomm.
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Lemma stack_concatenate_normalize1 {n: nat} (s: Stack sigma (S n))
    : stack_concatenate (stack_first s) (stack_rest s) = s.
  Proof.
    set (res := extract_sublist s (S n) 1 (stack2proof s) (natleh0n n)).
    apply stack_extens.
    simpl.
    change (pr1 (extract_substack_list s 1)) with (pr1 res).
    change (pr2 (extract_substack_list s 1)) with (pr1 (pr2 res)).
    induction res as [first [second [prooff [secondf conc]]]].
    exact conc.
  Defined.

  Lemma stack_concatenate_normalize2 (t: Term sigma) {n2: nat} (s2: Stack sigma n2)
    : stack_first (stack_concatenate t s2) = stack_first t.
  Proof.
    apply stack_extens.
    simpl.
    set (res := extract_substack_list_concatenate t  s2 1 (stack2proof t) (natleh0n 0)).
    apply (maponpaths pr1) in res.
    assumption.
  Defined.

  Lemma stack_concatenate_normalize3 (t: Term sigma) {n2: nat} (s2: Stack sigma n2)
    : stack_rest (stack_concatenate t s2) = s2.
  Proof.
    apply stack_extens.
    simpl.
    set (res := extract_substack_list_concatenate t s2 1 (stack2proof t) (natleh0n 0)).
    apply (maponpaths dirprod_pr2) in res.
    simpl in res.
    replace (pr2 (extract_substack_list t 1)) with (nil(A:=names sigma)) in res.
    - assumption.
    - rewrite extract_substack_list_norest.
      + reflexivity.
      + exact (stack2proof t).
  Defined.

  Lemma stack_first_term {t: Term sigma}: stack_first t = t.
  Proof.
    apply stack_extens.
    simpl.
    rewrite extract_substack_list_norest.
    - reflexivity.
    - exact (stack2proof t).
  Defined.

  Lemma stack_concatenate_normalize_arith (m n: nat): n = m + n - m .
  Proof.
    rewrite natpluscomm.
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Definition stack2terms {n: nat} (s: Stack sigma n): Vector (Term sigma) n.
  Proof.
    induction n.
    - exact vnil.
    - exact (vcons (stack_first s) (IHn (stack_rest s))).
  Defined.

  Lemma stack2terms_concat {t: Term sigma} {n: nat} (s2: Stack sigma n):
    stack2terms (stack_concatenate t s2) = vcons t (stack2terms s2).
  Proof.
    change (stack2terms (stack_concatenate t s2))
      with (vcons (stack_first (stack_concatenate t s2)) (stack2terms (stack_rest (stack_concatenate t s2)))).
    rewrite stack_concatenate_normalize2.
    rewrite stack_concatenate_normalize3.
    rewrite stack_first_term.
    apply idpath.
  Defined.

(*
  Lemma stack2terms_el {n: nat} {s: Stack sigma n} {i:  ⟦ n ⟧}:
    term2list (el (stack2terms s) i) = pr1 (extract_substack_list (pr2 (extract_substack_list s i)) 1).
  Proof.
    generalize s.
    induction i as [i ilessn].
    induction i.
    - induction n.
      + apply fromempty.
        apply isirreflnatlth in ilessn.
        assumption.
      + intros.
        rewrite extract_substack_list_zero.
        change (pr1 (extract_substack_list (pr2 (nil,, stack2list s)) 1))
          with (stack2list (stack_first s)).
        reflexivity.
    - induction n.
      + apply fromempty.
        apply (negnatlehsn0 i) in ilessn.
        assumption.
      + set (ind := IHi (

      change (el (stack2terms s) (S i,, ilessn)) with (hd


      reflexivity.
      cbn
      cbn.
      change (pr2 (extract_substack_list (stack2list s) 0)) with (stack2list s).
*)

  Lemma length_cons {A: UU} (x: A) (xs: list A):
    length (cons x xs) = S(length xs).
  Proof.
    reflexivity.
  Defined.

  Lemma length_concatenate (l1: list (names sigma)) (l2: list (names sigma)) :
    length (concatenate l1 l2) = length l1+ length l2.
  Proof.
    induction l1 as [len1 vec1].
    induction len1.
    - induction vec1.
      reflexivity.
    - change (concatenate (S len1,, vec1) l2)
        with (cons (hd vec1) (concatenate (len1  ,, tl vec1) l2)).
      rewrite length_cons.
      set (ind := IHlen1 (tl vec1)).
      change (length (S len1,, vec1)) with (S len1).
      change (length (len1,, tl vec1)) with len1 in ind.
      change (S len1 + length l2) with (S(len1 + length l2)).
      apply (maponpaths S).
      apply ind.
  Defined.

  Lemma length_terms2stack_list {n: nat} (s: Vector (list (names sigma)) n):
    ∏ i:  ⟦ n ⟧, length (el s i) ≤ length (terms2stack_list s).
  Proof.
    induction n.
    - intro i.
      induction i as [i iproof].
      apply fromempty.
      apply negnatlthn0 in iproof.
      assumption.
    - induction i as [i iproof].
      induction i.
      + change (terms2stack_list s) with (concatenate (hd s) (terms2stack_list (tl s))).
        change (el s (0,, iproof)) with (hd s).
        rewrite length_concatenate.
        apply natleh_add.
        apply isreflnatleh.
      + set (ind := IHn (tl s) (i,, iproof)).
        assert (X: el (tl s) (i,, iproof) = el s (S i,, iproof)).
        {
          rewrite <- drop_el.
          reflexivity.
        }
        rewrite <- X.
        assert (length (terms2stack_list (tl s)) ≤  length (terms2stack_list s)).
        {
          change s with (vcons (hd s) (tl s)).
          rewrite terms2stack_list_vcons.
          change  (tl (vcons (hd s) (tl s))) with (tl s).
          rewrite length_concatenate.
          rewrite natpluscomm.
          apply natleh_add.
          apply isreflnatleh.
        }
        apply (istransnatleh(m:=length (terms2stack_list (tl s)))).
        * assumption.
        * assumption.
  Defined.

  Lemma length_terms2stack {n: nat} (s: Vector (Term sigma) n):
    ∏ i:  ⟦ n ⟧, length (el s i) ≤ length (terms2stack s).
  Proof.
    intro i.
    change (length (terms2stack s)) with (length (terms2stack_list (vector_map stack2list s))).
    rewrite <- el_vector_map.
    apply length_terms2stack_list.
  Defined.

  Lemma terms2stack2terms {n: nat} (s: Stack sigma n): terms2stack (stack2terms s) = s.
  Proof.
    generalize s.
    induction n.
    - intros.
      rewrite stack_zero.
      apply idpath.
    - clear s.
      intro s.
      replace s with (stack_concatenate (stack_first s) (stack_rest s)).
      2: { rewrite stack_concatenate_normalize1. reflexivity. }
      simpl.
      rewrite stack_concatenate_normalize2.
      rewrite stack_concatenate_normalize3.
      rewrite stack_first_term.
      rewrite terms2stack_vcons.
      apply (maponpaths (λ s', stack_concatenate (stack_first s) s')).
      apply (IHn (stack_rest s)).
  Defined.

  Lemma nil_not_term: list2status(sigma:=sigma) nil != statusok 1.
  Proof.
    cbn.
    intro H.
    apply ii1_injectivity in H.
    apply negpaths0sx in H.
    contradiction.
  Defined.

  Theorem term_ind:
    ∏ (P: Term sigma → UU),
    ( ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (term_op nm vterm) )
    → (∏ t: Term sigma, P t).
  Proof.
    intros P HPind.
    assert (∏ (n vlen: nat) (vlehn: vlen ≤ n) (v: Vector (names sigma) vlen) (lp: list2status (vlen ,, v) = statusok 1), P (mkstack (vlen ,, v) lp)).
    intro n.
    induction n.
    - intros.
      apply fromempty.
      apply natleh0tois0 in vlehn.
      generalize v lp.
      rewrite vlehn.
      intros.
      induction v0.
      apply nil_not_term in lp0.
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

        apply dirprod_pr2 in l.
        rewrite natpluscomm in l.
        rewrite plusminusnmm in l.
        set (terms := stack2terms (mkstack (n ,, tl v) l)).
        assert (struct: mkstack (S n ,, v) lp = term_op (hd v) terms).
        * unfold term_op.
          unfold terms.
          rewrite terms2stack2terms.
          apply stack_extens.
          simpl.
          reflexivity.
        * rewrite struct.
          assert (prevterms: ∏ i: ⟦ arity (hd v) ⟧, P (el terms i)).
          {
            intro i.
            set (sizei:= length_terms2stack terms i).
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
    - intro t.
      induction t as [[lent vect] prooft].
      exact (X lent lent (isreflnatleh _) vect prooft).
  Defined.

  (** Cannot prove this lemma **)

  Lemma term_ind_destruct (nm: names sigma) (v: Vector (Term sigma) (arity nm)):
    ∏ (P: Term sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (term_op nm vterm)),
    term_ind P Ind (term_op nm v) = Ind nm v (λ i:  ⟦ arity nm ⟧, term_ind P Ind (el v i)).
  Proof.
    intros.
  Abort.

  Definition depth (t: Term sigma): nat
    := term_ind ( λ t: Term sigma, nat)
                ( λ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm))
                    (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) )
                t.

  Definition subterm (t: Term sigma): ⟦ arity (princ_op t) ⟧ → Term sigma.
  Proof.
    assert (subterm2: ∏ (s: list (names sigma)) (s_is_term: list2status s = statusok 1),
            ⟦ arity (princ_op (mkstack s s_is_term)) ⟧ → Term sigma).
    2: exact (subterm2 t (stack2proof t)).
    apply (list_ind (λ (s: list (names sigma)),
                     ∏ s_is_term : list2status s = statusok 1,
                                   ⟦ arity (princ_op (mkstack s s_is_term)) ⟧ → Term sigma)).
    - intro.
      apply fromempty.
      apply nil_not_term.
      assumption.
    - intros x tail IH s_is_term.
      cbn.
      intro arx.
      induction arx as [n n_lt_arx].
      rewrite list2status_cons in s_is_term.
      assert (s_ok: status_cons x (list2status tail) != statuserror).
      {
        rewrite s_is_term.
        apply negpathsii1ii2.
      }
      set (tail_ok := status_cons_noerror_r s_ok).
      induction tail_ok as [ tail_ar [tail_ar_bound  tail_status_prf]].
      rewrite tail_status_prf in s_is_term.
      assert ( tail_ar_x: tail_ar = arity x).
      {
        set (X := pr2( status_cons_statusok_fr s_is_term)).
        change (1) with (1+0) in X.
        change (S (tail_ar - arity x)) with (1 + (tail_ar - arity x)) in X.
        set (Y := natpluslcan _ _ _ X).
        set (Z := natdiff0 _ _ Y).
        apply natdiffasymm; assumption.
      }
      rewrite tail_ar_x in tail_status_prf.
      set (n_le_arx := natlthtoleh _ _ n_lt_arx).
      set (remove := extract_sublist tail (arity x) n tail_status_prf n_le_arx).
      induction remove as [first [ second  [ firstss [ secondss conc] ] ] ].
      assert ( extractok2: 1 ≤ arity x - n ).
      {
        apply (natlehandplusrinv _ _ n).
        rewrite minusplusnmm by (assumption).
        rewrite natpluscomm.
        apply natlthtolehp1.
        exact n_lt_arx.
      }
      set (res := extract_sublist second (arity x - n) 1 secondss extractok2).
      induction res as [result [second0 [result_is_term [second_ss conc1]]]].
      exact (mkstack result result_is_term).
  Defined.

End Term.

Section TermAlgebra.

  Definition term_algebra (sigma: Signature): Algebra sigma
    := mkalgebra (Term_hset sigma) term_op.

End TermAlgebra.
