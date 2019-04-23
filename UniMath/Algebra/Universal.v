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

  Definition mk_hom {a1 a2: Algebra sigma} (f: a1 → a2) (f_is_hom: is_hom f)
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
  Qed.

  Lemma idfun_is_hom (a: Algebra sigma): is_hom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    reflexivity.
  Defined.

  Definition hom_id (a: Algebra sigma): a ↦ a := mk_hom (idfun a) (idfun_is_hom a).

  Lemma comp_is_hom  {a1 a2 a3: Algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): is_hom (funcomp h1 h2).
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
    := mk_hom (funcomp h1 h2) (comp_is_hom h1 h2).

End Homomorphisms.

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mkalgebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

  Lemma is_hom_terminalhom {a: Algebra sigma}: is_hom(a2 := terminal_algebra) (λ x: a, tt).
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition terminal_hom (a : Algebra sigma): hom a terminal_algebra
    :=  mk_hom(a2 := terminal_algebra) (λ _: a, tt) is_hom_terminalhom.

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

  Lemma nat_movesubleft {a b c: nat}: c ≤ b → a = b - c  → a + c =b.
  Proof.
    intros hp1 hp2.
    apply (maponpaths  (λ n: nat, n + c)) in hp2.
    rewrite minusplusnmm in hp2 ; assumption.
  Defined.

  Lemma nat_movaddleft {a b c: nat}: a = b + c → a - c = b.
  Proof.
    intros hp.
    apply (maponpaths (λ n: nat, n - c)) in hp.
    rewrite plusminusnmm in hp.
    assumption.
  Defined.

  Lemma natleh_add { n1 n2 m: nat }: n1 ≤ n2 → n1 ≤ n2 + m.
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

  Lemma natleh_adddiff {n1 n2 n3: nat}: n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.
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

  Lemma nat_notgeh1 {n: nat}: ¬ (n ≥ 1) → n = 0.
  Proof.
    intro n_gte_1.
    induction n.
    - apply idpath.
    - apply fromempty.
      apply n_gte_1.
      apply natgthtogehsn.
      apply natgthsn0.
  Defined.

  Lemma nat_notgeh1_inv {n: nat}: n != 0 → n ≥ 1.
  Proof.
    intros.
    apply natgthtogehsn.
    apply natneq0togth0.
    apply nat_nopath_to_neq.
    assumption.
  Defined.

  (*** These axioms probably needs some additional hypotheses ***)

  Axiom natlehandminusl: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natlehandminusr: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natdiff0: ∏ a b: nat, 0 = a - b → b ≥ a.

  Axiom natdiffasymm: ∏ a b: nat, a ≤ b → a ≥ b → a=b.

  Axiom nat_ax: ∏ a b c: nat, a = S (b - c) → b = a + c -1.

  Axiom nat_ax3: ∏ a b c : nat, a + b - 1 - (c + b - 1) = a-c.

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
  Qed.

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
    status_cons nm status = statusok m → status = statusok (m + arity nm - 1).
  Proof.
    intro hp.
    induction status as [n | noerror].
    - apply status_cons_statusok_fr in hp.
      induction hp as [aritynm valm].
      apply (maponpaths inl).
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
  Qed.

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

  Lemma stack_positive {n: nat} (s: Stack sigma (S n)):
    ∑ (lentail: nat) (v: Vector (names sigma) (S lentail)) (proofs: _),
    s = mkstack (cons (hd v) (lentail ,, tl v)) proofs.
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
      exists s_is_stack.
      apply idpath.
  Defined.

  Definition stack_hd {n: nat} (s: Stack sigma (S n)): names sigma.
  Proof.
    set (s_struct := stack_positive s).
    induction s_struct as [lentail [v _]].
    exact (hd v).
  Defined.

  Lemma list2status_compositional {l1 l2: list (names sigma)}:
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

  Lemma is_stack_concatenate  {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : list2status (concatenate s1 s2) = statusok ( n1 + n2 ).
  Proof.
    rewrite <- list2status_compositional.
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

  Definition terms2stack {n: nat} (vec: Vector (Term sigma) n): Stack sigma n.
  Proof.
    induction n.
    - exact (stack_nil sigma).
    - exact (stack_concatenate (hd vec) (IHn (tl vec))).
  Defined.

  Definition term_op (nm: names sigma) (vec: Vector (Term sigma) (arity nm)): Term sigma.
  Proof.
    exists (cons nm (terms2stack vec)).
    rewrite list2status_cons.
    rewrite (stack2proof (terms2stack vec)).
    rewrite status_cons_statusok_f.
    - rewrite minuseq0'.
      apply idpath.
    - apply isreflnatleh.
  Defined.

  Definition princ_op (t: Term sigma): names sigma := stack_hd t.

  Lemma stack_arith1 {n m: nat}: n > 0 → m ≤ n + m - 1.
  Proof.
    intro.
    rewrite natpluscomm.
    rewrite <- natplusminusle.
    - apply natlehnplusnm.
    - assumption.
  Defined.

  Lemma stack_arith2 {n m: nat}: n > 0 → S(n + m - 1 - m) = n.
  Proof.
    intro.
    rewrite natminusminus.
    rewrite (natpluscomm 1 m).
    rewrite <- natminusminus.
    rewrite plusminusnmm.
    change (S (n - 1)) with (1 + (n - 1)).
    rewrite natplusminusle by (assumption).
    rewrite natpluscomm.
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Definition extract_sublist (s: list (names sigma)):
    ∏ n m: nat, list2status s = statusok m → n ≤ m  →
                ∑ first second: list (names sigma),
                                list2status first = statusok n ×
                                list2status second = statusok (m - n) ×
                                concatenate first second = s.
  Proof.
    apply (list_ind (λ s : list (names sigma), ∏ n m: nat, list2status s = statusok m → n ≤ m →
                     ∑ first second: list (names sigma), list2status first = statusok n ×
                                                         list2status second = statusok (m - n) ×
                                                         concatenate first second = s)).
    - intros n m s_status.
      cbn in s_status.
      apply ii1_injectivity in s_status.
      rewrite <- s_status.
      intro n_leh_0.
      apply nat0gehtois0 in n_leh_0.
      rewrite n_leh_0.
      exists nil.
      exists nil.
      do 2 ( split; try reflexivity ).
    - intros nm tail IH n m s_status m_geh_n.
      induction (isdeceqnat n 0) as [n_is_0 | n_gt_0].
      + rewrite n_is_0.
        exists nil.
        exists (cons nm tail).
        split.
        2: split.
        * apply idpath.
        * rewrite natminuseqn.
          assumption.
        * apply idpath.
      + apply nat_notgeh1_inv in n_gt_0.
        rewrite list2status_cons in s_status.
        assert ( tail_ok: ∑ tail_ar: nat, arity nm ≤ tail_ar ×
                                                list2status tail = statusok tail_ar ).
        {
          apply status_cons_noerror_r.
          rewrite s_status.
          apply negpathsii1ii2.
        }
        induction tail_ok as [ tail_ar [ tail_ar_bound tail_status_prf]].
        rewrite tail_status_prf in s_status.
        apply status_cons_statusok_fr in s_status.
        induction s_status as [aritynm valm].
        apply nat_ax in valm.
        assert (tail_ar_newbound: n + arity nm - 1 ≤ tail_ar).
        {
          abstract
            (rewrite valm;
             apply natlehandminusl;
             apply natlehandplus;
             [ assumption |
               apply isreflnatleh ]).
        }
        set (IH1 := IH (n + arity nm - 1) tail_ar tail_status_prf tail_ar_newbound).
        induction IH1 as [fst [snd [status_fst_prf [status_snd_prf conc]]]].
        rewrite valm in status_snd_prf.
        rewrite nat_ax3 in status_snd_prf.
        set (realfirst := cons nm fst).
        assert (list2status realfirst = statusok n).
        {
          unfold realfirst.
          rewrite list2status_cons.
          rewrite status_fst_prf.
          rewrite status_cons_statusok_f.
          * rewrite stack_arith2 by (assumption).
            apply idpath.
          * apply stack_arith1.
            assumption.
        }
        exists realfirst.
        exists snd.
        do 2 ( split ; try assumption ).
        unfold realfirst.
        rewrite concatenateStep.
        rewrite conc.
        apply idpath.
  Defined.

  Definition extract_substack {m: nat} (s: Stack sigma m) (n: nat):
    n ≤ m  → ∑ (first: Stack sigma n) (second: Stack sigma (m - n)),
    concatenate first second = s.
  Proof.
    intro n_leq_m.
    set (res := extract_sublist s n m (stack2proof s) n_leq_m).
    induction res as [fsupp [ssupp [fproof [sproof concproof]]]].
    exists (mkstack fsupp fproof).
    exists (mkstack ssupp sproof).
    assumption.
  Defined.

  Lemma nil_not_term: list2status(sigma:=sigma) nil != statusok 1.
  Proof.
    cbn.
    intro H.
    apply ii1_injectivity in H.
    apply negpaths0sx in H.
    contradiction.
  Defined.

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
      set (remove := extract_sublist tail n (arity x) tail_status_prf n_le_arx).
      induction remove as [first [ second  [ firstss [ secondss conc] ] ] ].
      assert ( extractok2: 1 ≤ arity x - n ).
      {
        apply (natlehandplusrinv _ _ n).
        rewrite minusplusnmm by (assumption).
        rewrite natpluscomm.
        apply natlthtolehp1.
        exact n_lt_arx.
      }
      set (res := extract_sublist second 1 (arity x - n) secondss extractok2).
      induction res as [result [second0 [result_is_term [second_ss conc1]]]].
      exact (mkstack result result_is_term).
  Defined.

  Definition term_ind: UU :=
    ∏ (P: Term sigma → UU),
    ( ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (term_op nm vterm) )
    → (∏ t: Term sigma, P t).

End Term.

Section TermAlgebra.

  Definition term_algebra (sigma: Signature): Algebra sigma
    := mkalgebra (Term_hset sigma) term_op.

End TermAlgebra.
