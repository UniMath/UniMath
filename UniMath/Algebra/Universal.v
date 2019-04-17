(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.

(** Basic definitions **)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names (sigma: Signature): hSet := pr1 sigma.

Definition arity {sigma: Signature} (nm: names sigma): Arity := pr2 sigma nm.

Definition mk_signature {n: nat} (v: Vector nat n): Signature := (stnset n,, el v).

Definition Algebra (sigma: Signature): UU
  := ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

Coercion support {sigma: Signature} (a: Algebra sigma): hSet := pr1 a.

Definition dom {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
  := Vector (support a) (arity nm).

Definition cod {sigma: Signature} (a: Algebra sigma) (nm: names sigma): UU
  := support a.

Definition op {sigma: Signature} (a: Algebra sigma) (nm: names sigma): (dom a nm) → (cod a nm)
  := pr2 a nm.

Definition mk_algebra {sigma : Signature} (support : hSet)
           (ops: ∏ nm: names sigma, Vector support (arity nm) → support) : Algebra sigma
  := (support,, ops).

(** Algebra homomorphism **)

Section Homomorphisms.

  Context { sigma: Signature }.

  Definition is_hom {a1 a2: Algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition hom (a1 a2: Algebra sigma): UU :=  ∑ (f: a1 → a2), is_hom f.

  Local Notation "a1 ↦ a2" := (hom a1 a2)  (at level 80, right associativity).

  Definition hom2fun {a1 a2: Algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2proof {a1 a2: Algebra sigma} (f: a1 ↦ a2): is_hom f := pr2 f.

  Definition mk_hom {a1 a2: Algebra sigma} (f: a1 → a2) (f_is_hom: is_hom f): hom a1 a2 := f ,, f_is_hom.

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

(** Terminal algebra **)

Section TerminalAlgebra.

  Context { sigma: Signature }.

  Definition terminal_algebra: Algebra sigma
    := mk_algebra unitset (λ nm: names sigma, (λ u: Vector unit (arity nm), tt)).

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

(** Terms **)

Section Terms.

  Definition Status: UU := nat ⨿ unit.

  Lemma Status_isaset: isaset Status.
  Proof.
    apply isasetcoprod.
    - apply isasetnat.
    - apply isasetunit.
  Qed.

  Definition stackok n: Status := ii1 n.

  Definition stackerror: Status := ii2 tt.

  Definition status_cons {sigma: Signature} (nm: names sigma) (status: Status): Status.
  Proof.
    induction status as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (stackok ( S(n - arity nm) ) ).
      + exact stackerror.
    - exact stackerror.
  Defined.

  Definition list2status {sigma: Signature} (l: list (names sigma)): Status
    := foldr status_cons (stackok 0) l.

  Definition Stack (sigma: Signature) (n: nat)
    : UU := ∑ s: list (names sigma), list2status s = stackok n.

  Lemma Stack_isaset (sigma: Signature) (n: nat): isaset (Stack sigma n).
  Proof.
    apply isaset_total2.
    - apply isofhlevellist.
      exact (pr2 (names sigma)).
    - intros.
      apply isasetaprop.
      apply Status_isaset.
  Qed.

  Definition mk_stack {sigma: Signature} (n: nat) (s: list (names sigma))
             (proofs: list2status s = stackok n)
    : Stack sigma n := s ,, proofs.

  Coercion stack2list {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list (names sigma) := pr1 s.

  Definition stack2proof {sigma: Signature} {n: nat} (s: Stack sigma n)
    : list2status s = stackok n := pr2 s.

  Lemma stack_extens {sigma : Signature} {n} {s1 s2 : Stack sigma n}
        (p : stack2list s1 = stack2list s2)
    : s1 = s2.
  Proof.
    apply subtypePath.
    2: exact p.
    intros s.
    apply Status_isaset.
  Defined.

  Lemma empty_status (sigma: Signature): list2status(sigma := sigma) nil = stackok 0.
  Proof.
    exact (idpath _).
  Defined.

  Definition stack_empty (sigma: Signature): Stack sigma 0 := nil ,, (empty_status sigma).

  Definition Term (sigma: Signature): UU := Stack sigma 1.

  Coercion term2list {sigma: Signature}
    : Term sigma → list (names sigma) := pr1.

  Definition Term_hset (sigma : Signature): hSet := make_hSet (Term sigma) (Stack_isaset sigma 1).

End Terms.

Section TermAlgebra.

  Context {sigma: Signature}.

  Definition status_concatenate (status1 status2: Status): Status.
  Proof.
    induction status2 as [len_s2 | error2].
    - induction status1 as [len_s1 | error1].
      + exact (stackok (len_s1 + len_s2)).
      + exact stackerror.
    - exact stackerror.
  Defined.

  Lemma list2status_cons {nm: names sigma} {l: list (names sigma)}:
    list2status (cons nm l) = status_cons nm (list2status l).
  Proof.
    reflexivity.
  Defined.

  Lemma is_stack_cons (nm: names sigma) {n: nat} (s: Stack sigma n) (p: arity nm ≤ n)
    : list2status (cons nm s) = stackok ( S (n - arity nm) ) .
  Proof.
    rewrite list2status_cons.
    rewrite (stack2proof s).
    cbn [stackok status_cons coprod_rect].
    induction (isdecrelnatleh (arity nm) n).
    - cbn; reflexivity.
    - contradiction.
  Defined.

  Definition stack_cons (nm: names sigma) {n: nat} (s: Stack sigma n) (p: arity nm ≤ n)
    : Stack sigma (S(n - arity nm)) := mk_stack ( S (n - arity nm)) (cons nm s) (is_stack_cons nm s p).

  Lemma status_cons_stackok {nm: names sigma} {n: nat}:
    status_cons nm (stackok n) != stackerror →  arity nm ≤ n.
  Proof.
    intro noerror.
    cbn [stackok status_cons coprod_rect] in noerror.
    induction (isdecrelnatleh (arity nm) n).
    - assumption.
    - cbn in noerror.
      contradiction.
 Defined.

  Lemma status_cons_stackok2 {nm: names sigma} {n: nat} {m: nat}:
    status_cons nm (stackok n) = stackok m → m = S(n - arity nm).
  Proof.
    intro scons.
    cbn [stackok status_cons coprod_rect] in scons.
    induction (isdecrelnatleh (arity nm) n).
    * cbn in scons.
      apply ii1_injectivity in scons.
      apply pathsinv0.
      assumption.
    * cbn in scons.
      apply negpathsii2ii1 in scons.
      contradiction.
  Defined.

  Lemma status_cons_noerror {nm: names sigma} {status: Status}:
    status_cons nm status != stackerror → ∑ n: nat, status = stackok n × arity nm ≤ n.
  Proof.
    intro noerror.
    induction status.
    - exists a.
      split.
      + apply idpath.
      + apply status_cons_stackok. assumption.
    - contradiction.
  Defined.

  Lemma status_cons_noerror2 {nm: names sigma} {status: Status}:
    status_cons nm status != stackerror → status != stackerror.
  Proof.
    apply negf.
    intro status_err.
    rewrite status_err.
    reflexivity.
  Defined.

  Lemma natleh_add: ∏( n1 n2 m: nat), n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    apply (istransnatleh(m:=n2)).
    - assumption.
    - apply natlehnplusnm.
  Defined.

  (** Forward chaining variant
  Lemma natleh_add: ∏( n1 n2 m: nat), n1 ≤ n2 → n1 ≤ n2 + m.
  Proof.
    intros.
    set (H := natlehnplusnm n2 m).
    exact (istransnatleh X H).
  Defined.
  **)

  (** to be proved later ***)
  Axiom natleh_adddiff: ∏(n1 n2 n3: nat), n3 ≤ n1 → n1 - n3 + n2 = n1 + n2 - n3.

  Lemma status_concatenate_statuscons {nm: names sigma} {status1 status2: Status}:
    (status_cons nm status1 != stackerror) →
    status_concatenate (status_cons nm status1) status2
    = status_cons nm (status_concatenate status1 status2).
  Proof.
    induction status1 as [a1 | error1].
    2: contradiction.
    induction status2 as [a2 | error2].
    2: reflexivity.
    intro noerror.
    cbn [status_concatenate status_cons stackok stackerror coprod_rect].
    induction (isdecrelnatleh (arity nm) a1).
    - cbn [stackok coprod_rect].
      induction (isdecrelnatleh (arity nm) (a1 + a2)) as [okarity | badarity].
      + cbn.
        apply maponpaths.
        abstract
          (apply (maponpaths S);
           apply natleh_adddiff;
           assumption).
      + apply fromempty.
        abstract
          (apply badarity, natleh_add;
           assumption).
    - apply fromempty, b.
      apply status_cons_stackok; assumption.
  Defined.

  Lemma list2status_compositional {l1 l2: list (names sigma)}:
    list2status l1 != stackerror →
    status_concatenate (list2status l1) (list2status l2) = list2status (concatenate l1 l2).
  Proof.
    apply (list_ind (λ s, list2status s != stackerror →
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
      + apply (status_cons_noerror2(nm:=nm)).
        assumption.
  Defined.

  Lemma is_stack_concatenate  {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : list2status (concatenate s1 s2) = stackok ( n1 + n2 ).
  Proof.
    rewrite <- list2status_compositional.
    - rewrite (stack2proof s1).
      rewrite (stack2proof s2).
      reflexivity.
    - rewrite (stack2proof s1).
      apply negpathsii1ii2.
  Defined.

  Definition stack_concatenate {n1 n2: nat} (s1: Stack sigma n1) (s2: Stack sigma n2)
    : Stack sigma (n1 + n2) := mk_stack (n1 + n2) (concatenate s1 s2) (is_stack_concatenate s1 s2).

  Definition stack_vector_concatenate {n: nat} (vec: Vector (Term sigma) n): Stack sigma n.
  Proof.
    induction n.
    - exact (stack_empty sigma).
    - exact (stack_concatenate (hd vec) (IHn (tl vec))).
  Defined.

  Definition term_op (nm: names sigma) (vec: Vector (Term sigma) (arity nm)): Term sigma.
  Proof.
    set (res := stack_cons nm (stack_vector_concatenate vec) (isreflnatleh (arity nm))).
    rewrite minuseq0' in res.
    assumption.
  Defined.

End TermAlgebra.

Definition term_algebra (sigma: Signature): Algebra sigma
  := mk_algebra (Term_hset sigma) term_op.

Section TermInduction.

  Context {sigma: Signature}.

  Lemma nil_not_term: @list2status sigma nil != stackok 1.
  Proof.
    cbn.
    intro H.
    apply ii1_injectivity in H.
    apply negpaths0sx in H.
    contradiction.
  Defined.

  Lemma list_destruct {A: UU} (l: list A): (l = nil) ⨿ ( ∑ (x: A) (xs: list A), l = cons x xs ).
  Proof.
    apply (list_ind (λ l: list A, (l = nil) ⨿ (∑ (x: A) (xs: list A), l = cons x xs))).
    - left.
      apply idpath.
    - right.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  Definition princ_op (t: Term sigma): names sigma.
  Proof.
    induction t as [l l_is_term].
    induction (list_destruct l) as [l_nil | l_cons].
    - rewrite l_nil in l_is_term.
      apply nil_not_term in l_is_term.
      contradiction.
    - induction l_cons as [x rest].
      exact x.
  Defined.

  (*** These axioms probably needs some additional hypotheses **)

  Axiom natlehandminusl: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natlehandminusr: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

  Axiom natdiff0: ∏ a b: nat, 0 = a - b → b ≥ a.

  Axiom natdiffasymm: ∏ a b: nat, a ≤ b → a ≥ b → a=b.

  Axiom nat_ax: ∏ a b c: nat, a = S (b - c) → b = a + c -1.

  Axiom nat_ax3: ∏ a b c : nat, a + b - 1 - (c + b - 1) = a-c.

  Lemma nat_notgeh1: ∏ n: nat, ¬ (n ≥ 1) → n = 0.
  Proof.
    intro.
    induction n.
    - intro.
      apply idpath.
    - intro n_gte_1.
      apply fromempty.
      abstract
        (apply n_gte_1,natgthtogehsn, natgthsn0).
  Defined.

  Lemma nat_notgeh1_inv: ∏ n: nat, n != 0 → n ≥ 1.
  Proof.
    intros.
    apply natgthtogehsn.
    apply natneq0togth0.
    apply nat_nopath_to_neq.
    assumption.
  Qed.

  Definition extract_sublist (s: list (names sigma)):
    ∏ n m: nat, list2status s = stackok m → n ≤ m  →
                ∑ first second: list (names sigma),
                        list2status first = stackok n ×
                        list2status second = stackok (m - n) ×
                        concatenate first second = s.
  Proof.
    apply (list_ind (λ s : list (names sigma), ∏ n m: nat, list2status s = stackok m → n ≤ m →
                     ∑ first second: list (names sigma), list2status first = stackok n ×
                                                  list2status second = stackok (m - n) ×
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
        * (**** THIS PROOF DOES NOT COMPUTE WELL ****)
          rewrite natminuseqn.
          assumption.
        * apply idpath.
      + apply nat_notgeh1_inv in n_gt_0.
        rewrite list2status_cons in s_status.
        assert ( tail_ok: ∑ tail_ar: nat, list2status tail = stackok tail_ar ×
                                                                      arity nm ≤ tail_ar ).
        {
          apply status_cons_noerror.
          rewrite s_status.
          apply negpathsii1ii2.
        }
        induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound]].
        rewrite tail_status_prf in s_status.
        apply status_cons_stackok2 in s_status.
        apply nat_ax in s_status.
        assert (tail_ar_newbound: n + arity nm - 1 ≤ tail_ar).
        {
          abstract
            (rewrite s_status;
             apply natlehandminusl;
             apply natlehandplus;
             [ assumption |
               apply isreflnatleh ]).
        }
        set (IH1 := IH (n + arity nm - 1) tail_ar tail_status_prf tail_ar_newbound).
        induction IH1 as [fst [snd [status_fst_prf [status_snd_prf conc]]]].
        rewrite s_status in status_snd_prf.
        rewrite nat_ax3 in status_snd_prf.
        set (realfirst := cons nm fst).
        assert (list2status realfirst = stackok n).
        {
          unfold realfirst.
          rewrite list2status_cons.
          rewrite status_fst_prf.
          unfold stackok.
          unfold status_cons.
          unfold coprod_rect at 1.
          induction (isdecrelnatleh (arity nm) (n + arity nm - 1)).
          - cbn.
            rewrite natminusminus.
            rewrite (natpluscomm 1 (arity nm)).
            rewrite <- natminusminus.
            rewrite plusminusnmm.
            change (S (n - 1)) with (1 + (n - 1)).
            rewrite natplusminusle.
            * apply maponpaths.
              abstract
                (rewrite natpluscomm, plusminusnmm;
                 apply idpath).
            * assumption.
          - induction b.
            abstract
              (rewrite natpluscomm;
               rewrite <- natplusminusle;
               [ apply natlehnplusnm | assumption ]).
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
    exists (fsupp ,, fproof).
    exists (ssupp ,, sproof).
    assumption.
  Defined.

  Definition subterm (t: Term sigma): ⟦ arity (princ_op t) ⟧ → Term sigma.
  Proof.
    assert (subterm2: ∏ (s: list (names sigma)) (s_is_term: list2status s = stackok 1),
            ⟦ arity (princ_op (s ,, s_is_term)) ⟧ → Term sigma).
    2: exact (subterm2 t (stack2proof t)).
    apply (list_ind (λ (s: list (names sigma)),
                     ∏ s_is_term : list2status s = stackok 1,
                                   ⟦ arity (princ_op (s,, s_is_term)) ⟧ → Term sigma)).
    - intro.
      set (contr := nil_not_term s_is_term).
      contradiction.
    - intros x tail IH s_is_term.
      cbn.
      intro arx.
      induction arx as [n n_lt_arx].
      rewrite list2status_cons in s_is_term.
      assert (s_ok: status_cons x (list2status tail) != stackerror).
      {
        rewrite s_is_term.
        apply negpathsii1ii2.
      }
      set (tail_ok := status_cons_noerror s_ok).
      induction tail_ok as [ tail_ar [ tail_status_prf tail_ar_bound ]].
      rewrite tail_status_prf in s_is_term.
      assert ( tail_ar_x: tail_ar = arity x).
      {
        set (X := status_cons_stackok2 s_is_term).
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
      exact (result ,, result_is_term).
  Defined.

  Definition term_ind: UU :=
    ∏ (P: Term sigma → UU),
    ( ∏ (nm: names sigma) (vterm: Vector (Term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (term_op nm vterm) )
    → (∏ t: Term sigma, P t).

End TermInduction.
