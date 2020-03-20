(***** Universal algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.

Section Basic.

  (** ** Signature *)

  Definition Arity: UU := nat.

  Definition signature: UU := ∑ (names: hSet), names → Arity.

  Definition make_signature (names: hSet) (aritymap: names → Arity): signature :=
    names ,, aritymap.

  Definition make_signature_simple {n: nat} (v: Vector nat n): signature := make_signature (stnset n) (el v).

  Definition names (sigma: signature): hSet := pr1 sigma.

  Definition arity {sigma: signature} (nm: names sigma): Arity := pr2 sigma nm.

  Definition dom {sigma: signature} (support: UU) (nm: names sigma):
    UU := Vector support (arity nm).

  Definition cod {sigma: signature} (support: UU) (nm: names sigma):
    UU := support.

  (** ** Algebra for a given signature *)

  Definition algebra (sigma: signature): UU :=
    ∑ (support: hSet), ∏ (nm: names sigma), dom support nm → cod support nm.

  Coercion support {sigma: signature} (a: algebra sigma): hSet := pr1 a.

  Definition op {sigma: signature} (a: algebra sigma) (nm: names sigma): (dom a nm) → (cod a nm) := pr2 a nm.

  Definition make_algebra (support : hSet) {sigma: signature} (ops: ∏ nm: names sigma, dom support nm → cod support nm):
     algebra sigma := (support ,, ops).

End Basic.

(** ** Homomorphism of algebras *)

Section Homomorphism.

  Context { sigma: signature }.

  Definition ishom {a1 a2: algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition make_ishom {a1 a2: algebra sigma} (f: a1 → a2)
                        (H: ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))))
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition hom (a1 a2: algebra sigma): UU :=  ∑ (f: a1 → a2), ishom f.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition pr1hom {a1 a2: algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion pr1hom: hom >-> Funclass.

  Definition homax {a1 a2: algebra sigma} (f: a1 ↦ a2): ishom f := pr2 f.

  Definition make_hom {a1 a2: algebra sigma} {f: a1 → a2} (is: ishom f): a1 ↦ a2 := f ,, is.

  Theorem isaprop_ishom {a1 a2: algebra sigma} (f: a1 → a2): isaprop (ishom f).
  Proof.
    unfold ishom.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply (setproperty a2).
  Defined.

  Theorem isasethom (a1 a2: algebra sigma): isaset (hom a1 a2).
  Proof.
    unfold hom.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      apply isasetaprop.
      apply isaprop_ishom.
  Defined.

  Local Lemma ishomidfun (a: algebra sigma): ishom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    apply idpath.
  Defined.

  Definition homid (a: algebra sigma): a ↦ a := make_hom (ishomidfun a).

  Local Lemma ishomcomp  {a1 a2 a3: algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): ishom (h2 ∘ h1).
  Proof.
    red.
    intros.
    induction h1 as [f1 ishomf1].
    induction h2 as [f2 ishomf2].
    cbn.
    rewrite vector_map_comp.
    rewrite ishomf1.
    rewrite ishomf2.
    apply idpath.
  Defined.

  Definition homcomp {a1 a2 a3: algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
    := make_hom (ishomcomp h1 h2).

End Homomorphism.

Declare Scope hom_scope.

Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity): hom_scope.

Delimit Scope hom_scope with hom.

Local Open Scope hom.

(** ** The trivial algebra with a single element *)

Section Unitalgebra.

  Definition unitalgebra (sigma: signature): algebra sigma :=
    make_algebra unitset (λ nm: names sigma, tounit).

  Context {sigma: signature}.

  Local Lemma homtounit_ishom (a: algebra sigma)
    : @ishom sigma a (unitalgebra sigma) tounit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition homtounit (a : algebra sigma): hom a (unitalgebra sigma)
    := @make_hom sigma a (unitalgebra sigma) tounit (homtounit_ishom a).

  Theorem iscontr_homstounit (a: algebra sigma): iscontr (hom a (unitalgebra sigma)).
  Proof.
    exists (homtounit a).
    intro t.
    use total2_paths2_f.
    - apply iscontrfuntounit.
    - apply proofirrelevance.
      apply isaprop_ishom.
  Defined.

End Unitalgebra.

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
    - apply idpath.
    - assumption.
  Defined.

End Natlemmas.

(** ** Status of a stack machine. *)

Section Status.

  Context {sigma: signature}.

  (**
    A status is either a natural number, representing the number of terms in the stack,
    or an error.
   **)

  Definition status: UU := nat ⨿ unit.

  Definition statusok (n: nat): status := ii1 n.

  Definition statuserror: status := ii2 tt.

  Lemma isasetstatus: isaset status.
  Proof.
    apply isasetcoprod.
    - apply isasetnat.
    - apply isasetunit.
  Defined.

  (** Computes the effect, on status, of pushing a function symbol on the top of a stack *)

  Definition status_cons (nm: names sigma) (s: status): status.
  Proof.
    induction s as [n | error].
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

  Lemma status_cons_statusok_r {nm: names sigma} {status: status} {m: nat}:
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

  Lemma status_cons_noerror_r {nm: names sigma} {status: status}:
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

  Definition status_concatenate (s1 s2: status): status.
  Proof.
    induction s2 as [len_s2 | error2].
    - induction s1 as [len_s1 | error1].
      + exact (statusok (len_s1 + len_s2)).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Lemma status_concatenate_statuscons {nm: names sigma} {s1 s2: status}:
    (status_cons nm s1 != statuserror) → status_concatenate (status_cons nm s1) s2
    = status_cons nm (status_concatenate s1 s2).
  Proof.
    induction s1 as [a1 | error1].
    2: contradiction.
    induction s2 as [a2 | error2].
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

(** ** Operations and definitions on stacks of function symbols *)

Section OpList.

  Definition oplist (sigma: signature) := list (names sigma).

  Identity Coercion oplistislist: oplist >-> list.

  Context {sigma: signature}.

  (**
    Computes the status of a sequence of function symbols. The sequence should be thought of
    as a stack. A stack will be formally defined as a non-erratic list of function symbols.
   **)

  Definition oplist2status (l: oplist sigma): status := foldr status_cons (statusok 0) l.

  Lemma oplist2status_cons {nm: names sigma} {l: oplist sigma}:
    oplist2status (cons nm l) = status_cons nm (oplist2status l).
  Proof.
    apply idpath.
  Defined.

  Lemma oplist2status_zero {l: oplist sigma}: oplist2status l = statusok 0 → l = nil.
  Proof.
    intro proof.
    induction l as [len v].
    induction len.
    - induction v.
      apply idpath.
    - apply status_cons_statusok_r in proof.
      induction proof as [contr _].
      apply isirreflnatgth in contr.
      contradiction.
  Defined.

  Lemma oplist2status_positive {l: oplist sigma} {n: nat}:
    oplist2status l = statusok (S n) →
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

  Lemma oplist2status_positive2 {n: nat} {v: Vector (names sigma) (S n)}:
    oplist2status ( S n ,,  v ) = statusok 1 → oplist2status (n,, tl v) = statusok (arity (hd v)).
  Proof.
    intro proof.
    change (S n,,v) with (cons (hd v) (n ,, tl v)) in proof.
    rewrite oplist2status_cons in proof.
    apply status_cons_statusok_r in proof.
    induction proof as [ _ proof].
    rewrite natpluscomm in proof.
    rewrite plusminusnmm in proof.
    assumption.
  Defined.

  Lemma oplist2status_concatenate {l1 l2: oplist sigma}:
    oplist2status l1 != statuserror →
    oplist2status (concatenate l1 l2) = status_concatenate (oplist2status l1) (oplist2status l2).
  Proof.
    apply (list_ind (λ s, oplist2status s != statuserror →
                          oplist2status (concatenate s l2) =
                          status_concatenate (oplist2status s) (oplist2status l2))).
    - intros.
      change (concatenate nil l2) with (l2).
      induction (oplist2status l2) as [okl2 | badl2].
      + apply idpath.
      + induction badl2.
        apply idpath.
    - intros nm l1tail IH noerror.
      rewrite oplist2status_cons.
      rewrite status_concatenate_statuscons by (assumption).
      rewrite <- IH.
      + apply idpath.
      + intro error.
        rewrite oplist2status_cons in noerror.
        rewrite error in noerror.
        contradiction.
  Defined.

  (** Split a stack in a stack of up to n terms and a stack of the remaining terms **)

  Definition extract_list (l: oplist sigma) (n: nat): oplist sigma × oplist sigma.
  Proof.
    revert l n.
    apply (list_ind (λ l: oplist sigma, ∏ (n : nat), oplist sigma × oplist sigma)).
    - intros.
      exact (nil,, nil).
    - intros x xs IH n.
      induction n.
      + exact (nil,, (cons x xs)).
      + set (resind := IH (n + arity x)).
        exact (cons x (pr1 resind) ,, pr2 resind).
  Defined.

  Lemma extract_list_zero {l: oplist sigma}: extract_list l 0 = nil,, l.
  Proof.
    apply (list_ind (λ l: oplist sigma, extract_list l 0 = nil,, l)).
    - apply idpath.
    - reflexivity.
  Defined.

  Lemma extract_list_cons {x: names sigma} {xs: oplist sigma} {n: nat}:
    extract_list (cons x xs) (S n) =
    cons x (pr1 (extract_list xs (n + arity x))) ,, (pr2 (extract_list xs (n + arity x))).
  Proof.
    apply idpath.
  Defined.

  Lemma extract_list_concatenate1 (l: oplist sigma) (n: nat):
    concatenate (pr1 (extract_list l n)) (pr2 (extract_list l n)) = l.
  Proof.
    revert l n.
    apply (list_ind (λ l : oplist sigma, ∏ (n: nat),
      concatenate (pr1 (extract_list l n)) (pr2 (extract_list l n)) = l)).
    - intros.
      apply idpath.
    - intros x xs HPxs n.
      induction n.
      + apply idpath.
      + rewrite extract_list_cons.
        cbn - [concatenate].
        rewrite concatenateStep.
        rewrite (HPxs (n + arity x)).
        apply idpath.
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

  Lemma extract_list_success (l: oplist sigma) {m: nat} (n: nat):
    oplist2status l = statusok m → n ≤ m  →
                    oplist2status (pr1 (extract_list l n)) = statusok n ×
                    oplist2status (pr2 (extract_list l n)) = statusok (m - n).
  Proof.
    revert l m n.
    apply (list_ind (λ l : oplist sigma, ∏ (m n: nat),
        oplist2status l = statusok m → n ≤ m  →
        oplist2status (pr1 (extract_list l n)) = statusok n ×
        oplist2status (pr2 (extract_list l n)) = statusok (m - n))).
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
        cbn - [oplist2status].
        rewrite oplist2status_cons in proofxxs.
        apply status_cons_statusok_r in proofxxs.
        induction proofxxs as [ _ proofxxs].
        eapply extract_list_arith1 in nlehm.
        induction (HPind (m + arity x - 1) (n + arity x) proofxxs nlehm) as [ind1 ind2].
        split.
        * rewrite oplist2status_cons.
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

  Lemma extract_list_norest {l: oplist sigma} {n: nat}
    : oplist2status l = statusok n →  extract_list l n = l ,, nil.
  Proof.
    intro proofl.
    set (H1 := extract_list_success l n proofl (isreflnatleh n)).
    set (concat := extract_list_concatenate1 l n).
    induction H1 as [first second].
    rewrite minuseq0' in second.
    apply oplist2status_zero in second.
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

  Lemma extract_list_concatenate2 (l1 l2: oplist sigma) {n1: nat} (n: nat)
    : oplist2status l1 = statusok n1 → n ≤ n1 →
        extract_list (concatenate l1 l2) n =
          pr1 (extract_list l1 n) ,, concatenate (pr2 (extract_list l1 n)) l2.
  Proof.
    revert l1 n1 n.
    apply (list_ind (λ l1 : oplist sigma, ∏ (n1 n: nat),
           oplist2status l1 = statusok n1 → n ≤ n1 → extract_list (concatenate l1 l2) n =
              pr1 (extract_list l1 n) ,, concatenate (pr2 (extract_list l1 n)) l2)).
    - intros n1 n proofl1 nlehn1.
      apply ii1_injectivity in proofl1.
      rewrite <- proofl1 in *.
      apply natleh0tois0 in nlehn1.
      rewrite nlehn1.
      cbn - [extract_list].
      rewrite extract_list_zero.
      apply idpath.
    - intros x xs HPind n1 n proofl1 nlehn1.
      rewrite concatenateStep.
      induction n.
      + apply idpath.
      + rewrite oplist2status_cons in proofl1.
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

Section OpListInduction.

  Context {sigma: signature}.

  Definition veclist_flatten {A: UU} {n: nat} (v: Vector (list A) n): list A :=
    vector_foldr concatenate nil v.

  Lemma veclist_flatten_status {n: nat} (v: Vector (oplist sigma) n)
    (vterms: ∏ (i: ⟦ n ⟧), oplist2status  (el v i) = statusok 1):
    oplist2status (veclist_flatten v) = statusok n.
  Proof.
    induction n.
    - induction v.
      apply idpath.
    - change (veclist_flatten v) with (concatenate (hd v) (veclist_flatten (tl v))).
      rewrite oplist2status_concatenate.
      + rewrite IHn.
        * set (H := vterms (●0)).
          change (el v (● 0)) with (hd v) in H.
          rewrite H.
          apply idpath.
        * intro.
          set (H := vterms (S i,, pr2 i)).
          rewrite el_tl.
          apply H.
      + set (H := vterms (●0)).
        change (el v (● 0)) with (hd v) in H.
        rewrite H.
        apply negpathsii1ii2.
  Defined.

  Local Lemma length_cons {A: UU} (x: A) (xs: list A):
    length (cons x xs) = S(length xs).
  Proof.
    apply idpath.
  Defined.

  Local Lemma length_concatenate {A: UU} (l1: list A) (l2: list A):
    length (concatenate l1 l2) = length l1 + length l2.
  Proof.
    induction l1 as [len1 vec1].
    induction len1.
    - induction vec1.
      apply idpath.
    - change (S (length (concatenate (len1,, tl vec1) l2)) = S (len1 + length l2)).
      apply maponpaths.
      apply (IHlen1 (tl vec1)).
  Defined.

  Local Lemma cons_inj {A: UU} (a1 a2: A) (r1 r2: list A):
    cons a1 r1 = cons a2 r2 → a1=a2 × r1=r2.
  Proof.
  Admitted.

  Local Lemma length_sublist1 {A: UU} (l1: list A) (l2: list A):
    length l1 ≤ length (concatenate l1 l2).
  Proof.
    repeat rewrite length_concatenate.
    apply natlehnplusnm.
  Defined.

  Local Lemma length_sublist2 {A: UU} (l1: list A) (l2: list A):
    length l2 ≤ length (concatenate l1 l2).
  Proof.
    repeat rewrite length_concatenate.
    rewrite natpluscomm.
    apply natlehnplusnm.
  Defined.

  Definition oplist2vecoplist (l: oplist sigma) {n: nat} (ln: oplist2status l = statusok n):
    ∑ (vec: Vector (oplist sigma) n), (∏ (i: ⟦ n ⟧), oplist2status  (el vec i) = statusok 1) ×
                                      (∏ (i: ⟦ n ⟧), length (el vec i) ≤ length l) ×
                                      veclist_flatten vec = l.
  Proof.
    revert l ln.
    induction n.
    - intros.
      exists vnil.
      repeat split.
      + intro i.
        apply fromstn0.
        assumption.
      + intro i.
        apply fromstn0.
        assumption.
      + apply oplist2status_zero in ln.
        rewrite ln.
        apply idpath.
    - intros.
      induction (extract_list_success l 1 ln (natleh0n 0)) as [firstp restp].
      set (first := pr1 (extract_list l 1)).
      set (rest := pr2 (extract_list l 1)).
      change (S n) with (1 + n) in restp.
      rewrite natpluscomm in restp.
      rewrite plusminusnmm in restp.
      set (H := IHn rest restp).
      induction H as [restvec [reststatus [restlength restflatten]]].
      exists (vcons first restvec).
      repeat split.
      + intro i.
        induction i as [i i_leq_sn].
        induction i.
        * exact firstp.
        * change (S i ,, i_leq_sn) with (dni_firstelement (i,, i_leq_sn)).
          rewrite el_vcons_tl.
          exact (reststatus (i ,, i_leq_sn)).
      + intro i.
        induction i as [i i_leq_sn].
        induction i.
        * change (el (vcons first restvec) (0,, i_leq_sn)) with first.
          set (H := extract_list_concatenate1 l 1).
          rewrite <- H.
          apply length_sublist1.
        * change (S i ,, i_leq_sn) with (dni_firstelement (i,, i_leq_sn)).
          rewrite el_vcons_tl.
          eapply istransnatleh.
          --  exact (restlength (i ,, i_leq_sn)).
          --  rewrite <- (extract_list_concatenate1 l 1).
              apply length_sublist2.
      + change (veclist_flatten (vcons first restvec)) with (concatenate first (veclist_flatten restvec)).
        rewrite restflatten.
        apply extract_list_concatenate1.
  Defined.

  Definition oplist_make_term (nm: names sigma) (vec: Vector (oplist sigma) (arity nm)): oplist sigma
    := cons nm (veclist_flatten vec).

  Lemma oplist_make_term_status (nm: names sigma) (vec: Vector (oplist sigma) (arity nm))
    (vecterms: (∏ (i: ⟦ arity nm ⟧), oplist2status  (el vec i) = statusok 1)):
    oplist2status (oplist_make_term nm vec) = statusok 1.
  Proof.
    unfold oplist_make_term.
    rewrite oplist2status_cons.
    rewrite veclist_flatten_status.
    - rewrite status_cons_statusok_f.
      + rewrite minuseq0'.
        apply idpath.
      + apply isreflnatleh.
   - exact vecterms.
  Defined.

  Definition oplist_decompose (l: oplist sigma) (l1: oplist2status l = statusok 1):
     ∑ (nm:names sigma) (vec: Vector (oplist sigma) (arity nm)),
       (∏ (i: ⟦ arity nm ⟧), oplist2status  (el vec i) = statusok 1)  ×
        (∏ (i: ⟦ arity nm  ⟧), length (el vec i) < length l) × oplist_make_term nm vec = l.
  Proof.
    induction l as [len vec].
    induction len.
    - induction vec.
      apply ii1_injectivity in l1.
      apply negpaths0sx in l1.
      contradiction.
    - set (nm := (hd vec)).
      set (tail := (len ,, tl vec)).
      change (S len ,, vec) with (cons nm tail) in *.
      exists nm.
      rewrite oplist2status_cons in l1.
      apply status_cons_statusok_r in l1.
      induction l1 as [_ ptail].
      rewrite natpluscomm in ptail.
      rewrite plusminusnmm in ptail.
      set (X := oplist2vecoplist tail ptail).
      induction X as [vectail [vecterms [veclength vecflatt]]].
      exists vectail.
      unfold oplist_make_term.
      rewrite vecflatt.
      repeat split.
      + exact vecterms.
      + intro i.
        change (length (cons nm tail)) with (S (length tail)).
        apply natlehtolthsn.
        apply veclength.
  Defined.

  Local Lemma oplist_ind_onlength
    (P: oplist sigma → UU)
    (HPind: ∏ (nm: names sigma) (vterm: Vector (oplist sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (oplist_make_term nm vterm))
    : (∏ (n: nat) (t: oplist sigma), oplist2status t = statusok 1 × length t ≤ n →  P t).
  Proof.
    induction n.
    - intros t HPs.
      induction HPs as [statust lent].
      apply fromempty.
      apply natleh0tois0 in lent.
      apply oplist2status_positive in statust.
      rewrite (pr2 (pr2 statust)) in lent.
      cbn in lent.
      apply negpathssx0 in lent.
      assumption.
    - intros t HPs.
      induction HPs as [statust lent].
      set (X := oplist_decompose t statust).
      induction X as [nm [vec [vecterms [veclength normalization]]]].
      apply (transportf P normalization).
      apply HPind.
      intro i.
      apply IHn.
      split.
      + exact (vecterms i).
      + change (S (length (el vec i)) ≤ S n).
        eapply istransnatleh.
        * apply natlthtolehsn.
          apply veclength.
        * apply lent.
  Defined.

  Theorem oplist_ind
    (P: oplist sigma → UU)
    (HPind: ∏ (nm: names sigma) (vterm: Vector (oplist sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (oplist_make_term nm vterm) )
    : (∏ (t: oplist sigma), oplist2status t = statusok 1 → P t).
  Proof.
    intros t prooft.
    exact (oplist_ind_onlength P HPind (length t) t (prooft ,, (isreflnatleh _))).
  Defined.

  Lemma oplist_ind_step (nm: names sigma) (v: Vector (oplist sigma) (arity nm)):
    ∏ (P: oplist sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (oplist sigma) (arity nm)),
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (oplist_make_term nm vterm))
      (vterms: ∏ (i:  ⟦ arity nm ⟧), oplist2status (el v i) = statusok 1),
    oplist_ind P Ind (oplist_make_term nm v) (oplist_make_term_status nm v vterms) =
       Ind nm v (λ i:  ⟦ arity nm ⟧, oplist_ind P Ind (el v i) (vterms i)).
  Proof.
    intros.
    unfold oplist_ind.
    unfold oplist_make_term in *.
    change (length (cons nm (veclist_flatten v))) with (S (length (veclist_flatten v))) in *.
    unfold oplist_ind_onlength.
    rewrite nat_rect_step.
    set (d := oplist_decompose (cons nm (veclist_flatten v)) (oplist_make_term_status nm v vterms)).
    induction d as [nm0 [vterms0 [v0status [v0len v0norm ]]]].
    unfold oplist_make_term in v0norm.
    pose (X := v0norm).
    apply cons_inj in X.
    induction X as [X1 X2].
    induction (! X1).
    assert (H: vterms0 = v). { admit. }
    induction (! H).
    assert (H1: v0norm = idpath _).
    { admit. }
    rewrite H1.
    rewrite idpath_transportf.
  Abort.


  Definition oplist_depth (t: oplist sigma) (prooft: oplist2status t = statusok 1): nat
    := oplist_ind (λ t: oplist sigma, nat)
                (λ (nm: names sigma) (vterm: Vector (oplist sigma) (arity nm))
                   (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) )
                  t prooft.

End OpListInduction.

Section Term.

  Definition stack (sigma: signature) (n: nat): UU :=
    ∑ s: oplist sigma, oplist2status s = statusok n.

  Definition make_stack {sigma: signature} {n: nat} (s: oplist sigma)
             (is: oplist2status s = statusok n):
    stack sigma n := s ,, is.

  Coercion stack2list {sigma: signature} {n: nat} (s: stack sigma n):
    oplist sigma := pr1 s.

  Definition stack2proof {sigma: signature} {n: nat} (s: stack sigma n):
    oplist2status s = statusok n := pr2 s.

  Definition term (sigma: signature): UU := stack sigma 1.

  Identity Coercion termisstack: term >-> stack.

  Lemma isasetstack (sigma: signature) (n: nat): isaset (stack sigma n).
  Proof.
    apply isaset_total2.
    - apply isofhlevellist.
      exact (setproperty (names sigma)).
    - intros.
      apply isasetaprop.
      apply isasetstatus.
  Defined.

  Definition stackset (sigma : signature) (n: nat): hSet
    := make_hSet (stack sigma n) (isasetstack sigma n).

  Context {sigma: signature}.

  Lemma stack_extens {n: nat} {s1 s2 : stack sigma n} (p : stack2list s1 = stack2list s2)
    : s1 = s2.
  Proof.
    apply subtypePath.
    2: exact p.
    intros s.
    apply isasetstatus.
  Defined.

  Definition stack_nil (sigma: signature): stack sigma 0 := stnpr nil.

  Lemma stack_isnil (s: stack sigma 0): s = stack_nil sigma.
  Proof.
    induction s as [l proof].
    apply stack_extens.
    apply oplist2status_zero.
    assumption.
  Defined.

  Local Lemma is_stack_concatenate  {n1 n2: nat} (s1: stack sigma n1) (s2: stack sigma n2)
    : oplist2status (concatenate s1 s2) = statusok (n1 + n2).
  Proof.
    change (statusok (n1 + n2)) with (status_concatenate (statusok n1) (statusok n2)).
    rewrite <- (stack2proof s1).
    rewrite <- (stack2proof s2).
    apply oplist2status_concatenate.
    rewrite (stack2proof s1).
    apply negpathsii1ii2.
  Defined.

  Definition stack_concatenate {n1 n2: nat} (s1: stack sigma n1) (s2: stack sigma n2)
    : stack sigma (n1 + n2) := make_stack (concatenate s1 s2) (is_stack_concatenate s1 s2).

  Lemma stack2list_stackconcatenate {n1 n2: nat} (s1: stack sigma n1) (s2: stack sigma n2)
    : stack2list (stack_concatenate s1 s2) = concatenate (stack2list s1) (stack2list s2).
  Proof.
    apply idpath.
  Defined.

  Definition terms2stack {n: nat} (vec: Vector (term sigma) n): stack sigma n.
  Proof.
    induction n.
    - exact (stack_nil sigma).
    - exact (stack_concatenate (hd vec) (IHn (tl vec))).
  Defined.

  Lemma terms2stack_vcons {n: nat} {v: Vector (term sigma) n} {t: term sigma} :
    terms2stack (vcons t v) = stack_concatenate t (terms2stack v).
  Proof.
    apply idpath.
  Defined.

  Lemma make_term_isterm (nm: names sigma) (vec: Vector (term sigma) (arity nm)):
    oplist2status (cons nm (terms2stack vec)) = statusok 1.
  Proof.
    rewrite oplist2status_cons.
    rewrite (stack2proof (terms2stack vec)).
    rewrite status_cons_statusok_f.
    - rewrite minuseq0'.
      apply idpath.
    - apply isreflnatleh.
  Defined.

  Definition make_term (nm: names sigma) (vec: Vector (term sigma) (arity nm)): term sigma
    := make_stack (cons nm (terms2stack vec)) (make_term_isterm nm vec).

  Local Definition extract_term {n: nat} (s: stack sigma (S n))
    : term sigma ×  stack sigma n.
  Proof.
    set (rest := extract_list_success s 1 (stack2proof s) (natleh0n n)).
    induction rest as [fproof sproof].
    split.
    - exact (make_stack (pr1 (extract_list s 1)) fproof).
    - change (S n - 1) with (1 + n - 1) in sproof.
      rewrite natpluscomm in sproof.
      rewrite plusminusnmm in sproof.
      exact (make_stack (pr2 (extract_list s 1)) sproof).
  Defined.

  Definition stack_first {n: nat} (s: stack sigma (S n)): term sigma
    := pr1 (extract_term s).

  Definition stack_rest {n: nat} (s: stack sigma (S n)): stack sigma n
    := pr2 (extract_term s).

  Lemma stack_concatenate_normalize1 {n: nat} (s: stack sigma (S n))
    : stack_concatenate (stack_first s) (stack_rest s) = s.
  Proof.
    apply stack_extens.
    apply (extract_list_concatenate1 s 1).
  Defined.

  Lemma stack_concatenate_normalize2 (t: term sigma) {n2: nat} (s2: stack sigma n2)
    : stack_first (stack_concatenate t s2) = stack_first t.
  Proof.
    apply stack_extens.
    cbn - [extract_list].
    set (res := extract_list_concatenate2 t s2 1 (stack2proof t) (natleh0n 0)).
    apply (maponpaths pr1) in res.
    assumption.
  Defined.

  Lemma stack_concatenate_normalize3 (t: term sigma) {n2: nat} (s2: stack sigma n2)
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

  Lemma stack_first_term {t: term sigma}: stack_first t = t.
  Proof.
    apply stack_extens.
    cbn.
    rewrite extract_list_norest.
    - apply idpath.
    - exact (stack2proof t).
  Defined.

  Definition stack2terms {n: nat} (s: stack sigma n): Vector (term sigma) n.
  Proof.
    induction n.
    - exact vnil.
    - exact (vcons (stack_first s) (IHn (stack_rest s))).
  Defined.

  Lemma stack2terms_concatenate {t: term sigma} {n: nat} (s2: stack sigma n):
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

  Lemma terms2stack2terms {n: nat} (s: stack sigma n): terms2stack (stack2terms s) = s.
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

  Lemma stack2terms2stack {n: nat} (terms: Vector (term sigma) n): stack2terms (terms2stack terms) = terms.
  Proof.
    induction n.
    - induction terms.
      apply idpath.
    - induction terms as [t rest].
      change (t ,, rest) with (vcons t rest).
      change (terms2stack (vcons t rest)) with (stack_concatenate t (terms2stack rest)).
      rewrite stack2terms_concatenate.
      rewrite (IHn rest).
      apply idpath.
  Defined.

  Definition term_decompose (t: term sigma):
    ∑ (op: names sigma) (subs: stack sigma (arity op)), stack2list t = cons op subs.
  Proof.
    induction t as [l proof].
    induction l as [len v].
    induction len.
    - induction v.
      apply fromempty.
      apply ii1_injectivity in proof.
      apply negpaths0sx in proof.
      assumption.
    - exists (hd v).
      change (S len ,, v) with (cons (hd v) (len ,, (tl v))) in *.
      pose (p := proof).
      rewrite oplist2status_cons in p.
      apply status_cons_statusok_r in p.
      induction p as [_ p].
      rewrite natpluscomm in p.
      rewrite plusminusnmm in p.
      exists (make_stack (len,, tl v) p).
      apply idpath.
  Defined.

  Definition princop (t: term sigma): names sigma
    := pr1 (term_decompose t).

  Definition term_rest (t: term sigma): stack sigma (arity (princop t))
    := (pr1 (pr2 (term_decompose t))).

  Definition subterms (t: term sigma):  Vector (term sigma) (arity (princop t))
    := stack2terms (term_rest t).

  Lemma term_list_decomp (t: term sigma): stack2list t = cons (princop t) (term_rest t).
  Proof.
    exact (pr2 (pr2 (term_decompose t))).
  Defined.

  Lemma term_rest_subterms (t: term sigma): term_rest t = terms2stack (subterms t).
  Proof.
    unfold subterms.
    rewrite terms2stack2terms.
    apply idpath.
  Defined.

  Lemma make_term_normalize (t: term sigma): make_term (princop t) (subterms t) = t.
  Proof.
    apply stack_extens.
    change (cons (princop t) (terms2stack (subterms t)) = stack2list t).
    unfold subterms.
    rewrite terms2stack2terms.
    rewrite <- term_list_decomp.
    apply idpath.
  Defined.

  Lemma make_term_normalize2 (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : princop (make_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Lemma make_term_normalize3 (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : term_rest (make_term nm v) = terms2stack v.
  Proof.
    apply stack_extens.
    apply idpath.
  Defined.

  Lemma make_term_normalize4 (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : subterms (make_term nm v) = v.
  Proof.
    unfold subterms.
    rewrite make_term_normalize3.
    rewrite stack2terms2stack.
    apply idpath.
  Defined.

End Term.

Section Lengthstack.

  Context {sigma: signature}.


  Lemma term_rest_length (t: term sigma): S(length (term_rest t)) = length t.
  Proof.
    rewrite term_list_decomp.
    rewrite length_cons.
    apply idpath.
  Defined.

  Lemma stack_first_minlength {n: nat} (s: stack sigma (S n)): length (stack_first s) > 0.
  Proof.
    induction (stack_first s) as [l proofl].
    pose (p := proofl).
    apply oplist2status_positive in p.
    induction p as [lent [v lstruct]].
    change (stack2list (l,, proofl)) with l.
    rewrite lstruct.
    change (length (S lent,, v)) with (S lent).
    apply natgthsn0.
  Defined.

  Lemma stack_first_maxlength {n: nat} (s: stack sigma (S n)): length (stack_first s) ≤ length s.
  Proof.
    set (X := stack_concatenate_normalize1 s).
    apply (maponpaths stack2list) in X.
    apply (maponpaths length) in X.
    change (stack2list (stack_concatenate (stack_first s) (stack_rest s))) with (concatenate (stack_first s) (stack_rest s)) in X.
    rewrite length_concatenate in X.
    apply nat_movplusright in X.
    rewrite X.
    apply natminuslehn.
  Defined.

  Lemma stack_rest_maxlength {n: nat} (s: stack sigma (S n)): length (stack_rest s) ≤ length s.
  Proof.
    set (X := stack_concatenate_normalize1 s).
    apply (maponpaths stack2list) in X.
    apply (maponpaths length) in X.
    change (stack2list (stack_concatenate (stack_first s) (stack_rest s))) with (concatenate (stack_first s) (stack_rest s)) in X.
    rewrite length_concatenate in X.
    rewrite natpluscomm in X.
    apply nat_movplusright in X.
    rewrite X.
    apply natminuslehn.
  Defined.

  Lemma stack2terms_length {n: nat} (s: stack sigma n) : ∏ (i : ⟦ n ⟧), length (el (stack2terms s) i) ≤ length s.
  Proof.
    induction n.
    - intro i.
      apply fromempty.
      apply negstn0 in i.
      assumption.
    - change (stack2terms s) with (vcons (stack_first s) (stack2terms (stack_rest s))).
      intro i.
      induction i as [i iproof].
      induction i.
      + change (el (vcons (stack_first s) (stack2terms (stack_rest s))) (0,, iproof)) with (stack_first s).
        apply stack_first_maxlength.
      + set ( X := IHn (stack_rest s) (i ,, iproof)).
        change (S i ,, iproof) with (dni_firstelement (i,, iproof)).
        rewrite el_vcons_tl.
        eapply istransnatleh.
        apply X.
        apply stack_rest_maxlength.
  Defined.

  Lemma subterms_length (t: term sigma):
    ∏ i : ⟦ arity (princop t) ⟧, length (el (subterms t) i) < length t.
  Proof.
    intro i.
    rewrite <- (term_rest_length t).
    apply natlehtolthsn.
    unfold subterms.
    apply stack2terms_length.
  Defined.

End Lengthstack.

Section termInduction.

  Context {sigma: signature}.

  Local Lemma term_ind_onlength
    (P: oplist sigma → UU)
    (HPind: ∏ (nm: names sigma) (vterm: Vector (term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (make_term nm vterm))
    : (∏ (n: nat) (t: term sigma), length (stack2list t) ≤ n →  P t).
  Proof.
    induction n.
    - induction t as [[len vec] proofl].
      intro lent.
      apply natleh0tois0 in lent.
      cbn in lent.
      revert vec proofl.
      rewrite lent.
      intros.
      induction vec.
      apply fromempty.
      apply ii1_injectivity in proofl.
      apply negpaths0sx in proofl.
      assumption.
    - intros t lent.
      rewrite <- (make_term_normalize t).
      apply HPind.
      intro i.
      apply IHn.
      eapply natlthlehtrans.
      + apply subterms_length.
      + assumption.
  Defined.

  Theorem term_ind
    (P: oplist sigma → UU)
    (HPind: ∏ (nm: names sigma) (vterm: Vector (term sigma) (arity nm)),
      (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (make_term nm vterm) )
    : (∏ t: term sigma, P t).
  Proof.
    intro t.
    exact (term_ind_onlength P HPind (length t) t (isreflnatleh _)).
  Defined.

  Lemma term_ind_step (nm: names sigma) (v: Vector (term sigma) (arity nm)):
    ∏ (P: oplist sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (term sigma) (arity nm)),
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (make_term nm vterm)),
    term_ind P Ind (make_term nm v) = Ind nm v (λ i:  ⟦ arity nm ⟧, term_ind P Ind (el v i)).
  Proof.
    intros.
    unfold term_ind.
    change (length (make_term nm v)) with (S (length (terms2stack v))).
    simpl.
    change (princop (make_term nm v)) with (nm).

    (** Almost there.. there is a unwanted internal_paths_rew and we cannot use
        make_term_normalize4 **)
  Abort.

  (** TODO: change term_ind so that this definition computes. **)

  Definition depth (t: term sigma): nat
    := term_ind ( λ t: oplist sigma, nat)
                ( λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                    (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) )
                t.

  Lemma depth_step (t: term sigma) (nm : names sigma) (args : Vector (term sigma) (arity nm))
     (levels : Vector nat (arity nm)) :
     depth (make_term nm args) = 1 + vector_foldr max 0 levels.
  Proof.
    unfold depth.
    unfold term_ind.
  Abort.

End termInduction.

Section termalgebra.

  Definition term_algebra (sigma: signature): algebra sigma
    := make_algebra (stackset sigma 1) make_term.

  (** TODO

  Definition initial_hom {sigma: signature} (a: algebra sigma): term_algebra sigma ↦ a.

  Definition initial_hom_unicity {sigma: signature} (a: algebra sigma) (f: hom term_algebra a)
     : f = initial_hom a.

  **)

End termalgebra.
