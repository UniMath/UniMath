(***** Universal algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope stn.
Local Open Scope nat.

Section Basic.

  (** * Signature *)

  Definition Arity: UU := nat.

  Definition signature: UU := ∑ (names: hSet), names → Arity.

  Definition make_signature (names: hSet) (aritymap: names → Arity): signature
    := names ,, aritymap.

  Definition make_signature_simple {n: nat} (v: Vector nat n): signature
    := make_signature (stnset n) (el v).

  Definition names (sigma: signature): hSet := pr1 sigma.

  Definition arity {sigma: signature} (nm: names sigma): Arity := pr2 sigma nm.

  Definition dom {sigma: signature} (support: UU) (nm: names sigma): UU
    := Vector support (arity nm).

  Definition cod {sigma: signature} (support: UU) (nm: names sigma): UU
    := support.

  (** * Algebra for a given signature *)

  Definition algebra (sigma: signature): UU
    := ∑ (support: hSet), ∏ (nm: names sigma), dom support nm → cod support nm.

  Coercion support {sigma: signature} (a: algebra sigma): hSet := pr1 a.

  Definition op {sigma: signature} (a: algebra sigma) (nm: names sigma)
    : dom a nm → cod a nm := pr2 a nm.

  Definition make_algebra (support : hSet) {sigma: signature}
    (ops: ∏ nm: names sigma, dom support nm → cod support nm)
    : algebra sigma := support ,, ops.

End Basic.

Section Homomorphism.

  (** * Homomorphisms of algebras *)

  Context {sigma: signature}.

  Definition ishom {a1 a2: algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), (f (op a1 nm x) = (op a2 nm (vector_map f x))).

  Definition hom (a1 a2: algebra sigma): UU := ∑ (f: a1 → a2), ishom f.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {a1 a2: algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2ax {a1 a2: algebra sigma} (f: a1 ↦ a2): ishom f := pr2 f.

  Definition make_hom {a1 a2: algebra sigma} {f: a1 → a2} (is: ishom f): a1 ↦ a2 := f ,, is.

  Theorem isapropishom {a1 a2: algebra sigma} (f: a1 → a2): isaprop (ishom f).
  Proof.
    red.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply setproperty.
  Defined.

  Theorem isasethom (a1 a2: algebra sigma): isaset (hom a1 a2).
  Proof.
    red.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      apply isasetaprop.
      apply isapropishom.
  Defined.

  Lemma ishomidfun (a: algebra sigma): ishom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    apply idpath.
  Defined.

  Definition homid (a: algebra sigma): a ↦ a := make_hom (ishomidfun a).

  Lemma ishomcomp  {a1 a2 a3: algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): ishom (h2 ∘ h1).
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

(** * Declaring the new hom_scope for homomorphisms *)

Declare Scope hom_scope.

Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity): hom_scope.

Delimit Scope hom_scope with hom.

Bind Scope hom_scope with hom.

Local Open Scope hom.

Section Unitalgebra.

  (** * The trivial algebra with a single element *)

  Definition unitalgebra (sigma: signature): algebra sigma
    := make_algebra unitset (λ nm: names sigma, tounit).

  Context {sigma: signature}.

  Lemma ishomtounit (a: algebra sigma)
    : @ishom sigma a (unitalgebra sigma) tounit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition unithom (a : algebra sigma): hom a (unitalgebra sigma)
    := make_hom (ishomtounit a).

  Theorem iscontrhomstounit (a: algebra sigma): iscontr (hom a (unitalgebra sigma)).
  Proof.
    exists (unithom a).
    intro t.
    use total2_paths2_f.
    - apply iscontrfuntounit.
    - apply proofirrelevance.
      apply isapropishom.
  Defined.

End Unitalgebra.

Section Natlemmas.

  (** * Lemmas on natural numbers that are used in the rest of the file. *)

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

  Local Lemma statuscons_arith {n1 n2 n3: nat}: n3 ≤ n2 → S (n2 - n3) = n1 → n2 = n1 + n3 - 1.
  Proof.
    intros hp valn1.
    rewrite <- valn1.
    change (S (n2 - n3)) with (1 + (n2 - n3)).
    rewrite natplusassoc.
    rewrite minusplusnmm.
    - rewrite natpluscomm.
      rewrite plusminusnmm.
      apply idpath.
    - assumption.
  Defined.

  Local Lemma oplistsplit_arith1 {n1 n2: nat}: S n1 + n2 - 1 = n1 + n2.
  Proof.
    change (S n1) with (1 + n1).
    rewrite natplusassoc.
    rewrite (natpluscomm 1 (n1 + n2)).
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_arith2 {n1 n2 n3: nat}: S n1 ≤ n2 → n1 + n3 ≤ n2 + n3 - 1.
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

End Natlemmas.

Section Maybe.

  (** * A simple implementation of the option monad *)

  Definition maybe (A: UU):= A ⨿ unit.

  Definition some {A: UU}: A → maybe A := ii1.

  Definition error {A: UU}: maybe A := ii2 tt.

  Context {A: UU}.

  Theorem isasetmaybe (H: isaset A): isaset (maybe A).
  Proof.
    apply isasetcoprod.
    - exact H.
    - exact isasetunit.
  Defined.

  Definition flatmap {B: UU} (f: A → maybe B): maybe A → maybe B
    := coprod_rect _ f (λ _, error).

  Lemma flatmap_some {B: UU} (f: A → maybe B) (a: A)
    : flatmap f (some a) = f a.
  Proof.
    apply idpath.
  Defined.

  Lemma flatmap_error {B: UU} (f: A → maybe B)
    : flatmap f error = error.
  Proof.
    apply idpath.
  Defined.

End Maybe.

Section Listlemmas.

  (** * Proof that cons for list is injective. *)

  Local Definition list_first {A: UU}: list A → maybe A.
  Proof.
    apply list_ind.
    - exact error.
    - exact (λ x xs IH, ii1 x).
  Defined.

  Local Definition list_tail {A: UU}: list A → maybe (list A).
  Proof.
    apply list_ind.
    - exact error.
    - exact (λ x xs IH, ii1 xs).
  Defined.

  Local Lemma list_cons_norm1 {A: UU} (x: A) (xs: list A)
    : list_first (cons x xs) = ii1 x.
  Proof.
    apply idpath.
  Defined.

  Local Lemma list_cons_norm2 {A: UU} (x: A) (xs: list A)
    : list_tail (cons x xs) = ii1 xs.
  Proof.
    apply idpath.
  Defined.

  Local Lemma cons_inj1 {A: UU} (a1 a2: A) (r1 r2: list A)
    : cons a1 r1 = cons a2 r2 → a1 = a2.
  Proof.
    intro H.
    apply (maponpaths list_first) in H.
    do 2 rewrite list_cons_norm1 in H.
    apply ii1_injectivity in H.
    assumption.
  Defined.

  Local Lemma cons_inj2 {A: UU} (a1 a2: A) (r1 r2: list A)
    : cons a1 r1 = cons a2 r2 → r1 = r2.
  Proof.
    intro H.
    apply (maponpaths list_tail) in H.
    do 2 rewrite list_cons_norm2 in H.
    apply ii1_injectivity in H.
    assumption.
  Defined.

  (** * Properties relating length of a list and list concatenation. *)

  Local Lemma length_cons {A: UU} (x: A) (xs: list A)
    : length (cons x xs) = S (length xs).
  Proof.
    apply idpath.
  Defined.

  Local Lemma length_concatenate {A: UU} (l1: list A) (l2: list A)
    : length (concatenate l1 l2) = length l1 + length l2.
  Proof.
    revert l1.
    apply list_ind.
    - apply idpath.
    - intros x xs IH.
      change (S (length (concatenate xs l2)) = S (length xs + length l2)).
      apply maponpaths.
      apply IH.
  Defined.

  Local Lemma length_sublist1 {A: UU} (l1: list A) (l2: list A)
    : length l1 ≤ length (concatenate l1 l2).
  Proof.
    rewrite length_concatenate.
    apply natlehnplusnm.
  Defined.

  Local Lemma length_sublist2 {A: UU} (l1: list A) (l2: list A)
    : length l2 ≤ length (concatenate l1 l2).
  Proof.
    rewrite length_concatenate.
    rewrite natpluscomm.
    apply natlehnplusnm.
  Defined.

  Local Lemma length_zero_b {A: UU} {l: list A}
    : length l = 0 → l = nil.
  Proof.
    intro.
    induction l.
    cbn in X.
    induction (!X).
    induction pr2.
    apply idpath.
  Defined.

End Listlemmas.

Section Oplist.

  (** * Definition of oplist (operations lists) *)
  (**
     An oplist is a list of function symbols, to be interpreted as terms in polish notation.
     To each oplist is associated a status, which may be either a natural numbers, giving the
     number of term corresponding to the oplist, or an error condition, if executing the oplist
     generates a stack underflow. A term is an oplist with status one.
   *)

  Local Definition oplist (sigma: signature) := list (names sigma).

  Identity Coercion oplistislist: oplist >-> list.

  (* ASK!
     Proofs that lists and oplists are sets. It's longer than expected. I would
     have expected a proof that isofhlevel 2 -> isaset, while only the opposite
     is provided.
   *)

  Theorem isasetlist (A: UU): isaset A → isaset (list A).
  Proof.
    intro isasetA.
    apply isaset_total2.
    - apply natset.
    - intro.
      induction x.
      + cbn.
        apply isasetunit.
      + change (Vector A (S x)) with (A × Vector A x).
        apply isaset_dirprod.
        * apply isasetA.
        * apply IHx.
  Defined.

  Local Corollary isasetoplist (sigma: signature): isaset (oplist sigma).
  Proof.
    apply isasetlist.
    apply setproperty.
  Defined.

  Local Definition status: UU := maybe nat.

  (* ASK! I would like to define statusok as "some", but then I would need to unfold "some"
     manually in selected proof. *)

  Local Definition statusok: nat → status := ii1.

  Local Definition statuserror: status := error.

  Local Lemma isasetstatus: isaset status.
  Proof.
    apply isasetmaybe.
    apply isasetnat.
  Defined.
  
  Context {sigma: signature}.
    
  Local Definition statuscons (nm: names sigma) (s: status): status.
  Proof.
    induction s as [n | error].
    - induction (isdecrelnatleh (arity nm) n).
      + exact (statusok ( S(n - arity nm) ) ).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Local Definition oplist2status (l: oplist sigma): status := foldr statuscons (statusok 0) l.
  
  Local Definition isaterm (s: oplist sigma) := oplist2status s = statusok 1.

  Local Definition isapropisaterm (s: oplist sigma): isaprop (isaterm s).
  Proof.
    unfold isaterm.
    apply isasetstatus.
  Defined.
  
End Oplist.

Section OplistProps.

  Context {sigma: signature}.

  (** ** Properties of the statuscons and oplist2status operators *)

  Local Lemma statuscons_statusok_f {nm: names sigma} {n: nat} (p: arity nm ≤ n)
    : statuscons nm (statusok n) = statusok (S (n - arity nm)).
  Proof.
    cbn [statuscons statusok some coprod_rect].
    induction (isdecrelnatleh (arity nm) n) as [ok | error] ; cbn.
    - apply idpath.
    - contradiction.
  Defined.

  Local Lemma statuscons_statusok_b {nm: names sigma} {status: status} {m: nat}
    : statuscons nm status = statusok m → m > 0 × status = statusok (m + arity nm - 1).
  Proof.
    intro scons.
    induction status as [n | error1].
    - cbn [statuscons statusok coprod_rect] in scons.
      induction (isdecrelnatleh (arity nm) n) as [ok | error2]; cbn in scons.
      + apply ii1_injectivity in scons.
        split.
        * rewrite <- scons.
          apply natgthsn0.
        * apply maponpaths.
          apply statuscons_arith ; assumption.
      + apply negpathsii2ii1 in scons.
        contradiction.
    - apply negpathsii2ii1 in scons.
      contradiction.
  Defined.

  Local  Lemma statuscons_zero_b {nm: names sigma} {status: status}
    : ¬ (statuscons nm status = statusok 0).
  Proof.
    intro scons.
    apply statuscons_statusok_b in scons.
    induction scons as [contr _].
    apply isirreflnatgth in contr.
    assumption.
  Defined.

  Local Lemma oplist2status_nil
    : oplist2status (nil: oplist sigma) = statusok 0.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_cons {nm: names sigma} {l: oplist sigma}
    : oplist2status (cons nm l) = statuscons nm (oplist2status l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_zero_b {l: oplist sigma}
    : oplist2status l = statusok 0 → l = nil.
  Proof.
    revert l.
    (* ASK! Why apply does not work in the next tactic? *)
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ proof.
      rewrite oplist2status_cons in proof.
      apply statuscons_zero_b in proof.
      contradiction.
  Defined.

  Local Lemma oplist2status_positive_b {l: oplist sigma} {n: nat}
    : oplist2status l = statusok (S n)
       → ∑ (x: names sigma) (xs: oplist sigma), l = cons x xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro proof.
      rewrite oplist2status_nil in proof.
      apply ii1_injectivity in proof.
      apply negpaths0sx in proof.
      contradiction.
    - intros x xs _ proof.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  (** * Behaviour of oplist2status w.r.t. the concatenate operation *)

  Local Definition status_concatenate (s1 s2: status): status.
  Proof.
    induction s2 as [len_s2 | error2].
    - induction s1 as [len_s1 | error1].
      + exact (statusok (len_s1 + len_s2)).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Local Lemma status_concatenate_statuscons {nm: names sigma} {s1 s2: status}
    : (statuscons nm s1 != statuserror)
       → status_concatenate (statuscons nm s1) s2 = statuscons nm (status_concatenate s1 s2).
  Proof.
    induction s1 as [a1 | error1].
    2: contradiction.
    induction s2 as [a2 | error2].
    2: reflexivity.
    intro noerror.
    cbn [statuscons coprod_rect] in noerror.
    cbn [status_concatenate statuscons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) a1) as [ok1 | error1] ; cbn in noerror.
    2: contradiction.
    induction (isdecrelnatleh (arity nm) (a1+a2)) as [ok2 | error2]; cbn.
    - repeat apply maponpaths.
      apply natleh_minusplus.
      assumption.
    - apply fromempty.
      apply error2.
      apply natleh_plusright.
      assumption.
  Defined.

  Local Lemma oplist2status_concatenate {l1 l2: oplist sigma}
    : oplist2status l1 != statuserror
      → oplist2status (concatenate l1 l2)
        = status_concatenate (oplist2status l1) (oplist2status l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
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

  (** * Splits an oplist in an oplist of up to n terms and an oplist of the remaining terms *)

  Local Definition oplistsplit (l: oplist sigma) (n: nat): oplist sigma × oplist sigma.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - intros.
      exact (nil,, nil).
    - intros x xs IH n.
      induction n.
      + exact (nil,, (cons x xs)).
      + set (resind := IH (n + arity x)).
        exact (cons x (pr1 resind) ,, pr2 resind).
  Defined.

  Local Lemma oplistsplit_zero {l: oplist sigma}: oplistsplit l 0 = nil,, l.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - apply idpath.
    - reflexivity.
  Defined.

  Local Lemma oplistsplit_nil {n: nat}: oplistsplit nil n = nil,, nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_cons {x: names sigma} {xs: oplist sigma} {n: nat}
    : oplistsplit (cons x xs) (S n)
      = cons x (pr1 (oplistsplit xs (n + arity x))) ,, (pr2 (oplistsplit xs (n + arity x))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_concatenate (l1 l2: oplist sigma) {m: nat} (n: nat)
    : oplist2status l1 = statusok m → n ≤ m
       → oplistsplit (concatenate l1 l2) n
         = pr1 (oplistsplit l1 n) ,, concatenate (pr2 (oplistsplit l1 n)) l2.
  Proof.
    revert l1 m n.
    refine (list_ind _ _ _).
    - intros m n proofl1 nlehm.
      apply ii1_injectivity in proofl1.
      rewrite <- proofl1 in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x xs IH m n proofl1 nlehn1.
      rewrite concatenateStep.
      induction n.
      + apply idpath.
      + rewrite oplist2status_cons in proofl1.
        apply statuscons_statusok_b in proofl1.
        induction proofl1 as [_ proofxs].
        assert (newnok: S n + arity x - 1 ≤ m + arity x - 1).
        {
          apply natgehandminusl, natlehandplusr.
          assumption.
        }
        set (ind := IH (m + arity x - 1) (S n + arity x - 1) proofxs newnok).
        rewrite oplistsplit_arith1 in ind.
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * apply (maponpaths (λ xs, cons x xs)).
          apply (maponpaths pr1) in ind.
          assumption.
        * apply (maponpaths dirprod_pr2) in ind.
          assumption.
  Defined.

  Local Lemma concatenate_oplistsplit (l: oplist sigma) (n: nat)
    : concatenate (pr1 (oplistsplit l n)) (pr2 (oplistsplit l n)) = l.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IH n.
      induction n.
      + apply idpath.
      + rewrite oplistsplit_cons.
        cbn - [concatenate].
        rewrite concatenateStep.
        rewrite IH.
        apply idpath.
  Defined.

  Local Lemma oplist2status_oplistsplit (l: oplist sigma) {m: nat} (n: nat)
    : oplist2status l = statusok m → n ≤ m
       → oplist2status (pr1 (oplistsplit l n)) = statusok n
         × oplist2status (pr2 (oplistsplit l n)) = statusok (m - n).
  Proof.
    revert l m n.
    refine (list_ind _ _ _).
    - intros m n proofnil nlehm.
      cbn.
      apply ii1_injectivity in proofnil.
      rewrite <- proofnil in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      split ; apply idpath.
    - intros x xs IH m n proofxxs nlehm.
      induction n.
      + rewrite oplistsplit_zero.
        rewrite natminuseqn.
        split ; [apply idpath | assumption].
      + rewrite oplistsplit_cons.
        cbn - [oplist2status].
        rewrite oplist2status_cons in proofxxs.
        apply statuscons_statusok_b in proofxxs.
        induction proofxxs as [ _ proofxxs].
        eapply oplistsplit_arith2 in nlehm.
        induction (IH (m + arity x - 1) (n + arity x) proofxxs nlehm) as [ind1 ind2].
        split.
        * rewrite oplist2status_cons.
          rewrite ind1.
          rewrite statuscons_statusok_f.
          -- apply maponpaths.
             rewrite plusminusnmm.
             apply idpath.
          -- rewrite natpluscomm.
             apply natleh_plusright.
             apply isreflnatleh.
        * rewrite ind2.
          apply maponpaths.
          rewrite NaturalNumbers.natminusminus.
          rewrite <- natplusassoc.
          rewrite (natpluscomm (1+n) (arity x)).
          rewrite <- NaturalNumbers.natminusminus.
          rewrite plusminusnmm.
          apply idpath.
  Defined.

  Local Corollary oplistsplit_self {l: oplist sigma} {n: nat}
    : oplist2status l = statusok n → oplistsplit l n = l ,, nil.
  Proof.
    intro proofl.
    set (H := oplist2status_oplistsplit l n proofl (isreflnatleh n)).
    induction H as [first second].
    set (concat := concatenate_oplistsplit l n).
    rewrite minuseq0' in second.
    apply oplist2status_zero_b in second.
    rewrite second in concat.
    rewrite concatenate_nil in concat.
    apply dirprodeq ; assumption.
  Defined.

End OplistProps.

(*

Section OplistInductionBare.

  Context {sigma: signature}.

  Local Definition oplist_flatten (l: list (oplist sigma)): oplist sigma
    := foldr concatenate nil l.

  Local Lemma oplist_flatten_cons (x: oplist sigma) (xs: list (oplist sigma))
    : oplist_flatten (cons x xs) = concatenate x (oplist_flatten xs).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist_ind_onlength_bare
    (P: oplist sigma → UU)
    (base: P nil)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (oplist sigma) (arity nm))
          (IH: ∏ (i: ⟦ arity nm ⟧), P (el vterm i))
        , P (oplist_make_term nm vterm))
    : (∏ (n: nat) (t: oplist sigma), length t ≤ n →  P t).
  Proof.
    induction n.
    - intros t lent.
      apply natleh0tois0 in lent.
      apply length_zero_b in lent.
      induction (!lent).
      exact base.
    - intros t lent.
    
      set (X := oplist_decompose t statust).
      induction X as [nm [vec [vecterms [veclength normalization]]]].
      induction normalization.
      apply R.
      + assumption.
      + intro i.
        apply IHn.
        * exact (vecterms i).
        * change (S (length (el vec i)) ≤ S n).
          eapply istransnatleh.
          -- apply natlthtolehsn.
             apply veclength.
          -- apply lent.
  Defined.
  
  
  Local Definition oplist_decompose_batre (l: oplist sigma)
    : maybe (∑ (nm:names sigma), Vector (oplist sigma) (arity nm)).
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - exact error.
    - intros x xs l1.
      apply some.
      exists x.
      induction l1 as [l1 | error].
      set (X := oplist2vecoplist_bare xs pxs).
      induction X as [vectail [vecterms [veclength vecflatt]]].
      exists vectail.
      repeat split.
      + exact vecterms.
      + intro i.
        apply natlehtolthsn.
        apply veclength.
      + unfold oplist_make_term.
        rewrite vecflatt.
        apply idpath.
  Defined.

End OplistInductionBare.
*)


Section OpListInduction.

  Context {sigma: signature}.
  
  Local Definition vecoplist2oplist {n: nat} (v: Vector (oplist sigma) n): oplist sigma
    := vector_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist sigma) (xs: Vector (oplist sigma) n)
    : vecoplist2oplist (vcons x xs) = concatenate x (vecoplist2oplist xs).
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n : nat} {v1 v2: Vector (oplist sigma) n}
    (p1: ∏ (i: ⟦ n ⟧), isaterm (el v1 i)) (p2: ∏ (i: ⟦ n ⟧), isaterm (el v2 i))
    : vecoplist2oplist v1 = vecoplist2oplist v2 → v1 = v2.
  Proof.
    intro eq.
    induction n.
    - induction v1.
      induction v2.
      apply idpath.
    - induction v1 as [v1first v1tail].
      induction v2 as [v2first v2tail].
      change (v1first,, v1tail) with (vcons v1first v1tail) in *.
      change (v2first,, v2tail) with (vcons v2first v2tail) in *.
      do 2 rewrite vecoplist2oplist_vcons  in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      rewrite (@oplistsplit_concatenate _ _ _ 1 1 (p1 (●0)) (isreflnatleh _)) in eq.
      rewrite (@oplistsplit_concatenate _ _ _ 1 1 (p2 (●0)) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_self (p1 (●0))) in eq.
      rewrite (oplistsplit_self (p2 (●0))) in eq.
      cbn in eq.
      apply map_on_two_paths.
      + apply (maponpaths pr1 eq).
      + apply IHn.
        * intro i.
          set (opi := (p1 (dni_firstelement i))).
          rewrite el_vcons_tl in opi.
          exact opi.
        * intro i.
          set (opi := (p2 (dni_firstelement i))).
          rewrite el_vcons_tl in opi.
          exact opi.
        * apply (maponpaths (λ l, pr2 l: oplist sigma)) in eq.
          assumption.
  Defined.

  Local Lemma vecoplist2oplist_status {n: nat} (v: Vector (oplist sigma) n)
    (vterms: ∏ (i: ⟦ n ⟧), isaterm (el v i))
    : oplist2status (vecoplist2oplist v) = statusok n.
  Proof.
    induction n.
    - induction v.
      apply idpath.
    - change v with (vcons (hd v) (tl v)).
      rewrite vecoplist2oplist_vcons.
      rewrite oplist2status_concatenate.
      + rewrite IHn.
        * change (hd v) with (el v (●0)).
          rewrite (vterms (●0)).
          apply idpath.
        * intro.
          rewrite el_tl.
          apply vterms.
      + change (hd v) with (el v (●0)).
        rewrite (vterms (●0)).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist (l: oplist sigma) {n: nat} (ln: oplist2status l = statusok n)
    : ∑ (vec: Vector (oplist sigma) n)
      , (∏ (i: ⟦ n ⟧), isaterm (el vec i))
        × (∏ (i: ⟦ n ⟧), length (el vec i) ≤ length l)
        × vecoplist2oplist vec = l.
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
      + apply oplist2status_zero_b in ln.
        rewrite ln.
        apply idpath.
    - intros.
      induction (oplist2status_oplistsplit l 1 ln (natleh0n 0)) as [firstp restp].
      set (first := pr1 (oplistsplit l 1)).
      set (rest := pr2 (oplistsplit l 1)).
      change (S n) with (1 + n) in restp.
      rewrite natpluscomm in restp.
      rewrite plusminusnmm in restp.
      set (H := IHn rest restp).
      induction H as [restvec [reststatus [restlength restvecoplist2oplist]]].
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
          set (H := concatenate_oplistsplit l 1).
          rewrite <- H.
          apply length_sublist1.
        * change (S i ,, i_leq_sn) with (dni_firstelement (i,, i_leq_sn)).
          rewrite el_vcons_tl.
          eapply istransnatleh.
          -- exact (restlength (i ,, i_leq_sn)).
          -- rewrite <- (concatenate_oplistsplit l 1).
             apply length_sublist2.
      + rewrite vecoplist2oplist_vcons.
        rewrite restvecoplist2oplist.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_make_term (nm: names sigma) (vec: Vector (oplist sigma) (arity nm))
    : oplist sigma := cons nm (vecoplist2oplist vec).

  Local Lemma oplist_make_term_status (nm: names sigma) (vec: Vector (oplist sigma) (arity nm))
    (vecterms: (∏ (i: ⟦ arity nm ⟧), isaterm (el vec i)))
    : isaterm (oplist_make_term nm vec).
  Proof.
    unfold oplist_make_term, isaterm.
    rewrite oplist2status_cons.
    rewrite vecoplist2oplist_status.
    - rewrite statuscons_statusok_f.
      + rewrite minuseq0'.
        apply idpath.
      + apply isreflnatleh.
   - exact vecterms.
  Defined.

  Definition oplist_decompose (l: oplist sigma) (l1: oplist2status l = statusok 1):
     ∑ (nm:names sigma) (vec: Vector (oplist sigma) (arity nm))
     , (∏ (i: ⟦ arity nm ⟧), isaterm (el vec i))
       × (∏ (i: ⟦ arity nm  ⟧), length (el vec i) < length l)
       × oplist_make_term nm vec = l.
  Proof.
    revert l l1.
    refine (list_ind _ _ _).
    - intro l1.
      apply ii1_injectivity in l1.
      apply negpaths0sx in l1.
      contradiction.
    - intros x xs IH l1.
      exists x.
      rewrite oplist2status_cons in l1.
      apply statuscons_statusok_b in l1.
      induction l1 as [_ pxs].
      rewrite natpluscomm in pxs.
      rewrite plusminusnmm in pxs.
      set (X := oplist2vecoplist xs pxs).
      induction X as [vectail [vecterms [veclength vecflatt]]].
      exists vectail.
      repeat split.
      + exact vecterms.
      + intro i.
        apply natlehtolthsn.
        apply veclength.
      + unfold oplist_make_term.
        rewrite vecflatt.
        apply idpath.
  Defined.

  Local Lemma oplist_ind_onlength
    (P: oplist sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (oplist sigma) (arity nm))
          (vtermproofs: ∏ (i: ⟦ arity nm ⟧), oplist2status (el vterm i) = statusok 1)
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (oplist_make_term nm vterm))
    : (∏ (n: nat) (t: oplist sigma), oplist2status t = statusok 1 → length t ≤ n →  P t).
  Proof.
    induction n.
    - intros t statust lent.
      apply fromempty.
      apply natleh0tois0 in lent.
      apply oplist2status_positive_b in statust.
      rewrite (pr2 (pr2 statust)) in lent.
      cbn in lent.
      apply negpathssx0 in lent.
      assumption.
    - intros t statust lent.
      set (X := oplist_decompose t statust).
      induction X as [nm [vec [vecterms [veclength normalization]]]].
      apply (transportf P normalization).
      apply R.
      + assumption.
      + intro i.
        apply IHn.
        * exact (vecterms i).
        * change (S (length (el vec i)) ≤ S n).
          eapply istransnatleh.
          -- apply natlthtolehsn.
             apply veclength.
          -- apply lent.
  Defined.

  Theorem oplist_ind
    (P: oplist sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (oplist sigma) (arity nm))
          (vtermproofs: ∏ (i: ⟦ arity nm ⟧), oplist2status (el vterm i) = statusok 1)
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (oplist_make_term nm vterm))
    : (∏ (t: oplist sigma), oplist2status t = statusok 1 → P t).
  Proof.
    intros t prooft.
    exact (oplist_ind_onlength P R (length t) t prooft (isreflnatleh _)).
  Defined.

  Lemma oplist_ind_onlength_step
    (P: oplist sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (oplist sigma) (arity nm))
          (vtermproofs: ∏ (i: ⟦ arity nm ⟧), oplist2status (el vterm i) = statusok 1)
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (oplist_make_term nm vterm))
    (n: nat) (t: oplist sigma) (statust: oplist2status t = statusok 1)
    (lent: length t ≤ S n)
    : oplist_ind_onlength P R (S n) t statust lent
      = transportf P (pr2 (pr2 (pr2 (pr2 (oplist_decompose t statust)))))
        (R (pr1 (oplist_decompose t statust))
          (pr1 (pr2 (oplist_decompose t statust)))
          (pr1 (pr2 (pr2 (oplist_decompose t statust))))
          (λ i : ⟦ arity (pr1 (oplist_decompose t statust)) ⟧,
            oplist_ind_onlength P R n (el (pr1 (pr2 (oplist_decompose t statust))) i)
              (pr1 (pr2 (pr2 (oplist_decompose t statust))) i)
              (istransnatleh
                (natlthtolehsn (length (el (pr1 (pr2 (oplist_decompose t statust))) i))
                    (length t) (pr1 (pr2 (pr2 (pr2 (oplist_decompose t statust)))) i))
                lent))).
  Proof.
    apply idpath.
  Defined.

  Lemma oplist_ind_onlength_nirrelevant
    (P: oplist sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (oplist sigma) (arity nm))
          (vtermproofs: ∏ (i: ⟦ arity nm ⟧), oplist2status (el vterm i) = statusok 1)
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (oplist_make_term nm vterm))
    : ∏ (n m1 m2: nat)
        (m1n: m1 ≤ n) (m2n: m2 ≤ n)
        (t: oplist sigma)
        (statust: oplist2status t = statusok 1)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , oplist_ind_onlength P R m1 t statust lenm1 = oplist_ind_onlength P R m2 t statust lenm2.
  Proof.
    induction n.
    - intros m1 m2 m1n m2n t statust lenm1 lenm2.
      apply fromempty.
      apply natleh0tois0 in m1n.
      rewrite m1n in lenm1.
      apply natleh0tois0 in lenm1.
      apply oplist2status_positive_b in statust.
      rewrite (pr2 (pr2 statust)) in lenm1.
      cbn in lenm1.
      apply negpathssx0 in lenm1.
      assumption.
    - intros m1 m2 m1n m2n t statust lenm1 lenm2.
      induction m1.
      {
        apply fromempty.
        apply natleh0tois0 in lenm1.
        apply oplist2status_positive_b in statust.
        rewrite (pr2 (pr2 statust)) in lenm1.
        cbn in lenm1.
        apply negpathssx0 in lenm1.
        assumption.
      }
      induction m2.
      {
        apply fromempty.
        clear IHm1.
        apply natleh0tois0 in lenm2.
        apply oplist2status_positive_b in statust.
        rewrite (pr2 (pr2 statust)) in lenm2.
        cbn in lenm2.
        apply negpathssx0 in lenm2.
        assumption.
      }
      pose (statust2 := statust).
      apply oplist2status_positive_b in statust2.
      induction statust2 as [x [xs tstruct]].
      induction (! tstruct).
      change (length (cons x xs)) with (S (length xs)) in *.
      do 2 rewrite oplist_ind_onlength_step.
      do 2 apply maponpaths.
      apply funextsec.
      intro i.
      apply IHn.
      + apply natlthsntoleh.
        apply nat_S_lt.
        apply natlehtolthsn.
        assumption.
      + apply natlthsntoleh.
        apply nat_S_lt.
        apply natlehtolthsn.
        assumption.
  Defined.

  Lemma oplist_ind_step
    (nm: names sigma)
    (v: Vector (oplist sigma) (arity nm))
    (vp: ∏ (i: ⟦ arity nm ⟧), oplist2status (el v i) = statusok 1):
    ∏ (P: oplist sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (oplist sigma) (arity nm))
              (vtermproofs: ∏ (i: ⟦ arity nm ⟧), oplist2status (el vterm i) = statusok 1) ,
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (oplist_make_term nm vterm))
      (vterms: ∏ (i:  ⟦ arity nm ⟧), oplist2status (el v i) = statusok 1),
    oplist_ind P Ind (oplist_make_term nm v) (oplist_make_term_status nm v vterms) =
       Ind nm v vp (λ i:  ⟦ arity nm ⟧, oplist_ind P Ind (el v i) (vterms i)).
  Proof.
    intros.
    unfold oplist_ind.
    unfold oplist_make_term in *.
    change (length (cons nm (vecoplist2oplist v))) with (S (length (vecoplist2oplist v))) in *.
    unfold oplist_ind_onlength at 1.
    rewrite nat_rect_step.
    set (d := oplist_decompose (cons nm (vecoplist2oplist v)) (oplist_make_term_status nm v vterms)).
    induction d as [nm0 [vterms0 [v0status [v0len v0norm ]]]].
    unfold oplist_make_term in v0norm.
    pose (X1 := v0norm).
    pose (X2 := v0norm).
    apply cons_inj1 in X1.
    apply cons_inj2 in X2.
    induction (! X1).
    apply vecoplist2oplist_inj in X2.
    induction (! X2).
    assert (H1: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetoplist.
    }
    rewrite H1.
    rewrite idpath_transportf.
    assert (H2: vterms = v0status).
    {
      apply impred_isaprop.
      intros.
      apply isasetstatus.
    }
    induction H2.
    assert (H3: vterms = vp).
    {
          apply impred_isaprop.
      intros.
      apply isasetstatus.
    }
    induction H3.
    apply maponpaths.
    apply funextsec.
    intro i.
    assert ( oplist_ind_onlength P Ind
                (length (el v i))
                (el v i) (vterms i)
                (isreflnatleh (length (el v i)))  =

                oplist_ind_onlength P Ind
                (length (vecoplist2oplist v))
                (el v i) (vterms i)  (istransnatleh
                (natlthtolehsn (length (el v i)) (length (cons nm (vecoplist2oplist v)))
                   (v0len i)) (isreflnatleh (S (length (vecoplist2oplist v))))) ).
    {
       apply (oplist_ind_onlength_nirrelevant P Ind (length (vecoplist2oplist v))).
       - apply natlthsntoleh.
         apply (v0len i).
       - apply isreflnatleh.
    }
    rewrite X.
    apply idpath.
    assumption.
    assumption.
  Defined.

  Definition oplist_depth (t: oplist sigma) (prooft: oplist2status t = statusok 1): nat
    := oplist_ind (λ t: oplist sigma, nat)
                (λ (nm: names sigma) vterm vp
                   (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) )
                  t prooft.

End OpListInduction.

Section Term.

  Definition term (sigma: signature)
     := ∑ s: oplist sigma, isaterm s.

  Definition make_term {sigma: signature} (s: oplist sigma) (p: isaterm s)
    : term sigma := s ,, p.

  Coercion term2oplist {sigma: signature} (t: term sigma):
    oplist sigma := pr1 t.

  Definition term2proof {sigma: signature} (t: term sigma):
    isaterm t := pr2 t.

  Lemma isasetterm(sigma: signature): isaset (term sigma).
  Proof.
    apply isaset_total2.
    - apply isasetoplist.
    - intros.
      apply isasetaprop.
      apply isasetstatus.
  Defined.

  Definition termset (sigma : signature): hSet
    := make_hSet (term sigma) (isasetterm sigma).

  Context {sigma: signature}.

  Lemma term_extens {s1 s2 : term sigma} (p : term2oplist s1 = term2oplist s2)
    : s1 = s2.
  Proof.
    apply subtypePath.
    2: exact p.
    intros s.
    apply isasetstatus.
  Defined.

  Definition build_term (nm: names sigma) (vec: Vector (term sigma) (arity nm)): term sigma.
  Proof.
    exists (oplist_make_term nm (vector_map term2oplist vec)).
    apply oplist_make_term_status.
    intro i.
    rewrite el_vector_map.
    exact (term2proof (el vec i)).
  Defined.

  Definition princop (t: term sigma): names sigma
    := pr1 (oplist_decompose (term2oplist t) (term2proof t)).

  Definition subterms (t: term sigma): Vector (term sigma) (arity (princop t))
    := let X := oplist_decompose (term2oplist t) (term2proof t) in
       let nm := pr1 X in
       let terms := pr1 ( pr2 X ) in
       let termproofs := pr1 (pr2 (pr2 X)) in
       (mk_vector (λ (i: ⟦ arity nm ⟧), (el terms i ,, termproofs i): term sigma)).

End Term.

Section TermInduction1.

  Context {sigma: signature}.

  (* direct proof without using oplist_ind *)

  Lemma vectormap_mkvector {A B: UU} {n} {g: ⟦ n ⟧ → A} {f: A → B}
    : vector_map f (mk_vector g) = mk_vector (f ∘ g).
  Proof.
    apply vector_extens.
    intro i.
    apply (transportb (λ x, x = _) (el_vector_map _ _ _)).
    apply (transportb (λ x, f (x i) = _) (el_mk_vector _)).
    apply (transportb (λ x, _ = x i) (el_mk_vector _)).
    apply idpath.
  Defined.
  
  Lemma mk_vector_fun {A: UU} {n:nat} {v: Vector A n}
    : mk_vector (λ (i: ⟦ n ⟧), el v i) = v.
  Proof.
    apply vector_extens.
    intro i.
    rewrite el_mk_vector.
    apply idpath.
  Defined.

  Definition term_decompose (t: term sigma):
       ∑ (nm:names sigma) (vec: Vector (term sigma) (arity nm))
      , (∏ (i: ⟦ arity nm  ⟧), length (el vec i) < length t)
         × build_term nm vec = t.
  Proof.
    induction t as [l l1].
    revert l l1.
    refine (list_ind _ _ _).
    - intro l1.
      apply fromempty.
      unfold isaterm in l1.
      apply ii1_injectivity in l1.
      apply negpaths0sx in l1.
      contradiction.
    - intros x xs IH l1.
      exists x.
      unfold isaterm in l1.
      rename l1 into l1prime.
      pose (l1 := l1prime).
      rewrite oplist2status_cons in l1.
      apply statuscons_statusok_b in l1.
      induction l1 as [_ pxs].
      rewrite natpluscomm in pxs.
      rewrite plusminusnmm in pxs.
      set (X := oplist2vecoplist xs pxs).
      induction X as [vectail [vecterms [veclength vecflatt]]].
      exists (mk_vector (λ i: ⟦ arity x ⟧, make_term (el vectail i) (vecterms i))).
      split.
      + intro i.
        rewrite el_mk_vector.
        cbn - [natlth].
        apply natlehtolthsn.
        apply veclength.
      + apply subtypePath.
        * unfold isPredicate.
          intro.
          apply isapropisaterm.
        * cbn.
          unfold oplist_make_term.
          rewrite vectormap_mkvector.
          change (term2oplist ∘ (λ i : ⟦ arity x ⟧, make_term (el vectail i) (vecterms i))) with (λ i : ⟦ arity x ⟧, el vectail i).
          rewrite mk_vector_fun.
          apply maponpaths.
          apply vecflatt.
  Defined.
  
  Lemma term_ind_onlength
    (P: term sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm) )
    : ∏ (n: nat) (t: term sigma), length t ≤ n →  P t.
  Proof.
    induction n.
    - intros t lent.
      induction t as [t statust].
      cbn in lent.
      apply fromempty.
      apply natleh0tois0 in lent.
      unfold isaterm in statust.
      apply oplist2status_positive_b in statust.
      rewrite (pr2 (pr2 statust)) in lent.
      cbn in lent.
      apply negpathssx0 in lent.
      assumption.
    - intros t lent.
      set (X := term_decompose t).
      induction X as [nm [vec [veclen normalization]]].
      apply (transportf P normalization).
      (* rewrite <- normalization. *)
      (* induction normalization. *)(* only in term_ind, not in term_rec *)
      apply (R nm vec).
      intro i.
      apply (IHn (el vec i)).
      change (S (length (el vec i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
         apply veclen.
      -- apply lent.
  Defined.
  
  Theorem term_ind
    (P: term sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm) )
    : ∏ (t: term sigma), P t.
  Proof.
    intro t.
    exact (term_ind_onlength P R (length t) t (isreflnatleh _)).
  Defined.
  
  Lemma term_ind_onlength_step
    (P: term sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm) )
    (n: nat) (t: term sigma)
    (lent: length t ≤ S n)
    : term_ind_onlength P R (S n) t lent = transportf P (pr2 (pr2 (pr2 (term_decompose t))))
    (R (pr1 (term_decompose t)) (pr1 (pr2 (term_decompose t)))
       (λ i : ⟦ arity (pr1 (term_decompose t)) ⟧,
        term_ind_onlength P R n (el (pr1 (pr2 (term_decompose t))) i)
          (istransnatleh
             (natlthtolehsn (length (el (pr1 (pr2 (term_decompose t))) i)) 
                (length t) (pr1 (pr2 (pr2 (term_decompose t))) i)) lent))).
  Proof.
    apply idpath.
  Defined.
 
  Lemma term_ind_onlength_nirrelevant
    (P: term sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm))
    : ∏ (n m1 m2: nat)
        (m1n: m1 ≤ n) (m2n: m2 ≤ n)
        (t: term sigma)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 t lenm1 = term_ind_onlength P R m2 t lenm2.
  Proof.
    induction n.
    - intros m1 m2 m1n m2n t lenm1 lenm2.
      induction t as [t statust]. (* for term_ind *)
      cbn in lenm1, lenm2. (* for term_ind *)
      unfold isaterm in statust. (* for term_ind *)
      apply fromempty.
      apply natleh0tois0 in m1n.
      rewrite m1n in lenm1.
      apply natleh0tois0 in lenm1.
      apply oplist2status_positive_b in statust.
      rewrite (pr2 (pr2 statust)) in lenm1.
      cbn in lenm1.
      apply negpathssx0 in lenm1.
      assumption.
    - intros m1 m2 m1n m2n t lenm1 lenm2.
      induction t as [t statust]. (* for term_ind *)
      cbn in lenm1, lenm2. (* for term_ind *)
      unfold isaterm in statust. (* for term_ind *)
      induction m1.
      {
        apply fromempty.
        apply natleh0tois0 in lenm1.
        apply oplist2status_positive_b in statust.
        rewrite (pr2 (pr2 statust)) in lenm1.
        cbn in lenm1.
        apply negpathssx0 in lenm1.
        assumption.
      }
      induction m2.
      {
        apply fromempty.
        clear IHm1.
        apply natleh0tois0 in lenm2.
        apply oplist2status_positive_b in statust.
        rewrite (pr2 (pr2 statust)) in lenm2.
        cbn in lenm2.
        apply negpathssx0 in lenm2.
        assumption.
      }
      pose (statust2 := statust).
      apply oplist2status_positive_b in statust2.
      induction statust2 as [x [xs tstruct]].
      induction (! tstruct).
      change (length (cons x xs)) with (S (length xs)) in *.
      do 2 rewrite term_ind_onlength_step.
      do 2 apply maponpaths.
      apply funextsec.
      intro i.
      apply IHn.
      + apply natlthsntoleh.
        apply nat_S_lt.
        apply natlehtolthsn.
        assumption.
      + apply natlthsntoleh.
        apply nat_S_lt.
        apply natlehtolthsn.
        assumption.
  Defined.

  Lemma term_ind_step
    (nm: names sigma)
    (v: Vector (term sigma) (arity nm))
    : ∏ (P: term sigma → UU)
        (R: ∏ (nm: names sigma)
              (vterm: Vector (term sigma) (arity nm))
              (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
            , P (build_term nm vterm))
      , term_ind P R (build_term nm v)
         = R nm v (λ i:  ⟦ arity nm ⟧, term_ind P R (el v i)).
  Proof.
    intros.
    unfold term_ind.
    unfold build_term in *.
    unfold oplist_make_term in *.
    unfold term2oplist.
    cbn [pr1].
    change (length (cons nm (vecoplist2oplist (vector_map (λ t : term sigma, pr1 t) v)))) with 
      (S (length (vecoplist2oplist (vector_map (λ t : term sigma, pr1 t) v)))).
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    set (p := oplist_make_term_status nm (vector_map (λ t : term sigma, pr1 t) v)
                 (λ i : ⟦ arity nm ⟧,
                  internal_paths_rew_r (oplist sigma)
                    (el (vector_map (λ t : term sigma, pr1 t) v) i) 
                    (pr1 (el v i)) (λ o : oplist sigma, isaterm o)
                    (term2proof (el v i)) (el_vector_map (λ t : term sigma, pr1 t) v i))).
    set (t := (cons nm (vecoplist2oplist (vector_map (λ t : term sigma, pr1 t) v)))).
    set (d := term_decompose (t ,, p)).
    change (term_decompose (t ,, p)) with d.
    induction d as [nm0 [vterms0 [v0len v0norm]]].
    unfold p in v0norm.
    unfold t in v0norm.
    unfold build_term in v0norm.
    unfold oplist_make_term in v0norm.
    pose (X1 := maponpaths pr1 v0norm).
    cbn in X1.
    pose (X2 := maponpaths pr1 v0norm).
    cbn in X2.
    apply cons_inj1 in X1.
    apply cons_inj2 in X2.
    induction (! X1).
    apply vecoplist2oplist_inj in X2.
    - 
      unfold term2oplist in X2.
      unfold term2oplist in v0norm.
      assert ( X3: vterms0 = v ).
      {
        apply vector_extens.
        intro i.
        apply term_extens.
        apply (maponpaths (λ v, el v i)) in X2.
        do 2 rewrite el_vector_map in X2.
        apply X2. 
      }
      induction (! X3).
      assert (H1: v0norm = idpath _).
      {
        apply proofirrelevance.
        apply isasetterm.
      }
      rewrite H1.
      rewrite idpath_transportf.
      apply maponpaths.
      apply funextsec.
      intro i.
      assert ( term_ind_onlength P R
                  (length (el v i))
                  (el v i)
                  (isreflnatleh (length (el v i)))  =

                  term_ind_onlength P R
                  (length (vecoplist2oplist (vector_map (λ t0 : term sigma, pr1 t0) v)))
                  (el v i)  (istransnatleh
       (natlthtolehsn (length (term2oplist (el v i))) (length (term2oplist (t,, p)))
          (v0len i))
       (isreflnatleh
          (S (length (vecoplist2oplist (vector_map (λ t0 : term sigma, pr1 t0) v))))))
                  ).
      {
         apply (term_ind_onlength_nirrelevant P R (length (vecoplist2oplist (vector_map (λ t0 : term sigma, pr1 t0) v)))).
         - apply natlthsntoleh.
           apply (v0len i).
         - apply isreflnatleh.
      }
      unfold term2oplist in X.
      rewrite X.
      apply idpath.
    - intro i.
      rewrite el_vector_map.
      apply (el vterms0 i).
    - intro i.
      rewrite el_vector_map.
      apply (el v i).
  Defined.

  Definition depth_ind: term sigma → nat
    := term_ind (λ _, nat)
                (λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                   (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels)).

  Lemma term_rec_onlength {A: UU}
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ⟦ arity nm ⟧ → A)
        , A )
    : ∏ (n: nat) (t: term sigma), length t ≤ n →  A.
  Proof.
    induction n.
    - intros t lent.
      induction t as [t statust].
      cbn in lent.
      apply fromempty.
      apply natleh0tois0 in lent.
      unfold isaterm in statust.
      apply oplist2status_positive_b in statust.
      rewrite (pr2 (pr2 statust)) in lent.
      cbn in lent.
      apply negpathssx0 in lent.
      assumption.
    - intros t lent.
      set (X := term_decompose t).
      induction X as [nm [vec [veclen normalization]]].
      apply (R nm vec).
      intro i.
      apply (IHn (el vec i)).
      change (S (length (el vec i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
         apply veclen.
      -- apply lent.
  Defined.
  
  Theorem term_rec {A: UU}
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), A)
        , A )
    : ∏ (t: term sigma), A.
  Proof.
    intro t.
    exact (term_rec_onlength R (length t) t (isreflnatleh _)).
  Defined.
  
  Definition depth_rec: term sigma → nat
    := term_rec ( λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                    (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) ).
                    
End TermInduction1.

Section TermInduction2.

  Context {sigma: signature}.
  
  (* uses oplist_ind *)
  
  Definition make_vector_term {n}
    (vterm: Vector (oplist sigma) n)
    (vtermproofs: ∏ (i: ⟦ n ⟧), isaterm (el vterm i))
    : Vector (term sigma) n
    := mk_vector (λ i, make_term (el vterm i) (vtermproofs i)).

  Lemma make_vector_term1 (nm: names sigma)
    (vterm: Vector (oplist sigma) (arity nm))
    (vtermproofs: ∏ (i: ⟦ arity nm ⟧), isaterm (el vterm i))
    (w: isaterm (oplist_make_term nm vterm))
    : make_term (oplist_make_term nm vterm) w = build_term nm (make_vector_term vterm vtermproofs).
  Proof.
    unfold build_term.
    apply subtypePath.
    - intro.
      apply isapropisaterm.
    - cbn.
      apply maponpaths.
      apply vector_extens.
      intro i.
      unfold make_vector_term.
      rewrite vectormap_mkvector.
      rewrite el_mk_vector.
      apply idpath.
  Defined.
  
  Lemma make_vector_term2 (nm: names sigma)
    (vterm: Vector (oplist sigma) (arity nm))
    (vtermproofs: ∏ (i: ⟦ arity nm ⟧), isaterm (el vterm i))
    : oplist_make_term nm vterm = build_term nm (make_vector_term vterm vtermproofs).
  Proof.
    unfold build_term.
    cbn.
    apply maponpaths.
    apply vector_extens.
    intro i.
    unfold make_vector_term.
    rewrite vectormap_mkvector.
    rewrite el_mk_vector.
    apply idpath.
  Defined.
 
  Theorem term_ind2
    (P: term sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm) )
    : (∏ t: term sigma, P t).
  Proof.
    intro t.
    set (Q := λ (s: oplist sigma), ∏ (w: isaterm s), P (make_term s w)).
    apply (oplist_ind Q).
    2: apply t.
    unfold Q.
    intros.
    rewrite (make_vector_term1 nm vterm vtermproofs).
    apply R.
    intro.
    unfold make_vector_term.
    rewrite el_mk_vector.
    apply IH.
  Defined.
  
  Theorem term_ind3
    (P: oplist sigma → UU)
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i:  ⟦ arity nm ⟧), P (el vterm i))
        , P (build_term nm vterm) )
    : (∏ t: term sigma, P t).
  Proof.
    intro t.
    apply oplist_ind.
    2: apply t.
    intros.
    (* we do not have improvements by using rewrite or induction *)
    apply (transportb P (make_vector_term2 nm vterm vtermproofs)).
    apply R.
    intro.
    unfold make_vector_term.
    (* we do not have improvements by using rewrite or induction *)
    apply (transportb (λ f, P (term2oplist (f i))) (el_mk_vector (λ i0 : ⟦ arity nm ⟧, (make_term (el vterm i0) (vtermproofs i0))))).
    apply IH.
  Defined.

  Definition depth_ind2: term sigma → nat
    := term_ind2 (λ _, nat)
                 (λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                     (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels)).
                     
  Definition depth_ind3: term sigma → nat
    := term_ind2 (λ _, nat)
                 (λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                     (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels)).
  
  Theorem term_rec2 {A: UU}
    (R: ∏ (nm: names sigma)
          (vterm: Vector (term sigma) (arity nm))
          (IH: ∏ (i: ⟦ arity nm ⟧), A)
        , A )
    : (∏ t: term sigma, A).
  Proof.
    intro t.
    set (Q := λ (s: oplist sigma), A).
    refine (oplist_ind Q _ t (term2proof t)).
    unfold Q.
    intros.
    set (vterm' := make_vector_term vterm vtermproofs).
    apply (R nm vterm' IH).
  Defined.

  Definition depth_rec2: term sigma → nat
    := term_rec2 (λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                    (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels) ).

(*
  Lemma term_ind_step (nm: names sigma) (v: Vector (term sigma) (arity nm)):
    ∏ (P: oplist sigma → UU)
      (Ind: ∏ (nm: names sigma) (vterm: Vector (term sigma) (arity nm)),
              (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (build_term nm vterm)),
              term_ind P Ind (build_term nm v) = Ind nm v (λ i:  ⟦ arity nm ⟧, term_ind P Ind (el v i)).
  Proof.
    intros.
    unfold term_ind.
    unfold build_term.
    simpl.
    assert (vproofterms : ∏ (i: ⟦ arity nm ⟧), isaterm (el (vector_map term2oplist v) i)).
    {
      intro i.
      rewrite el_vector_map.
      apply (term2proof (el v i)).
    }
    rewrite oplist_ind_step with (vp := vproofterms).
    assert (X: make_vector_term (vector_map term2oplist v) vproofterms = v).
    {
      apply vector_extens.
      intro i.
      unfold make_vector_term.
      rewrite el_mk_vector.
      apply term_extens.
      cbn.
      rewrite el_vector_map.
      apply idpath.
    }
    set (Y := (make_vector_term1 nm (vector_map term2oplist v) vproofterms
       (oplist_make_term_status nm (vector_map term2oplist v)
          (λ i : ⟦ arity nm ⟧,
           transportb (λ x : oplist sigma, oplist2status x = statusok 1)
             (el_vector_map term2oplist v i) (pr2 (el v i)))))).
    clearbody Y.
    unfold build_term in Y.
    rewrite X in Y.
    .induction (!X) in Y.
    assert (Yidpath : Y = idpath _).
    {  apply proofirrelevance.
       apply isasetterm.
    }
    rewrite Yidpath.

  Abort.

  **)

 
End TermInduction2.

Section termalgebra.

  Definition term_algebra (sigma: signature): algebra sigma
    := make_algebra (termset sigma) build_term.

  (** TODO

  Definition initial_hom {sigma: signature} (a: algebra sigma): term_algebra sigma ↦ a.

  Definition initial_hom_unicity {sigma: signature} (a: algebra sigma) (f: hom term_algebra a)
     : f = initial_hom a.

  **)

End termalgebra.
