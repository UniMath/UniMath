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
    := ∏ (nm: names sigma) (x: dom a1 nm), f (op a1 nm x) = (op a2 nm (vector_map f x)).

  Definition hom (a1 a2: algebra sigma): UU := ∑ (f: a1 → a2), ishom f.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {a1 a2: algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2axiom {a1 a2: algebra sigma} (f: a1 ↦ a2): ishom f := pr2 f.

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

  Theorem isasethom (a1 a2: algebra sigma): isaset (a1 ↦ a2).
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
    intros.
    apply subtypePairEquality'.
    - apply iscontrfuntounit.
    - apply isapropishom.
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

  (** * Properties of the length of a list. *)

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

End Listlemmas.

Section Oplist.

  (** * Definition of oplist (operations lists) *)
  (**
     An oplist is a list of function symbols, to be interpreted as sequence of terms in
     polish notation. To each oplist is associated a status, which may be either a natural
     number, giving the number of terms corresponding to the oplist, or an error condition,
     if executing the oplist generates a stack underflow. A term is an oplist with status one.
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
    - intro n.
      induction n.
      + cbn.
        apply isasetunit.
      + change (Vector A (S n)) with (A × Vector A n).
        apply isaset_dirprod.
        * apply isasetA.
        * apply IHn.
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
    induction s as [s | serror].
    - induction (isdecrelnatleh (arity nm) s) as [arityok | arityerror].
      + exact (statusok ( S(s - arity nm) ) ).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Local Definition oplist2status (l: oplist sigma): status := foldr statuscons (statusok 0) l.

  Local Definition isaterm (l: oplist sigma) := oplist2status l = statusok 1.

  Local Lemma isapropisaterm (l: oplist sigma): isaprop (isaterm l).
  Proof.
    unfold isaterm.
    apply isasetstatus.
  Defined.

End Oplist.

Section OplistProps.

  Context {sigma: signature}.

  (** ** Properties of the statuscons and oplist2status operators *)

  Local Lemma statuscons_statusok_f {nm: names sigma} {n: nat} (aritynm: arity nm ≤ n)
    : statuscons nm (statusok n) = statusok (S (n - arity nm)).
  Proof.
    cbn [statuscons statusok coprod_rect].
    (* ASK
       Alternatively, "unfold statuscons, statusok, coprod_rect" produces a better
       looking term, but with a match. Which is better?
    *)
    induction (isdecrelnatleh (arity nm) n) as [arityok | arityerror] ; cbn.
    - apply idpath.
    - contradiction.
  Defined.

  Local Lemma statuscons_statusok_b {nm: names sigma} {s: status} {m: nat}
    : statuscons nm s = statusok m → m > 0 × s = statusok (m + arity nm - 1).
  Proof.
    intro scons.
    induction s as [s | serror].
    - cbn [statuscons statusok coprod_rect] in scons.
      induction (isdecrelnatleh (arity nm) s) as [arityok | arityerror]; cbn in scons.
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

  Local  Lemma statuscons_zero_b {nm: names sigma} {s: status}
    : ¬ (statuscons nm s = statusok 0).
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
    - intros x xs _ lstatus.
      rewrite oplist2status_cons in lstatus.
      apply statuscons_zero_b in lstatus.
      contradiction.
  Defined.

  Local Lemma oplist2status_positive_b {l: oplist sigma} {n: nat}
    : oplist2status l = statusok (S n)
      → ∑ (x: names sigma) (xs: oplist sigma), l = cons x xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro nilstatus.
      rewrite oplist2status_nil in nilstatus.
      apply ii1_injectivity in nilstatus.
      apply negpaths0sx in nilstatus.
      contradiction.
    - intros x xs _ lstatus.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  (** * Behaviour of oplist2status w.r.t. the concatenate operation *)

  Local Definition statusconcatenate (s1 s2: status): status.
  Proof.
    induction s2 as [s2 | s2error].
    - induction s1 as [s1 | s1error].
      + exact (statusok (s1 + s2)).
      + exact statuserror.
    - exact statuserror.
  Defined.

  Local Lemma statusconcatenate_statuscons {nm: names sigma} {s1 s2: status}
    : (statuscons nm s1 != statuserror)
       → statusconcatenate (statuscons nm s1) s2 = statuscons nm (statusconcatenate s1 s2).
  Proof.
    induction s1 as [s1 | s1error].
    2: contradiction.
    induction s2 as [s2 | s2error].
    2: reflexivity.
    intro noerror.
    cbn [statuscons coprod_rect] in noerror.
    cbn [statusconcatenate statuscons statusok coprod_rect].
    induction (isdecrelnatleh (arity nm) s1) as [arityok1 | arityerror1] ; cbn in noerror.
    2: contradiction.
    induction (isdecrelnatleh (arity nm) (s1+s2)) as [arityok2 | arityerror2]; cbn.
    - repeat apply maponpaths.
      apply natleh_minusplus.
      assumption.
    - apply fromempty.
      apply arityerror2.
      apply natleh_plusright.
      assumption.
  Defined.

  Local Lemma oplist2status_concatenate {l1 l2: oplist sigma}
    : oplist2status l1 != statuserror
      → oplist2status (concatenate l1 l2)
        = statusconcatenate (oplist2status l1) (oplist2status l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
    - intros.
      change (concatenate nil l2) with (l2).
      induction (oplist2status l2) as [s2 | s2error].
      + apply idpath.
      + induction s2error.
        apply idpath.
    - intros x xs IH noerror.
      rewrite oplist2status_cons.
      rewrite statusconcatenate_statuscons by (assumption).
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
      + induction (IH (n + arity x)) as [IHfirst IHsecond].
        exact (cons x IHfirst ,, IHsecond).
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
    - intros m n l1status nlehm.
      apply ii1_injectivity in l1status.
      rewrite <- l1status in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IH m n l1status nlehm.
      rewrite concatenateStep.
      induction n.
      + apply idpath.
      + rewrite oplist2status_cons in l1status.
        apply statuscons_statusok_b in l1status.
        induction l1status as [_ xs1status].
        assert (newnok: S n + arity x1 - 1 ≤ m + arity x1 - 1).
        {
          apply natgehandminusl, natlehandplusr.
          assumption.
        }
        set (IHinst := IH (m + arity x1 - 1) (S n + arity x1 - 1) xs1status newnok).
        rewrite oplistsplit_arith1 in IHinst.
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * cbn.
          apply maponpaths.
          apply (maponpaths pr1) in IHinst.
          cbn in IHinst.
          assumption.
        * apply (maponpaths dirprod_pr2) in IHinst.
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
    - intros m n nilstatus nlehm.
      cbn.
      apply ii1_injectivity in nilstatus.
      rewrite <- nilstatus in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      split ; apply idpath.
    - intros x xs IH m n lstatus nlehm.
      induction n.
      + rewrite oplistsplit_zero.
        rewrite natminuseqn.
        split ; [apply idpath | assumption].
      + rewrite oplistsplit_cons.
        cbn - [oplist2status].
        rewrite oplist2status_cons in lstatus.
        apply statuscons_statusok_b in lstatus.
        induction lstatus as [ _ xsstatus].
        eapply oplistsplit_arith2 in nlehm.
        induction (IH (m + arity x - 1) (n + arity x) xsstatus nlehm) as [IH1 IH2].
        split.
        * rewrite oplist2status_cons.
          rewrite IH1.
          rewrite statuscons_statusok_f.
          -- apply maponpaths.
             rewrite plusminusnmm.
             apply idpath.
          -- rewrite natpluscomm.
             apply natleh_plusright.
             apply isreflnatleh.
        * rewrite IH2.
          apply maponpaths.
          rewrite natminusminus.
          rewrite <- natplusassoc.
          rewrite (natpluscomm (1+n) (arity x)).
          rewrite <- natminusminus.
          rewrite plusminusnmm.
          apply idpath.
  Defined.

  Local Corollary oplistsplit_self {l: oplist sigma} {n: nat}
    : oplist2status l = statusok n → oplistsplit l n = l ,, nil.
  Proof.
    intro lstatus.
    set (H := oplist2status_oplistsplit l n lstatus (isreflnatleh n)).
    induction H as [l1status l2status].
    set (normalization := concatenate_oplistsplit l n).
    rewrite minuseq0' in l2status.
    apply oplist2status_zero_b in l2status.
    rewrite l2status in normalization.
    rename l2status into oplistsplit_first.
    rewrite concatenate_nil in normalization.
    rename normalization into oplisplit_second.
    apply dirprodeq ; assumption.
  Defined.

  (** ** Extract of subterms of an oplist, in the form of vectors of oplists *)

  Local Definition vecoplist2oplist {n: nat} (v: Vector (oplist sigma) n): oplist sigma
    := vector_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist sigma) (v: Vector (oplist sigma) n)
    : vecoplist2oplist (vcons x v) = concatenate x (vecoplist2oplist v).
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n : nat} {v1 v2: Vector (oplist sigma) n}
    (v1status: ∏ (i: ⟦ n ⟧), isaterm (el v1 i))
    (v2status: ∏ (i: ⟦ n ⟧), isaterm (el v2 i))
    : vecoplist2oplist v1 = vecoplist2oplist v2 → v1 = v2.
  Proof.
    intro eq.
    induction n.
    - induction v1.
      induction v2.
      apply idpath.
    - change v1 with (vcons (hd v1) (tl v1)) in *.
      change v2 with (vcons (hd v2) (tl v2)) in *.
      do 2 rewrite vecoplist2oplist_vcons in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 (v1status firstelement) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 (v2status firstelement) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_self (v1status firstelement)) in eq.
      rewrite (oplistsplit_self (v2status firstelement)) in eq.
      cbn in eq.
      apply map_on_two_paths.
      + apply (maponpaths pr1 eq).
      + apply IHn.
        * intro i.
          rewrite el_tl.
          apply v1status.
        * intro i.
          rewrite el_tl.
          apply v2status.
        * apply (maponpaths (λ l, pr2 l: oplist sigma)) in eq.
          assumption.
  Defined.

  Local Lemma oplist2status_vecoplist2oplist {n: nat} {v: Vector (oplist sigma) n}
    (vstatus: ∏ (i: ⟦ n ⟧), isaterm (el v i))
    : oplist2status (vecoplist2oplist v) = statusok n.
  Proof.
    induction n.
    - induction v.
      apply idpath.
    - change v with (vcons (hd v) (tl v)).
      rewrite vecoplist2oplist_vcons.
      rewrite oplist2status_concatenate.
      + rewrite IHn.
        * change (hd v) with (el v firstelement).
          rewrite (vstatus firstelement).
          apply idpath.
        * intro.
          rewrite el_tl.
          apply vstatus.
      + change (hd v) with (el v firstelement).
        rewrite (vstatus firstelement).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist (l: oplist sigma) {n: nat} (lstatus: oplist2status l = statusok n)
    : ∑ (v: Vector (oplist sigma) n)
      , (∏ (i: ⟦ n ⟧), isaterm (el v i))
        × (∏ (i: ⟦ n ⟧), length (el v i) ≤ length l)
        × vecoplist2oplist v = l.
  Proof.
    revert l lstatus.
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
      + apply oplist2status_zero_b in lstatus.
        rewrite lstatus.
        apply idpath.
    - intros.
      induction (oplist2status_oplistsplit l 1 lstatus (natleh0n 0)) as [firststatus reststatus].
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      cbn in rest.
      change (S n) with (1 + n) in reststatus.
      rewrite natpluscomm in reststatus.
      rewrite plusminusnmm in reststatus.
      induction (IHn rest reststatus) as [v [vstatus [vlen vflatten]]].
      exists (vcons first v).
      repeat split.
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * exact firststatus.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite el_vcons_tl.
          exact (vstatus (i ,, ilehsn)).
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * change (el (vcons first v) (0,, ilehsn)) with first.
          rewrite <- (concatenate_oplistsplit l 1).
          apply length_sublist1.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite el_vcons_tl.
          eapply istransnatleh.
          -- exact (vlen (i ,, ilehsn)).
          -- rewrite <- (concatenate_oplistsplit l 1).
             apply length_sublist2.
      + rewrite vecoplist2oplist_vcons.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_build_term (nm: names sigma) (v: Vector (oplist sigma) (arity nm))
    : oplist sigma := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_term_status (nm: names sigma) (v: Vector (oplist sigma) (arity nm))
    (vstatus: (∏ (i: ⟦ arity nm ⟧), isaterm (el v i)))
    : isaterm (oplist_build_term nm v).
  Proof.
    unfold oplist_build_term, isaterm.
    rewrite oplist2status_cons.
    rewrite oplist2status_vecoplist2oplist.
    - rewrite statuscons_statusok_f.
      + rewrite minuseq0'.
        apply idpath.
      + apply isreflnatleh.
   - exact vstatus.
  Defined.

  Local Definition oplist_decompose (l: oplist sigma) (l1status: isaterm l):
     ∑ (nm:names sigma) (v: Vector (oplist sigma) (arity nm))
     , (∏ (i: ⟦ arity nm ⟧), isaterm (el v i))
       × (∏ (i: ⟦ arity nm  ⟧), length (el v i) < length l)
       × oplist_build_term nm v = l.
  Proof.
    revert l l1status.
    refine (list_ind _ _ _).
    - intro l1status.
      apply ii1_injectivity in l1status.
      apply negpaths0sx in l1status.
      contradiction.
    - intros x xs IH l1status.
      exists x.
      unfold isaterm in l1status.
      rewrite oplist2status_cons in l1status.
      apply statuscons_statusok_b in l1status.
      induction l1status as [_ statusxs].
      rewrite natpluscomm in statusxs.
      rewrite plusminusnmm in statusxs.
      induction (oplist2vecoplist xs statusxs) as [vtail [vstatus [vlen vflatten]]].
      exists vtail.
      repeat split.
      + exact vstatus.
      + intro i.
        apply natlehtolthsn.
        apply vlen.
      + unfold oplist_build_term.
        rewrite vflatten.
        apply idpath.
  Defined.

End OplistProps.

Section Term.

  (** * Definition of the term type and term induction *)

  Definition term (sigma: signature)
    := ∑ s: oplist sigma, isaterm s.

  Definition make_term {sigma: signature} (l: oplist sigma) (lstatus: isaterm l)
    : term sigma := l ,, lstatus.

  Coercion term2oplist {sigma: signature}: term sigma → oplist sigma := pr1.

  Definition term2proof {sigma: signature}: ∏ t: term sigma, isaterm t := pr2.

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

  Lemma term_extens {t1 t2 : term sigma} (p : term2oplist t1 = term2oplist t2)
    : t1 = t2.
  Proof.
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    exact p.
  Defined.

  Definition build_term (nm: names sigma) (v: Vector (term sigma) (arity nm)): term sigma.
  Proof.
    exists (oplist_build_term nm (vector_map term2oplist v)).
    apply oplist_build_term_status.
    intro i.
    rewrite el_vector_map.
    exact (term2proof (el v i)).
  Defined.

  Local Lemma vector_map_mkvector {A B: UU} {n: nat} {g: ⟦ n ⟧ → A} {f: A → B}
    : vector_map f (mk_vector g) = mk_vector (f ∘ g).
  Proof.
    apply vector_extens.
    intro i.
    rewrite el_vector_map.
    rewrite el_mk_vector.
    rewrite el_mk_vector.
    apply idpath.
  Defined.

  Local Lemma mk_vector_fun {A: UU} {n:nat} {v: Vector A n}
    : mk_vector (λ (i: ⟦ n ⟧), el v i) = v.
  Proof.
    apply vector_extens.
    intro i.
    rewrite el_mk_vector.
    apply idpath.
  Defined.

  Local Definition term_decompose (t: term sigma)
    : ∑ (nm:names sigma) (v: Vector (term sigma) (arity nm))
      , (∏ (i: ⟦ arity nm  ⟧), length (el v i) < length t)
        × build_term nm v = t.
  Proof.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    exists nm.
    exists (mk_vector (λ (i: ⟦ arity nm ⟧), make_term (el v i) (vstatus i))).
    split.
    - intro i.
      rewrite el_mk_vector.
      cbn - [natlth].
      exact (vlen i).
    - apply subtypePairEquality'.
      2: apply isapropisaterm.
      rewrite vector_map_mkvector.
      unfold funcomp.
      cbn.
      rewrite mk_vector_fun.
      apply normalization.
  Defined.

  Definition princop (t: term sigma): names sigma
    := pr1 (term_decompose t).

  Definition subterms (t: term sigma): Vector (term sigma) (arity (princop t))
    := pr1 (pr2 (term_decompose t)).

  Local Lemma term_notnil {X: UU} {l: oplist sigma}
    : isaterm l → length l ≤ 0 → X.
  Proof.
    intros lstatus llen.
    apply natleh0tois0 in llen.
    apply oplist2status_positive_b in lstatus.
    rewrite (pr2 (pr2 lstatus)) in llen.
    cbn in llen.
    apply negpathssx0 in llen.
    contradiction.
  Defined.

  Definition term_ind_HP (P: term sigma → UU) :=
    ∏ (nm: names sigma)
      (v: Vector (term sigma) (arity nm))
      (IH: ∏ (i:  ⟦ arity nm ⟧), P (el v i))
    , P (build_term nm v).

  Local Lemma term_ind_onlength (P: term sigma → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (t: term sigma), length t ≤ n →  P t.
  Proof.
    induction n.
    - intros t tlen.
      induction t as [l lstatus].
      exact (term_notnil lstatus tlen).
    - intros t tlen.
      induction (term_decompose t) as [nm [v [vlen normalization]]].
      apply (transportf P normalization). (* only in term_ind, not in term_rec *)
      (* rewrite <- normalization. *)
      (* induction normalization. *)
      apply (R nm v).
      intro i.
      apply (IHn (el v i)).
      change (S (length (el v i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
         apply vlen.
      -- apply tlen.
  Defined.

  Theorem term_ind (P: term sigma → UU) (R: term_ind_HP P) (t: term sigma)
    : P t.
  Proof.
    exact (term_ind_onlength P R (length t) t (isreflnatleh _)).
  Defined.

  (* Simple lemma to simplify later proofs *)
  Local Lemma term_ind_onlength_step (P: term sigma → UU) (R: term_ind_HP P)
    (n: nat) (t: term sigma)  (lent: length t ≤ S n)
    : term_ind_onlength P R (S n) t lent
      = transportf P (pr2 (pr2 (pr2 (term_decompose t))))
          (R (pr1 (term_decompose t)) (pr1 (pr2 (term_decompose t)))
             (λ i : ⟦ arity (pr1 (term_decompose t)) ⟧,
             term_ind_onlength P R n (el (pr1 (pr2 (term_decompose t))) i)
                (istransnatleh
                  (natlthtolehsn (length (el (pr1 (pr2 (term_decompose t))) i))
                      (length t) (pr1 (pr2 (pr2 (term_decompose t))) i)) lent))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma term_ind_onlength_nirrelevant (P: term sigma → UU) (R: term_ind_HP P)
    : ∏ (n m1 m2: nat)
        (m1lehn: m1 ≤ n) (m2lehn: m2 ≤ n)
        (t: term sigma)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 t lenm1 = term_ind_onlength P R m2 t lenm2.
  Proof.
    induction n.
    - intros m1 m2 m1lehn m2lehn t lenm1 lenm2.
      induction t as [t statust].
      cbn - [natleh] in lenm1, lenm2.
      apply (istransnatleh lenm1) in m1lehn.
      exact (term_notnil statust m1lehn).
    - intros m1 m2 m1lehn m2lehn t lenm1 lenm2.
      induction t as [t statust].
      unfold isaterm in statust.
      cbn - [natleh] in lenm1, lenm2.
      induction m1.
      + exact (term_notnil statust lenm1).
      + induction m2.
        * exact (term_notnil statust lenm2).
        * induction (oplist2status_positive_b statust) as [x [xs tstruct]].
          induction (! tstruct).
          change (length (cons x xs)) with (S (length xs)) in *.
          do 2 rewrite term_ind_onlength_step.
          do 2 apply maponpaths.
          apply funextsec.
          intro i.
          apply IHn.
          -- apply natlthsntoleh.
             apply nat_S_lt.
             apply natlehtolthsn.
             assumption.
          -- apply natlthsntoleh.
             apply nat_S_lt.
             apply natlehtolthsn.
             assumption.
  Defined.

  Lemma term_ind_step (P: term sigma → UU) (R: term_ind_HP P)
    (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : term_ind P R (build_term nm v)
         = R nm v (λ i:  ⟦ arity nm ⟧, term_ind P R (el v i)).
  Proof.
    unfold term_ind.
    unfold build_term in *.
    (* ASK!
      Is there a better way to guide the execution of cbn and similar?
    *)
    cbn [term2oplist pr1].
    unfold oplist_build_term in *.
    (* ASK!
      Why "rewrite length_cons" does not work here?
    *)
    change (length (cons nm (vecoplist2oplist (vector_map term2oplist v))))
           with (S (length (vecoplist2oplist (vector_map term2oplist v)))).
    set (l := (cons nm (vecoplist2oplist (vector_map term2oplist v)))).
    set (statusl := oplist_build_term_status nm (vector_map term2oplist v)
                 (λ i : ⟦ arity nm ⟧,
                  internal_paths_rew_r (oplist sigma)
                    (el (vector_map term2oplist v) i)
                    (term2oplist (el v i)) (λ o : oplist sigma, isaterm o)
                    (term2proof (el v i)) (el_vector_map term2oplist v i))).
    set (t := (l,, statusl): term sigma).
    (* ASK! Why do I need this change tactic?  *)
    change (l ,, statusl) with t.
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    induction (term_decompose t) as [nm0 [v0 [v0len v0norm]]].
    unfold t in v0norm.
    unfold build_term in v0norm.
    unfold oplist_build_term in v0norm.
    set (v0norm_list := maponpaths pr1 v0norm).
    cbn in v0norm_list.
    assert (nm0isnm: nm0 = nm).
    {
      apply cons_inj1 in v0norm_list.
      assumption.
    }
    induction (! nm0isnm).
    assert (v0isv: v0 = v).
    {
      apply cons_inj2 in v0norm_list.
      apply vecoplist2oplist_inj in v0norm_list.
      unfold term2oplist in v0norm_list.
      - apply vector_extens.
        intro i.
        apply term_extens.
        apply (maponpaths (λ v, el v i)) in v0norm_list.
        do 2 rewrite el_vector_map in v0norm_list.
        apply v0norm_list.
      - intro i.
        rewrite el_vector_map.
        apply (el v0 i).
      - intro i.
        rewrite el_vector_map.
        apply (el v i).
    }
    induction (! v0isv).
    assert (v0normisid: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetterm.
    }
    rewrite v0normisid.
    rewrite idpath_transportf.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply (term_ind_onlength_nirrelevant P R (length (vecoplist2oplist (vector_map pr1 v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh.
      apply (v0len i).
  Defined.

  Definition term_rec_HP {A: UU}: UU :=
    ∏ (nm: names sigma)
      (v: Vector (term sigma) (arity nm))
      (IH: ∏ (i:  ⟦ arity nm ⟧), A)
    , A.

  Local Lemma term_rec_onlength {A: UU} (R: @term_rec_HP A)
    : ∏ (n: nat) (t: term sigma), length t ≤ n →  A.
  Proof.
    induction n.
    - intros t tlen.
      induction t as [l lstatus].
      exact (term_notnil lstatus tlen).
    - intros t tlen.
      induction (term_decompose t) as [nm [v [vlen normalization]]].
      apply (R nm v).
      intro i.
      apply (IHn (el v i)).
      change (S (length (el v i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
        apply vlen.
      -- apply tlen.
    Defined.

  Theorem term_rec {A: UU} (R: @term_rec_HP A) (t: term sigma): A.
  Proof.
    exact (term_rec_onlength R (length t) t (isreflnatleh _)).
  Defined.

  Definition depth: term sigma → nat
    := term_rec (λ (nm: names sigma) (vterm: Vector (term sigma) (arity nm))
                   (levels: ⟦ arity nm ⟧ → nat), 1 + vector_foldr max 0 (mk_vector levels)).

  Lemma term_rec_ind {A: UU} (R: @term_rec_HP A) (t: term sigma)
    : term_rec R t = term_ind  (λ _: term sigma, A) R t.
  Proof.
    unfold term_rec, term_ind.
    unfold term_rec_onlength, term_ind_onlength.
    (* ASK! a faster way to do this? *)
    assert (H: @transportf _ (λ _ : term sigma, A)  = λ _ _ _, idfun A).
    {
      apply funextsec.
      intro x.
      apply funextsec.
      intro x'.
      apply funextsec.
      intro e.
      rewrite transportf_const.
      apply idpath.
    }
    rewrite H.
    apply idpath.
 Defined.

  Corollary term_rec_step {A: UU} (R: @term_rec_HP A)
    (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : term_rec R (build_term nm v)
         = R nm v (λ i:  ⟦ arity nm ⟧, term_rec R (el v i)).
  Proof.
    rewrite term_rec_ind.
    rewrite term_ind_step.
    apply maponpaths.
    apply funextsec.
    intro i.
    rewrite term_rec_ind.
    apply idpath.
  Defined.

End Term.

Section termalgebra.

  Definition term_algebra (sigma: signature): algebra sigma
    := make_algebra (termset sigma) build_term.

  Context {sigma: signature}.

  Definition eval (a: algebra sigma): term_algebra sigma → a
    := term_rec (λ nm vterms IH, op a nm (mk_vector IH)).

  Lemma evalstep {a: algebra sigma} (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : eval a (build_term nm v) = op a nm (vector_map (eval a) v).
  Proof.
    unfold eval.
    rewrite term_rec_step.
    apply maponpaths.
    apply vector_extens.
    intro.
    rewrite el_mk_vector.
    rewrite el_vector_map.
    apply idpath.
  Defined.

  Lemma ishomeval (a: algebra sigma): ishom (eval a).
  Proof.
    unfold ishom.
    intros.
    simpl.
    apply evalstep.
  Defined.

  Definition evalhom (a: algebra sigma): term_algebra sigma ↦ a
    := make_hom (ishomeval a).

  Definition iscontrhomsfromterm (a: algebra sigma): iscontr (term_algebra sigma ↦ a).
  Proof.
    exists (evalhom a).
    intro.
    rename t into f.
    apply subtypePairEquality'.
    2: apply isapropishom.
    apply funextfun.
    unfold homot.
    apply term_ind.
    unfold term_ind_HP.
    intros.
    change (build_term nm v) with (op (term_algebra sigma) nm v) at 1.
    rewrite (hom2axiom f).
    rewrite evalstep.
    apply maponpaths.
    apply vector_extens.
    intros.
    do 2 rewrite el_vector_map.
    rewrite IH.
    apply idpath.
  Defined.

End termalgebra.
