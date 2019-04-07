(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Open Scope stn.

(** Basic definitions *)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names (sigma: Signature): hSet := pr1 sigma.

Definition arity {sigma: Signature}: names sigma → Arity := pr2 sigma.

Definition make_signature_from_vector {n: nat} (v: Vector nat n): Signature
  := (stnset n,, el v).

Definition Algebra (sigma: Signature): UU :=
  ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

Definition mk_algebra {sigma : Signature}
           (support : hSet)
           (ops : ∏ nm:names sigma, Vector support (arity nm) → support) : Algebra sigma
  := (support,, ops).

Definition support {sigma: Signature}: Algebra sigma → hSet := pr1.

Definition dom {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  Vector (support a) (arity nm).

Definition cod {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  support a.

Definition op {sigma: Signature} {a: Algebra sigma} (nm: names sigma): (dom nm) → (cod nm) :=
  pr2 a nm.

Definition final_algebra (signature : Signature) : Algebra signature
  := mk_algebra unitset (λ nm:names signature, (λ u:Vector unit (arity nm), tt)).

(** Algebra homomorphism **)

Section Homomorphisms.

Context { sigma: Signature }.

Definition is_hom {a1 a2: Algebra sigma} (f: support a1 → support a2): UU :=
   ∏ (nm: names sigma) (x: dom nm), (f (op nm x) = (op nm (vector_map f x))).

Definition hom (a1 a2: Algebra sigma) :=  ∑ (f: support a1 → support a2), is_hom f.

Notation "m1 |-> m2" := (hom m1 m2) (at level 80, right associativity).

Definition hom_to_fun {a1 a2: Algebra sigma}: (a1 |-> a2) → support a1 → support a2 := pr1.

Definition hom_id {a: Algebra sigma}: a |-> a.
  exists (idfun (support a)).
  red.
  intros.
  rewrite vector_map_id.
  reflexivity.
Defined.

Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 |-> a2) (h2: a2 |-> a3) : a1 |-> a3.
  exists (funcomp (hom_to_fun h1) (hom_to_fun h2)).
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

Definition final_hom (a : Algebra sigma) : a |-> (final_algebra sigma).
  red.
  exists (λ _, tt).
  red.
  reflexivity.
Defined.

End Homomorphisms.

(** ** Free term algebra. *)

Section TermAlgebra.

Context { sigma: Signature }.

Definition NameStack: UU := list (names sigma).

Definition NameStackStatus: UU := coprod nat unit.

Definition stackok n: NameStackStatus := ii1 n.

Definition stackerror: NameStackStatus := ii2 tt.

Definition nss_cons (nm: names sigma) (s: NameStackStatus): NameStackStatus.
Proof.
  destruct s as [n | error].
  induction (isdecrelnatleh (arity nm) n).
    - exact (stackok ( S(n - arity nm) )).
    - exact (stackerror).
  - exact (stackerror).
Defined.

Lemma nss_cons_stackok (nm: names sigma) (n: nat):
  nss_cons nm (stackok n) != stackerror →  arity nm ≤ n.
Proof.
  intro noerror.
  unfold stackok in noerror.
  unfold nss_cons in noerror.
  induction (isdecrelnatleh (arity nm) n) as [okarity | badarity].
  * assumption.
  * induction noerror.
    reflexivity.
Defined.

Lemma nss_cons_noerror (nm: names sigma) (ss: NameStackStatus):
  nss_cons nm ss != stackerror → ∑ n: nat, ss = stackok n × arity nm ≤ n.
Proof.
  intro noerror.
  induction ss.
  - exists a.
    split.
    + apply idpath.
    + apply nss_cons_stackok.
      assumption.
  - induction noerror.
    apply idpath.
Defined.

Lemma nss_cons_noerror2 (nm: names sigma) (ss: NameStackStatus):
  nss_cons nm ss != stackerror → ss != stackerror.
Proof.
  assert ( negres: ss = stackerror → nss_cons nm ss = stackerror ).
  - intro sserror.
    rewrite sserror.
    reflexivity.
  - exact (negf negres).
Defined.

Definition nss_concatenate (s1 s2: NameStackStatus): NameStackStatus.
  induction s2 as [len_s2 | error2].
  - induction s1 as [len_s1 | error1].
    + exact (stackok (len_s1 + len_s2)).
    + exact stackerror.
  - exact stackerror.
Defined.

(** to be proved later ***)
Axiom natleh_add: ∏( n1 n2 m: nat), n1 ≤ n2 → n1 ≤ (n2 + m).

(** to be provd later ***)
Axiom natleh_adddiff: ∏( n1 n2 n3: nat), n3 ≤ n1 → n1 - n3 + n2 = n1+ n2 -n3.

Lemma nss_concatenate_nsscons (nm: names sigma) (ss1 ss2: NameStackStatus):
   (nss_cons nm ss1 != stackerror) →
   nss_concatenate (nss_cons nm ss1) ss2 = nss_cons nm (nss_concatenate ss1 ss2).
Proof.
  induction ss1 as [a1 | error1].
  - induction ss2 as [a2 | error2].
    + intro noerror.
      assert (arity nm ≤ a1) by ( apply nss_cons_stackok; assumption ).
      etrans.
      * unfold nss_cons.
        induction (isdecrelnatleh (arity nm) a1).
        -- cbn. apply idpath.
        -- induction b. trivial.
      * simpl (nss_concatenate (inl a1) (inl a2)).
        unfold nss_cons.
        unfold stackok.
        induction (isdecrelnatleh (arity nm) (a1 + a2)) as [okarity | badarity].
        -- cbn.
           rewrite (natleh_adddiff) by (assumption).
           reflexivity.
        -- assert (arity nm ≤ a1 + a2) by ( apply natleh_add; assumption ).
           contradiction.
    + reflexivity.
  - contradiction.
Defined.

Definition s2ss: NameStack → NameStackStatus.
  apply (foldr(A := names sigma)).
  - exact nss_cons.
  - exact (stackok 0).
Defined.

Lemma s2nss_cons (nm: names sigma) (ns: NameStack): s2ss (cons nm ns) = nss_cons nm (s2ss ns).
  reflexivity.
Defined.

Lemma s2nss_compositional (s1 s2: NameStack):
  s2ss s1 != stackerror → nss_concatenate (s2ss s1) (s2ss s2) = s2ss (concatenate s1 s2).
Proof.
  apply (list_ind (λ s, s2ss s != stackerror → nss_concatenate (s2ss s) (s2ss s2) = s2ss (concatenate s s2))).
  - change (s2ss (concatenate nil s2)) with (s2ss s2).
    change (s2ss nil) with (stackok 0).
    induction (s2ss s2) as [oks2 | bads2].
    + reflexivity.
    + induction bads2.
      reflexivity.
  - intros nm ns1tail IH wfnmrest.
    rewrite s2nss_cons in wfnmrest.
    assert (s2ss ns1tail != stackerror).
    { apply nss_cons_noerror2 with (nm:=nm); assumption. }
    rewrite s2nss_cons.
    rewrite nss_concatenate_nsscons by (assumption).
    rewrite (IH X).
    rewrite <- s2nss_cons.
    reflexivity.
Defined.

Definition ns_vector_flatten {n} (v: Vector NameStack n): NameStack :=
  vector_foldr (λ (t: NameStack) (s: NameStack), concatenate t s) nil v.

Definition nss_vector_flatten {n} (v: Vector NameStackStatus n): NameStackStatus :=
  vector_foldr (λ (t: NameStackStatus) (s: NameStackStatus), nss_concatenate t s) (stackok 0) v.

Lemma nss_flatten_functorial {n} (v: Vector NameStack n):
  (∏ m : ⟦ n ⟧, s2ss (el v m) != stackerror) → nss_vector_flatten(vector_map s2ss v) = s2ss(ns_vector_flatten v).
Proof.
  apply (vector_ind (λ (n: nat) (v: Vector NameStack n), (∏ m : ⟦ n ⟧, s2ss (el v m) != stackerror)
          → nss_vector_flatten(vector_map s2ss v) = s2ss(ns_vector_flatten v))).
  - intro.
    reflexivity.
  - intros x n0 v0 IH okallm.
    simpl.
    rewrite IH.
    + rewrite s2nss_compositional.
      * apply idpath.
      * set (ok0 := (okallm (●0))).
        simpl in ok0.
        assumption.
    + intro m.
      set (okm := (okallm (dni_firstelement m))).
      generalize okm.
      rewrite el_vcons_tl.
      trivial.
Defined.

Definition ns_is_term (ns: NameStack): UU := s2ss ns = stackok 1.

Definition term := ∑ ns: NameStack, ns_is_term ns.

Coercion term_to_s(t: term): NameStack := pr1 t.

Definition term_isaset: isaset term.
  apply isaset_total2.
  apply isofhlevellist.
  - exact (pr2 (names sigma)).
  - intro nm.
    unfold ns_is_term.
    apply hlevelntosn.
    apply isaproppathstoisolated.
    apply isolatedtoisolatedii1.
    apply isisolatedn.
Defined.

Lemma nss_flatten_bound1 {n} (v: Vector NameStackStatus n) (a: nat):
  (∏ m : ⟦ n ⟧, ∑ b: nat, el v m = stackok b × b ≤ a) → ∑ c: nat, nss_vector_flatten v  = stackok c × c ≤ n * a.
Proof.
  apply (vector_ind (λ  (n: nat) (v: Vector NameStackStatus n), (∏ m : ⟦ n ⟧, ∑ b: nat, el v m = stackok b × b ≤ a) → ∑ c: nat, nss_vector_flatten v  = stackok c × c ≤ n * a)).
  - intros.
    exists 0.
    split ; reflexivity.
  - intros.
    assert (∏ m : ⟦ n0 ⟧, ∑ b : nat, el v0 m = stackok b × b ≤ a).
    {
      intro.
      rewrite <- (el_vcons_tl v0 x).
      exact (X0 (dni_firstelement m)).
    }
    set (X2 := (X X1)).
    induction X2 as [c'  [ IH bound']].
    set (xok := X0 (●0)).
    induction xok as [xval [xok xbounded]].
    simpl (el (vcons x v0) (stnpr 0)) in xok.
    rewrite xok.
    exists (xval + c').
    split.
    + change (nss_vector_flatten (vcons (stackok xval) v0)) with (nss_concatenate (stackok xval) (nss_vector_flatten v0)).
      rewrite IH.
      reflexivity.
    + rewrite multsnm.
      apply natlehandplus ; assumption.
Defined.

Lemma nss_flatten_eq {n} (v: Vector NameStackStatus n) (a: nat):
  (∏ m : ⟦ n ⟧, el v m = stackok a) → nss_vector_flatten v  = stackok (n * a).
Proof.
  apply (vector_ind (λ  (n: nat) (v: Vector NameStackStatus n), (∏ m : ⟦ n ⟧, el v m = stackok a) → ∑ c: nat, nss_vector_flatten v  = stackok ( n * a))).
  - intros.
    exists 0.
    split ; reflexivity.
  - intros.
    assert (∏ m : ⟦ n0 ⟧, el v0 m = stackok a).
    {
      intro.
      rewrite <- (el_vcons_tl v0 x).
      exact (X0 (dni_firstelement m)).
    }
    set (X2 := (X X1)).
    induction X2 as [c'  IH].
    set (xok := X0 (●0)).
    simpl (el (vcons x v0) (stnpr 0)) in xok.
    rewrite xok.
    exists ( c').
    + change (nss_vector_flatten (vcons (stackok a) v0)) with (nss_concatenate (stackok a) (nss_vector_flatten v0)).
      rewrite IH.
      simpl.
      rewrite natpluscomm.
      reflexivity.
Defined.

Lemma nss_flatten_eq1 {n} (v: Vector NameStackStatus n):
  (∏ m : ⟦ n ⟧, el v m = stackok 1) → nss_vector_flatten v  = stackok n.
Proof.
  intro.
  set (temp :=  nss_flatten_eq v 1 X).
  apply (transportf (λ n, nss_vector_flatten v = stackok n) (natmultr1 n)).
  assumption.
Defined.

Definition term_op (nm: names sigma)(v: Vector term (arity nm)): term.
  exists (cons nm (ns_vector_flatten (vector_map term_to_s v))).
  assert (∏ m : ⟦ arity nm ⟧, s2ss (el v m) = stackok 1).
  - intro m.
    exact (pr2 (el v m)).
  - unfold ns_is_term.
    rewrite s2nss_cons.
    rewrite <- nss_flatten_functorial.
    + change (vector_map s2ss (vector_map term_to_s v)) with (((vector_map s2ss) ∘ (vector_map term_to_s)) v).
      rewrite <- vector_map_comp.
      assert (s2ss ∘ term_to_s = λ _ , stackok 1).
      {
        apply funextfun. intro. exact (pr2 x).
      }
      rewrite X0.
      assert (nss_vector_flatten (vector_map (λ _ : term, stackok 1) v) = stackok (arity nm)).
      {
        assert (arity nm = (arity nm) * 1) by ( rewrite natmultr1; apply idpath).
        apply nss_flatten_eq1.
        intro.
        apply el_vector_map.
      }
      rewrite X1.
      simpl.
      induction (isdecrelnatleh (arity nm) (arity nm)) as [okarity | badarity].
      * cbn.
        rewrite minuseq0'.
        reflexivity.
      * induction badarity.
        apply isreflnatleh.
   + intro m.
     rewrite el_vector_map.
     assert ( s2ss (el v m) = stackok 1) by (exact (X m)).
     rewrite X0.
     apply negpathsii1ii2.
Defined.

Definition term_hset: hSet := make_hSet term (term_isaset).

Definition term_algebra: Algebra sigma
  := mk_algebra term_hset term_op.

End TermAlgebra.
