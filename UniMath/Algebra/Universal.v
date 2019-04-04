(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Open Scope stn.

(** Basic definitions *)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names: Signature -> hSet := pr1.

Definition arity: ∏ (sigma: Signature), names sigma → Arity := pr2.

Definition make_signature_from_vector {n: nat} (v: Vector nat n): Signature.
  unfold Signature.
  exists (make_hSet (⟦ n ⟧) (isasetstn n)).
  exact (el v).
Defined.

Definition Algebra (sigma: Signature): UU :=
  ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity sigma nm) → support.

Definition support {sigma: Signature}: Algebra sigma → hSet := pr1.

Definition dom {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  Vector (support a) (arity sigma nm).

Definition op {sigma: Signature} {m: Algebra sigma}:
  ∏ (nm: names sigma), (dom nm) → support m := pr2 m.

(** Examples of signatures and algebras *)

Definition nat_signature := make_signature_from_vector (vcons 0 (vcons 1 vnil)).

Definition nat_zero: names nat_signature := (●0).
Definition nat_succ: names nat_signature := (●1).

Definition bool_signature := make_signature_from_vector (vcons 0 (vcons 1 (vcons  1 (vcons 2 vnil)))).

Definition bool_false: names bool_signature := (●0).
Definition bool_true: names bool_signature := (●1).
Definition bool_not: names bool_signature := (●2).
Definition bool_and: names bool_signature := (●3).

Definition nat_algebra: Algebra nat_signature.
  unfold Algebra.
  exists natset.
  intro.
  cbn in nm.
  induction nm as [n proofn].
  induction n.
  cbn.
  exact (λ _, 0).
  induction n.
  cbn.
  exact (λ x, S(pr1 x)).
  exact (fromempty (nopathsfalsetotrue proofn)).
Defined.

(** Algebra homomorphism **)

Section Homomorphisms.

Context { sigma: Signature }.

Definition is_hom {a1 a2: Algebra sigma} (f: support a1 → support a2): UU :=
   ∏ (nm: names sigma) (x: dom nm), (f (op nm x) = (op nm (vector_map f x))).

Definition hom (a1 a2: Algebra sigma) :=  ∑ (f: support a1 → support a2), is_hom f.

Notation "m1 |-> m2" := (hom m1 m2) (at level 80, right associativity).

Definition hom_to_fun {a1 a2: Algebra sigma} (h: a1 |-> a2): (support a1) -> (support a2) := pr1 h.

Definition hom_comp {a1 a2 a3: Algebra sigma} (h1: a1 |-> a2) (h2: a2 |-> a3) : a1 |-> a3.
  exists (funcomp (hom_to_fun h1) (hom_to_fun h2)).
  unfold is_hom.
  intros.
  induction h1 as [f1 ishomf1].
  induction h2 as [f2 ishomf2].
  cbn.
  rewrite vector_map_comp.
  rewrite ishomf1.
  rewrite ishomf2.
  reflexivity.
Defined.

Lemma is_hom_idfun {a: Algebra sigma}: is_hom (idfun (support a)).
Proof.
  red.
  intros.
  rewrite vector_map_id.
  reflexivity.
Defined.

Definition hom_idfun {a: Algebra sigma}: a |-> a.
  exists (idfun (support a)).
  exact (is_hom_idfun).
Defined.

End Homomorphisms.

Section TermAlgebra.

Context { sigma: Signature }.

Definition NameStack: UU := list (names sigma).

Definition ns (l: list(names sigma)): NameStack := l.

Definition NameStackStatus: UU := coprod nat unit.

Definition stackok n: NameStackStatus := ii1 n.

Definition stackerror: NameStackStatus := ii2 tt.

Definition nss (ns: NameStack): NameStackStatus.
  induction ns as [n v].
  induction n as [  | m h].
  - exact (stackok 0).
  - set (maybe_rest := h (tl v)).
    induction maybe_rest as [rest| error].
    + set (is_error := natgtb (arity sigma (hd v)) rest).
      exact (if is_error then stackerror else stackok ( S(rest - (arity sigma (hd v))) )).
    + exact stackerror.
Defined.

Definition ns_is_wf (ns: NameStack): UU := nss ns != stackerror.

Definition nss_concatenate (s1 s2: NameStackStatus): NameStackStatus.
  induction s2 as [len_s2 | error2].
  - induction s1 as [len_s1 | error1].
    + exact (stackok (len_s1 + len_s2)).
    + exact stackerror.
  - exact stackerror.
Defined.

Search ( _ = nil).
Lemma nss_compositional (ns1 ns2: NameStack): nss_concatenate (nss ns1) (nss ns2) = nss (concatenate ns1 ns2).
Proof.
  induction ns1 as [len_ns1 vec_ns1].
  induction len_ns1.
  - cbn in vec_ns1.
Abort.

Definition ns_is_term (ns: NameStack): UU := nss ns = stackok 1.

Definition term := ∑ ns: NameStack, ns_is_term ns.

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

Definition term_hset: hSet := make_hSet term (term_isaset).

Definition term_algebra: Algebra sigma.
 exists term_hset.
Abort.

End TermAlgebra.

Section Tests.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Definition test1: nss (ns (nat_succ :: nat_zero :: nil)) = stackok 1 := idpath _.
Definition test2: nss(sigma := nat_signature) nil = stackok 0 := idpath _.
Definition test3: nss (nat_zero :: nat_zero :: nil) = stackok 2 := idpath _.
Definition test4: nss (nat_succ :: nil) = stackerror := idpath _.

End Tests.