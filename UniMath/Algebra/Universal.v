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

Definition arity {sigma: Signature}: names sigma → Arity := pr2 sigma.

Definition make_signature_from_vector {n: nat} (v: Vector nat n): Signature.
  unfold Signature.
  exists (make_hSet (⟦ n ⟧) (isasetstn n)).
  exact (el v).
Defined.

Definition Algebra (sigma: Signature): UU :=
  ∑ (support: hSet), ∏ (nm: names sigma), Vector support (arity nm) → support.

Definition support {sigma: Signature}: Algebra sigma → hSet := pr1.

Definition dom {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU :=
  Vector (support a) (arity nm).

Definition op {sigma: Signature} {m: Algebra sigma}:
  ∏ (nm: names sigma), (dom nm) → support m := pr2 m.

(** Examples of signatures and algebras *)

Definition nat_signature := make_signature_from_vector (vcons 0 (vcons 1 vnil)).

Definition nat_zero: names nat_signature := (●0).
Definition nat_succ: names nat_signature := (●1).

Definition bool_signature := make_signature_from_vector (vcons 0 (vcons 0 (vcons  1 (vcons 2 vnil)))).

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
  - cbn.
    exact (λ _, 0).
  - induction n.
    + cbn.
      exact (λ x, S(pr1 x)).
    + exact (fromempty (nopathsfalsetotrue proofn)).
Defined.

Definition andb := λ a b : bool, if a then (if b then true else false) else false.

Definition bool_algebra: Algebra bool_signature.
  unfold Algebra.
  exists boolset.
  intro.
  cbn in nm.
  induction nm as [n proofn].
  induction n.
  { cbn.
    exact (λ _, false). }
  induction n.
  { cbn.
    exact (λ _, true). }
  induction n.
  { cbn.
    exact (λ x, negb(pr1 x)). }
  induction n.
  { cbn.
    exact (λ x, andb (pr1 x) (pr1 (pr2 x))). }
  exact (fromempty (nopathsfalsetotrue proofn)).
Defined.

Definition final_algebra (signature : Signature) : Algebra signature.
  unfold Algebra.
  exists unitset.
  intro.
  exact (λ _, tt).
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

Definition final_hom {signature : Signature} (algebra : Algebra signature) : hom algebra (final_algebra signature).
  unfold hom.
  exists (λ _, tt).
  unfold is_hom.
  intros.
  reflexivity.
Defined.

Section TermAlgebra.

Context { sigma: Signature }.

Definition NameStack: UU := list (names sigma).

Definition NameStackStatus: UU := coprod nat unit.

Definition stackok n: NameStackStatus := ii1 n.

Definition stackerror: NameStackStatus := ii2 tt.

Definition nss_cons (nm: names sigma) (s: NameStackStatus): NameStackStatus.
  destruct s as [n | error].
  - set (is_error := natgtb (arity nm) n).
    exact (if is_error then stackerror else stackok ( S(n - (arity nm)) )).
  - exact (stackerror).
Defined.

Lemma nss_cons_stackerror (nm: names sigma) (s: NameStackStatus): s = stackerror → nss_cons nm s = stackerror.
Proof.
  intro.
  rewrite X.
  reflexivity.
Defined.

Lemma nss_cons_nostakerror (nm: names sigma) (ss: NameStackStatus):
  nss_cons nm ss != stackerror → ∑ n: nat, ss = stackok n × natgtb (arity nm) n = false.
Proof.
  intro noerror.
  induction ss.
  - exists a.
    split.
    + reflexivity.
    + unfold nss_cons in noerror.
      induction (natgtb (arity nm) a).
      * destruct noerror.
        apply idpath.
      * apply idpath.
  - simpl in noerror.
    destruct noerror.
    apply idpath.
Defined.

Definition nss: NameStack → NameStackStatus.
  apply (foldr(A := names sigma)).
  - exact nss_cons.
  - exact (stackok 0).
Defined.

Lemma nss_ind (nm: names sigma) (ns: NameStack): nss (cons nm ns) = nss_cons nm (nss ns).
  reflexivity.
Defined.

Definition nss_concatenate (ns1 ns2: NameStackStatus): NameStackStatus.
  induction ns2 as [len_ns2 | error2].
  - induction ns1 as [len_ns1 | error1].
    + exact (stackok (len_ns1 + len_ns2)).
    + exact stackerror.
  - exact stackerror.
Defined.

Lemma natgtb_add (n1 n2 m:nat): natgtb n1 n2 = false → natgtb n1 (n2 + m) = false.
  induction n1.
  - reflexivity.
  - intro.
    rewrite natpluscomm.
    induction m.
    + apply X.
    + cbn.
Abort.

(** to be proved later ***)
Axiom natgtb_add: ∏( n1 n2 m: nat), natgtb n1 n2 = false → natgtb n1 (n2 + m) = false.

(** to be provd later ***)
Axiom natgtb_adddiff: ∏( n1 n2 n3: nat), natgtb n2 n1 = false → n1 - n2 + n3 = n1+ n3 -n2.

Lemma nss_concatenate_ind (nm: names sigma) (ss1 ss2: NameStackStatus):
   (nss_cons nm ss1 != stackerror) → nss_concatenate (nss_cons nm ss1) ss2 = nss_cons nm (nss_concatenate ss1 ss2).
Proof.
  induction ss1 as [a1 | error1].
  - induction ss2 as [a2 | error2].
    + intro noerror.
      assert (∑ n: nat, (stackok a1 = stackok n × natgtb (arity nm) n = false)).
      * apply nss_cons_nostakerror.
        assumption.
      * destruct X as [ n [ sseq arityok ] ].
        apply ii1_injectivity in sseq.
        rewrite <- sseq in *.
        etrans.
        -- unfold nss_cons.
           rewrite arityok.
           cbn.
           apply idpath.
        -- unfold nss_cons.
           cbn.
           assert (arityok2 : natgtb (arity nm) (a1 + a2) = false).
           { apply natgtb_add. assumption. }
           rewrite arityok2.
           rewrite natgtb_adddiff.
           ++ reflexivity.
           ++ assumption.
    + reflexivity.
  - cbn.
    intro.
    induction X.
    apply idpath.
Defined.

Lemma nss_compositional (ns1 ns2: NameStack): nss ns1 != stackerror → nss_concatenate (nss ns1) (nss ns2) = nss (concatenate ns1 ns2).
Proof.
  apply (list_ind (λ s, nss s != stackerror → nss_concatenate (nss s) (nss ns2) = nss (concatenate s ns2))).
  - change (nss (concatenate nil ns2)) with (nss ns2).
    change (nss nil) with (stackok 0).
    induction (nss ns2).
    + reflexivity.
    + induction b.
      reflexivity.
  - intros nm ns1tail IH wfnmrest.
    rewrite nss_ind in wfnmrest.
    assert (nss ns1tail != stackerror).
    {
       apply (negf (nss_cons_stackerror nm (nss ns1tail))).
       assumption.
    }
    set (IH' := IH X).
    cut (∏ u, u = nss ns2 → nss_concatenate (nss (cons nm ns1tail)) u = nss (cons nm (concatenate ns1tail ns2))).
    { intro. apply X0. reflexivity. }
    rewrite !nss_ind.
    rewrite <- IH'.
    intros.
    rewrite X0.
    apply nss_concatenate_ind.
    assumption.
Defined.

Definition ns_vector_flatten {n} (v: Vector NameStack n): NameStack :=
  vector_foldr (λ (t: NameStack) (s: NameStack), concatenate t s) nil v.

Definition nss_vector_flatten {n} (v: Vector NameStackStatus n): NameStackStatus :=
  vector_foldr (λ (t: NameStackStatus) (s: NameStackStatus), nss_concatenate t s) (stackok 0) v.
  
Lemma nss_fuctorial: ∏ {n:nat} (v: Vector NameStack n), (∏ m : ⟦ n ⟧, nss (el v m) != stackerror) → nss_vector_flatten(vector_map nss v) = nss(ns_vector_flatten v).
  apply (vector_ind (λ (n: nat) (v: Vector NameStack n), (∏ m : ⟦ n ⟧, nss (el v m) != stackerror) → nss_vector_flatten(vector_map nss v) = nss(ns_vector_flatten v))).
  - intro.
    reflexivity.
  - intros.
    change (ns_vector_flatten (vcons x v)) with (concatenate x (ns_vector_flatten v)).
    change (nss_vector_flatten (vector_map nss (vcons x v))) with (nss_concatenate (nss x) (nss_vector_flatten (vector_map nss v))).
    rewrite X.
    + rewrite nss_compositional.
      apply idpath.
Abort.
  
Definition ns_is_term (ns: NameStack): UU := nss ns = stackok 1.

Definition term := ∑ ns: NameStack, ns_is_term ns.

Coercion term_to_ns(t: term): NameStack := pr1 t.

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

Definition term_op (nm: names sigma)(v: Vector term (arity nm)): term.
  exists (cons nm (ns_vector_flatten (vector_map term_to_ns v))).
  unfold ns_is_term.
  rewrite nss_ind.
  unfold nss_cons.
  induction (arity nm).
  - rewrite (vector0_eq v vnil).
    reflexivity.
Abort.

Definition term_op2 (nm: names sigma)(v: Vector term (arity nm)): term.
  exists (cons nm (vector_foldr (λ (t: term) (s: NameStack), concatenate (pr1 t) s) nil v)).
  unfold ns_is_term.
  rewrite nss_ind.
  apply (nat_ind (λ n: nat, arity nm = n → nss_cons nm (nss (vector_foldr (λ (t : term) (s : NameStack), concatenate (pr1 t) s) nil v)) =
stackok 1)) with (n:= arity nm).
  - intro.
    generalize v.
    clear v.
    rewrite X.
    intro.
    rewrite (vector0_eq v vnil).
    cbn.
    rewrite X.
    reflexivity.
Abort.
 
Definition term_hset: hSet := make_hSet term (term_isaset).

Definition term_algebra: Algebra sigma.
 exists term_hset.
Abort.

End TermAlgebra.

Section Tests.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Definition test1: nss (nat_succ :: nat_zero :: nil) = stackok 1 := idpath _.
Definition test2: nss(sigma := nat_signature) nil = stackok 0 := idpath _.
Definition test3: nss (nat_zero :: nat_zero :: nil) = stackok 2 := idpath _.
Definition test4: nss (nat_succ :: nil) = stackerror := idpath _.

End Tests.
