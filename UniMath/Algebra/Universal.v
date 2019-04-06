(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.Bool.

Open Scope stn.

(** Basic definitions *)

Definition Arity: UU := nat.

Definition Signature: UU := ∑ (names: hSet), names → Arity.

Definition names (sigma: Signature): hSet := pr1 sigma.

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
  
Definition cod {sigma: Signature} {a: Algebra sigma} (nm: names sigma): UU := 
  support a.

Definition op {sigma: Signature} {m: Algebra sigma} (nm: names sigma): (dom nm) → support m := 
  pr2 m nm.

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

Definition bool_algebra: Algebra bool_signature.
  unfold Algebra.
  exists boolset.
  intro.
  cbn in nm.
  induction nm as [n proofn].
  induction n.
  { cbn. exact (λ _, false). }
  induction n.
  { cbn. exact (λ _, true). }
  induction n.
  { cbn. exact (λ x, negb(pr1 x)). }
  induction n.
  { cbn. exact (λ x, andb (pr1 x) (pr1 (pr2 x))). }
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

Coercion hom_to_fun {a1 a2: Algebra sigma} (h: a1 |-> a2): (support a1) -> (support a2) := pr1 h.

Definition hom_id {a: Algebra sigma}: a |-> a.
  exists (idfun (support a)).
  red.
  intros.
  rewrite vector_map_id.
  reflexivity.
Defined.

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

End Homomorphisms.

Definition hom_final {signature : Signature} (algebra : Algebra signature) : hom algebra (final_algebra signature).
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

Definition ss_cons (nm: names sigma) (s: NameStackStatus): NameStackStatus.
  destruct s as [n | error].
  induction (isdecrelnatleh (arity nm) n).
    - exact (stackok ( S(n - arity nm) )).
    - exact (stackerror).
  - exact (stackerror).
Defined.

Lemma ss_cons_error (nm: names sigma) (s: NameStackStatus): 
  s = stackerror → ss_cons nm s = stackerror.
Proof.
  intro.
  rewrite X.
  reflexivity.
Defined.

Lemma ss_cons_noerror (nm: names sigma) (n: nat):
  ss_cons nm (stackok n) != stackerror →  arity nm ≤ n.
Proof.
  intro noerror.
  unfold stackok in noerror.
  unfold ss_cons in noerror.
  induction (isdecrelnatleh (arity nm) n) as [okarity | badarity].
  * assumption.
  * destruct noerror.
    reflexivity.
Defined.

Lemma ss_cons_noerror2 (nm: names sigma) (ss: NameStackStatus):
  ss_cons nm ss != stackerror → ∑ n: nat, ss = stackok n × arity nm ≤ n.
Proof.
  intro noerror.
  induction ss.
  - exists a.
    split.
    + reflexivity.
    + apply ss_cons_noerror.
      assumption.
  - simpl in noerror.
    destruct noerror.
    apply idpath.
Defined.

Definition ss_concatenate (ns1 ns2: NameStackStatus): NameStackStatus.
  induction ns2 as [len_ns2 | error2].
  - induction ns1 as [len_ns1 | error1].
    + exact (stackok (len_ns1 + len_ns2)).
    + exact stackerror.
  - exact stackerror.
Defined.

Definition s2ss: NameStack → NameStackStatus.
  apply (foldr(A := names sigma)).
  - exact ss_cons.
  - exact (stackok 0).
Defined.

Lemma s2ss_cons (nm: names sigma) (ns: NameStack): s2ss (cons nm ns) = ss_cons nm (s2ss ns).
  reflexivity.
Defined.

(** to be proved later ***)
Axiom natleh_add: ∏( n1 n2 m: nat), n1 ≤ n2 → n1 ≤ (n2 + m).

(** to be provd later ***)
Axiom natleh_adddiff: ∏( n1 n2 n3: nat), n3 ≤ n1 → n1 - n3 + n2 = n1+ n2 -n3.

Lemma nss_concatenate_ind (nm: names sigma) (ss1 ss2: NameStackStatus):
   (ss_cons nm ss1 != stackerror) → ss_concatenate (ss_cons nm ss1) ss2 = ss_cons nm (ss_concatenate ss1 ss2).
Proof.
  induction ss1 as [a1 | error1].
  - induction ss2 as [a2 | error2].
    + intro noerror.
      assert (arity nm ≤ a1).
      { apply ss_cons_noerror. assumption. }
      etrans.
      * unfold ss_cons.
        induction (isdecrelnatleh (arity nm) a1).
        -- cbn. apply idpath.
         -- destruct b. trivial.
      * unfold ss_cons.
        change (ss_concatenate (inl a1) (inl a2)) with (stackok (a1+a2)).
        unfold stackok.
        induction (isdecrelnatleh (arity nm) (a1 + a2)) as [okarity | badarity].
        -- cbn.
           rewrite (natleh_adddiff).
           ++ reflexivity.
           ++ assumption.
        -- cbn.
           assert (arity nm ≤ a1 + a2).
           { apply natleh_add. assumption. }
           contradiction.
    + reflexivity.
  - intro.
    cbn.
    contradiction.
Defined.

Lemma s2ss_compositional (ns1 ns2: NameStack): s2ss ns1 != stackerror → ss_concatenate (s2ss ns1) (s2ss ns2) = s2ss (concatenate ns1 ns2).
Proof.
  apply (list_ind (λ s, s2ss s != stackerror → ss_concatenate (s2ss s) (s2ss ns2) = s2ss (concatenate s ns2))).
  - change (s2ss (concatenate nil ns2)) with (s2ss ns2).
    change (s2ss nil) with (stackok 0).
    induction (s2ss ns2).
    + reflexivity.
    + induction b.
      reflexivity.
  - intros nm ns1tail IH wfnmrest.
    rewrite s2ss_cons in wfnmrest.
    assert (s2ss ns1tail != stackerror).
    {
       apply (negf (ss_cons_error nm (s2ss ns1tail))).
       assumption.
    }
    set (IH' := IH X).
    cut (∏ u, u = s2ss ns2 → ss_concatenate (s2ss (cons nm ns1tail)) u = s2ss (cons nm (concatenate ns1tail ns2))).
    { intro. apply X0. reflexivity. }
    rewrite !s2ss_cons.
    rewrite <- IH'.
    intros.
    rewrite X0.
    apply nss_concatenate_ind.
    assumption.
Defined.

Definition ns_vector_flatten {n} (v: Vector NameStack n): NameStack :=
  vector_foldr (λ (t: NameStack) (s: NameStack), concatenate t s) nil v.

Definition nss_vector_flatten {n} (v: Vector NameStackStatus n): NameStackStatus :=
  vector_foldr (λ (t: NameStackStatus) (s: NameStackStatus), ss_concatenate t s) (stackok 0) v.
  
Lemma nss_fuctorial: ∏ {n:nat} (v: Vector NameStack n), (∏ m : ⟦ n ⟧, s2ss (el v m) != stackerror) → nss_vector_flatten(vector_map s2ss v) = s2ss(ns_vector_flatten v).
  apply (vector_ind (λ (n: nat) (v: Vector NameStack n), (∏ m : ⟦ n ⟧, s2ss (el v m) != stackerror) → nss_vector_flatten(vector_map s2ss v) = s2ss(ns_vector_flatten v))).
  - intro.
    reflexivity.
  - intros.
    change (ns_vector_flatten (vcons x v)) with (concatenate x (ns_vector_flatten v)).
    change (nss_vector_flatten (vector_map s2ss (vcons x v))) with (ss_concatenate (s2ss x) (nss_vector_flatten (vector_map s2ss v))).
    rewrite X.
    + rewrite s2ss_compositional.
      apply idpath.
Abort.
  
Definition ns_is_term (ns: NameStack): UU := s2ss ns = stackok 1.

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
  rewrite s2ss_cons.
  unfold ss_cons.
  induction (arity nm).
  - rewrite (vector0_eq v vnil).
    reflexivity.
Abort.

Definition term_op2 (nm: names sigma)(v: Vector term (arity nm)): term.
  exists (cons nm (vector_foldr (λ (t: term) (s: NameStack), concatenate (pr1 t) s) nil v)).
  unfold ns_is_term.
  rewrite s2ss_cons.
  apply (nat_ind (λ n: nat, arity nm = n → ss_cons nm (s2ss (vector_foldr (λ (t : term) (s : NameStack), concatenate (pr1 t) s) nil v)) =
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

Definition test1: s2ss (nat_succ :: nat_zero :: nil) = stackok 1 := idpath _.
Definition test2: s2ss(sigma := nat_signature) nil = stackok 0 := idpath _.
Definition test3: s2ss (nat_zero :: nat_zero :: nil) = stackok 2 := idpath _.
Definition test4: s2ss (nat_succ :: nil) = stackerror := idpath _.

End Tests.
