(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Open Scope stn.
Open Scope nat.

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

Lemma nss_cons_stackok2 (nm: names sigma)  (n: nat) (m: nat):
  nss_cons nm (stackok n) = stackok m → m = S(n - arity nm).
Proof.
  intro comp.
  unfold stackok in comp.
  unfold nss_cons in comp.
  induction (isdecrelnatleh (arity nm) n) as [okarity | badarity].
  * cbn in comp.
    apply ii1_injectivity in comp.
    apply pathsinv0 in comp. 
    assumption.
  * cbn in comp.
    assert (stackerror != inl m) by (apply negpathsii2ii1).
    contradiction.
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

Lemma s2ss_length(s: NameStack): ( ∑ n: nat, s2ss s = stackok n × n > 0 ) → length s > 0.
Proof.
  apply (list_ind (λ l, (∑ n : nat, s2ss l = stackok n × n > 0) → length l > 0)).
  - intro X.
    induction X as [n [ n_is_ss n_gt_0 ]].
    cbn in n_is_ss.
    apply ii1_injectivity in n_is_ss.
    rewrite n_is_ss in n_gt_0.
    set (contr := isirreflnatgth n n_gt_0).
    contradiction.
  - intros.
    unfold cons.
    cbn.
    apply idpath.
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

Lemma nil_not_term: ¬ ns_is_term nil.
Proof.
  unfold ns_is_term.
  cbn.
  intro s0s1.
  set (contr := ii1_injectivity 0 1 s0s1).
  exact (negpaths0sx 0 contr).
Defined.

Definition term := ∑ ns: NameStack, ns_is_term ns.

Definition mkseq {n: nat} (vec: Vector term n): ∑ s: NameStack, s2ss s = stackok n.
Proof.
  induction n.
   - exists nil.
     reflexivity.
   - set (rest := IHn (tl vec)).
     induction rest as [l l_ss].
     set (result := concatenate (pr1 (hd vec)) l).
     exists result.
     unfold result.  
     rewrite <- s2nss_compositional.
     + rewrite (pr2 (hd vec)).
       rewrite l_ss.
       cbn.
       apply idpath.
     + rewrite (pr2 (hd vec)).
       apply negpathsii1ii2.
Defined.

Definition mkterm (n: names sigma) (vec: Vector term (arity n)): term.
Proof.
  set (seq := mkseq vec).
  induction seq as [tail tailss].
  exists (cons n tail).
  red.
  rewrite s2nss_cons.
  rewrite tailss.
  change (stackok (arity n)) with (ii1 (B:=unit)(arity n)).
  unfold nss_cons.
  induction (isdecrelnatleh (arity n) (arity n)).
  - cbn.
    rewrite minuseq0'.
    apply idpath.
  - induction b.
    apply isreflnatleh.
Defined.

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

Definition princ_op(t: term): names sigma.
Proof.
  induction t as [s sterm].
  generalize sterm.
  apply (list_ind (λ s : NameStack, ns_is_term s → names sigma)).
  - intro nilterm.
    unfold ns_is_term in nilterm.
    cbn in nilterm.
    apply ii1_injectivity in nilterm.
    apply negpaths0sx in nilterm.
    contradiction.
  - intros.
    exact x.
Defined.

Lemma lengthnil {A: UU} (l: list A): length l = 0 → l = nil.
Proof.
  apply (list_ind (λ l: list A, length l = 0 → l = nil)).
  - reflexivity.
  - intros x xs IH lencons.
    cbn in lencons.
    apply negpathssx0 in lencons.
    contradiction.
Defined.

Definition headtail {A: UU} (l: list A): length l > 0 → A × list A.
Proof.
  apply (list_ind (λ l: list A, length l > 0 → A × list A)).
  - cbn.
    intro tf.
    apply pathsinv0 in tf.
    apply nopathstruetofalse in tf.
    contradiction.
  - intros x xs IH lencons.
    exact (x ,, xs).
Defined.

Definition head  {A: UU} (l: list A) (lenl: length l > 0): A := pr1 (headtail l lenl).

Definition tail  {A: UU} (l: list A) (lenl: length l > 0): list A := pr2 (headtail l lenl).

(*
Lemma s2ssok_to_len (s: NameStack): (∑ n: nat, s2ss s = stackok n × n > 0) → length s > 0.
Proof.
  intro sok.
  induction sok as [n [ss ngt0]].
  *)

(*** These axioms probably needs some addition hypotheses **)

Axiom natlehandminusl: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

Axiom natlehandminusr: ∏ n m k : nat, n ≤ m → n - k ≤ m - k.

Axiom natdiff0: ∏ a b: nat, 0 = a - b → b ≥ a.

Axiom natdiffasymm: ∏ a b: nat, a ≤ b → a ≥ b → a=b.

Axiom nat_ax: ∏ a b c: nat, a = S (b - c) → b = a + c -1. 

Axiom nat_ax2: ∏ a b c d : nat, a = b + c -d → a - c = b - d.

Axiom nat_ax3: ∏ a b c : nat, a + b - 1 - (c + b - 1) = a-c.

Lemma nat_ax4: ∏ n: nat, ¬ (n ≥ 1) → n = 0.
Proof.
  intro.
  induction n.
  - intro.
    apply idpath.
  - intro n_gte_1.
    apply fromempty.
    apply n_gte_1.
    apply natgthtogehsn.
    apply natgthsn0.
Defined.

Definition extract_subnss (s: NameStack): 
  ∏ n m: nat, s2ss s = stackok m → n ≤ m →  ∑ first second: NameStack, s2ss first = stackok n × s2ss second = stackok (m - n) ×  concatenate first second = s.
Proof.
   apply (list_ind (λ s : NameStack, ∏ n m: nat, s2ss s = stackok m → n ≤ m → 
          ∑ first second: NameStack, s2ss first = stackok n × s2ss second = stackok (m - n) × 
          concatenate first second = s)).
   - intros n m ss.
     cbn in ss.
     apply ii1_injectivity in ss.
     rewrite <- ss.
     intro n0.
     apply nat0gehtois0 in n0.
     rewrite n0.
     exists nil.
     exists nil.
     repeat split.
   - intros nm nms IH n m ss mgtn.
     induction (isdeceqnat n 0) as [nis0 | ngt0].
     + rewrite nis0.
       exists nil.
       exists (cons nm nms).
       repeat split.
       * rewrite natminuseqn.
         assumption.
     + assert (ngte1: n >= 1).
       {
         apply natgthtogehsn.
         apply natneq0togth0.
         apply nat_nopath_to_neq.
         assumption.
       }
       rewrite s2nss_cons in ss.
       assert ( X: ∑ sstail: nat, s2ss nms = stackok sstail ×  arity nm ≤ sstail ). {
         apply nss_cons_noerror.
         rewrite ss.
         apply negpathsii1ii2.
       }
       induction X as [ss_nms [ss_nms_proof ss_nms_bound]].
       rewrite ss_nms_proof in ss.
       apply nss_cons_stackok2 in ss.
       apply nat_ax in ss.
       assert (X: n + arity nm - 1 ≤ ss_nms).
       {
          rewrite ss.
          apply natlehandminusl.
          apply natlehandplus.
          - assumption.
          - apply isreflnatleh.
       }
       set (IH1 := IH (n + arity nm - 1) ss_nms  ss_nms_proof X).
       induction IH1 as [first [rest [ssfirst [ssrest conc]]]]. 
       rewrite ss in ssrest.
       rewrite nat_ax3 in ssrest.
       set (realfirst := cons nm first).
       assert (s2ss realfirst = stackok n).
       {
         unfold realfirst.
         rewrite s2nss_cons.
         rewrite ssfirst.
         change (stackok (n + arity nm - 1)) with (ii1(B:=unit) (n + arity nm - 1)).
         unfold nss_cons.
         induction (isdecrelnatleh (arity nm) (n + arity nm - 1)).
         - cbn.
           assert (S (n + arity nm - 1 - arity nm) = n).
           { 
             rewrite natminusminus.
             rewrite (natpluscomm 1 (arity nm)).
             rewrite <- natminusminus.
             rewrite plusminusnmm.
             change (S (n - 1)) with (1 + (n - 1)).
             rewrite natplusminusle.
             * rewrite natpluscomm.
               rewrite plusminusnmm.
               apply idpath.
             * assumption.
           }
           rewrite X0.
           apply idpath.
         - induction b.
           rewrite natpluscomm.
           rewrite <- natplusminusle.
           + apply natlehnplusnm.
           + assumption.
       }   
       exists realfirst.
       exists rest.
       repeat split.
       * assumption.
       * assumption.
       * unfold realfirst.
         rewrite concatenateStep.
         rewrite conc.
         apply idpath.
Defined.

Definition subterm(l: NameStack): ∏ (l_is_term: ns_is_term l),  ⟦ arity (princ_op (l ,, l_is_term)) ⟧ → term.
Proof.
  apply (list_ind (λ (l: NameStack), ∏ l_is_term : ns_is_term l, ⟦ arity (princ_op (l,, l_is_term)) ⟧ → term)).
  - intro.
    set (contr := nil_not_term l_is_term).
    contradiction.
  - intros x xs IH xxs_is_term.
    cbn.
    intro arx.
    induction arx as [n n_lt_arx].
    red in xxs_is_term.
    rewrite s2nss_cons in xxs_is_term.
    assert (xxs_ok: nss_cons x (s2ss xs) != stackerror).
    {
      rewrite xxs_is_term.
      apply negpathsii1ii2.
    }
    set ( xs_ok := nss_cons_noerror x (s2ss xs) xxs_ok).
    induction xs_ok as [xs_ss [ xs_ss_proof xs_ss_bound ]].
    rewrite xs_ss_proof in xxs_is_term.
    assert ( xs_arity: xs_ss = arity x).
    {
      set ( X := nss_cons_stackok2 x xs_ss 1  xxs_is_term).
      change (1) with (1+0) in X.
      change (S (xs_ss - arity x)) with (1 + (xs_ss - arity x)) in X.
      set (Y := natpluslcan _ _ _ X).
      set (Z := natdiff0 _ _ Y).
      apply natdiffasymm; assumption.
    }
    rewrite xs_arity in xs_ss_proof.
    induction (isdecrelnatgeh n 1) as [n_gte_1 | n_eq_0].
    + assert ( extractok: n- 1 ≤ arity x).
      {
        apply (istransnatleh(m := arity x - 1)).
        - apply natlehandminusl.
          apply natlthtoleh.
          assumption.
        - apply natminuslehn.
      }
      set (remove := extract_subnss xs (n - 1) (arity x) xs_ss_proof extractok).
      induction remove as [first [ second  [ firstss [ secondss conc] ] ] ].
      assert ( extractok2: 1 ≤ arity x - (n - 1) ).
      {
        apply (natlehandplusrinv _ _ (n - 1)).
        rewrite minusplusnmm by (assumption).
        rewrite natplusminusle by (assumption).
        rewrite natpluscomm.
        rewrite <- natplusminusle by (apply idpath).
        simpl (1 - 1).
        rewrite natplusr0.
        apply natlthtoleh.
        assumption.
      }
      set (res := extract_subnss second 1 (arity x - (n - 1)) secondss extractok2).
      induction res as [result [second0 [result_is_term [second_ss conc1]]]].
      exact (result ,, result_is_term).
   + assert (n_is_0: n = 0) by ( apply nat_ax4; assumption ).
     assert (extractok: 1 ≤ arity x ).
     {
       apply natlthtolehsn.
       rewrite <- n_is_0.
       assumption.
     }
     set (res := extract_subnss xs 1 (arity x) xs_ss_proof extractok).
     induction res as [result  [second0 [result_is_term [second_ss conc1]]]].
     exact (result ,, result_is_term).
Defined.

Definition term_ind :=
  ∏ (P: term → UU),
     ( ∏ (nm: names sigma) (vterm: Vector term (arity nm)), (∏ (i:  ⟦ arity nm ⟧), P (el vterm i)) → P (mkterm nm vterm) ) →
     (∏ t: term, P t).

End TermAlgebra.
