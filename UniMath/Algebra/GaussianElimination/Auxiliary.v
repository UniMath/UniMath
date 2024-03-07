(** * Matrices

  Miscellaneous background lemmas for [GaussianElimination.Elimination]

  Primary Author: Daniel @Skantz (November 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Maybe.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Algebra.RigsAndRings.

(** Results of this file are required for the [Elimination] subpackage but aren’t specifically part of the topic; probably could/should be upstreamed within [UniMath] *)

(** * Logic *)

Section Logic.

  (* not obvious how to deduce this from existing [isapropisdecprop] *)
  Lemma isaprop_dec_with_negProp {P : hProp} (Q : negProp P) : isaprop (P ⨿ Q).
  Proof.
    apply isapropcoprod.
    - apply propproperty.
    - apply propproperty.
    - intros p q; revert p. apply (negProp_to_neg q).
  Defined.

End Logic.

(** * Naturals *)
(** Lemmas for standard functions on natural numbers *)
Section Nat.

  Lemma natminus1lthn
    (n : nat) : n > 0 -> n - 1 < n.
  Proof.
    intros n_gt_0.
    apply natminuslthn.
    - assumption.
    - reflexivity.
  Defined.

  (* Next two lemmas are from PAdics.lemmas, restated here for accessibility.
     They are only used in this file, in the dualelement section. *)

  Lemma minussn1' ( n : nat ) : ( S n ) - 1 = n.
  Proof.
    destruct n; apply idpath.
  Defined.

  Local Lemma pathssminus' ( n m : nat ) ( p : natlth m ( S n ) ) :
    S ( n - m ) = ( S n ) - m.
  Proof.
    revert m p; induction n.
    intros m p; destruct m. {auto. }
    apply fromempty.
    apply nopathstruetofalse. apply pathsinv0. assumption.
    - intros m p. destruct m.
        + auto.
        + apply IHn. apply p.
  Defined.

  (* End duplicated proofs. *)

  Lemma eq_of_le_le {a b : nat} (le_a_b : a ≤ b) (le_b_a : b ≤ a)
    : a = b.
  Proof.
    destruct (natlehchoice _ _ le_a_b) as [lt_a_b | e_a_b].
    2: { assumption. }
    apply fromempty. eapply natlthtonegnatgeh; eassumption.
  Qed.

  Lemma prev_nat
    (n : nat) (p : n > 0): ∑ m, S m = n.
  Proof.
    destruct n as [| n]. { contradiction (negnatlthn0 _ p). }
    exists n; reflexivity.
  Defined.

  Lemma from_natneq_eq
    {X : UU} (m n : nat) : (m = n) -> (m ≠ n) -> X.
  Proof.
    intros m_eq_n m_neq_n.
    apply fromempty.
    destruct m_eq_n.
    eapply isirrefl_natneq.
    exact (m_neq_n).
  Defined.

  Lemma isaprop_nat_eq_or_neq {m n : nat} : isaprop ((m = n) ⨿ (m ≠ n)).
  Proof.
    refine (@isaprop_dec_with_negProp (_,,_) (natneq _ _)).
    apply isasetnat.
  Defined.

  Lemma nat_eq_or_neq_refl (i : nat)
    : nat_eq_or_neq i i = inl (idpath i).
  Proof.
    apply isaprop_nat_eq_or_neq.
  Defined.

  Lemma nat_eq_or_neq_left {i j: nat} (p : i = j)
    : nat_eq_or_neq i j = inl p.
  Proof.
    apply isaprop_nat_eq_or_neq.
  Defined.

  Lemma nat_eq_or_neq_right {i j: nat} (p : i ≠ j)
    : nat_eq_or_neq i j = inr p.
  Proof.
    apply isaprop_nat_eq_or_neq.
  Defined.

  Lemma min_le_l:
    ∏ a b : (nat), min a b ≤ a.
  Proof.
    intros; unfold min; revert a.
    induction b as [| b IH]; destruct a ; try reflexivity.
    apply IH.
  Defined.

  Lemma min_le_r:
    ∏ a b : (nat), min a b ≤ b.
  Proof.
    intros; unfold min; revert a.
    induction b as [| b IH]; destruct a ; try reflexivity.
    apply IH.
  Defined.

  Lemma min_le_iff :
    ∏ a b c : nat, (a ≤ min b c) <-> (a ≤ b ∧ a ≤ c).
  Proof.
    intros a b c; split.
    - intros le_a_mbc; split; eapply (istransnatleh le_a_mbc).
      + apply min_le_l.
      + apply min_le_r.
    - revert a c; induction b as [ | b' IH ]; intros a c [le_a_b le_a_c].
      { intros; exact le_a_b. } (* case b = 0 *)
      destruct c as [ | c' ].
      { exact le_a_c. } (* case c = 0 *)
      destruct a as [ | a' ].
      { apply natleh0n. } (* case a = 0 *)
      (* when all successors, done by the reductions
          [ min (S b') (S c')  ~~>  S (min b' c') ]
          [ S x ≤ S y  ~~>  x ≤ y ] *)
      apply IH.
      split; assumption.
  Qed.

  (** All further properties of [min] should be derivable from [min_le_iff]:
  the inductive definition of [min] should never need unfolding again
  (though of course it can be, if that makes a proof nicer). *)

  Lemma min_of_le {a b : nat} (le_a_b : a ≤ b) : min a b = a.
  Proof.
    apply eq_of_le_le.
    - apply min_le_l.
    - apply min_le_iff. split; try assumption. apply isreflnatleh.
  Qed.

  Lemma min_comm (a b : nat) : min a b = min b a.
  Proof.
    apply eq_of_le_le;
      apply min_le_iff; split; auto using min_le_l, min_le_r.
  Qed.

  Lemma min_eq_a_or_eq_b :
    ∏ a b : (nat), coprod (min a b = a) (min a b = b).
  Proof.
    intros a b. destruct (natleorle a b) as [le_a_b | le_b_a].
    - apply inl. apply min_of_le; assumption.
    - apply inr. rewrite min_comm. apply min_of_le; assumption.
  Qed.

End Nat.

(** * Standard finite sets *)
(** lemmas for working with [Stn], the standard finite sets *)

Section Stn.

  Lemma minabstn_to_astn
    { a b : nat } : ⟦ min a b ⟧%stn -> ⟦ a ⟧%stn.
  Proof.
    apply stnmtostnn, min_le_l.
  Defined.

  Lemma minabstn_to_bstn
    { a b : nat } : ⟦ min a b ⟧%stn -> ⟦ b ⟧%stn.
  Proof.
    apply stnmtostnn, min_le_r.
  Defined.

  Lemma stn_inhabited_implies_succ
    {n:nat} (i : ⟦ n ⟧%stn)
  : ∑ m, n = S m.
  Proof.
    destruct n as [| m].
    - destruct i as [i le_i_0].
      destruct (negnatlthn0 _ le_i_0).
    - exists m. apply idpath.
  Defined.

  Lemma isaprop_stn_eq_or_neq {n} (i j : ⟦n⟧%stn)
    : isaprop ((i = j) ⨿ (i ≠ j)).
  Proof.
    refine (@isaprop_dec_with_negProp (_,,_) (stnneq _ _)).
    apply isasetstn.
  Defined.

  Lemma stn_eq_or_neq_refl {n} {i : ⟦ n ⟧%stn}
    : stn_eq_or_neq i i = inl (idpath i).
  Proof.
    apply isaprop_stn_eq_or_neq.
  Defined.

  Lemma stn_eq_or_neq_left {n} {i j: (⟦ n ⟧)%stn}
    : forall p : i = j, stn_eq_or_neq i j = inl p.
  Proof.
    intros; apply isaprop_stn_eq_or_neq.
  Defined.

  Lemma stn_eq_or_neq_right {n} {i j : (⟦ n ⟧)%stn}
    : forall (p : i ≠ j), stn_eq_or_neq i j = inr p.
  Proof.
    intros; apply isaprop_stn_eq_or_neq.
  Defined.

  Lemma stn_implies_ngt0
    { n : nat} (i : ⟦ n ⟧%stn) : n > 0.
  Proof.
    eapply natgthgehtrans. { exact (stnlt i). }
    apply natgehn0.
  Defined.

  Lemma stn_implies_nneq0
    { n : nat } (i : ⟦ n ⟧%stn) : n ≠ 0.
  Proof.
    apply natgthtoneq, stn_implies_ngt0, i.
  Defined.

  Lemma snlehm_to_nltm
    (m n : nat) : (S n ≤ m) -> n < m.
  Proof.
    intros le_sn_m; exact le_sn_m.
  Defined.

  Lemma stn_eq {k : nat} (i j : stn k) (eq : pr1 i = pr1 j)
    : i = j.
  Proof.
    now apply subtypePath_prop.
  Defined.

  Lemma stn_eq_2 {k : nat} (i: stn k) (j : nat) (eq : pr1 i = j) (P : j < k)
    : i = (j,, P).
  Proof.
    intros; apply stn_eq, eq.
  Defined.

  (* perhaps generalise to a version for any [isincl], and use [isinclstntonat]? *)
  Lemma stn_eq_nat_eq
    { n : nat } (i j : ⟦ n ⟧%stn) : i = j <-> (pr1 i = pr1 j).
  Proof.
    split.
    - apply maponpaths.
    - apply subtypePath_prop.
  Defined.

  Lemma stn_neq_nat_neq
    { n : nat } (i j : ⟦ n ⟧%stn) : i ≠ j <-> (pr1 i ≠ pr1 j).
  Proof.
    split; apply idfun.
  Defined.

  Lemma issymm_stnneq {n : nat} {i j : stn n} (neq : i ≠ j)
    : (j ≠ i).
  Proof.
    apply issymm_natneq; assumption.
  Defined.

  Lemma prev_stn
    {n : nat} (i : ⟦ n ⟧%stn) (p : i > 0) : ∑ j : ⟦ n ⟧%stn, S j = i.
  Proof.
    destruct (prev_nat i p) as [j Sj_i].
    use tpair.
    - exists j.
      refine (istransnatlth _ _ _ (natgthsnn j) _ ).
      rewrite Sj_i.
      apply (pr2 i).
    - exact Sj_i.
  Defined.

  (** General symmetry for decidable equality is tricky to state+prove (requires Hedberg’s theorem); but for non-dependent case-splits, it’s cleaner. *)
  (** Should also be generalisable using [negProp], ideally *)
  Lemma stn_eq_or_neq_symm_nondep {n} {x y : ⟦n⟧%stn}
        (de_xy : (x = y) ⨿ (x ≠ y)%stn) (de_yx : (y = x) ⨿ (y ≠ x)%stn)
       {Z} (z1 z2 : Z)
    : coprod_rect (fun _ => Z) (fun _ => z1) (fun _ => z2) de_xy
    = coprod_rect (fun _ => Z) (fun _ => z1) (fun _ => z2) de_yx.
  Proof.
    destruct de_xy as [e_xy | ne_xy];
      destruct de_yx as [e_yx | ne_yx];
      simpl;
    (** consistent cases: *)
      try reflexivity;
    (** inconsistent cases: *)
      eapply fromempty, nat_neq_to_nopath; try eassumption;
      apply pathsinv0, maponpaths; assumption.
  Defined.

End Stn.

(** Lemmas on the “dual” function on the standard finite sets, reversing the order *)

(** Note: the definition of [dualelement] upstream has an unnecessary case split.
    We provide an alternative to simplify proofs in this section, that could potentially be upstreamed. *)
Section Dual.

  Definition dualelement' {n : nat} (i : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
  Proof.
    refine (make_stn n (n - 1 - i) _).
    apply StandardFiniteSets.dualelement_lt. (* Make non-local upstream? *)
    now apply stn_implies_ngt0.
  Defined.

  Definition dualelement_defs_eq {n : nat} (i : ⟦ n ⟧%stn)
    : dualelement i = dualelement' i.
  Proof.
    unfold dualelement', dualelement.
    apply subtypePath_prop; simpl.
    destruct (natchoice0 _) as [eq0 | gt]; reflexivity.
  Defined.

  Lemma dualelement_2x
    {n : nat} (i : ⟦ n ⟧%stn) : dualelement (dualelement i) = i.
  Proof.
    do 2 rewrite dualelement_defs_eq; unfold dualelement'.
    unfold make_stn.
    apply subtypePath_prop; simpl.
    rewrite minusminusmmn; try reflexivity.
    apply natgthtogehm1, (pr2 i).
  Defined.

  Lemma dualelement_eq
    {n : nat} (i j : ⟦ n ⟧%stn)
  : dualelement i = j
    -> i = dualelement j.
  Proof.
    do 2 rewrite dualelement_defs_eq; unfold dualelement'.
    intros H; apply subtypePath_prop; revert H; simpl.
    intros eq; rewrite <- eq; simpl.
    rewrite minusminusmmn; try reflexivity.
    apply natlthsntoleh.
    apply natgthtogehm1, (pr2 i).
  Defined.

  Lemma dualelement_lt_comp
    {n : nat} (i j : ⟦ n ⟧%stn)
  : i < j -> (dualelement i) > (dualelement j).
  Proof.
    intros lt.
    do 2 rewrite dualelement_defs_eq; unfold dualelement'.
    apply minusgth0inv; simpl.
    rewrite natminusminusassoc, natpluscomm,
    <- natminusminusassoc, minusminusmmn.
    2: {apply (natgthtogehm1 _ _ (pr2 j)). }
    apply (minusgth0 _ _ lt).
  Defined.

  Lemma dualelement_lt_comp'
    {n : nat} (i j : ⟦ n ⟧%stn)
  : (dualelement i) < (dualelement j)
    -> j < i.
  Proof.
    intros lt.
    pose (H := @dualelement_lt_comp _ (dualelement i) (dualelement j) lt).
    now do 2 rewrite dualelement_2x in H.
  Defined.

  Lemma dualelement_le_comp
    {n : nat} (i j : ⟦ n ⟧%stn)
  : i ≤ j -> (dualelement j) ≤ (dualelement i).
  Proof.
    intros le.
    destruct (natlehchoice i j) as [lt | eq]; try assumption.
    { apply natlthtoleh. apply (dualelement_lt_comp _ _ lt). }
    rewrite (stn_eq _ _ eq).
    apply isreflnatgeh.
  Defined.

  Lemma dualelement_le_comp'
    {n : nat} (i j : ⟦ n ⟧%stn)
  : (dualelement i) ≤ (dualelement j)
    -> j ≤ i.
  Proof.
    intros le.
    pose (H := @dualelement_le_comp _ (dualelement i) (dualelement j) le).
    now do 2 rewrite dualelement_2x in H.
  Defined.

  Lemma dualelement_lt_trans_2
    {m n k q: nat} (p1 : n < k ) (p2 : n < q) (p3 : k < q)
    (lt_dual : m < dualelement (n,, p1))
    : (m < (dualelement (n,, p2))).
  Proof.
    rewrite dualelement_defs_eq; unfold dualelement'.
    refine (istransnatlth _ _ _ _ _). {exact lt_dual. }
    rewrite dualelement_defs_eq.
    simpl; do 2 rewrite natminusminus.
    apply natlthandminusl; try assumption.
    refine (natlehlthtrans _ _ _ _ _); try assumption.
    2: { exact p3. }
    rewrite natpluscomm.
    apply natlthtolehp1.
    exact p1; assumption.
  Defined.

  Lemma dualelement_sn_eq
    {m n k q: nat} (lt : S n < S k)
    : pr1 (dualelement (n,, lt)) = (pr1 (dualelement (S n,, lt))).
  Proof.
    do 2 rewrite dualelement_defs_eq; unfold dualelement'; simpl.
    now rewrite natminuseqn, natminusminus.
  Defined.

  Lemma dualelement_sn_le
    {m n k q: nat} (lt : S n < S k)
    : pr1 (dualelement (n,, lt)) <= (pr1 (dualelement (S n,, lt))).
  Proof.
    rewrite (@dualelement_sn_eq n n k k lt).
    apply isreflnatleh.
  Defined.

  Lemma dualelement_sn_le_2
  {m n k q: nat} (lt : S n < S k)
  : pr1 (dualelement (n,, lt)) >= (pr1 (dualelement (S n,, lt))).
  Proof.
    rewrite (@dualelement_sn_eq n n k k lt).
    apply isreflnatleh.
  Defined.

  Lemma dualelement_sn_stn_nge_0
   {n : nat} (i : stn n)
   : forall lt : (0 < S n), i >= (dualelement (0,, lt)) -> empty.
  Proof.
    intros lt gt.
    rewrite dualelement_defs_eq in gt; unfold dualelement' in gt.
    simpl in gt.
    do 2 rewrite natminuseqn in gt.
    contradiction (natgthtonegnatleh _ _ (pr2 i)).
  Defined.

  Lemma dualelement_sn_stn_ge_n
   {n : nat} (i : stn n) : i >= (dualelement (n,, natgthsnn n)).
  Proof.
    rewrite dualelement_defs_eq.
    simpl.
    rewrite (@natminuseqn _), minuseq0'.
    apply idpath.
  Defined.

  Lemma dualelement_lt_to_le_s
    {n k : nat}
    (i : stn n)
    (p : k < n)
    (leh: dualelement (k,, p) < i)
    : dualelement (k,, istransnatlth _ _ (S n) (natgthsnn k) p) <= i.
  Proof.
    rewrite dualelement_defs_eq; rewrite dualelement_defs_eq in leh;
    unfold dualelement' in leh |- *; simpl in leh |- *.
    rewrite natminuseqn.
    apply natgthtogehsn in leh.
    rewrite pathssminus' in leh.
    2: { rewrite pathssminus'.
         - now rewrite minussn1'.
         - now apply (stn_implies_ngt0 i). }
    assert (e : n = S (n - 1)).
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0, minusplusnmm, (natlthtolehp1 _ _ (stn_implies_ngt0 i)). }
    now destruct (!e).
  Defined.

  Lemma dualvalue_eq
    {X : UU} {n : nat}
    (v : ⟦ n ⟧%stn -> X) (i : ⟦ n ⟧%stn)
  : (v i) = (λ i' : ⟦ n ⟧%stn, v (dualelement i')) (dualelement i).
  Proof.
    simpl; now rewrite dualelement_2x.
  Defined.

End Dual.

(** * Rings, fields *)

(** Lemmas on general rings and fields, and in particular their decidable equality *)

Section Rings_and_Fields.

  #[reversible=no] Coercion multlinvpair_of_multinvpair {R : rig} (x : R)
    : @multinvpair R x -> @multlinvpair R x.
  Proof.
    intros [y [xy yx]]. esplit; eauto.
  Defined.

  #[reversible=no] Coercion multrinvpair_of_multinvpair {R : rig} (x : R)
    : @multinvpair R x -> @multrinvpair R x.
  Proof.
    intros [y [xy yx]]. esplit; eauto.
  Defined.

  Lemma ringplusminus
    {R: ring} (a b : R) : (a + b - b)%ring = a.
  Proof.
    rewrite ringassoc1.
    rewrite ringrinvax1.
    apply (rigrunax1 R).
  Defined.

  Lemma ringminusdistr' { X : commring } ( a b c : X ) :
    (a * (b - c))%ring = (a * b - a * c)%ring.
  Proof.
    intros. rewrite ringldistr. rewrite ringrmultminus. apply idpath.
  Defined.

  Lemma fldchoice0 {X : fld} (e : X) : coprod (e = 0%ring) (e != 0%ring).
  Proof.
    destruct (fldchoice e) as [ x_inv | x_0 ].
    - right.
      apply isnonzerofromrinvel. { apply nonzeroax. }
      exact x_inv.
    - left; assumption.
  Defined.

  Lemma fldchoice0_left {X : fld} (e : X) (eq : (e = 0)%ring):
    (fldchoice0 e) = inl eq.
  Proof.
    apply isapropdec, setproperty.
  Defined.

  Lemma fldchoice0_right {X : fld} (e : X) (neq : (e != 0)%ring):
    (fldchoice0 e) = inr neq.
  Proof.
    apply isapropdec, setproperty.
  Defined.

  Lemma fldmultinvlax {X: fld} (e : X) (ne : e != 0%ring) :
    (fldmultinv e ne * e)%ring = 1%ring.
  Proof.
    exact (pr1 (pr2 (fldmultinvpair _ e ne))).
  Defined.

  Lemma fldmultinvrax {X: fld} (e : X) (ne : e != 0%ring) :
    (e * fldmultinv e ne)%ring = 1%ring.
  Proof.
    exact (pr2 (pr2 (fldmultinvpair _ e ne))).
  Defined.

  Definition fldmultinv' {X : fld} (e : X) : X.
  Proof.
    destruct (fldchoice0 e) as [eq0 | neq].
    - exact 0%ring.
    - exact (fldmultinv e neq).
  Defined.

  Lemma fldmultinvlax' {X: fld} (e : X) (ne : e != 0%ring) :
    (fldmultinv' e * e)%ring = 1%ring.
  Proof.
    unfold fldmultinv'.
    destruct (fldchoice0 _).
    - contradiction.
    - apply fldmultinvlax.
  Defined.

  Lemma fldmultinvrax' {X: fld} (e : X) (ne : e != 0%ring) :
    (e * fldmultinv' e)%ring = 1%ring.
  Proof.
    unfold fldmultinv'.
    destruct (fldchoice0 _).
    - contradiction.
    - apply fldmultinvrax.
  Defined.

End Rings_and_Fields.

(** * Rationals. Commented out to respect import dependency ordering. Could be downstreamed or removed. *)
(* Section Rationals.

  Lemma hqone_neq_hqzero : 1%hq != 0%hq.
  Proof.
    intro contr.
    assert (contr_hz : intpart 1%hq != intpart 0%hq).
    { unfold intpart. apply hzone_neg_hzzero. }
    apply contr_hz.
    apply maponpaths, contr.
  Defined.
  (* A more obvious approach might be to use the injectivity of the map from the integers:
    [apply hzone_neg_hzzero; refine (invmaponpathsincl _ isinclhztohq 1%hz 0%hz contr).]
  However, this turns out very slow, apparently because recognising [hztohq 1%hz = 1%hq] is slow (and similarly for 0).  Seems surprising that this is slower than computing [intpart 1%hq = 1%hz]!
*)

  Lemma hqplusminus
    (a b : hq) : (a + b - b)%hq = a.
  Proof.
    apply (@ringplusminus hq).
  Defined.

End Rationals. *)

(** * Maybe *)

(** Lemmas on the general “maybe” construction *)

Section Maybe.

  Lemma isdeceqmaybe
    {X : UU} (dec : isdeceq X) : isdeceq (maybe X).
  Proof.
    apply isdeceqcoprod.
    - exact dec.
    - exact isdecequnit.
  Defined.

  Definition maybe_choice
    {X : UU} (e : maybe X)
  : coprod (e != nothing) (e = nothing).
  Proof.
    destruct e as [? | u].
    - apply ii1. apply negpathsii1ii2.
    - apply ii2. now induction u.
  Defined.

  Definition maybe_choice'
    {X : UU} (e : maybe X)
  : coprod (∑ x:X, e = just x) (e = nothing).
  Proof.
    destruct e as [x | u].
    - apply ii1. exists x; reflexivity.
    - apply ii2. now induction u.
  Defined.

  Definition from_maybe
    {X : UU} (m : maybe X) (p : m != nothing) : X.
  Proof.
    unfold nothing in p.
     destruct m as [x | u].
     - exact x.
     - contradiction p.
       now induction u.
  Defined.

End Maybe.
