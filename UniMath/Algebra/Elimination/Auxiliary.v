(** * Matrices

  Miscellaneous background lemmas for [Elimination.Elimination]

  Author: Daniel @Skantz (September 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Maybe.

Require Import UniMath.PAdics.lemmas.

Require Import UniMath.NumberSystems.RationalNumbers.

Require Import UniMath.RealNumbers.Prelim.

(** Results of this file are required for the [Elimination] subpackage but aren’t specifically part of the topic; probably could/should be upstreamed within [UniMath] *)

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

  Lemma eq_to_natleh (m n : nat) : m = n -> m ≤ n.
  Proof.
    intros e; destruct e. apply isreflnatleh.
  Qed.

  Lemma eq_of_le_le {a b : nat} (le_a_b : a ≤ b) (le_b_a : b ≤ a)
    : a = b.
  Proof.
    destruct (natlehchoice _ _ le_a_b) as [lt_a_b | e_a_b].
    2: { assumption. }
    apply fromempty. eapply natlthtonegnatgeh; eassumption.
  Qed.


  Lemma minussn1'
    ( n : nat ) : n ≤ ( S n ) - 1.
  Proof.
    apply eq_to_natleh, pathsinv0, minussn1.
  Defined.

  Lemma prev_nat
    (n : nat) (p : n > 0): ∑ m, S m = n.
  Proof.
    destruct n as [| n]. { contradiction (negnatlthn0 _ p). }
    exists n; reflexivity.
  Defined.

  (* alias for searchability *)
  Lemma isdeceqnatcommrig : isdeceq natcommrig.
  Proof.
    apply isdeceqnat.
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

  Lemma nat_eq_or_neq_refl
    (i : nat) : nat_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    destruct (nat_eq_or_neq i i) as [ ? | cnt].
    2: { eapply fromempty, isirrefl_natneq, cnt. }
    apply maponpaths, isasetnat.
  Defined.

  Lemma nat_eq_or_neq_left:
    ∏ {i j: nat} (p : (i = j)),
      nat_eq_or_neq i j = inl p.
  Proof.
    intros i j i_eq_j.
    destruct i_eq_j.
    apply nat_eq_or_neq_refl.
  Defined.

  Lemma nat_eq_or_neq_right:
    ∏ {i j: nat} (p : (i ≠ j)),
      nat_eq_or_neq i j = inr p.
  Proof.
    intros i j i_neq_j.
    destruct (nat_eq_or_neq i j) as [i_eq_j | ?].
    { apply (from_natneq_eq i j i_eq_j i_neq_j). }
    apply maponpaths, propproperty.
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

  Lemma stn_eq_or_neq_refl
    {n : nat} {i : ⟦ n ⟧%stn} : stn_eq_or_neq i i = inl (idpath i).
  Proof.
    intros; unfold stn_eq_or_neq; simpl.
    destruct (nat_eq_or_neq i i) as [? | neq].
    2 : { contradiction (isirrefl_natneq _ neq). }
    simpl. apply maponpaths, isasetstn.
  Defined.

  Lemma stn_eq_or_neq_left :
    ∏ {n : nat} {i j: (⟦ n ⟧)%stn} (p : (i = j)),
      stn_eq_or_neq i j = inl p.
  Proof.
    intros ? ? ? p. rewrite p. apply stn_eq_or_neq_refl.
  Defined.

  Lemma stn_eq_or_neq_right
    : ∏ {n : nat} {i j : (⟦ n ⟧)%stn} (p : (i ≠ j)),
    stn_eq_or_neq i j = inr p.
  Proof.
    intros n i j i_neq_j.
    destruct (stn_eq_or_neq i j) as [i_eq_j | ?].
    { apply fromempty.
      destruct i_eq_j; eapply isirrefl_natneq, i_neq_j. }
    apply maponpaths, propproperty.
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

  Lemma stn_eq
    {k : nat} (i j : stn k) (eq : pr1 i = pr1 j) : i = j.
  Proof.
    now apply subtypePath_prop.
  Defined.

  Lemma stn_eq_2
    {k : nat} (i: stn k) (j : nat) (eq : pr1 i = j)
      : forall P : j < k, i = (j,, P).
  Proof.
    intros; apply stn_eq, eq.
  Defined.

  Lemma stn_eq_3
    {k : nat} (i: nat) (j : stn k) (eq : i = pr1 j)
      : forall P : i < k, j = (i,, P).
  Proof.
    intros; apply stn_eq, pathsinv0, eq.
  Defined.

  (* perhaps generalise to a version for any [isincl], and use [isinclstntonat]? *)
  Lemma stn_eq_nat_eq
    { n : nat} (i j : ⟦ n ⟧%stn) : i = j <-> (pr1 i = pr1 j).
  Proof.
    split.
    - apply maponpaths.
    - apply subtypePath_prop.
  Defined.

  Lemma stn_neq_nat_neq
    { n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j <-> (pr1 i ≠ pr1 j).
  Proof.
    split; apply idfun.
  Defined.

  Lemma issymm_stnneq {n : nat} {i j : stn n} (neq : i ≠ j)
    : (j ≠ i).
  Proof.
    destruct (stn_eq_or_neq j i) as [contr_eq | ?].
    - rewrite contr_eq in neq.
      contradiction (isirrefl_natneq i).
    - assumption.
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
  (** Should also be generalisable, but non-unifiedness of definitions of ≠ makes that harder than it should be. *)
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

Section Dual.

  Lemma dualelement_2x
    {n : nat} (i : ⟦ n ⟧%stn) : dualelement (dualelement i) = i.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | gt].
    { apply fromstn0. now rewrite <- contr_eq in i. }
    unfold make_stn.
    apply subtypePath_prop; simpl.
    rewrite (doubleminuslehpaths (n - 1) i); try reflexivity.
    apply minusnleh1; apply (pr2 i).
  Defined.

  Lemma dualelement_eq
    {n : nat} (i j : ⟦ n ⟧%stn)
  : dualelement i = j
    -> i = dualelement j.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0. apply fromstn0. rewrite <- contr_eq in i. assumption. }
    intros H; apply subtypePath_prop; revert H; simpl.
    intros eq; rewrite <- eq; simpl.
    rewrite minusminusmmn; try reflexivity.
    apply natlthsntoleh.
    rewrite minussn1non0; try assumption; exact (pr2 i).
  Defined.

  Lemma dualelement_lt_comp
    {n : nat} (i j : ⟦ n ⟧%stn)
  : i < j -> (dualelement i) > (dualelement j).
  Proof.
    intros lt.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0. rewrite contr_eq. assumption. }
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
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    { simpl; apply fromstn0. now rewrite contr_eq. }
    rewrite eq; apply isreflnatgeh.
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
    unfold dualelement.
    destruct (natchoice0 _) as [eq | ?]; simpl.
    { rewrite <- eq in p3; contradiction (negnatgth0n _ p3). }
    refine (istransnatlth _ _ _ _ _). {exact lt_dual. }
    unfold dualelement.
    destruct (natchoice0 _) as [contr_eq | ?].
    - apply fromempty; clear lt_dual.
      rewrite <- contr_eq in p1.
      contradiction (negnatgth0n _ p1).
    - simpl; do 2 rewrite natminusminus.
      apply natlthandminusl; try assumption.
      refine (natlehlthtrans _ _ _ _ _); try assumption.
      rewrite natpluscomm.
      apply natlthtolehp1.
      exact p1.
      assumption.
  Defined.

  Lemma dualelement_sn_eq
    {m n k q: nat} (lt : S n < S k)
    : pr1 (dualelement (n,, lt)) = (pr1 (dualelement (S n,, lt))).
  Proof.
    unfold dualelement.
    destruct (natchoice0 _) as [eq | ?].
    - apply fromempty.
      rewrite <- eq in lt.
      contradiction (nopathsfalsetotrue).
    - destruct (natchoice0 _); simpl.
      + now rewrite natminuseqn, natminusminus.
      + now rewrite natminuseqn, natminusminus.
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
    unfold dualelement in gt.
    destruct (natchoice0 (S n)) as [contreq0 | ?] in gt.
    { clear gt; now apply negpaths0sx in contreq0. }
    unfold make_stn in gt.
    destruct (natchoice0 n) as [contr_eq | ?].
    {simpl. apply fromstn0. now rewrite contr_eq. }
    simpl in gt.
    do 2 rewrite minus0r in gt.
    contradiction (natgthtonegnatleh _ _ (pr2 i)).
  Defined.

  Lemma dualelement_lt_to_le_s
    {n k : nat}
    (i : stn n)
    (p : k < n)
    (leh: dualelement (k,, p) < i)
    : dualelement (k,, istransnatlth _ _ (S n) (natgthsnn k) p) <= i.
  Proof.
    unfold dualelement in leh |- *.
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0; rewrite contr_eq; assumption. }
    rewrite coprod_rect_compute_2 in * |-.
    unfold dualelement.
    destruct (natchoice0 (S n)) as [contr_eq | gt].
    { pose (contr := (natneq0sx n));
      rewrite <- contr_eq in contr.
      contradiction (isirrefl_natneq _ contr). }
    simpl coprod_rect.
    destruct (natchoice0 n) as [eq | gt'].
    {apply fromstn0; now rewrite eq. }
    simpl in leh |- *.
    rewrite minus0r.
    apply natgthtogehsn in leh.
    rewrite pathssminus in leh.
    2: { rewrite pathssminus.
         - now rewrite minussn1.
         - now apply gt'. }
    assert (e : n = S (n - 1)).
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0. apply minusplusnmm. assumption. }
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

(** * Fields *)

(** Lemmas on fields, and in particular their decidable equality *)

Section Fields.

  Lemma fldchoice0 {X : fld} (e : X) : coprod (e = 0%ring) (e != 0%ring).
  Proof.
    destruct (fldchoice e).
    2: {left; assumption. }
    right.
    unfold multinvpair, invpair in m.
    destruct m as [m1 [m2 m3]].
    apply (@ringneq0andmultlinv X e m1).
    change 1%ring with 1%multmonoid in m3.
    assert (eq: (e * m1)%ring = 1%ring).
    { symmetry in m2. apply m3. }
    rewrite eq; apply nonzeroax.
  Defined.

  Lemma fldchoice0_left {X : fld} (e : X) (eq : (e = 0)%ring):
    (fldchoice0 e) = inl eq.
  Proof.
    destruct (fldchoice0 _).
    - apply proofirrelevance.
      apply isapropcoprod.
      + use setproperty.
      + apply isapropneg.
      + intros; contradiction.
    - contradiction.
  Defined.

  Lemma fldchoice0_right {X : fld} (e : X) (neq : (e != 0)%ring):
    (fldchoice0 e) = inr neq.
  Proof.
    destruct (fldchoice0 _).
    - contradiction.
    - apply proofirrelevance; apply isapropcoprod.
      + use setproperty.
      + apply isapropneg.
      + intros; contradiction.
  Defined.

  Lemma fldmultinvlax {X: fld} (e : X) (ne : e != 0%ring) :
    (fldmultinv e ne * e)%ring = 1%ring.
  Proof.
    unfold fldmultinv.
    unfold fldmultinvpair.
    destruct (fldchoice _) as [? | contr_eq].
    2: { apply fromempty.
         rewrite contr_eq in ne.
         contradiction. }
    destruct m as [m1 [m2 m3]].
    simpl.
    change (m1 * e)%ring with (m1 * e)%multmonoid.
    rewrite m2.
    reflexivity.
  Defined.

  Lemma fldmultinvrax {X: fld} (e : X) (ne : e != 0%ring) :
    (e * fldmultinv e ne)%ring = 1%ring.
  Proof.
    rewrite ringcomm2; apply fldmultinvlax.
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

  Lemma fldplusminus
    {F: fld} (a b : F) : (a + b - b)%ring = a.
  Proof.
    replace (a + b - b)%ring with (a + b + (- b))%ring.
    - rewrite ringassoc1.
      replace (b + - b)%ring with (b  - b)%ring.
      + rewrite ringrinvax1. apply (@rigrunax1 F).
      + reflexivity.
   - rewrite <- ringcomm1.
     reflexivity.
  Defined.

End Fields.

(** * Rationals *)
Section Rationals.

  (* could try to simplify/speed up? perhaps refactor with general injectivity of map from integers to rationals (proved either by this same technique or more directly) *)
  Lemma hqone_neq_hqzero : 1%hq != 0%hq.
  Proof.
    intro contr.
    assert (contr_hz : intpart 1%hq != intpart 0%hq).
    { unfold intpart. apply hzone_neg_hzzero. }
    apply contr_hz.
    apply maponpaths, contr.
  Defined.

  Lemma hqplusminus
    (a b : hq) : (a + b - b)%hq = a.
  Proof.
    apply (@fldplusminus hq).
  Defined.

End Rationals.

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
    - apply ii2. rewrite u. exists.
  Defined.

  Definition maybe_choice'
    {X : UU} (e : maybe X)
  : coprod (X) (e = nothing).
  Proof.
  destruct e as [x | u].
  - apply ii1. exact x.
  - apply ii2. rewrite u; exists.
  Defined.

  Definition maybe_stn_choice
    {X : UU} { n : nat }
    (e : maybe (⟦ n ⟧)%stn)
  : coprod (∑ i : ⟦ n ⟧%stn, e = just i) (e = nothing).
  Proof.
  destruct e as [i | u].
  - apply ii1. now exists i.
  - apply ii2. rewrite u; exists.
  Defined.

  Definition from_maybe
    {X : UU} (m : maybe X) (p : m != nothing) : X.
  Proof.
    unfold nothing in p.
     destruct m as [x | u].
     - exact x.
     - contradiction p.
       now rewrite u.
  Defined.

End Maybe.
