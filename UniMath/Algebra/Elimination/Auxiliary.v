 (** * Matrices

Miscellaneous background lemmas for [Elimination.Elimination]

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.Maybe.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.PAdics.lemmas.

Require Import UniMath.NumberSystems.RationalNumbers.

(* The first few sections contain Definitions and Lemmas that
   should be moved further up the project tree *)

(* Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation  Σ := (iterop_fun 0%hq op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2). *)

Section Misc.

  Definition min'
    (n m : nat) : nat.
  Proof.
    induction (natgthorleh n m).
    - exact m.
    - exact n.
  Defined.

  Lemma min'_eq_min
    (n m : nat)
    : min n m = min' n m.
  Proof.
  Abort.

  Lemma min_le_b:
    ∏ a b : (nat), min a b ≤ b.
  Proof.
    intros.
    unfold min.
    revert a.
    induction b; destruct a ; try reflexivity.
    apply IHb.
  Defined.

  Lemma min_le_a:
    ∏ a b : (nat), min a b ≤ a.
  Proof.
    intros.
    unfold min.
    revert a.
    induction b; destruct a ; try reflexivity.
    apply IHb.
  Defined.

  Lemma min_eq_a_or_eq_b :
    ∏ a b : (nat),  coprod (min a b = a) (min a b = b).
  Proof.
    intros.
    destruct (natgthorleh a b).
    - apply ii2.
      unfold min.
      revert h. revert b.
      induction a; destruct b; try reflexivity.
      { intros. apply fromempty. apply negnatgth0n in h. assumption.  }
      intros; rewrite IHa. {reflexivity. }
      apply h.
    - apply ii1.
      unfold min; revert h. revert b.
      induction a; destruct b; try reflexivity.
      { intros; apply negnatlehsn0 in h.
        apply fromempty; assumption. }
      intros.
      rewrite IHa. {reflexivity. }
      apply h.
  Defined.

  Lemma minsymm
    (a b : nat) : min a b = min b a.
  Proof.
  Abort.

  Lemma minabstn_to_astn
    { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ a ⟧%stn.
  Proof.
    intros.
    refine (pr1 i,, _).
    exact (natlthlehtrans _ _ _ (pr2 i)  (min_le_a a b)).
  Defined.
  Lemma minabstn_to_bstn
    { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ b ⟧%stn.
  Proof.
    intros.
    refine (pr1 i,, _).
    exact (natlthlehtrans _ _ _ (pr2 i)  (min_le_b a b)).
  Defined.

  Lemma natminus1lthn
    (n : nat) : n > 0 -> n - 1 < n.
  Proof.
    intros n_gt_0.
    apply natminuslthn.
    - assumption.
    - reflexivity.
  Defined.

  (*
   TODO: perhaps rename to avoid clash with current [PAdics.Lemmas.minussn1]? *)
  Lemma minussn1
    ( n : nat ) : n ≤ ( S n ) - 1.
  Proof.
    intros. destruct n. apply idpath.
    assert (e : (S (S n)) > (S n)).
    { apply natgthsnn. }
    apply natgthtogehm1 in e. assumption.
  Defined.

  Lemma prev_nat
    (n : nat) (p : n > 0): ∑ m, S m = n.
  Proof.
    destruct n as [| n]. {contradiction (negnatlthn0 _ p). }
    use tpair; try apply n; reflexivity.
  Defined.

  Lemma fldchoice0 {X : fld} (e : X) : coprod (e = 0%ring) (e != 0%ring).
  Proof.
    destruct (fldchoice e).
    2: {left; assumption. }
    right.
    unfold multinvpair, invpair in m.
    destruct m as [m1 m2].
    destruct m2 as [m2 m3].
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

  Lemma fldmultinv_eq {F : fld} : forall (e1 e2 : F), forall p1 : e1 != 0%ring,
    forall p2: e2 != 0%ring, e1 = e2 -> fldmultinv e1 p1 = fldmultinv e2 p2.
  Proof.
    intros.
    unfold fldmultinv, fldmultinvpair.
    destruct (fldchoice _) as [eq0 | neq0].
    - destruct (fldchoice _) as [eq0' | neq0'].
      +  
        unfold multinvpair in *.
        
        pose (H1 := invtolinv _ _ eq0).
        pose (H2 := invtorinv _ _ eq0').
        unfold linvpair in H1.
        unfold rinvpair in H2.
        rewrite <- X in H2.
        unfold invpair in eq0.
        pose (H3 := pathslinvtorinv _ _ H1 H2).
        simpl in H3.

        rewrite <- X in H3.
        destruct eq0 as [eq0 ?].
        rewrite H3.
        pose (H4 := invtolinv _ _ eq0).
        pose (H5 := invtorinv _ _ eq0').
        clear H3.
        rewrite X in H4.
        pose (H6 := pathslinvtorinv _ _ H4 H5).
        simpl.
        simpl in H6.
        rewrite <- H6.
        simpl.

        apply pathslinvtorinv.
        unfold H2.
        assumption.
        apply H3.
        destruct eq0 as [inv rinv].
        destruct eq0' as [inv' rinv'].
        Search "unique".
        simpl.
        Search "multmonoid".
        Search "inv2".
        Search rigmultmonoid.
        Search "ringinv".
        Search 1%multmonoid.
        Search "rinvel".
        Search "uniq".
        Search invpair.
        Search "invuniq".
        About nonzeroax.
        unfold 1%multmonoid in *.
        rewrite X.

  Lemma hqplusminus
    (a b : hq) : (a + b - b)%hq = a.
  Proof.
    replace (a + b - b)%hq with (a + b + (- b))%hq.
    - rewrite hqplusassoc.
      replace (b + - b)%hq with (b  - b)%hq.
      + rewrite hqrminus; apply (@rigrunax1 hq).
      + reflexivity.
   - symmetry.
     rewrite hqpluscomm.
     reflexivity.
  Defined.

  Lemma fromnatcontr
    {X : UU} (m n : nat) : (m = n) -> (m ≠ n) -> X.
  Proof.
    intros m_eq_n m_neq_n.
    rewrite m_eq_n in m_neq_n.
    apply isirrefl_natneq in m_neq_n.
    apply fromempty.
    exact (m_neq_n).
  Defined.

  Lemma nat_eq_or_neq_refl
    (i : nat) : nat_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    destruct (nat_eq_or_neq i i) as [ ? | cnt].
    2 : { remember cnt as cnt'. clear Heqcnt'.
          apply isirrefl_natneq in cnt. contradiction. }
    apply maponpaths.
    apply proofirrelevance.
    apply isaproppathsfromisolated.
    apply isisolatedn.
  Defined.

      (* TODO: look for other places this can simplify proofs! and upstream? *)
  Lemma stn_eq_or_neq_refl
    {n : nat} {i : ⟦ n ⟧%stn} : stn_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    unfold stn_eq_or_neq.
    simpl.
    destruct (nat_eq_or_neq i i).  (* TODO rewrite h*)
    2 : { remember h as h'. clear Heqh'. apply isirrefl_natneq in h. contradiction. }
    rewrite coprod_rect_compute_1.
    apply maponpaths.
    remember p as p'. clear Heqp'.
    apply subtypePath_prop in p.
    set (fst := pr1 i).
    assert (X : fst = fst). { apply idpath. }
    apply proofirrelevance.
    apply isaproppathsfromisolated.
    apply isisolatedinstn.
  Defined.

  Lemma nat_eq_or_neq_left:
    ∏ {i j: nat} (p : (i = j)),
      nat_eq_or_neq i j = inl p.
  Proof.
    intros i j i_eq_j.
    rewrite i_eq_j.
    apply nat_eq_or_neq_refl.
  Defined.

  Lemma nat_eq_or_neq_right:
    ∏ {i j: nat} (p : (i ≠ j)),
      nat_eq_or_neq i j = inr p.
  Proof.
    intros i j i_neq_j.
    destruct (nat_eq_or_neq i j) as [i_eq_j | ?].
    - apply (fromnatcontr i j i_eq_j i_neq_j).
    - apply proofirrelevance.
      apply isapropcoprod.
      + apply isaproppathsfromisolated.
        apply isisolatedn.
      + apply propproperty.
      + intros i_eq_j.
        apply (fromnatcontr i j i_eq_j i_neq_j).
  Defined.

End Misc.


Section PrelStn.

  Lemma stn_inhabited_implies_succ
    {n:nat} (i : ⟦ n ⟧%stn)
  : ∑ m, n = S m.
  Proof.
    destruct n as [| m].
    - destruct i as [i le_i_0].
      destruct (nopathsfalsetotrue le_i_0).
    - exists m. apply idpath.
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
    intros ? ? ? p. unfold stn_eq_or_neq.
    destruct (nat_eq_or_neq i j).
    - apply fromempty. rewrite p0 in p.
       apply isirrefl_natneq in p.
       assumption.
    -  apply isapropcoprod.
       + apply stn_ne_iff_neq in p. apply isdecpropfromneg. assumption.
       + apply negProp_to_isaprop.
       + intros i_eq_j.
         rewrite i_eq_j in p.
         apply isirrefl_natneq in p.
         apply fromempty; assumption.
  Defined.

  Lemma stn_implies_nneq0
    { n : nat } (i : ⟦ n ⟧%stn) : n ≠ 0.
  Proof.
    induction (natchoice0 n) as [T | F].
    - rewrite <- T in i.
      apply weqstn0toempty in i. apply fromempty. assumption.
    - change (0 < n) with (n > 0) in F.
      destruct n.
      + apply isirreflnatgth in F. apply fromempty. assumption.
      + apply natgthtoneq in F. reflexivity.
  Defined.

  Lemma stn_implies_ngt0
    { n : nat} (i : ⟦ n ⟧%stn) : n > 0.
  Proof.
    exact (natneq0to0lth n (stn_implies_nneq0 i)).
  Defined.

  Lemma snlehtotonlt
    (m n : nat) : n > 0 -> (S n ≤ m) -> n < m.
  Proof.
    intros ngt0 snltm.
    assert (n_lt_sn : n < S n).
      { apply natlthnsn. }
    apply natlehsntolth.
      assumption.
  Defined.

  Lemma stn_eq_nat_eq
    { n : nat} (i j : ⟦ n ⟧%stn) : i = j <-> (pr1 i = pr1 j).
  Proof.
    split.
    - intros i_eq_j.
      { rewrite i_eq_j. apply idpath. }
    - intros pr1i_eq_pr1j.
      { apply subtypePath_prop; assumption. }
  Defined.

  Lemma stn_neq_nat_neq
    { n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j <-> (pr1 i ≠ pr1 j).
  Proof.
    split.
    - intros i_neq_j.
      { apply i_neq_j. }
    - intros pr1i_neq_pr1j.
      { apply pr1i_neq_pr1j. }
  Defined.

  Lemma stnmn_to_stn0n
    { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact (make_stn (S n) 0 (natgthsn0 0)).
  Defined.

  Lemma stnmn_to_stn01
    { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ 1 ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact (make_stn (S 0) 0 (natgthsn0 0)).
  Defined.

  Lemma issymm_stnneq
    (A : UU) {n : nat} (i j : ⟦ n ⟧%stn) :
    (i ≠ j) -> (j ≠ i).
  Proof.
    intros i_neq_j.
    destruct i, j.
    apply issymm_natneq.
    assumption.
  Defined.

  Lemma prev_stn
    {n : nat} (i : ⟦ n ⟧%stn) (p : i > 0): ∑ j : ⟦ n ⟧%stn, S j = i.
  Proof.
    pose (m := prev_nat i p).
    destruct m as [m eq].
    use tpair.
    - use tpair. {exact m. } simpl. refine (istransnatlth _ _ _ (natgthsnn m) _ ).
      rewrite eq. apply (pr2 i).
    - exact eq.
  Defined.

  (* General symmetry for decidable equality is tricky to state+prove (requires Hedberg’s theorem); but for non-dependent case-splits, it’s cleaner. *)
  (* Should also be generalisable, but non-unifiedness of definitions of ≠ makes that harder than it should be. *)
  Lemma stn_eq_or_neq_symm_nondep {n} {x y : ⟦n⟧%stn}
        (de_xy : (x = y) ⨿ (x ≠ y)%stn) (de_yx : (y = x) ⨿ (y ≠ x)%stn)
       {Z} (z1 z2 : Z)
    : coprod_rect (fun _ => Z) (fun _ => z1) (fun _ => z2) de_xy
    = coprod_rect (fun _ => Z) (fun _ => z1) (fun _ => z2) de_yx.
  Proof.
    destruct de_xy as [e_xy | ne_xy];
      destruct de_yx as [e_yx | ne_yx];
      simpl;
    (* consistent cases: *)
      try reflexivity;
    (* inconsistent cases: *)
      eapply fromempty, nat_neq_to_nopath; try eassumption;
      apply pathsinv0, maponpaths; assumption.
  Defined.

End PrelStn.

Section Maybe.

  Definition maybe_choice
    {X : UU} (e : maybe X)
  : coprod (e != nothing) (e = nothing).
  Proof.
  destruct e as [? | u].
  - apply ii1. apply negpathsii1ii2.
  - apply ii2. rewrite u. exists.
  Defined.

  Definition maybe_stn_choice
    {X : UU} { n : nat }
    (e : maybe (⟦ n ⟧)%stn)
  : coprod (∑ i : ⟦ n ⟧%stn, e = just i) (e = nothing).
  Proof.
  destruct e as [i | u].
  - apply ii1. use tpair. {exact i. } simpl. reflexivity.
  - apply ii2. rewrite u. exists.
  Defined.

  Definition from_maybe {X : UU} (m : maybe X) (p : m != nothing) : X.
  Proof.
    unfold nothing in p.
     destruct m as [x | u].
     - exact x.
     - contradiction p.
       rewrite u; reflexivity.
  Defined.

End Maybe.

Section Dual.

  Lemma dualelement_2x
    {n : nat} (i : ⟦ n ⟧%stn) : dualelement (dualelement i) = i.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | gt].
    { simpl. apply fromstn0. rewrite <- contr_eq in i. assumption. }
    simpl.
    set (m := n - 1).
    unfold make_stn.
    apply subtypePath_prop.
    simpl.
    rewrite (doubleminuslehpaths m i); try reflexivity.
    unfold m.
    apply minusnleh1.
    apply (pr2 i).
  Defined.

  Lemma dualelement_eq
    {n : nat} (i j : ⟦ n ⟧%stn)
  : dualelement i = j -> i = dualelement j.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0. apply fromstn0. rewrite <- contr_eq in i. assumption. }
    intros H; apply subtypePath_prop; revert H; simpl.
    intros eq; rewrite <- eq; simpl.
    set (m := n - 1).
    rewrite minusminusmmn; try reflexivity.
    apply (natlthsntoleh); unfold m.
    rewrite minussn1non0; try assumption; exact (pr2 i).
  Defined.

  Lemma dualelement_lt_comp
    {n : nat} (i j : ⟦ n ⟧%stn)
  : i < j -> (dualelement i) > (dualelement j).
  Proof.
    intros lt.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    { simpl. apply fromstn0. rewrite contr_eq. assumption.  }
    simpl.
    set (m := (n - 1)).
    apply minusgth0inv.
    rewrite natminusminusassoc.
    rewrite natpluscomm.
    rewrite <- natminusminusassoc.
    rewrite minusminusmmn.
    2: {unfold m. apply (natgthtogehm1 _ _ (pr2 j)). }
    apply (minusgth0 _ _ lt).
  Defined.

  Lemma dualelement_le_comp
    {n : nat} (i j : ⟦ n ⟧%stn)
  : i ≤ j -> (dualelement i) ≥ (dualelement j).
  Proof.
    intros le.
    destruct (natlehchoice i j) as [lt | eq]; try assumption.
    { apply natlthtoleh. apply (dualelement_lt_comp _ _ lt). }
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    { simpl; apply fromstn0. rewrite contr_eq. assumption.  }
    rewrite eq.
    apply isreflnatgeh.
  Defined.

  Lemma dualvalue_eq
    {X : UU} {n : nat} (v : ⟦ n ⟧%stn -> X) (i : ⟦ n ⟧%stn)
  : (v i) = (λ i' : ⟦ n ⟧%stn, v (dualelement i')) (dualelement i).
  Proof.
    simpl; rewrite dualelement_2x; reflexivity.
  Defined.

End Dual.
