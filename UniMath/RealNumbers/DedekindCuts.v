(** * Usual constructive Dedekind cuts *)
(** Catherine LELAY. July 2017 *)
(** This file formalizes the usual definitions of constructive Dedekind cuts.
- The two-sided definition come from the HoTT-book
- The one-sided definition come from Robert S Lubarsky and Michael Rathjen. On the constructive
Dedekind reals. Logic and Analysis.

I first prove the equivalence between these two definitions, then I prove the equivalence between
the non-negative numbers of the one-sided definition and the set Dcuts *)

Require Export UniMath.NumberSystems.RationalNumbers.
Require Import UniMath.RealNumbers.Prelim.
Require Import UniMath.RealNumbers.NonnegativeRationals.
Require Import UniMath.RealNumbers.NonnegativeReals.

Unset Kernel Term Sharing.

(** ** Usual definitions *)

Open Scope hq_scope.

Definition is2sided (L U : hq → hProp) : UU :=
  ((∏ q : hq, L q <-> ∃ r : hq, L r ∧ hqlth q r)
     × (∏ q : hq, U q <-> ∃ r : hq, U r ∧ hqlth r q))
    × ((∃ q : hq, L q) × (∃ q : hq, U q))
    × (∏ q : hq, ¬ (U q ∧ L q))
    × (∏ q r : hq, hqlth q r → L q ∨ U r).

Definition is1sided (S : hq → hProp) : UU :=
  ((∃ r : hq, S r) ∧ (∃ r : hq, ¬ S r))
    × (∏ r : hq, S r → ∃ q : hq, S q ∧ hqlth r q)
    × (∏ r s : hq, hqlth r s → S r ∨ ¬ S s).

(** ** Equivalence between these two definitions *)

Lemma is2sided_1sided :
  ∏ (L U : hq → hProp), is2sided L U → is1sided L.
Proof.
  intros L U H.
  split ; split.
  - exact (pr1 (pr1 (pr2 H))).
  - generalize (pr1 (pr2 (pr2 H))) (pr2 (pr1 (pr2 H))) ; intros H0.
    apply hinhfun.
    intros q.
    exists (pr1 q).
    intros Lq.
    apply (H0 (pr1 q)).
    split.
    + exact (pr2 q).
    + exact Lq.
  - intros r Lr.
    generalize (pr1 (pr1 H)) ; intros H0.
    exact (pr1 (H0 r) Lr).
  - intros r s Hrs.
    generalize (pr1 (pr2 (pr2 H))) (pr2 (pr2 (pr2 H))) ; intros H0 H1.
    generalize (H1 _ _ Hrs).
    apply hinhfun, sumofmaps.
    + exact ii1.
    + intros Us.
      apply ii2.
      intros Ls.
      apply (H0 s).
      split.
      exact Us.
      exact Ls.
Qed.

Lemma is1sided_2sided :
  ∏ (S : hq → hProp),
  is1sided S → is2sided S (λ s : hq, ∃ r : hq, hqlth r s × ¬ S r).
Proof.
  intros S H.
  split ; split ; [ | | split | split].
  - intros q ; split.
    + exact (pr1 (pr2 H) q).
    + apply hinhuniv ; intros r.
      generalize (pr2 (pr2 H) _ _ (pr2 (pr2 r))).
      apply hinhuniv, sumofmaps.
      intros Sq ; apply Sq.
      intros Sr.
      apply fromempty.
      apply Sr, (pr1 (pr2 r)).
  - intros q ; split.
    + apply hinhfun.
      intros r.
      set (s := Prelim.hqlth_between _ _ (pr1 (pr2 r))).
      exists (pr1 s).
      split.
      * apply hinhpr.
        exists (pr1 r).
        { split.
          - exact (pr1 (pr2 s)).
          - exact (pr2 (pr2 r)).
        }
      * exact (pr2 (pr2 s)).
    + apply hinhuniv.
      intros r.
      generalize (pr1 (pr2 r)).
      apply hinhfun.
      intros s.
      exists (pr1 s).
      split.
      * apply istranshqlth with (pr1 r).
        exact (pr1 (pr2 s)).
        exact (pr2 (pr2 r)).
      * exact (pr2 (pr2 s)).
  - exact (pr1 (pr1 H)).
  - generalize (pr2 (pr1 H)).
    apply hinhfun.
    intros r.
    exists (pr1 r+1).
    apply hinhpr.
    exists (pr1 r).
    split.
    + exact (hqlthnsn _).
    + exact (pr2 r).
  - intros q Hq.
    generalize (pr1 Hq).
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros r.
    generalize (pr2 (pr2 H) _ _ (pr1 (pr2 r))).
    apply hinhuniv, sumofmaps.
    + exact (pr2 (pr2 r)).
    + intros Sq ; apply Sq.
      exact (pr2 Hq).
  - intros q r Hqr.
    set (s := Prelim.hqlth_between _ _ Hqr).
    generalize (pr2 (pr2 H) _ _ (pr1 (pr2 s))).
    apply hinhfun, sumofmaps.
    + exact ii1.
    + intros Sr.
      apply ii2, hinhpr.
      exists (pr1 s).
      split.
      * exact (pr2 (pr2 s)).
      * exact Sr.
Qed.

Lemma weq2sided1sided :
  weq (∑ L U : hq → hProp, is2sided L U) (∑ S : hq → hProp, is1sided S).
Proof.
  set (f := (λ (LU : ∑ L U : hq → hProp, is2sided L U),
            pr1 LU,, is2sided_1sided (pr1 LU) (pr1 (pr2 LU)) (pr2 (pr2 LU)))
            : (∑ L U : hq → hProp, is2sided L U) → ∑ S, is1sided S).
  set (g := (λ S : (∑ S : hq → hProp, is1sided S),
                   pr1 S ,, (λ s : hq, ∃ r : hq, r < s × ¬ pr1 S r)
                       ,, is1sided_2sided (pr1 S) (pr2 S))
            : (∑ S, is1sided S) → ∑ L U : hq → hProp, is2sided L U).
  apply (weqgradth f g).
  - intros LU.
    rewrite (tppr (g (f LU))).
    eapply pathscomp0, pathsinv0, (tppr LU).
    apply pair_path_in2.
    simple refine (subtypeEquality_prop (B := λ _, hProppair _ _) _).
    +  apply isapropdirprod.
       apply isapropdirprod ;
         apply impred_isaprop ; intro q ;
         apply isapropdirprod ; apply isapropimpl, propproperty.
       apply isapropdirprod.
       apply isapropdirprod ; apply propproperty.
       apply isapropdirprod.
       apply impred_isaprop ; intro q.
       apply isapropneg.
       apply impred_isaprop ; intro q.
       apply impred_isaprop ; intro r.
       apply isapropimpl, propproperty.
    + apply funextfun ; intros q.
      apply hPropUnivalence.
      * apply hinhuniv.
        intros r.
        generalize (pr2 (pr2 (pr2 (pr2 (pr2 LU)))) _ _ (pr1 (pr2 r))).
        apply hinhuniv, sumofmaps.
        intro Lr ; apply fromempty, (pr2 (pr2 r)), Lr.
        intros Uq ; apply Uq.
      * intros Uq.
        generalize (pr1 (pr2 (pr1 (pr2 (pr2 LU))) _) Uq).
        apply hinhfun.
        intros r.
        exists (pr1 r).
        split.
        apply (pr2 (pr2 r)).
        intros Lr.
        apply (pr1 (pr2 (pr2 (pr2 (pr2 LU)))) (pr1 r)).
        split.
        apply (pr1 (pr2 r)).
        apply Lr.
  - intros S.
    simple refine (subtypeEquality_prop (B := λ _, hProppair _ _) _).
    + apply isapropdirprod.
      apply propproperty.
      apply isapropdirprod.
      apply impred_isaprop ; intro r.
      apply isapropimpl, propproperty.
      apply impred_isaprop ; intro r.
      apply impred_isaprop ; intro s.
      apply isapropimpl, propproperty.
    + reflexivity.
Qed.

(** ** Equivalence of Dcuts with usual definitions *)

Lemma is1sided_Dcuts_bot :
  ∏ D, is1sided D → Dcuts_def_bot (λ r, D (pr1 r)).
Proof.
  intros D H r Dr q Hq.
  generalize (le_eqorltNonnegativeRationals _ _ Hq) ; clear Hq.
  apply sumofmaps ; intros H0.
  - rewrite H0.
    exact Dr.
  - rewrite ltNonnegativeRationals_correct in H0.
    generalize (pr2 (pr2 H) _ _ H0).
    apply hinhuniv, sumofmaps ; intros Dq.
    + exact Dq.
    + apply fromempty, Dq, Dr.
Qed.
Lemma is1sided_Dcuts_open :
  ∏ D, is1sided D → Dcuts_def_open (λ r, D (pr1 r)).
Proof.
  intros D H r Dr.
  generalize ((pr1 (pr2 H)) (pr1 r) Dr).
  apply hinhfun.
  intros q.
  assert (Hq : 0 <= pr1 q).
  { apply istranshqleh with (pr1 r).
    exact (pr2 r).
    apply hqlthtoleh, (pr2 (pr2 q)). }
  exists (pr1 q,,Hq).
  split.
  - change (D (NonnegativeRationals_to_Rationals
                 (pr1 q,,Hq))).
    exact (pr1 (pr2 q)).
  - rewrite ltNonnegativeRationals_correct.
    change (pr1 r < (NonnegativeRationals_to_Rationals (pr1 q,,Hq))).
    exact (pr2 (pr2 q)).
Qed.

Lemma is1sided_translation :
  ∏ (D : hq → hProp) (c : hq),
  is1sided D → is1sided (λ q, D (q + c)).
Proof.
  intros D c Hd.
  split ; split.
  - generalize (pr1 (pr1 Hd)).
    apply hinhfun.
    intros r.
    exists (pr1 r - c).
    unfold hqminus.
    rewrite hqplusassoc, hqlminus, hqplusr0.
    exact (pr2 r).
  - generalize (pr2 (pr1 Hd)).
    apply hinhfun.
    intros r.
    exists (pr1 r - c).
    unfold hqminus.
    rewrite hqplusassoc, hqlminus, hqplusr0.
    exact (pr2 r).
  - intros r D'r.
    generalize (pr1 (pr2 Hd) _ D'r).
    apply hinhfun.
    intros q.
    exists (pr1 q - c).
    split.
    + unfold hqminus.
      rewrite hqplusassoc, hqlminus, hqplusr0.
      exact (pr1 (pr2 q)).
    + apply hqlthandplusrinv with c.
      unfold hqminus.
      rewrite hqplusassoc, hqlminus, hqplusr0.
      exact (pr2 (pr2 q)).
  - intros r s Hrs.
    apply (pr2 (pr2 Hd)).
    apply hqlthandplusr, Hrs.
Qed.
Lemma is1sided_Dcuts_corr :
  ∏ D, is1sided D → Dcuts_def_corr (λ r, D (pr1 r)).
Proof.
  intros D H c Hc.
  rewrite ltNonnegativeRationals_correct in Hc.
  generalize (pr2 (pr2 H) _ _ Hc).
  apply hinhuniv ; intros H0.
  apply coprodcomm in H0.
  revert H0 ; apply sumofmaps ; intros H0.
  apply hinhpr, ii1, H0.
  enough (Hq : ∃ q : NonnegativeRationals, D (pr1 q) × ¬ D (pr1 (q + c)%NRat)).
  { revert Hq.
    apply hinhfun, ii2. }

  generalize (pr2 (pr1 H)).
  apply hinhuniv.
  intros r.
  generalize (isarchhq (hqdiv (pr1 r) (hqdiv (pr1 c) 2%hq))).
  apply hinhuniv.
  intros n.
  assert (Hc' : hqdiv (pr1 c) 2 > 0).
  { apply hqmultgth0gth0.
    exact Hc.
    apply hqgthandmultlinv with 2.
    exact hq2_gt0.
    rewrite hqmultx0, hqisrinvmultinv.
    exact hq1_gt0.
    apply hqgth_hqneq, hq2_gt0. }
  assert (H1 : hqlth (pr1 r) (nattorng (pr1 n) * (hqdiv (pr1 c) 2))).
  { unfold hqlth in Hc.
    apply hqgthandmultrinv with (/ (hqdiv (pr1 c) 2)).
    - apply hqgthandmultlinv with (hqdiv (pr1 c) 2).
      + exact Hc'.
      + rewrite hqmultx0, hqisrinvmultinv.
        exact hq1_gt0.
        apply hqgth_hqneq, Hc'.
    - rewrite hqmultassoc, hqisrinvmultinv.
      rewrite hqmultr1.
      unfold hqdiv in n.
      exact (pr2 n).
      apply hqgth_hqneq, Hc'. }
  assert (Hn : ¬ D (nattorng (pr1 n) * hqdiv (pr1 c) 2)).
  { generalize (pr2 (pr2 H) _ _ H1).
    apply (hinhuniv (P := hneg _)), sumofmaps ; intro H2.
    apply fromempty, (pr2 r), H2.
    apply H2. }
  assert (H2 : ∏ (m : nat),
               nattorng m * hqdiv (pr1 c) 2 + pr1 c = nattorng (m + 2) * hqdiv (pr1 c) 2).
  { intros m.
    unfold nattorng.
    rewrite 2!(@nattorig_natmult hq).
    rewrite natmult_plus.
    apply maponpaths.
    simpl.
    unfold hqdiv.
    rewrite <- hqmult2r, hqmultassoc.
    rewrite hqislinvmultinv.
    apply pathsinv0, hqmultr1.
    apply hqgth_hqneq, hq2_gt0. }

  generalize (pr1 n) Hn.
  clear -H H0 Hc Hc' H2 ; intros n Hn.
  assert (Hm : D (nattorng O * hqdiv (pr1 c) 2)).
  { rewrite hqmult0x.
    exact H0. }
  destruct n.
  { apply fromempty, Hn, Hm. }
  rewrite <- (natplusl0 n), plus_n_Sm in Hn.
  revert Hm Hn.
  set (m := O).
  change (D (nattorng m * hqdiv (pr1 c) 2)
  → ¬ D (nattorng (m + S n) * hqdiv (pr1 c) 2)
    → ∃ q : NonnegativeRationals, D (pr1 q) × ¬ D (pr1 (q + c)%NRat)).
  generalize m ; clear m H0.
  revert D H.
  induction n as [ | n IHn] ; intros D H m Hm Hn.
  - apply hinhpr.
    mkpair.
    mkpair.
    apply (nattorng m * hqdiv (pr1 c) 2).
    abstract (apply hq0lehandmult ;
              [ clear ;
                induction m ;
                [ apply isreflhqleh
                | unfold nattorng ;
                  rewrite nattorigS ;
                  apply hq0lehandplus ;
                  [ exact hq1ge0 | exact IHm ]]
              | apply hqlthtoleh, Hc' ]).
    simpl.
    split.
    exact Hm.
    change (¬ D ((nattorng m * hqdiv (pr1 c) 2) + (pr1 c))).
    intros H0.
    refine (hinhuniv' _ _ _).
    apply isapropempty.
    2: apply (pr2 (pr2 H) (nattorng (m + 1) * hqdiv (pr1 c) 2) (nattorng m * hqdiv (pr1 c) 2 + pr1 c)).
    apply sumofmaps.
    exact Hn.
    intros H1 ; apply H1, H0.
    rewrite H2.
    apply hqlthandmultr.
    exact Hc'.
    unfold nattorng.
    rewrite <- (plus_n_Sm m 1%nat).
    rewrite nattorigS, hqpluscomm.
    apply hqlthnsn.
  - refine (hinhuniv _ _).
    2: apply (pr2 (pr2 H) (nattorng (m + 1) * hqdiv (pr1 c) 2) (nattorng (m + 2) * hqdiv (pr1 c) 2)).
    apply sumofmaps ; intros Hm'.
    + apply IHn with (m + 1)%nat.
      * exact H.
      * exact Hm'.
      * rewrite natplusassoc.
        exact Hn.
    + apply hinhpr.
      mkpair.
      mkpair.
      apply (nattorng m * hqdiv (pr1 c) 2).
      abstract (apply hq0lehandmult ;
                [ clear ;
                  induction m ;
                  [ apply isreflhqleh
                  | unfold nattorng ;
                    rewrite nattorigS ;
                    apply hq0lehandplus ;
                    [ exact hq1ge0 | exact IHm ]]
                | apply hqlthtoleh, Hc' ]).
      simpl.
      split.
      exact Hm.
      change (¬ D ((nattorng m * hqdiv (pr1 c) 2) + (pr1 c))).
      rewrite H2.
      exact Hm'.
    + apply hqlthandmultr.
      exact Hc'.
      unfold nattorng.
      rewrite <- (plus_n_Sm m 1%nat).
      rewrite nattorigS, hqpluscomm.
      apply hqlthnsn.
Qed.

Lemma isDcuts_1sided :
  ∏ (D : NonnegativeRationals → hProp),
  Dcuts_def_bot D → Dcuts_def_open D → Dcuts_def_corr D
  → is1sided (λ q : hq, sumofmaps (λ _ : 0 > q, htrue) (λ Hq : 0 <= q, D (q,, Hq)) (hqgthorleh 0 q)).
Proof.
  intros D Hbot Hopen Hcorr.
  split ; split.
  - apply hinhpr.
    exists (-(1)).
    induction (hqgthorleh 0 (- (1))) as [H | H].
    + exact tt.
    + apply fromempty.
      refine (hqlehtoneghqgth _ _ _ _).
      apply H.
      apply hqgthandplusrinv with 1.
      rewrite hqlminus, hqplusl0.
      exact hq1_gt0.
  - generalize (Hcorr _ ispositive_oneNonnegativeRationals).
    apply hinhfun, sumofmaps ; intros H.
    + exists 1.
      induction (hqgthorleh 0 1) as [H0 | H0].
      * apply fromempty.
        refine (hqgthtoneghqleh _ _ _ _).
        exact H0.
        exact hq1ge0.
      * assert (H1 : 1%NRat = (1 ,, H0))
          by (apply subtypeEquality_prop ; reflexivity).
        rewrite H1 in H.
        exact H.
    + rename H into q.
      exists (pr1 (pr1 q) + 1).
      induction (hqgthorleh 0 (pr1 (pr1 q) + 1)) as [H0 | H0].
      * apply fromempty.
        refine (hqgthtoneghqleh _ _ _ _).
        apply H0.
        apply hq0lehandplus.
        exact (pr2 (pr1 q)).
        exact hq1ge0.
      * assert (Hq1 : (pr1 q + 1)%NRat = (pr1 (pr1 q) + 1 ,, H0))
          by (apply subtypeEquality_prop ; reflexivity).
        generalize (pr2 (pr2 q)) ; intro Hq.
        rewrite Hq1 in Hq.
        exact Hq.
  - intros r Dr.
    induction (hqgthorleh 0 r) as [Hr | Hr].
    + set (q := hqlth_between _ _ Hr).
      apply hinhpr.
      exists (pr1 q).
      split.
      induction (hqgthorleh 0 (pr1 q)) as [Hq | Hq].
      * exact tt.
      * apply fromempty.
        refine (hqlehtoneghqgth _ _ _ _).
        exact Hq.
        unfold hqlth in q.
        exact (pr2 (pr2 q)).
      * exact (pr1 (pr2 q)).
    + generalize (Hopen _ Dr).
      apply hinhfun.
      intros q.
      exists (pr1 (pr1 q)).
      induction (hqgthorleh 0 (pr1 (pr1 q))) as [Hq | Hq].
      * apply fromempty.
        refine (hqgthtoneghqleh _ _ _ _).
        apply Hq.
        exact (pr2 (pr1 q)).
      * split.
        assert (Hq1 : pr1 q = (pr1 (pr1 q) ,, Hq))
          by (apply subtypeEquality_prop ; reflexivity).
        generalize (pr1 (pr2 q)) ; intro Hq'.
        rewrite Hq1 in Hq'.
        exact Hq'.
        generalize (pr2 (pr2 q)) ; intro Hq'.
        rewrite ltNonnegativeRationals_correct in Hq'.
        exact Hq'.
  -intros r q Hrq.
    induction (hqgthorleh 0 r) as [Hr | Hr].
    apply hinhpr, ii1, tt.
    induction (hqgthorleh 0 q) as [Hq | Hq].
    + apply fromempty.
      refine (hqlehtoneghqgth _ _ _ _).
      apply Hr.
      apply istranshqgth with q.
      exact Hq.
      unfold hqlth in Hrq.
      exact Hrq.
    + apply (Dcuts_locatedness (D,,Hbot,,Hopen,,Hcorr)).
      rewrite ltNonnegativeRationals_correct.
      exact Hrq.
Qed.

Lemma weq1sidedDcuts :
  weq (∑ S : hq → hProp, is1sided S × ∏ q : hq, q < 0 → S q) Dcuts.
Proof.
  set (f := (λ (D : ∑ S : hq → hProp, is1sided S × (∏ q : hq, q < 0 → S q)),
             mk_Dcuts (λ r : NonnegativeRationals, pr1 D (pr1 r))
                     (is1sided_Dcuts_bot (pr1 D) (pr1 (pr2 D)))
                     (is1sided_Dcuts_open (pr1 D) (pr1 (pr2 D)))
                     (is1sided_Dcuts_corr (pr1 D) (pr1 (pr2 D))))
            : (∑ S : hq → hProp, is1sided S × (∏ q : hq, q < 0 → S q)) → Dcuts).
  assert (Hg : ∏ (D : Dcuts) (q : hq),
               q < 0
               → sumofmaps (λ _ : 0 > q, htrue) (λ Hq : 0 <= q, pr1 D (q,, Hq)) (hqgthorleh 0 q)).
  { intros D q Hq.
    induction (hqgthorleh 0 q) as [Hq' | Hq'].
    exact tt.
    apply fromempty.
    refine (hqlehtoneghqgth _ _ _ _).
    apply Hq'.
    unfold hqlth in Hq.
    exact Hq. }
set (g := (λ D : Dcuts,
    (λ q : hq,
     sumofmaps (λ _ : 0 > q, htrue) (λ Hq : 0 <= q, pr1 D (q,, Hq))
       (hqgthorleh 0 q)),,
    isDcuts_1sided (pr1 D) (is_Dcuts_bot D) (is_Dcuts_open D)
    (is_Dcuts_corr D),, Hg D)
          : Dcuts → ∑ S : hq → hProp, is1sided S × (∏ q : hq, q < 0 → S q)).
  apply (weqgradth f g).
  - intros D.
    simple refine (subtypeEquality_prop (B := λ _, hProppair _ _) _).
    + apply isapropdirprod.
      apply isapropdirprod.
      apply propproperty.
      apply isapropdirprod.
      apply impred_isaprop ; intro r.
      apply isapropimpl, propproperty.
      apply impred_isaprop ; intro r.
      apply impred_isaprop ; intro s.
      apply isapropimpl, propproperty.
      apply impred_isaprop ; intro q.
      apply isapropimpl, propproperty.
    + apply funextfun ; intros q.
      apply hPropUnivalence.
      * change (sumofmaps (λ _ : 0 > q, htrue) (λ _ : ¬ (0 > q), pr1 D q) (hqgthorleh 0 q) → pr1 D q).
        induction (hqgthorleh 0 q) as [Hq | Hq].
        intros _.
        apply (pr2 (pr2 D)).
        exact Hq.
        intros H ; apply H.
      * change (pr1 D q → sumofmaps (λ _ : 0 > q, htrue) (λ _ : ¬ (0 > q), pr1 D q) (hqgthorleh 0 q)).
        intros Dq.
        induction (hqgthorleh 0 q) as [Hq | Hq].
        exact tt.
        exact Dq.
  - intros D.
    apply subtypeEquality_prop.
    apply funextfun ; intros q.
    apply hPropUnivalence.
    + change (sumofmaps (λ _ : 0 > pr1 q, htrue)
                        (λ Hq : ¬ (0 > pr1 q), pr1 D (pr1 q,, Hq)) (hqgthorleh 0 (pr1 q))
              → pr1 D q).
      induction (hqgthorleh 0 (pr1 q)) as [Hq | Hq].
      apply fromempty.
      refine (hqlehtoneghqgth _ _ _ _).
      exact (pr2 q).
      exact Hq.
      intros H.
      assert (Hq1 : q = (pr1 q,, Hq))
        by (apply subtypeEquality_prop ; reflexivity).
      rewrite Hq1 ; exact H.
    + change (pr1 D q
  → sumofmaps (λ _ : 0 > pr1 q, htrue)
              (λ Hq : ¬ (0 > pr1 q), pr1 D (pr1 q,, Hq)) (hqgthorleh 0 (pr1 q))).
      intros Dq.
      induction (hqgthorleh 0 (pr1 q)) as [Hq | Hq].
      apply fromempty.
      refine (hqlehtoneghqgth _ _ _ _).
      exact (pr2 q).
      exact Hq.
      assert (Hq1 : q = (pr1 q,, Hq))
        by (apply subtypeEquality_prop ; reflexivity).
      rewrite Hq1 in Dq ; exact Dq.
Qed.
