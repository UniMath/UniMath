(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Sets.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.NonnegativeReals.

Open Scope Dcuts_scope.

(** ** Definition *)

Definition hr_commrng : commrng := commrigtocommrng NonnegativeReals.

Definition NR_to_hr : NonnegativeReals × NonnegativeReals -> hr_commrng.
Proof.
  intros x.
  assert (Hx : ∀ y : NonnegativeReals × NonnegativeReals, isaprop (pr1 x + pr2 y = pr1 y + pr2 x)).
  { intros y ; apply (pr2 Dcuts_set). }
  exists (λ y, hProppair _ (Hx y)).
  split.
  - apply hinhpr.
    exists x ; simpl.
    reflexivity.
  - split.
    + intros x1 x2 H Heq.
      revert H ; apply hinhuniv ; intros (x0,H) ; simpl in * |- *.
      apply plusNonnegativeReals_eqcompat_l with (pr1 x1 + x0).
      rewrite !isassoc_plusNonnegativeReals, iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x2)).
      change (pr1 x1 + pr2 x2 + x0) with (pr1 x1 + pr2 x2 + x0)%rng.
      rewrite H.
      change (pr1 x2 + pr2 x1 + x0)%rng with (pr1 x2 + pr2 x1 + x0).
      rewrite !isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_r.
      rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
      rewrite Heq.
      rewrite iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals.
      now rewrite (iscomm_plusNonnegativeReals (pr1 x1)).
    + simpl ; intros x1 x2 Heq1 Heq2.
      apply hinhpr.
      change (Σ x0 : NonnegativeReals, (pr1 x1 + pr2 x2 + x0) = (pr1 x2 + pr2 x1 + x0)).
      exists (pr1 x + pr2 x).
      rewrite !isassoc_plusNonnegativeReals, <- (isassoc_plusNonnegativeReals (pr2 x2)), (iscomm_plusNonnegativeReals (pr2 x2)), (iscomm_plusNonnegativeReals _ (pr2 x)), <- (isassoc_plusNonnegativeReals (pr1 x1)).
      simpl ; rewrite <- Heq1, Heq2.
      rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_r.
      rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
      rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_r.
      apply iscomm_plusNonnegativeReals.
Defined.
Definition hr_to_NR ( X : hr_commrng) :
  hexists(λ x : NonnegativeReals × NonnegativeReals, pr1 X x).
Proof.
  intros (X,(Hx,(Hx1,Hx2))) ; simpl.
  apply Hx.
Defined.

Lemma hr_inside_carac :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 X y -> pr1 x + pr2 y = pr1 y + pr2 x.
Proof.
  intros X x y Hx Hy.
  generalize (pr2 (pr2 (pr2 X)) _ _ Hx Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))).
  simpl ; intros (c,H).
  apply (plusNonnegativeReals_eqcompat_l c).
  exact H.
Qed.
Lemma hr_inside_carac' :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x -> pr1 X x -> pr1 X y.
Proof.
  intros X x y Heq Hx.
  apply (pr1 (pr2 (pr2 X)) x y).
  apply hinhpr.
  exists 0 ; simpl.
  change (pr1 x + pr2 y + 0 = pr1 y + pr2 x + 0).
  now rewrite !isrunit_zero_plusNonnegativeReals.
  exact Hx.
Qed.

Definition hr_lt_rel : hrel hr_commrng :=
  λ X Y : hr_commrng, ∃ x y : NonnegativeReals × NonnegativeReals, pr1 X x × pr1 Y y × pr1 x + pr2 y < pr1 y + pr2 x.
Definition hr_le_rel : hrel hr_commrng :=
  λ X Y : hr_commrng, ∃ x y : NonnegativeReals × NonnegativeReals, pr1 X x × pr1 Y y × pr1 x + pr2 y <= pr1 y + pr2 x.
Lemma hr_notlt_le :
  ∀ X Y, ¬ hr_lt_rel X Y -> hr_le_rel Y X.
Proof.
  intros X Y Hlt.
  generalize (hr_to_NR X) (hr_to_NR Y) ;
    apply hinhfun2 ; intros (x,Hx) (y,Hy).
  exists y, x ; repeat split.
  exact Hy.
  exact Hx.
  apply Dcuts_nlt_ge.
  intro H ; apply Hlt.
  apply hinhpr.
  now exists x,y ; repeat split.
Qed.
Lemma isantisymm_hr_le :
  isantisymm hr_le_rel.
Proof.
  intros X Y Hxy Hyx.
  apply subtypeEquality.
  + intros Z.
    now apply isapropiseqclass.
  + apply funextfunax ; simpl ; intro x.
    apply weqtopathshProp, logeqweq.
    * intros Hx.
      revert Hxy Hyx ; apply hinhuniv2 ; intros (x1,(y1,(Hx1,(Hy1,Hxy)))) (y2,(x2,(Hy2,(Hx2,Hyx)))).
      generalize Hy1 ; apply (pr1 (pr2 (pr2 Y)) y1).
      apply hinhpr ; simpl.
      exists 0.
      change (pr1 y1 + pr2 x + 0 = pr1 x + pr2 y1 + 0).
      rewrite !isrunit_zero_plusNonnegativeReals.
      apply isantisym_leNonnegativeReals ; split.
      { apply_pr2 (plusNonnegativeReals_lecompat_l (pr2 y2)).
        rewrite iscomm_plusNonnegativeReals, <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y2)), (hr_inside_carac _ _ _ Hy1 Hy2), <- !(iscomm_plusNonnegativeReals (pr2 y1)), !isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_r.
        apply_pr2 (plusNonnegativeReals_lecompat_l (pr1 x2)).
        rewrite isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)), (hr_inside_carac X _ _ Hx2), isassoc_plusNonnegativeReals, !(iscomm_plusNonnegativeReals (pr1 x)), <- isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_l.
        now rewrite (iscomm_plusNonnegativeReals (pr2 y2)).
        exact Hx. }
      { apply_pr2 (plusNonnegativeReals_lecompat_r (pr2 x1)).
        rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x1)), (λ Hx, hr_inside_carac _ _ _ Hx Hx1), <-isassoc_plusNonnegativeReals, <- !(iscomm_plusNonnegativeReals (pr2 x)), !isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_r.
        now rewrite (iscomm_plusNonnegativeReals (pr2 x1)).
        exact Hx. }
    * intros Hy ; rename x into y.
      revert Hxy Hyx ; apply hinhuniv2 ; intros (x1,(y1,(Hx1,(Hy1,Hxy)))) (y2,(x2,(Hy2,(Hx2,Hyx)))).
      generalize Hx1 ; apply (pr1 (pr2 (pr2 X)) x1).
      apply hinhpr ; simpl.
      exists 0.
      change (pr1 x1 + pr2 y + 0 = pr1 y + pr2 x1 + 0).
      rewrite !isrunit_zero_plusNonnegativeReals.

      apply isantisym_leNonnegativeReals ; split.
      { apply_pr2 (plusNonnegativeReals_lecompat_l (pr1 y1)).
        rewrite isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)), (hr_inside_carac _ _ _ Hy1), isassoc_plusNonnegativeReals, !(iscomm_plusNonnegativeReals (pr1 y)), <- isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_l.
        now rewrite (iscomm_plusNonnegativeReals (pr2 x1)).
        exact Hy. }
      { apply_pr2 (plusNonnegativeReals_lecompat_l (pr2 y2)).
        rewrite iscomm_plusNonnegativeReals, <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y2)), (λ H, hr_inside_carac _ _ _ H Hy2), <- !(iscomm_plusNonnegativeReals (pr2 y)), !isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_r.
        apply_pr2 (plusNonnegativeReals_lecompat_l (pr1 x2)).
        rewrite isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x1)), (hr_inside_carac X _ _ Hx2 Hx1), (iscomm_plusNonnegativeReals (pr1 x1)), <- isassoc_plusNonnegativeReals, iscomm_plusNonnegativeReals, isassoc_plusNonnegativeReals.
        apply plusNonnegativeReals_lecompat_r.
        now rewrite (iscomm_plusNonnegativeReals (pr2 y2)).
        exact Hy. }
Qed.

Lemma isStrongOrder_hr_lt : isStrongOrder hr_lt_rel.
Proof.
  split.
  - intros X Y Z.
    apply hinhuniv2 ; intros (x,(y1,(Hx,(Hy1,Hxy)))) (y2,(z,(Hy2,(Hz,Hyz)))).
    apply hinhpr.
    exists x, z.
    repeat split.
    + exact Hx.
    + exact Hz.
    + apply_pr2 (plusNonnegativeReals_ltcompat_r (pr2 y1)).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y1)).
      eapply istrans_ltNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_l.
      exact Hxy.
      rewrite (iscomm_plusNonnegativeReals (pr1 y1)), isassoc_plusNonnegativeReals, iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_l.
      apply_pr2 (plusNonnegativeReals_ltcompat_r (pr2 y2)).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y2)).
      rewrite (hr_inside_carac _ _ _ Hy1 Hy2).
      rewrite (iscomm_plusNonnegativeReals (pr1 y2)), <- (iscomm_plusNonnegativeReals (pr1 z)), isassoc_plusNonnegativeReals, iscomm_plusNonnegativeReals, <- ! isassoc_plusNonnegativeReals, <- (iscomm_plusNonnegativeReals (pr1 z)).
      now apply plusNonnegativeReals_ltcompat_l.
  - intros X Hlt.
    revert Hlt ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x,(y,(Hx,(Hy)))).
    rewrite (hr_inside_carac _ _ _ Hx Hy).
    apply isirrefl_ltNonnegativeReals.
Qed.
Lemma iscotrans_hr_lt :
  iscotrans hr_lt_rel.
Proof.
  intros X Y Z.
  apply hinhuniv ; intros (x,(z,(Hx,(Hz,Hlt)))).
  generalize (hr_to_NR Y) ;
    apply hinhuniv ; intros (y,Hy).
  apply (plusNonnegativeReals_ltcompat_r (pr2 y)) in Hlt.
  generalize (iscotrans_ltNonnegativeReals _ (pr1 y + pr2 x + pr2 z) _ Hlt).
  clear Hlt ; apply hinhfun ; intros [Hlt | Hlt].
  - left ; apply hinhpr.
    exists x, y ; repeat split.
    exact Hx.
    exact Hy.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 z)).
    rewrite (iscomm_plusNonnegativeReals (pr1 x)), isassoc_plusNonnegativeReals.
    exact Hlt.
  - right ; apply hinhpr.
    exists y, z ; repeat split.
    exact Hy.
    exact Hz.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 x)).
    rewrite isassoc_plusNonnegativeReals, <- (iscomm_plusNonnegativeReals (pr2 x)), (iscomm_plusNonnegativeReals (pr1 z)), isassoc_plusNonnegativeReals, <- isassoc_plusNonnegativeReals.
    exact Hlt.
Qed.

Definition hr_ap_rel : hrel hr_commrng :=
  λ X Y : hr_commrng, ∥ Σ x y : NonnegativeReals × NonnegativeReals, pr1 X x × pr1 Y y × pr1 x + pr2 y ≠ pr1 y + pr2 x ∥.
Lemma hr_ap_lt :
  ∀ X Y : hr_commrng, hr_ap_rel X Y <-> hr_lt_rel X Y ∨ hr_lt_rel Y X.
Proof.
  intros X Y ; split.
  - apply hinhuniv ; intros (x,(y,(Hx,(Hy,Hap)))).
    apply_pr2_in ap_ltNonnegativeReals Hap.
    revert Hap ; apply hinhfun ; intros [Hlt | Hlt].
    + left ; apply hinhpr.
      now exists x, y ; repeat split.
    + right ; apply hinhpr.
      now exists y, x ; repeat split.
  - apply hinhuniv ; intros [|] ; apply hinhfun ; intros (x,(y,(Hx,(Hy,Hlt)))).
    + exists x, y ; repeat split.
      exact Hx.
      exact Hy.
      apply ap_ltNonnegativeReals.
      now apply hinhpr ; left.
    + exists y, x ; repeat split.
      exact Hy.
      exact Hx.
      apply ap_ltNonnegativeReals.
      now apply hinhpr ; right.
Qed.

Lemma istightap_hr_ap : istightap hr_ap_rel.
Proof.
  repeat split.
  - intros X.
    unfold neg.
    apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x,(y,(Hx,(Hy)))).
    rewrite (hr_inside_carac _ _ _ Hx Hy).
    now apply isirrefl_apNonnegativeReals.
  - intros X Y.
    apply hinhfun ; intros (x,(y,(Hx,(Hy,Hap)))).
    exists y, x ; repeat split.
    exact Hy.
    exact Hx.
    apply issymm_apNonnegativeReals.
    now apply Hap.
  - intros X Y Z Hap.
    apply hr_ap_lt in Hap.
    revert Hap ; apply hinhuniv ; intros [Hlt|Hlt].
    + apply (iscotrans_hr_lt X Y Z) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * left ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; left.
      * right ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; left.
    + apply (iscotrans_hr_lt _ Y _) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * right ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; right.
      * left ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; right.
  - intros X Y Hap.
    apply isantisymm_hr_le.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now apply hinhpr ; right.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now apply hinhpr ; left.
Qed.

Definition hr_zero : hr_commrng := 0%rng.
Definition hr_one : hr_commrng := 1%rng.
Definition hr_plus : binop hr_commrng := λ x y, (x + y)%rng.
Definition hr_mult : binop hr_commrng := λ x y, (x * y)%rng.

Lemma hr_plus_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (hr_plus X Y) z
    <-> ∃ x y : NonnegativeReals × NonnegativeReals, pr1 X x × pr1 Y y × pr1 z = pr1 x + pr1 y × pr2 z = pr2 x + pr2 y.
Proof.
  intros X Y ; split.
  - intro Hz.
    unfold hr_plus, BinaryOperations.op1 in Hz ;
      simpl in Hz.
    unfold rigtorngop1 in Hz ; simpl in Hz.
    Opaque iscompbinoptransrel.
    set (H := (iscompbinoptransrel
                (X := setwithbinopdirprod _ _)
                (hrelabgrfrac (rigaddabmonoid NonnegativeReals))
                (eqreltrans
                   (eqrelabgrfrac (rigaddabmonoid NonnegativeReals)))
                (isbinophrelabgrfrac (rigaddabmonoid NonnegativeReals)))).
    change  (iscompbinoptransrel
                (X := setwithbinopdirprod _ _)
                (hrelabgrfrac (rigaddabmonoid NonnegativeReals))
                (eqreltrans
                   (eqrelabgrfrac (rigaddabmonoid NonnegativeReals)))
                (isbinophrelabgrfrac (rigaddabmonoid NonnegativeReals))) with H in Hz.
    clearbody H ; clear -Hz.
    unfold eqrelabgrfrac in Hz ; simpl in Hz.
    Opaque iseqrelabgrfrac.
    set (H0 := (iseqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
    change (iseqrelabgrfrac (rigaddabmonoid NonnegativeReals)) with H0 in Hz.
    clearbody H0 ; clear -Hz.
    unfold Sets.setquotfun2 in Hz ; simpl in Hz.
    Opaque iscompsetquotpr.
    set (H1 := λ x x' x0 x0' r r0, iscompsetquotpr (eqrelpair _ H0) _ _ (H x x' x0 x0' r r0)).
    change (λ x x' x0 x0' r r0, iscompsetquotpr (eqrelpair _ H0) _ _ (H x x' x0 x0' r r0))
    with H1 in Hz.
    clearbody H1 ; clear -Hz ; simpl in H1.
    unfold Sets.setquotuniv2 in Hz.
    (context Hz [Sets.setquotfun2 _ _ _ ?is _ _]).
Qed.

Lemma islapbinop_plus : islapbinop (X := _,,_,,istightap_hr_ap) hr_plus.
Proof.
  intros X Y Z.
  apply hinhuniv ; intros (x,(y,(Hx,(Hy,Hap)))).

  destruct Hx.
  simpl in Hx, Hy.
Qed.

Definition hr_ConstructiveField : ConstructiveField.
Proof.
  exists hr_commrng.
  exists (_,,istightap_hr_ap).
  repeat split.
Defined.