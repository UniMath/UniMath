Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Combinatorics.KFiniteTypes.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Open Scope stn.

Definition removeterm {X : UU} (y : X) : X → UU := λ x, x != y.

Lemma isPredicateremoveterm {X : UU} (y : X) : isPredicate (removeterm y).
Proof.
  intros x. apply isapropneg.
Qed.

Lemma removetermequiv {X : UU} (y : X) : isdeceq X → (∑ (x : X), ¬ (x = y)) ⨿ unit ≃ X.
Proof.
  intros deceqx.
  use weq_iso.
  - intros [[x neq] | tt]; [apply x | apply y].
  - intros x. induction (deceqx x y); [right; apply tt | left].
    apply tpair with (pr1 := x), b. 
  - intros [[x neq] | tt].
    + induction (deceqx x y).
      * apply fromempty, neq, a.
      * simpl. apply maponpaths, subtypePath; 
        [apply isPredicateremoveterm | apply idpath].
    + induction (deceqx y y).
      * induction tt. apply idpath.
      * apply fromempty, b, idpath.
  - intros x; cbn beta.
    induction (deceqx x y); simpl;
    try induction a; apply idpath.
Qed.

Definition snton {X : UU} {n : nat} (f : stn (S n) → X) : stn n → X.
Proof.
    intros [m lem].
    apply f. apply (make_stn _  m). apply natlthtolths, lem.
Defined.

Definition helper_fun {X : UU} {n : nat} (f : stn (S n) → X) : 
      ¬ hfiber (snton f) (f lastelement) → stn n → 
      (∑ (x : X), ¬ (x = (f lastelement))).
Proof.
    intros.
    exists (snton f X1).
    intros contra. apply X0.
    eexists. apply contra.
Defined.

Lemma issurjective_helper_fun {X : UU} {n : nat} (f : stn (S n) → X) 
      (nfib : ¬ hfiber (snton f) (f lastelement)) : issurjective f → 
      issurjective (helper_fun f nfib).
Proof.
    intros surjf y.
    destruct y as [x neq].
    use squash_to_prop.
    - exact (hfiber f x).
    - exact (surjf x).
    - apply propproperty.
    - intros [[m lth] q]; clear surjf. apply hinhpr.
      induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
      + apply (tpair _ (m ,, a)).
        unfold helper_fun, snton, make_stn.
        apply subtypePath; try (apply isPredicateremoveterm); simpl.
        induction q. apply maponpaths, stn_eq, idpath. 
      + assert (m ,, lth = lastelement) by apply stn_eq, b.
        apply fromempty, neq. induction X0. apply pathsinv0, q.
Qed.

Lemma isdeceq_total2' {X : UU} (P : X → UU) : 
  isdeceq X → isPredicate P → isdeceq (∑ x : X, P x).
Proof.
  intros deceqX predP. apply isdeceq_total2.
  + apply deceqX.
  + intros x. apply isdeceqifisaprop, predP.
Qed. 

Lemma surjfromstn0toneg {X : UU} (f : ⟦ 0 ⟧ → X ) : (issurjective f) → ⟦ 0 ⟧ ≃ X.
Proof.
  intros surj. apply tpair with (pr1 := f). intros x.
  apply fromempty, (squash_to_prop (surj x) (isapropempty)).
  intros [contra eq]; clear surj.
  apply negstn0, contra.
Qed.

Lemma isdeceq_isdecsurj {X : UU} {n : nat} (f : ⟦ n ⟧ → X ) (y : X) : 
    isdeceq X → decidable (hfiber f y).
Proof.
  generalize dependent X.
  induction n; intros X f x deceqX.
  - right. intros [contra eq]. apply weqstn0toempty, contra.
  - set (g := snton f). specialize IHn with (f := g) (y := x).
    set (H := IHn deceqX).
    induction H.
    + left. destruct a as [[m lth] eq].
      apply tpair with (pr1 := (m ,, (natlthtolths _ _ lth))), eq.
    + induction (deceqX (f (lastelement)) x); [left | right].
      * apply (tpair _ lastelement). assumption.
      * intros [[m lth] eq].
        induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
        -- apply b. apply tpair with (pr1 := (m ,, a)).
           induction eq. unfold g, snton, make_stn.
           apply maponpaths, stn_eq, idpath.
        -- apply b0. unfold lastelement. induction b1, eq.
           apply maponpaths, stn_eq, idpath.
Qed.

Lemma surjstnon {X : UU} {n : nat} (f : ⟦ S n ⟧ → X) : isdeceq X → issurjective f → 
      hfiber (snton f) (f lastelement) → issurjective (snton f).
Proof.
  intros deceqX surj [x eq].
  intros y'.
  induction (deceqX (f lastelement) y').
  - induction a. apply hinhpr, tpair with (pr1 := x), eq.
  - apply (squash_to_prop (surj y')); try apply propproperty.
    intros [[m lth] eq']. apply hinhpr.
    induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
    + apply tpair with (pr1 := m ,, a).
      unfold snton, make_stn.
      induction eq'. apply maponpaths, stn_eq, idpath.
    + induction eq', b0. apply fromempty, b. unfold lastelement. 
      apply maponpaths, stn_eq, idpath.
Qed.

Lemma kfinstruct_dec_finstruct {X : UU} : kfinstruct X → isdeceq X → finstruct X.
Proof.
    intros [n [f surj]] deceqX.
    generalize dependent X.
    induction n; intros.
    - apply tpair with (pr1 := 0).
      apply surjfromstn0toneg with (f := f). assumption. 
    - set (g := snton f).
      set (y := f lastelement).
      induction (isdeceq_isdecsurj g y deceqX).
      + apply IHn with (f := g); try apply surjstnon; assumption.
      + set (g' := helper_fun f b).
        set (surjg' := (issurjective_helper_fun f b surj)).
        specialize IHn with (f := g').
        apply IHn in surjg'; 
        [ | apply isdeceq_total2'; try assumption; intros x; apply isapropneg ].
        destruct surjg' as [s1 s2].
        apply tpair with (pr1 := (S s1)); unfold nelstruct.
        eapply weqcomp. 
        * apply invweq, weqdnicoprod, lastelement.
        * eapply weqcomp. 
          { eapply weqcoprodf1, s2. }
          apply removetermequiv; assumption.
Qed.

Lemma iskfinitedectoisfinite {X : UU} : iskfinite X → isdeceq X → isfinite X.
Proof.
    intros iskfin deceq.
    use squash_to_prop.
    - exact (kfinstruct X).
    - exact iskfin.
    - apply propproperty.
    - intros; clear iskfin; apply hinhpr.
      apply kfinstruct_dec_finstruct; assumption.
Qed.