Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.KFiniteTypes.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Open Scope stn.

Lemma helper1 {X : UU} (y : X) : isdeceq X → (∑ (x : X), ¬ (x = y)) ⨿ unit ≃ X.
Proof.
    intros deceqX.
    assert (∏ (x1 x2 : X), isProofIrrelevant (x1 = x2)).
    { intros. apply proofirrelevance, isasetifdeceq, deceqX. }
    use make_weq.
    - intros [[x neq] | tt].
      + apply x.
      + apply y.
    - intros y0.
      induction (deceqX y0 y).
      + use tpair.
        * use tpair.
          -- right. exact tt.
          -- simpl; apply pathsinv0; assumption.
        * intros [fib bla].
          induction fib. destruct a0. induction a; contradiction.
          induction b.
          specialize X0 with (x1 := y) (x2 := y0).
          induction (X0 (! a) bla). apply idpath.
      + use tpair.
        * use tpair.
          -- exact (inl (y0 ,, b)).  
          -- apply idpath.
        * simpl.
          intros [hfib bla].
          induction hfib.
          -- destruct a. induction bla.
             assert (b = pr2).
             { use proofirrelevance. apply isapropimpl, isapropempty. } 
             induction X1. apply idpath.
          -- apply fromempty.
             apply b, pathsinv0, bla.
Qed.

Definition snton {X : UU} {n : nat} (f : stn (S n) → X) : stn n → X.
Proof.
    intros [m lem].
    apply f. apply (make_stn _  m). apply natlthtolths, lem.
Defined.

Definition helper_fun {X : UU} {n : nat} (f : stn (S n) → X) : ¬ hfiber (snton f) (f lastelement) → stn n → (∑ (x : X), ¬ (x = (f lastelement))).
Proof.
    intros.
    exists (snton f X1).
    intros contra.
    apply X0.
    eexists. apply contra.
Defined.

Lemma issurjective_helper_fun {X : UU} {n : nat} (f : stn (S n) → X) (nfib : ¬ hfiber (snton f) (f lastelement)) : issurjective f → issurjective (helper_fun f nfib).
Proof.
    intros surjf y.
    destruct y as [x neq].
    use squash_to_prop.
    - exact (hfiber f x).
    - exact (surjf x).
    - apply propproperty.
    - intros [[m lth] q]; clear surjf. apply hinhpr.
      induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
      + exists (m ,, a).
        unfold helper_fun, snton, make_stn.
        assert (natlthtolths m n a = lth).
        { apply proofirrelevance, propproperty. }
        induction X0, q.
        assert ((λ contra : f (m,, natlthtolths m n a) = f lastelement,
 nfib ((m,, a),, contra)) = neq) by apply proofirrelevance, isapropimpl, isapropempty. induction X0. apply idpath.
      + assert (m ,, lth = lastelement) by apply stn_eq, b.
        apply fromempty, neq. induction X0. apply pathsinv0, q.
Qed.

Lemma isdeceqremoveterm {X : UU} (y : X) : isdeceq X → isdeceq (∑ x : X, x != y).
Proof.
    intros decX [a neq1] [b neq2].
    induction (decX a b).
    - induction a0.
      assert (neq1 = neq2) by apply proofirrelevance, isapropimpl, isapropempty.
      induction X0. left. apply idpath.
    - right. intros eq. apply b0. apply maponpaths with (f := pr1) in eq. apply eq.
Qed. 

Lemma isdeceq_isdecsurj {X : UU} {n : nat} (f : stn n → X ) (y : X) : isdeceq X → decidable (hfiber f y).
Proof.
  generalize dependent X.
  induction n; intros X f x deceqX.
  - right. intros [contra eq]. apply weqstn0toempty, contra.
  - set (g := snton f). specialize IHn with (f := g) (y := x).
    set (H := IHn deceqX).
    induction H.
    + left. destruct a as [[m lth] eq].
      exists (m ,, (natlthtolths _ _ lth)).
      apply eq.
    + induction (deceqX (f (lastelement)) x).
      * left. exists lastelement. assumption.
      * right. intros [[m lth] eq].
        induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
        -- apply b. exists (m ,, a).
           assert (f (m ,, lth) = g (m ,, a)).
           { unfold g, snton, make_stn. 
             assert (lth = natlthtolths m n a) by apply proofirrelevance, propproperty. induction X0. apply idpath. }
           induction X0. assumption.
        -- apply b0. unfold lastelement. induction b1.
           assert (lth = natgthsnn m).
           { apply proofirrelevance, propproperty. }
           induction X0. assumption.
Qed.

Lemma kfinstruct_dec_finstruct {X : UU} : kfinstruct X → isdeceq X → finstruct X.
Proof.
    intros [n [f surj]] deceqX.
    generalize dependent X.
    induction n; intros.
    - exists 0.
      assert (H : X → ∅).
      { intros x.  
        assert (hyp : ∥ hfiber f x ∥) by (exact (surj x)). 
        eapply squash_to_prop.
        + apply hyp.
        + apply isapropempty. 
        + intros [n eq].
            apply negstn0; assumption.
        }
        apply weqiff; [ | apply isapropifnegtrue, negstn0 | apply isapropifnegtrue, H ].
      + split; [apply f | intros x; apply fromempty; apply H, x ].
    - set (g := snton f).
      set (y := f lastelement).
      induction (isdeceq_isdecsurj g y deceqX).
      + assert (H : issurjective g).
        * intros y'.
          induction (deceqX y y').
          -- induction a0. apply hinhpr, a.
          -- use squash_to_prop.
             ++ exact (hfiber f y').
             ++ apply surj.
             ++ apply propproperty.
             ++ intros [[m lth] x].
                apply hinhpr.
                induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
                ** exists (m ,, a0).
                   assert (g (m ,, a0) = f (m ,, lth)).
                   --- unfold g, snton, make_stn.
                       assert (natlthtolths m n a0 = lth) by (apply proofirrelevance, propproperty). induction X0.
                       apply idpath.
                   --- induction X0. assumption.
                ** assert (f (m ,, lth) = f lastelement).
                   { unfold lastelement. induction b0.
                     assert (lth = natgthsnn m) by (apply proofirrelevance, propproperty). induction X0. apply idpath. }
                   unfold y in b. rewrite <- X0 in b.
                   apply fromempty.
                   exact (b x). 
        * apply IHn with (f := g); assumption.
      + set (g' := helper_fun f b).
        set (surjg' := (issurjective_helper_fun f b surj)).
        specialize IHn with (f := g').
        apply IHn in surjg'; try apply isdeceqremoveterm; try assumption.
        destruct surjg' as [m eq].
        exists (S m).
        use weqcomp.
        * exact (coprod (stn m) unit).
        * apply invweq. apply weqdnicoprod_provisional. exact firstelement.
        * use weqcomp.
          -- exact (coprod (∑ (x : X), ¬ (x = y)) unit).
          -- apply weqcoprodf1, eq.
          -- apply helper1, deceqX.
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