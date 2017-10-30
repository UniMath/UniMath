(** * Facts about the natural numbers that depend on definitions from algebra *)

Require Export UniMath.Algebra.Archimedean.
Require Export UniMath.Algebra.Domains_and_Fields.
Require Export UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Tactics.

Definition nataddabmonoid : abmonoid :=
  abmonoidpair (setwithbinoppair natset (λ n m : nat, n + m))
               (dirprodpair
                  (dirprodpair natplusassoc
                               (@isunitalpair natset _ 0 (dirprodpair natplusl0 natplusr0)))
                  natpluscomm).


Definition natmultabmonoid : abmonoid :=
  abmonoidpair
    (setwithbinoppair natset (λ n m : nat, n * m))
    (dirprodpair
       (dirprodpair natmultassoc (@isunitalpair natset _ 1 (dirprodpair natmultl1 natmultr1)))
       natmultcomm).

(** *** Submonoid of non-zero elements in [nat] *)

Definition natnonzero : @subabmonoid natmultabmonoid.
Proof.
  split with (λ a, a ≠ 0). unfold issubmonoid. split.
  - unfold issubsetwithbinop. intros a a'.
    apply (natneq0andmult _ _ (pr2 a) (pr2 a')).
  - apply (ct (natneq, isdecrel_natneq, 1, 0)).
Defined.

Lemma natnonzerocomm (a b : natnonzero) :
  (@op natnonzero a b) = (@op natnonzero b a).
Proof.
  intros.
  apply (invmaponpathsincl _ (isinclpr1carrier _) (@op natnonzero a b) (@op natnonzero b a)).
  simpl. apply natmultcomm.
Defined.

(** *** [nat] as a commutative rig *)

Definition natcommrig : commrig.
Proof.
  split with (setwith2binoppair natset (dirprodpair (λ n m : nat, n + m) (λ n m : nat, n * m))).
  split.
  - split.
    + split with
      (dirprodpair
         (dirprodpair
            (dirprodpair natplusassoc (@isunitalpair natset _ 0 (dirprodpair natplusl0 natplusr0)))
            natpluscomm)
         (dirprodpair natmultassoc (@isunitalpair natset _ 1 (dirprodpair natmultl1 natmultr1)))).
      apply (dirprodpair natmult0n natmultn0).
    + apply (dirprodpair natldistr natrdistr).
  - unfold iscomm. apply natmultcomm.
Defined.

Lemma nattorig_nat :
  ∏ n : nat, nattorig (X := natcommrig) n = n.
Proof.
  induction n as [|n IHn].
  reflexivity.
  rewrite nattorigS, IHn.
  reflexivity.
Qed.

(** *** Properties of comparisons in the terminology of algebra1.v *)

Local Open Scope rig_scope.

(** [natgth] *)

Lemma isplushrelnatgth : @isbinophrel nataddabmonoid natgth.
Proof.
  split. apply natgthandplusl. apply natgthandplusr.
Defined.

Lemma isinvplushrelnatgth : @isinvbinophrel nataddabmonoid natgth.
Proof.
  split. apply natgthandpluslinv. apply natgthandplusrinv.
Defined.

Lemma isinvmulthrelnatgth : @isinvbinophrel natmultabmonoid natgth.
Proof.
  split.
  - intros a b c r. apply (natlthandmultlinv _ _ _ r).
  - intros a b c r. apply (natlthandmultrinv _ _ _ r).
Defined.

Lemma isrigmultgtnatgth : isrigmultgt natcommrig natgth.
Proof.
  intros a.
  induction a as [|a IHa].
  - intros ? ? ? rab rcd. contradicts rab (negnatgth0n b).
  - intros ? ? ? rab rcd.
    induction b as [|b IHb].
    + simpl.
      rewrite <- 2? plus_n_O.
      simpl in IHa.
      rewrite 2? (natmult0n) in IHa.
      rewrite <- 2? plus_n_O in IHa.
      apply (natlthandmultl _ _ _ (natgthtoneq _ _ rab) rcd).
    + simpl.
      set (rer := abmonoidrer nataddabmonoid).
      unfold op1, op2; simpl.
      rewrite (rer _ _ _ d). rewrite (rer _ _ _ c).
      unfold op1, op2; simpl.
      rewrite (natpluscomm c d).
      apply (natlthandplusr (a * d + b * c) (a * c + b * d) (d + c)).
      apply (IHa _ _ _ rab rcd).
Defined.

Lemma isinvrigmultgtnatgth : isinvrigmultgt natcommrig natgth.
Proof.
  set (rer := abmonoidrer nataddabmonoid).
  simpl in rer. apply isinvrigmultgtif.
  intros a b c d. generalize a b c. clear a b c.
  induction d as [ | d IHd ].
  - intros a b c g gab. change (pr1 ((a * c + b * 0) > (a * 0 + b * c))) in g.
    destruct c as [ | c ].
    + rewrite (natmultn0 _) in g. destruct (isirreflnatgth _ g).
    + apply natgthsn0.
  - intros a b c g gab. destruct c as [ | c ].
    + change (pr1 ((a * 0 + b * S d) > (a * S d + b * 0))) in g.
      rewrite (natmultn0 _) in g. rewrite (natmultn0 _) in g.
      rewrite (natplusl0 _) in g. rewrite (natplusr0 _) in g.
      set (g' := natgthandmultrinv _ _ _ g).
      destruct (isasymmnatgth _ _ gab g').
    + change (pr1 (natgth (a * S c + b * S d) (a * S d + b * S c))) in g.
      rewrite (multnsm _ _) in g. rewrite (multnsm _ _) in g.
      rewrite (multnsm _ _) in g. rewrite (multnsm _ _) in g.
      rewrite (rer _ (a * c) _ _) in g. rewrite (rer _ (a * d) _ _) in g.
      set (g' := natgthandpluslinv _ _ (a + b) g). apply (IHd a b c g' gab).
Defined.

(** [natlth] *)

Lemma isplushrelnatlth : @isbinophrel nataddabmonoid natlth.
Proof.
  split.
  - intros a b c. apply (natgthandplusl b a c).
  - intros a b c. apply (natgthandplusr b a c).
Defined.

Lemma isinvplushrelnatlth : @isinvbinophrel nataddabmonoid natlth.
Proof.
  split.
  - intros a b c. apply (natgthandpluslinv b a c).
  - intros a b c. apply (natgthandplusrinv b a c).
Defined.

Lemma isinvmulthrelnatlth : @isinvbinophrel natmultabmonoid natlth.
Proof.
  split.
  - intros a b c r. apply (natlthandmultlinv _ _ _ r).
  - intros a b c r. apply (natlthandmultrinv _ _ _ r).
Defined.

(** [natleh] *)

Lemma isplushrelnatleh : @isbinophrel nataddabmonoid natleh.
Proof.
  split. apply natlehandplusl. apply natlehandplusr.
Defined.

Lemma isinvplushrelnatleh : @isinvbinophrel nataddabmonoid natleh.
Proof.
  split. apply natlehandpluslinv. apply natlehandplusrinv.
Defined.

Lemma ispartinvmulthrelnatleh : @ispartinvbinophrel natmultabmonoid (λ x, x ≠ 0) natleh.
Proof.
  split.
  - intros a b c s r. apply (natlehandmultlinv _ _ _ s r).
  - intros a b c s r. apply (natlehandmultrinv _ _ _ s r).
Defined.

(** [natgeh] *)

Lemma isplushrelnatgeh : @isbinophrel nataddabmonoid natgeh.
Proof.
  split.
  - intros a b c. apply (natlehandplusl b a c).
  - intros a b c. apply (natlehandplusr b a c).
Defined.

Lemma isinvplushrelnatgeh : @isinvbinophrel nataddabmonoid natgeh.
Proof.
  split.
  - intros a b c. apply (natlehandpluslinv b a c).
  - intros a b c. apply (natlehandplusrinv b a c).
Defined.

Lemma ispartinvmulthrelnatgeh : @ispartinvbinophrel natmultabmonoid (λ x, x ≠ 0) natgeh.
Proof.
  split.
  - intros a b c s r. apply (natlehandmultlinv _ _ _ s r).
  - intros a b c s r. apply (natlehandmultrinv _ _ _ s r).
Defined.

(** *** [nat] is an archimedean rig *)

Lemma isarchnat_diff :
  ∏ (y1 y2 : nat),
  y1 > y2 → ∃ n : nat, n * y1 > 1 + n * y2.
Proof.
  intros y1 y2 Hy.
  apply natlthchoice2 in Hy.
  induction Hy as [Hy | <-].
  - apply hinhpr.
    exists 1%nat.
    exact Hy.
  - apply hinhpr.
    exists 2%nat.
    rewrite !multsnm ; simpl.
    rewrite natplusr0.
    apply natgthandplusl, natgthsnn.
Defined.

Lemma isarchnat_gth :
  ∏ x : nat, ∃ n : nat, n > x.
Proof.
  intros n.
  apply hinhpr.
  exists (S n).
  now apply natgthsnn.
Defined.

Lemma isarchnat_pos :
  ∏ x : nat, ∃ n : nat, n + x > 0.
Proof.
  intros n.
  apply hinhpr.
  now exists 1%nat.
Defined.

Lemma isarchnat :
  isarchrig (X := natcommrig) natgth.
Proof.
  repeat split.
  - intros y1 y2 Hy.
    generalize (isarchnat_diff y1 y2 Hy).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    rewrite nattorig_nat.
    exact (pr2 n).
  - intros n.
    generalize (isarchnat_gth n).
    apply hinhfun.
    intros n'.
    exists (pr1 n').
    rewrite nattorig_nat.
    exact (pr2 n').
  - intros n.
    generalize (isarchnat_pos n).
    apply hinhfun.
    intros n'.
    exists (pr1 n').
    rewrite nattorig_nat.
    exact (pr2 n').
Defined.
