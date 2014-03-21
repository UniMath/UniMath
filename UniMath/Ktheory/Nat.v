(* -*- coding: utf-8 *)

(** * Natural numbers *)

Unset Automatic Introduction.
Require Import algebra1b hnat funextfun pathnotations auxiliary_lemmas_HoTT Utilities.
Import PathNotations. 
Import Utilities.Notation.
Import Utilities.NatNotation.

Fixpoint nat_dist (m n:nat) : nat :=
  match m , n with
    | S m, S n => nat_dist m n
    | 0, n => n
    | m, 0 => m end.

Fixpoint nat_discern (m n:nat) : Type :=
  match m , n with
    | S m, S n => nat_discern m n
    | 0, S n => empty
    | S m, 0 => empty
    | 0, 0 => unit end.

Goal forall m n, nat_discern m n -> nat_discern (S m) (S n).
Proof. intros ? ? e. exact e. Defined.

Lemma nat_discern_inj m n : nat_discern (S m) (S n) -> nat_discern m n.
Proof. intros ? ? e. induction m.
       { induction n. { exact tt. } { simpl in e. exact (fromempty e). } }
       { induction n. { simpl in e. exact (fromempty e). } { simpl in e. exact e. } }
Defined.

Lemma nat_discern_isaprop m n : isaprop (nat_discern m n).
Proof. intros m. induction m. 
       { intros n. induction n.
         { apply isapropifcontr. apply iscontrunit. }
         { simpl. apply isapropempty. } }
       { intros n. induction n. 
         { simpl. apply isapropempty. }
         { simpl. apply IHm. } } Defined.

Lemma nat_discern_unit m : nat_discern m m == unit.
Proof. intros m. induction m. { reflexivity. } { simpl. apply IHm. } Defined.

Lemma nat_discern_iscontr m : iscontr (nat_discern m m).
Proof. intros m. apply iscontr_if_inhab_prop.
       { apply nat_discern_isaprop. }
       { induction m. { exact tt. } { simpl. exact IHm. } } Defined.

Fixpoint A m n : nat_dist m n == 0 -> nat_discern m n.
Proof. intros ? ?. destruct m as [|m'].
       { destruct n as [|n'].
         { intros _. exact tt. } { simpl. exact (negpathssx0 n'). } }
       { destruct n as [|n'].
         { simpl. exact (negpathssx0 m'). } { simpl. exact (A m' n'). } } Defined.

Fixpoint B m n : nat_discern m n -> m == n.
Proof. intros ? ?. destruct m as [|m'].
       { destruct n as [|n'].
         { intros _. reflexivity. } { simpl. exact fromempty. } }
       { destruct n as [|n'].
         { simpl. exact fromempty. }
         { simpl. intro i. assert(b := B _ _ i); clear i. 
           destruct b. reflexivity. } } Defined.

Goal forall m n (e:nat_discern m n), ap S (B m n e) == B (S m) (S n) e.
Proof. reflexivity. Defined.

Fixpoint C m n : m == n -> nat_discern m n.
Proof. intros ? ? e. destruct e.
       (* alternatively:
        destruct m. { exact tt. } { simpl. exact (the (nat_discern_iscontr _)). }  
        *)
       exact (cast (! nat_discern_unit m) tt).
Defined.

Lemma apSC m n (e:m==n) : C m n e == C (S m) (S n) (ap S e).
Proof. intros. apply proofirrelevance. apply nat_discern_isaprop. Defined.

Definition D m n : isweq (B m n).
Proof. intros. refine (gradth _ (C _ _) _ _).
       { intro e. assert(p := ! B _ _ e). destruct p.
         apply proofirrelevancecontr. apply nat_discern_iscontr. }
       { intro e. destruct e. induction m.
         { reflexivity. }
         { exact (  ap (B (S m) (S m)) (! apSC _ _ (idpath m)) 
                  @ ap (ap S) IHm). } } Defined.

Definition E m n : weq (nat_discern m n) (m == n).
Proof. intros. exact (weqpair (B _ _) (D _ _)). Defined.

Definition nat_dist_anti m n : nat_dist m n == 0 -> m == n.
Proof. intros ? ? i. exact (B _ _ (A _ _ i)). Defined.

Fixpoint nat_dist_symm m n : nat_dist m n == nat_dist n m.
Proof. intros ? ?. destruct m as [|m'].
       { destruct n as [|n']. { reflexivity. } { simpl. reflexivity. } }
       { destruct n as [|n']. 
         { simpl. reflexivity. }
         { simpl. apply nat_dist_symm. } } Defined.

Fixpoint nat_dist_ge m n : m >= n -> nat_dist m n == m-n.
Proof. intros ? ?. destruct m as [|m'].
       { destruct n as [|n']. { reflexivity. }
         { simpl. intro f. apply fromempty. apply f. reflexivity. } }
       { destruct n as [|n']. { simpl. intros _. reflexivity. }
         { simpl. apply nat_dist_ge. } } Defined.

Definition nat_dist_0m m : nat_dist 0 m == m.
Proof. reflexivity. Defined.

Definition nat_dist_m0 m : nat_dist m 0 == m.
Proof. intro m. destruct m. { reflexivity. } { reflexivity. } Defined.

Fixpoint nat_dist_plus m n : nat_dist (m + n) m == n.
Proof. intros [|m'] ?.
       { simpl. apply nat_dist_m0. }
       { simpl. apply nat_dist_plus. } Defined.

Fixpoint nat_dist_le m n : m <= n -> nat_dist m n == n-m.
Proof. intros ? ?. destruct m as [|m'].
       { destruct n as [|n']. { reflexivity. } { simpl. intros _. reflexivity. } }
       { destruct n as [|n'].
         { simpl. intro f. apply fromempty. apply f. reflexivity. } 
         { simpl. apply nat_dist_le. } } Defined.

Definition nat_dist_minus m n : m <= n -> nat_dist (n - m) n == m.
Proof. intros ? ? e. set (k := n-m). assert(b := ! minusplusnmm n m e).
       rewrite (idpath _ : n-m == k) in b. rewrite b.
       rewrite nat_dist_symm. apply nat_dist_plus. Qed.

Fixpoint nat_dist_gt m n : m > n -> S (nat_dist m (S n)) == nat_dist m n.
Proof. intros ? ?. destruct m as [|m'].
       { unfold natgth; simpl. intro x. 
         apply fromempty. apply nopathsfalsetotrue. exact x. }
       { intro i. simpl.
         destruct n as [|n'].
         { apply (ap S). apply nat_dist_m0. }
         { simpl. apply nat_dist_gt. exact i. } } Defined.

Definition nat_dist_S m n : nat_dist (S m) (S n) == nat_dist m n.
Proof. reflexivity. Defined.

Definition natminuseqlr m n x : m<=n -> n-m == x -> n == x+m.
Proof. intros ? ? ? i j.
       rewrite <- (minusplusnmm _ _ i). rewrite j. reflexivity. Defined.

Definition nat_dist_between_le m n a b : 
  m <= n -> nat_dist m n == a + b -> 
  total2 (fun x => dirprod (nat_dist x m == a) (nat_dist x n == b)).
Proof. intros ? ? ? ? i j. exists (m+a). split.
       { apply nat_dist_plus. }
       { rewrite (nat_dist_le m n i) in j.
         assert (k := natminuseqlr _ _ _ i j); clear j.
         assert (l := nat_dist_plus (m+a) b).
         rewrite nat_dist_symm. rewrite (natpluscomm (a+b) m) in k.
         rewrite (natplusassoc m a b) in l. rewrite <- k in l. exact l. } Defined.

Definition nat_dist_between_ge m n a b : 
  n <= m -> nat_dist m n == a + b -> 
  total2 (fun x => dirprod (nat_dist x m == a) (nat_dist x n == b)).
Proof. intros ? ? ? ? i j. 
       rewrite nat_dist_symm in j.
       rewrite natpluscomm in j.
       exists (pr1 (nat_dist_between_le n m b a i j)).
       apply (weqdirprodcomm _ _).
       exact (pr2 (nat_dist_between_le n m b a i j)).
Defined.

Definition nat_dist_between m n a b : 
  nat_dist m n == a + b -> 
  total2 (fun x => dirprod (nat_dist x m == a) (nat_dist x n == b)).
Proof. intros ? ? ? ? j. 
       induction (natgthorleh m n) as [r|s].
       { apply nat_dist_between_ge. apply natlthtoleh. exact r. exact j. }
       { apply nat_dist_between_le. exact s. exact j. }
Defined.

Definition natleorle m n : coprod (m<=n) (n<=m).
Proof. intros.
       induction (natgthorleh m n) as [r|s].
       { apply ii2. apply natlthtoleh. exact r. }
       { apply ii1. exact s. } Defined.

Definition nat_dist_trans x y z : nat_dist x z <= nat_dist x y + nat_dist y z.
Proof. intros. induction (natleorle x y) as [r|s].
       { rewrite (nat_dist_le _ _ r).
         induction (natleorle y z) as [t|u].
         { assert (u := istransnatgeh _ _ _ t r). rewrite (nat_dist_le _ _ t).
           rewrite (nat_dist_le _ _ u). apply (natlehandplusrinv _ _ x).
           rewrite (minusplusnmm _ _ u). rewrite (natpluscomm _ x).
           rewrite <- natplusassoc. rewrite (natpluscomm x).
           rewrite (minusplusnmm _ _ r). rewrite (natpluscomm y).
           rewrite (minusplusnmm _ _ t). apply isirreflnatgth. }
         { rewrite (nat_dist_ge _ _ u).
           induction (natleorle x z) as [p|q].
           { rewrite (nat_dist_le _ _ p). apply (natlehandplusrinv _ _ x).
             rewrite (minusplusnmm _ _ p). rewrite natpluscomm.
             rewrite <- natplusassoc. rewrite (natpluscomm x).
             rewrite (minusplusnmm _ _ r). apply (natlehandplusrinv _ _ z).
             rewrite natplusassoc. rewrite (minusplusnmm _ _ u).
             apply (istransnatleh _ (y+z)).
             { apply natlehandplusr. exact u. }
             { apply natlehandplusl. exact u. } }
           { rewrite (nat_dist_ge _ _ q). apply (natlehandplusrinv _ _ z).
             rewrite (minusplusnmm _ _ q). rewrite natplusassoc.                              
             rewrite (minusplusnmm _ _ u). rewrite natpluscomm.
             apply (natlehandplusrinv _ _ x). rewrite natplusassoc.                              
             rewrite (minusplusnmm _ _ r). apply (istransnatleh _ (x+y)).
             { apply natlehandplusl. assumption. }
             { apply natlehandplusr. assumption. } } } }
       { rewrite (nat_dist_ge _ _ s).
         induction (natleorle z y) as [u|t].
         { assert (w := istransnatleh _ _ _ u s). rewrite (nat_dist_ge _ _ w).
           rewrite (nat_dist_ge _ _ u). apply (natlehandplusrinv _ _ z).
           rewrite (minusplusnmm _ _ w). rewrite natplusassoc.                              
           rewrite (minusplusnmm _ _ u). rewrite (minusplusnmm _ _ s). 
           apply isirreflnatgth. }
         { rewrite (nat_dist_le _ _ t).
           induction (natleorle x z) as [p|q].
           { rewrite (nat_dist_le _ _ p). apply (natlehandplusrinv _ _ x).
             rewrite (minusplusnmm _ _ p). apply (natlehandpluslinv _ _ y).
             rewrite (natplusassoc (x-y)). rewrite <- (natplusassoc y).
             rewrite (natpluscomm y (x-y)). rewrite (minusplusnmm _ _ s).                              
             apply (natlehandplusrinv _ _ y). rewrite (natplusassoc x).
             rewrite (natplusassoc _ x y). rewrite (natpluscomm x y).
             rewrite <- (natplusassoc _ y x). rewrite (minusplusnmm _ _ t).
             rewrite (natpluscomm z x). rewrite <- (natplusassoc x).
             rewrite (natplusassoc y). rewrite (natpluscomm z y).
             rewrite <- (natplusassoc y). apply (natlehandplusr _ _ z).
             apply (istransnatleh _ (x+y)).
             { apply natlehandplusr. assumption. } 
             { apply natlehandplusl. assumption. } }
           { rewrite (nat_dist_ge _ _ q). apply (natlehandplusrinv _ _ z).
             rewrite (minusplusnmm _ _ q). apply (natlehandpluslinv _ _ y).
             rewrite (natplusassoc (x-y)). rewrite <- (natplusassoc y).
             rewrite (natpluscomm y (x-y)). rewrite (minusplusnmm _ _ s).                              
             apply (natlehandplusrinv _ _ y). rewrite (natplusassoc x).
             rewrite (natplusassoc _ z y). rewrite (natpluscomm z y).
             rewrite <- (natplusassoc _ y z). rewrite (minusplusnmm _ _ t).
             rewrite (natpluscomm y x). rewrite (natplusassoc x).
             apply natlehandplusl. apply (istransnatleh _ (z+y)).
             { apply natlehandplusr. assumption. } 
             { apply natlehandplusl. assumption. } } } } Defined.

Lemma plusmn0n0 m n : m + n == 0 -> n == 0.
Proof. intros ? ? i. assert (a := natlehmplusnm m n). rewrite i in a.
       apply natleh0tois0. assumption. Defined.

Lemma plusmn0m0 m n : m + n == 0 -> m == 0.
Proof. intros ? ? i. assert (a := natlehnplusnm m n). rewrite i in a.
       apply natleh0tois0. assumption. Defined.

Lemma natminus0le {m n} : m-n == 0 -> n >= m.
Proof. intros ? ? i j. assert (a := minusgth0 m n j); clear j.
       rewrite i in a; clear i. exact (negnatgth0n 0 a). Defined.

Lemma minusxx m : m - m == 0.
Proof. intro. induction m. reflexivity. simpl. assumption. Defined.

Lemma minusSxx m : S m - m == 1.
Proof. intro. induction m. reflexivity. assumption. Defined.

Lemma natminusminus n m : m <= n -> n - (n - m) == m.
Proof. intros ? ? i. assert (b := plusminusnmm m (n-m)).
       rewrite natpluscomm in b. rewrite (minusplusnmm _ _ i) in b.
       exact b. Defined.

Lemma natplusminus m n k : k==m+n -> k-n==m.
Proof. intros ? ? ? i. rewrite i. apply plusminusnmm. Defined.

Lemma natleplusminus k m n : k + m <= n -> k <= n - m.
Proof. intros ? ? ? i.
       apply (natlehandplusrinv _ _ m).
       rewrite minusplusnmm.
       { exact i. }
       { change (m <= n).
         refine (istransnatleh m (k+m) n _ i); clear i.
         apply natlehmplusnm. } Defined.

Lemma natltminus1 m n : m < n -> m <= n - 1.
Proof. intros ? ? i. assert (a := natlthp1toleh m (n - 1)).
       assert (b := natleh0n m). assert (c := natlehlthtrans _ _ _ b i).
       assert (d := natlthtolehsn _ _ c). assert (e := minusplusnmm _ _ d).
       rewrite e in a. exact (a i). Defined.

Fixpoint natminusminusassoc m n k : (m-n)-k == m-(n+k).
Proof. intros. destruct m. { reflexivity. }
       { destruct n. { rewrite natminuseqn. reflexivity. }
         { simpl. apply natminusminusassoc. } } Defined.

Definition natminusplusltcomm m n k : k <= n -> m <= n - k -> k <= n - m.
Proof. intros ? ? ? i p.
       assert (a := natlehandplusr m (n-k) k p); clear p.
       assert (b := minusplusnmm n k i); clear i.
       rewrite b in a; clear b. apply natleplusminus. 
       rewrite natpluscomm. exact a. Qed.

Require Import MetricTree.

Definition nat_tree : Tree.
Proof. refine (make nat nat_dist _ _ _ _ _).
       { intro m. induction m. { reflexivity. } { rewrite nat_dist_S. assumption. } }
       { apply nat_dist_anti. } { apply nat_dist_symm. } 
       { apply nat_dist_trans. }
       { intros m n e. assert (d := natneqchoice _ _ e). clear e.
         destruct d as [h|h].
         { exists (S n).
           { split.
             { apply nat_dist_gt. exact h. }
             { destruct (natgthorleh (S n) n) as [_|j].
               { clear h. induction n. { reflexivity. } { apply IHn. } } 
               { apply fromempty. clear h. exact (j (natgthsnn n)). }}} }
         { exists (n - 1).
           { split.
             { assert (a := natltminus1 m n h). assert (b := natlthtoleh m n h).
               assert (c := nat_dist_le _ _ a). assert (d := nat_dist_le _ _ b).
               rewrite c, d; clear c d. rewrite natminusminusassoc. simpl.
               change (1 + (n - (1+m)) == n - m). rewrite (natpluscomm 1 m).
               rewrite <- natminusminusassoc. rewrite natpluscomm.
               apply (minusplusnmm (n-m) 1).
               apply (natminusplusltcomm m n 1).
               { assert(e := natleh0n m). 
                 assert(f := natlehlthtrans _ _ _ e h).
                 exact (natlthtolehsn _ _ f). }
               { exact a. } }
             { assert (a := natleh0n m).
               assert (b := natlehlthtrans _ _ _ a h).
               assert (c := natlthtolehsn _ _ b).
               exact (nat_dist_minus 1 n c). } } } } Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Nat.vo"
End:
*)
