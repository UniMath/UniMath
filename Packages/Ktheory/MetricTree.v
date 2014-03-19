(* -*- coding: utf-8 *)

(** * Metric trees *)

Unset Automatic Introduction.
Require Import algebra1b hnat funextfun pathnotations auxiliary_lemmas_HoTT Ktheory.Utilities.
Import PathNotations. 
Import Utilities.Notation.

(** ** Definitions *)

Local Notation "m <= n" := (natleh m n).
Local Notation "m >= n" := (natgeh m n).
Local Notation "m > n" := (natgth m n).
Local Notation "m < n" := (natlth m n).
Local Notation "x != y" := (not (x == y)) (at level 40).

Record Tree := 
  make {
      mt_set:> Type;
      mt_dist: mt_set -> mt_set -> nat;
      mt_refl: forall x, mt_dist x x == 0;
      mt_anti: forall x y, mt_dist x y == 0 -> x == y;
      mt_symm: forall x y, mt_dist x y == mt_dist y x;
      mt_trans: forall x y z, mt_dist x z <= mt_dist x y + mt_dist y z;
      mt_step: forall x z, x!=z ->
                 total2 (fun y => dirprod 
                                     (S (mt_dist x y) == mt_dist x z)
                                     (mt_dist y z == 1)) }.
      
Lemma mt_path_refl (T:Tree) (x y:T) : x==y -> mt_dist _ x y == 0.
Proof. intros ? ? ? e. destruct e. apply mt_refl. Qed.

Lemma tree_deceq (T:Tree) : isdeceq T.
Proof. intros. intros t u. induction (isdeceqnat (mt_dist T t u) 0).
       { apply inl. apply mt_anti. assumption. }
       { apply inr. intro e. apply b. destruct e. apply mt_refl. } Qed.

Corollary tree_isaset (T:Tree) : isaset T.
Proof. intros. apply isasetifdeceq. apply tree_deceq. Qed.

Definition step (T:Tree) (x z:T) (ne:x!=z) : T := pr1 (mt_step _ x z ne).

Definition tree_induction (T:Tree) (x:T) (P:T->Type)
           (p0 : P x)
           (pn : forall z (ne:x!=z), P (step T x z ne) -> P z) :
  forall z, P z.
Proof. intros ? ? ? ? ?.
       assert(d_ind : forall n z, mt_dist _ x z == n -> P z).
       { intros ?.
         induction n as [|n IH].
         { intros. assert (k:x==z). 
           { apply mt_anti. assumption. } destruct k. assumption. }
         { intros. 
           assert (ne : x != z).
           { intros s. exact (negpaths0sx _ (! mt_path_refl _ _ _ s @ H)). }
           refine (pn z ne _).
           { apply IH.
             unfold step; simpl.
             set (y := mt_step T x z ne).
             destruct y as [y [i j]]; simpl.
             apply invmaponpathsS. exact (i@H). } } }
       intro. apply (d_ind (mt_dist _ x z)). reflexivity. Defined.

(* Definition nat_dist : nat -> nat -> nat. *)
(* Proof. intros m n. exact ((m-n)+(n-m)). Defined. *)

(* Fixpoint nat_dist (m n:nat) : nat. *)
(* Proof. intros m n. *)
(*        destruct m as [|m]. *)
(*        { exact n. } *)
(*        { destruct n as [|n]. *)
(*          { exact (S m). } *)
(*          { exact (nat_dist m n). } } Defined. *)

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

Fixpoint A m n : nat_dist m n == 0 -> nat_discern m n.
Proof. intros ? ?.
       destruct m as [|m'].
       { destruct n as [|n'].
         { intros _. exact tt. }
         { simpl. exact (negpathssx0 n'). } }
       { destruct n as [|n'].
         { simpl. exact (negpathssx0 m'). }
         { simpl. exact (A m' n'). } } Defined.

Fixpoint B m n : nat_discern m n -> m == n.
Proof. intros ? ?.
       destruct m as [|m'].
       { destruct n as [|n'].
         { intros _. reflexivity. }
         { simpl. exact fromempty. } }
       { destruct n as [|n'].
         { simpl. exact fromempty. }
         { simpl. intro i. assert(b := B _ _ i); clear i. 
           destruct b. reflexivity. } } Defined.

Definition nat_dist_anti m n : nat_dist m n == 0 -> m == n.
Proof. intros ? ? i. exact (B _ _ (A _ _ i)). Qed.

Fixpoint nat_dist_symm m n : nat_dist m n == nat_dist n m.
Proof. intros ? ?.
       destruct m as [|m'].
       { destruct n as [|n'].
         { reflexivity. }
         { simpl. reflexivity. } }
       { destruct n as [|n'].
         { simpl. reflexivity. }
         { simpl. apply nat_dist_symm. } } Defined.

Fixpoint nat_dist_ge m n : m >= n -> nat_dist m n == m-n.
Proof. intros ? ?.
       destruct m as [|m'].
       { destruct n as [|n'].
         { reflexivity. }
         { simpl. intro f. apply fromempty. apply f. reflexivity. } }
       { destruct n as [|n'].
         { simpl. intros _. reflexivity. }
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
Proof. intros ? ?.
       destruct m as [|m'].
       { destruct n as [|n'].
         { reflexivity. }
         { simpl. intros _. reflexivity. } }
       { destruct n as [|n'].
         { simpl. intro f. apply fromempty. apply f. reflexivity. } 
         { simpl. apply nat_dist_le. } } Defined.

Fixpoint nat_dist_gt m n : m > n -> S (nat_dist m (S n)) == nat_dist m n.
Proof. intros ? ?.
       destruct m as [|m'].
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
       rewrite <- (minusplusnmm _ _ i). rewrite j. reflexivity. Qed.

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
       apply natleh0tois0. assumption. Qed.

Lemma plusmn0m0 m n : m + n == 0 -> m == 0.
Proof. intros ? ? i. assert (a := natlehnplusnm m n). rewrite i in a.
       apply natleh0tois0. assumption. Qed.

Lemma natminus0le {m n} : m-n == 0 -> n >= m.
Proof. intros ? ? i j. assert (a := minusgth0 m n j); clear j.
       rewrite i in a; clear i. exact (negnatgth0n 0 a). Defined.

Lemma minusxx m : m - m == 0.
Proof. intro. induction m. reflexivity. simpl. assumption. Qed.

Lemma minusSxx m : S m - m == 1.
Proof. intro. induction m. reflexivity. assumption. Qed.

Lemma natminusminus n m : m <= n -> n - (n - m) == m.
Proof. intros ? ? i. assert (b := plusminusnmm m (n-m)).
       rewrite natpluscomm in b. rewrite (minusplusnmm _ _ i) in b.
       exact b. Qed.

Lemma natplusminus m n k : k==m+n -> k-n==m.
Proof. intros ? ? ? i. rewrite i. apply plusminusnmm. Defined.

(* Lemma minusSS m n : m > n -> S (m - S n) == m - n. *)
(* Proof. intros ? ? i. *)
(*        assert (t := natminusminus m (S n) (natgthtogehsn _ _ i)). *)
(*        set (k := m - S n). *)
(*        rewrite (idpath _ : m - S n == k) in t. *)
(*        admit. Qed. *)

Definition nat_tree : Tree.
Proof. refine (make nat nat_dist _ _ _ _ _).
       { intro m.
         induction m. { reflexivity. } { rewrite nat_dist_S. assumption. } }
       { apply nat_dist_anti. }
       { apply nat_dist_symm. } 
       { apply nat_dist_trans. }
       { intros m n e.
         assert (d := natneqchoice _ _ e). clear e.
         destruct d as [h|h].
         { exists (S n).
           { split.
             { apply nat_dist_gt. exact h. }
             { destruct (natgthorleh (S n) n) as [_|j].
               { clear h. induction n. { reflexivity. } { apply IHn. } } 
               { apply fromempty. clear h. exact (j (natgthsnn n)). }}} }
         { exists (n - 1).
           { split.
             { admit. }
             { unfold nat_dist,hz.hzabsvalint; simpl.
               destruct (natgthorleh (n - 1) n) as [i|j].
               { apply fromempty; clear h. exact (natminuslehn n 1 i). }
               { clear j. admit. }}} } }
Defined.                      

(*
Local Variables:
compile-command: "make -C ../.. TAGS Packages/Ktheory/MetricTree.vo"
End:
*)
