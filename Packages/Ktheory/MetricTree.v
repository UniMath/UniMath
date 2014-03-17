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
      mt_step: forall x z, x!=z -> iscontr
                 (total2 (fun y => dirprod 
                                     (S (mt_dist x y) == mt_dist x z)
                                     (mt_dist y z == 1))) }.
      
Lemma mt_path_refl (T:Tree) (x y:T) : x==y -> mt_dist _ x y == 0.
Proof. intros ? ? ? e. destruct e. apply mt_refl. Qed.

Lemma tree_deceq (T:Tree) : isdeceq T.
Proof. intros. intros t u. induction (isdeceqnat (mt_dist T t u) 0).
       { apply inl. apply mt_anti. assumption. }
       { apply inr. intro e. apply b. destruct e. apply mt_refl. } Qed.

Corollary tree_isaset (T:Tree) : isaset T.
Proof. intros. apply isasetifdeceq. apply tree_deceq. Qed.

Definition step (T:Tree) (x z:T) (ne:x!=z) : T := pr1 (the (mt_step _ x z ne)).

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
             destruct y as [[y [i j]] r]; simpl.
             apply invmaponpathsS. exact (i@H). } } }
       intro. apply (d_ind (mt_dist _ x z)). reflexivity. Defined.

Definition nat_dist : nat -> nat -> nat.
Proof. intros m n. exact ((m-n)+(n-m)). Defined.

Definition nat_dist_S m n : nat_dist (S m) (S n) == nat_dist m n.
Proof. reflexivity. Defined.

Lemma plusmn0n0 m n : m + n == 0 -> n == 0.
Proof. intros ? ? i. assert (a := natlehmplusnm m n). rewrite i in a.
       apply natleh0tois0. assumption. Qed.

Lemma plusmn0m0 m n : m + n == 0 -> m == 0.
Proof. intros ? ? i. assert (a := natlehnplusnm m n). rewrite i in a.
       apply natleh0tois0. assumption. Qed.

Lemma natminus0le {m n} : m-n == 0 -> n >= m.
Proof. intros ? ? i j. assert (a := minusgth0 m n j); clear j.
       rewrite i in a; clear i. exact (negnatgth0n 0 a). Defined.

Definition nat_dist_anti m n : nat_dist m n == 0 -> m == n.
Proof. intros ? ? i. apply isantisymmnatgeh. 
       { apply natminus0le. 
         apply (plusmn0n0 (m-n) (n-m)). assumption. }
       { apply natminus0le. 
         apply (plusmn0m0 (m-n) (n-m)). assumption. } Qed.

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

Lemma minusSS m n : m > n -> S (m - S n) == m - n.
Proof. intros ? ? i.
       assert (t := natminusminus m (S n) (natgthtogehsn _ _ i)).
       set (k := m - S n).
       rewrite (idpath _ : m - S n == k) in t.
       admit. Qed.

Definition nat_tree : Tree.
Proof. refine (make nat nat_dist _ _ _ _ _).
       { intro m.
         induction m. { reflexivity. } { rewrite nat_dist_S. assumption. } }
       { apply nat_dist_anti. }
       { intros m n. apply natpluscomm. } 
       { admit. }
       { intros m n e.
         assert (d := natneqchoice _ _ e). clear e.
         destruct d.
         { refine ((S n,,_),,_).
           { split.
             { induction (natgthorleh m (S n)) as [i|j].
               { induction (natgthorleh m n) as [_|s].
                 { clear i. admit. }
                 { apply fromempty. clear i. apply (natgthtonegnatleh m n h s). } }
               { induction (natgthorleh m n) as [_|s].
                 { assert (u : S n == m). 
                   { assert (w := natgthtogehsn m n h); clear h.
                     apply (isantisymmnatgeh (S n) m).
                     { assumption. } { assumption. } } 
                   destruct u. clear h j. 
                   admit. }
                 { apply fromempty; clear j. apply (natgthtonegnatleh m n h s). }}}
             { destruct (natgthorleh (S n) n) as [_|j].
               { clear h. induction n. { reflexivity. } { apply IHn. } } 
               { apply fromempty. clear h. exact (j (natgthsnn n)). }}}
           { intros [k [i j]]; simpl. 
             apply pair_path_props.
             { admit. }
             intro. apply isofhleveltotal2.
             { apply isasetnat. }
             { intro t. apply isasetnat. } } }
         { refine ((n - 1,,_),,_).
           { split.
             { admit. }
             { unfold nat_dist,hz.hzabsvalint; simpl.
               destruct (natgthorleh (n - 1) n) as [i|j].
               { apply fromempty; clear h. exact (natminuslehn n 1 i). }
               { clear j. admit. }}}
           { intros [k [i j]]; simpl. 
             apply pair_path_props.
             { admit. }
             intro. apply isofhleveltotal2.
             { apply isasetnat. }
             { intro t. apply isasetnat. } } } }
Defined.                      

(*
Local Variables:
compile-command: "make -C ../.. TAGS Packages/Ktheory/MetricTree.vo"
End:
*)
