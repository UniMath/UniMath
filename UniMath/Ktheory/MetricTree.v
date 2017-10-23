(* -*- coding: utf-8 *)

(** * Metric trees *)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.Foundations.NaturalNumbers
               UniMath.Foundations.UnivalenceAxiom
               UniMath.CategoryTheory.total2_paths
               UniMath.Ktheory.Utilities.
Unset Automatic Introduction.

(** ** Definitions *)

Record Tree :=
  make {
      mt_set:> Type;
      mt_dist: mt_set -> mt_set -> nat;
      mt_refl: ∏ x, mt_dist x x = 0;
      mt_anti: ∏ x y, mt_dist x y = 0 -> x = y;
      mt_symm: ∏ x y, mt_dist x y = mt_dist y x;
      mt_trans: ∏ x y z, mt_dist x z <= mt_dist x y + mt_dist y z;
      mt_step: ∏ x z, x != z ->
                      ∑ y, (S (mt_dist x y) = mt_dist x z) × (mt_dist y z = 1)
    }.

Lemma mt_path_refl (T:Tree) (x y:T) : x = y -> mt_dist _ x y = 0.
Proof. intros ? ? ? e. destruct e. apply mt_refl. Qed.

Lemma tree_deceq (T:Tree) : isdeceq T.
Proof. intros. intros t u. induction (isdeceqnat (mt_dist T t u) 0) as [a|b].
       { apply inl. apply mt_anti. assumption. }
       { apply inr. intro e. apply b. destruct e. apply mt_refl. } Qed.

Corollary tree_isaset (T:Tree) : isaset T.
Proof. intros. apply isasetifdeceq. apply tree_deceq. Qed.

Definition step (T:Tree) {x z:T} (ne:x != z) : T := pr1 (mt_step _ x z ne).

Definition tree_induction (T:Tree) (x:T) (P:T->Type)
           (p0 : P x)
           (pn : ∏ z (ne:x != z), P (step T ne) -> P z) :
  ∏ z, P z.
Proof. intros ? ? ? ? ?.
       assert(d_ind : ∏ n z, mt_dist _ x z = n -> P z).
       { intros ?.
         induction n as [|n IH].
         { intros. assert (k:x=z).
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

Require Import UniMath.Ktheory.Nat.
        Import UniMath.Ktheory.Nat.Discern.

Definition nat_tree : Tree.
Proof. refine (make nat nat_dist _ _ _ _ _).
       { intro m. induction m as [|m IHm]. { reflexivity. } { rewrite nat_dist_S. assumption. } }
       { apply nat_dist_anti. } { apply nat_dist_symm. }
       { apply nat_dist_trans. }
       { intros m n e. assert (d := natneqchoice _ _ (neg_to_negProp e)). clear e.
         destruct d as [h|h].
         { exists (S n).
           { split.
             { apply nat_dist_gt. exact h. }
             { destruct (natgthorleh (S n) n) as [_|j].
               { clear h. induction n as [|n IHn]. { reflexivity. } { apply IHn. } }
               { apply fromempty. clear h. contradicts j (negnatSleh n). }}} }
         { exists (n - 1).
           { split.
             { assert (a := natltminus1 m n h). assert (b := natlthtoleh m n h).
               assert (c := nat_dist_le _ _ a). assert (d := nat_dist_le _ _ b).
               rewrite c, d; clear c d. rewrite natminusminusassoc. simpl.
               change (1 + (n - (1+m)) = n - m). rewrite (natpluscomm 1 m).
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
compile-command: "make -C ../.. TAGS UniMath/Ktheory/MetricTree.vo"
End:
*)
