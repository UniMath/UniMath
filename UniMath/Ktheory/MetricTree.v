(* -*- coding: utf-8 *)

(** * Metric trees *)

Unset Automatic Introduction.
Require Import algebra1b hnat funextfun pathnotations auxiliary_lemmas_HoTT Ktheory.Utilities.
Import PathNotations Utilities.Notation Utilities.NatNotation.

(** ** Definitions *)

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

Definition step (T:Tree) {x z:T} (ne:x!=z) : T := pr1 (mt_step _ x z ne).

Definition tree_induction (T:Tree) (x:T) (P:T->Type)
           (p0 : P x)
           (pn : forall z (ne:x!=z), P (step T ne) -> P z) :
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

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/MetricTree.vo"
End:
*)
