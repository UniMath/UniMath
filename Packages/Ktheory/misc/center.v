(* -*- coding: utf-8-unix -*- *)

Require Import Foundations.hlevel2.algebra1b.
Require Import RezkCompletion.pathnotations.
        Import RezkCompletion.pathnotations.PathNotations.

Local Notation "x '_1'" := (pr1 x) (at level 80, only parsing).
Local Notation "x '_2'" := (pr2 x) (at level 80, only parsing).

Definition isincenter {G:gr} (g:G) := forall h:G, op g h == op h g.
Lemma isaprop_isincenter {G:gr} (g:G) : isaprop(isincenter g).
Proof.
  intros.
  apply impred.
  intros h.
  apply (G _1 _1 _2).
Qed.

Definition center (G:gr)
  := (fun g:G => hProppair (isincenter g) (isaprop_isincenter g))
  : hsubtypes G.

Lemma issubgr_center (G:gr) : issubgr (center G).
Proof.
  split.
  split.
  - unfold issubsetwithbinop.
    intros [g i] [h j].
    unfold center; simpl.
    unfold isincenter.  intros k.
    (* Set Printing All. *)
    assert (r1 : op (op k g) h == op k (op g h)). admit.
    Set Printing All.
    simpl.
    unfold pr1hSet, pr1monoid in r1.
    unfold isgrop.

rewrite <- r1.              (* sigh *)
