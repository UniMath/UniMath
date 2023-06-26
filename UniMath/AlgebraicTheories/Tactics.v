Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Lemma upgrade_isofhlevel
  (n : nat)
  : ∏ T, isofhlevel n T → isofhlevel (S n) T.
Proof.
  induction n.
  - intros T HT t t'.
    exists ((pr2 HT) _ @ !(pr2 HT) _).
    intro.
    induction t0.
    exact (!pathsinv0r _).
  - intros T HT t t'.
    apply IHn.
    apply HT.
Qed.

(* Reduce a goal about hlevels to its components *)
Ltac prove_hlevel :=
  (* Convert different proofs to a proof about hlevels *)
  match goal with
  | [ |- _ = ?a] =>
    let T := type of a in
    refine (pr1 ((_ : isofhlevel 1 T) _ _))
  | [ |- iscontr _ ] => refine (_ : isofhlevel 0 _)
  | [ |- isaprop _ ] => refine (_ : isofhlevel 1 _)
  | [ |- isaset _ ] => refine (_ : isofhlevel 2 _)
  | _ => idtac
  end;
  (* Repeatedly reduce the different possible constructions *)
  repeat match goal with
  | [ |- isofhlevel _ (_ × _) ] => apply isofhleveldirprod
  | [ |- isofhlevel _ (_ → _) ] => apply impredfun
  | [ |- isofhlevel _ (∑ _, _) ] => (apply isofhleveltotal2; [ | intro ])
  | [ |- isofhlevel _ (∏ _, _) ] => (apply impred; intro)
  | [ |- isofhlevel ?n (?a = _) ] =>
    let T := type of a in
    refine ((_ : isofhlevel (S n) T) _ _)
  | _ => progress cbn -[isofhlevel]
  end;
  (* Try to close the goal in one of the standard ways *)
  try (
    (repeat match goal with
    | [ |- isofhlevel (S (S (S _))) _ ] => apply upgrade_isofhlevel
    end);
    (
      (apply setproperty) +
      match goal with
      | [ |- isofhlevel 2 _ ] => apply upgrade_isofhlevel
      | _ => idtac
      end;
      (
        (apply propproperty) +
        (apply isapropunit)
      )
    )
  ).
