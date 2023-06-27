Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Lemma upgrade_isofhlevel
  (n : nat)
  : ∏ T, isofhlevel n T → isofhlevel (S n) T.
Proof.
  induction n.
  - intros ? HT ? ?.
    exact (isapropifcontr HT _ _).
  - intros ? HT ? ?.
    exact (IHn _ (HT _ _)).
Qed.

(* Convert different proofs to a proof about hlevels *)
Local Ltac convert_to_hlevel :=
  match goal with
  | [ |- isofhlevel _ _ ] => idtac
  | [ |- _ = _] => refine (pr1 ((_ : isofhlevel 1 _) _ _))
  | [ |- iscontr _ ] => refine (_ : isofhlevel 0 _)
  | [ |- isaprop _ ] => refine (_ : isofhlevel 1 _)
  | [ |- isaset _ ] => refine (_ : isofhlevel 2 _)
  | _ => fail
  end.

(* Reduce the different possible constructions *)
Local Ltac progress_hlevel :=
  match goal with
  | [ |- isofhlevel ?n (_ = _) ] => refine ((_ : isofhlevel (S n) _) _ _)
  | [ |- isofhlevel 1 (_ ⨿ _) ] => refine (isapropcoprod _ _ (_ : isofhlevel _ _) (_ : isofhlevel _ _) _)
  | [ |- isofhlevel (S (S _)) (_ ⨿ _) ] => apply isofhlevelssncoprod
  | [ |- isofhlevel _ (_ × _) ] => apply isofhleveldirprod
  | [ |- isofhlevel _ (∑ _, _) ] => (apply isofhleveltotal2; [ | intro ])
  | [ |- isofhlevel _ (_ → _) ] => apply impredfun
  | [ |- isofhlevel _ (∏ _, _) ] => (apply impred; intro)
  end.

Local Ltac finish_contr :=
  apply iscontrunit.

Local Ltac finish_prop :=
  (apply propproperty) +
  (apply upgrade_isofhlevel; finish_contr).

Local Ltac finish_set :=
  (apply setproperty) +
  (apply upgrade_isofhlevel; finish_prop).

(* Try to close the goal in one of the standard ways *)
Local Ltac finish :=
  match goal with
  | [ |- isofhlevel 0 _ ] => finish_contr
  | [ |- isofhlevel 1 _ ] => finish_prop
  | [ |- isofhlevel 2 _ ] => finish_set
  | [ |- isofhlevel (S (S (S _))) _ ] => apply upgrade_isofhlevel; finish
  end.

Ltac unfold_hlevel_expression :=
  refine (_ : isofhlevel _ (_ = _)) ||
  refine (_ : isofhlevel (S _) (_ ⨿ _)) ||
  refine (_ : isofhlevel _ (_ × _)) ||
  refine (_ : isofhlevel _ (∑ _, _)) ||
  refine (_ : isofhlevel _ (_ → _)) ||
  refine (_ : isofhlevel _ (∏ tmp, _)).

(* Reduce a goal about hlevels to its components *)
Ltac prove_hlevel' n :=
  convert_to_hlevel;
  repeat progress_hlevel;
  match n with
  | _ ?n' => unfold_hlevel_expression; prove_hlevel' n'
  | _ => try finish
  end.

Tactic Notation "prove_hlevel" :=
  prove_hlevel' 0.

Tactic Notation "prove_hlevel" constr(n) :=
  prove_hlevel' n.
