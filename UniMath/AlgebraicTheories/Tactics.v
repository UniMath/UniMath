Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Convert different proofs to a proof about hlevels *)
Local Ltac convert_to_hlevel :=
  match goal with
  | [ |- isofhlevel _ _ ] => idtac
  | [ |- iscontr _ ] => refine (_ : isofhlevel 0 _)
  | [ |- isaprop _ ] => refine (_ : isofhlevel 1 _)
  | [ |- isaset _ ] => refine (_ : isofhlevel 2 _)
  | _ => fail
  end.

(* Reduce the different possible constructions *)
Local Ltac progress_hlevel :=
  match goal with
  | [ |- isofhlevel ?n        (_ = _)  ] => refine ((_ : isofhlevel (S n) _) _ _)
  | [ |- isofhlevel 1         (_ ⨿ _)  ] =>
    refine (isapropcoprod _ _ (_ : isofhlevel _ _) (_ : isofhlevel _ _) _)
  | [ |- isofhlevel (S (S _)) (_ ⨿ _)  ] => apply isofhlevelssncoprod
  | [ |- isofhlevel _         (_ × _)  ] => apply isofhleveldirprod
  | [ |- isofhlevel _         (∑ _, _) ] => (apply isofhleveltotal2; [ | intro ])
  | [ |- isofhlevel _         (_ → _)  ] => apply impredfun
  | [ |- isofhlevel _         (∏ _, _) ] => (apply impred; intro)
  end.

(* Try to close the goal in one of the standard ways *)
Local Ltac finish :=
  match goal with
  | [ |- isofhlevel 0 _ ] => apply iscontrunit
  | [ |- isofhlevel 1 _ ] => apply propproperty
  | [ |- isofhlevel 2 _ ] => apply setproperty
  | _ =>
    apply isofhlevel_HLevel ||
    apply hlevelntosn; finish
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
