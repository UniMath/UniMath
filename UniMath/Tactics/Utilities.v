(** Author: Michael A. Warren (maw@mawarren.net).*)
(** Date: Spring 2015.*)
(** Description: Some helper tactics.*)
Unset Automatic Introduction.

(** Imports *)

Require Import UniMath.Foundations.PartD
               UniMath.Foundations.Propositions
               UniMath.Foundations.Sets.

Arguments tpair {_ _} _ _.

(** We introduce the notation ap for maponpaths as in KTheory. *)

Module Export Notation.
  Notation ap := maponpaths.
  Notation "p # x" := (transportf _ p x) (right associativity, at level 65) : transport.
  Open Scope transport.
  Notation "{ x : X & P }" := (total2 (λ x:X, P)) : type_scope.
  Notation "X ** Y" := (X × Y) (right associativity, at level 80) : type_scope.
End Notation.

Definition neq (X : UU) : X -> X -> hProp
  := λ x y : X, hProppair (x != y) (isapropneg (x = y)).

Ltac check_cons f g :=
  let h T :=
      f T; g T
  in
  h.

Ltac id_check T := idtac.

Ltac make_hyp_check e :=
  let T0 := type of e in
  let f T :=
      match T with
        | T0 => fail 1
        | _ => idtac
      end
  in f.

(** In some cases we may need to obtain the current left-hand side of a goal equation (it may have been rewritten since initially being passed in via a match clause and a subsequent match on the new state should be performed.  E.g., in matched_rewrite below.*)
Ltac get_current_lhs :=
  match goal with
    | |- ?lhs = ?rhs => lhs
  end.

Ltac get_current_rhs :=
  match goal with
    | |- ?lhs = ?rhs => rhs
  end.

Ltac get_current_lhs_in H :=
  let T := type of H in
  match T with
    | ?lhs = ?rhs => lhs
  end.

Ltac get_current_rhs_in H :=
  let T := type of H in
  match T with
    | ?lhs = ?rhs => rhs
  end.

Ltac matched_rewrite e :=
  match type of e with
    | ?l = ?r =>
      let lhs := get_current_lhs in
      match lhs with
        | context [l] => rewrite e
        | context [r] => rewrite <- e
      end
  end.
