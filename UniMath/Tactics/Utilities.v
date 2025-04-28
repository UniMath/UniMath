(**

  Tactic Utilities and Helper Tactics

  This file introduces some miscellaneous tactics and tactic parts.

  Contents
  1. Ltac1 utilities
  2. Ltac2 utilities

  Initially written in 2015 by Michael A. Warren

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.

(** * 1. Ltac1 utilities *)

Set Default Proof Mode "Classic".

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
  := λ x y : X, make_hProp (x != y) (isapropneg (x = y)).

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

(** In some cases we may need to obtain the current left-hand side of a goal equation (it may have
  been rewritten since initially being passed in via a match clause and a subsequent match on the
  new state should be performed.  E.g., in matched_rewrite below.*)
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

(** * 2. Ltac2 utilities *)

Set Default Proof Mode "Ltac2".

(** Executes `f` for all elements of `l`, until it returns something *)
Ltac2 rec iterate_until
  (f : 'a -> 'a list -> 'b option)
  (l : 'a list)
  : 'b option
  := match l with
  | []     => None
  | x :: l => match f x l with
    | Some y => Some y
    | None   => iterate_until f l
    end
  end.

(** Executes `f`, and if it returns a value, recurses with that value *)
Ltac2 rec repeat_while
  (f : 'a -> ('a option))
  (t : 'a)
  : unit
  :=
  match f t with
  | Some t' => repeat_while f t'
  | None => ()
  end.

(** Fails with an arbitrary return type, because the `fail` tactic is only of type `unit -> unit` *)
Ltac2 failv0 () : 'a := zero (Tactic_failure None).
Ltac2 Notation "failv" := failv0 ().

(** Executes a tactic. Returns its result if it succeeds and `None` if not. *)
Ltac2 try_opt (f : unit -> 'a) : 'a option :=
  once_plus
    (fun () => Some (f ()))
    (fun _ => None).

(** Notation for defining a value of the pattern type, like `pn:((_ = _) → _)` *)
Ltac2 Notation "pn:" p(pattern) : 0 := p.

(** Unfolds locally (via `pose` or `set`) defined identifiers, because the current Ltac2 unfold
  does not allow this yet (April, 2025) *)
Ltac2 unfold_local0 (v : (ident * Std.occurrences) list) (c : Std.clause option) :=
  Std.unfold (List.map (fun (a, b) => (Std.VarRef a, b)) v) (default_on_concl c).

Ltac2 Notation "unfold_local" v(list1(seq(ident, occurrences), ",")) cl(opt(clause))
  := unfold_local0 v cl.
