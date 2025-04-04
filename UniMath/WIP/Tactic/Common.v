Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.

(** Executes a function for all terms of a list, until the function returns something *)
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

Ltac2 Notation "pn:" p(pattern) : 0 := p.

Ltac2 unfold_local0 (v : (ident * Std.occurrences) list) (c : Std.clause option) :=
  Std.unfold (List.map (fun (a, b) => (Std.VarRef a, b)) v) (default_on_concl c).

Ltac2 Notation "unfold_local" v(list1(seq(ident, occurrences), ",")) cl(opt(clause))
  := unfold_local0 v cl.
