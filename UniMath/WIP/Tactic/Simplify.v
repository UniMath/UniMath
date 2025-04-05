Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Notations.

Require Import Foundations.PartA.
Require Import Common.

(**
  A traversal consists of
  - A pattern `p`, describing the goal `p = _` where the traversal activates;
  - A term `t` describing the step `refine '(maponpaths t _)`;
  - Strings `l` and `r` such that the string `λ x, l x r` is `t`.
*)
Ltac2 Type rec t_traversal := {
  c : unit -> constr;
  s : (string * string);
  t : (t_traversal list) option
}.

Ltac2 make_traversal (c : unit -> constr) (l : string) (r : string)
  : t_traversal
  := {c := c; s := (l, r); t := None}.

(**
  A rewrite consists of
  - A pattern `p`, describing the goal `p = _` where the rewrite activates;
  - A term `t` of an identity type, describing the rewrite;
  - A string representation of `t`.
*)
Ltac2 Type t_rewrite := (pattern * (unit -> constr) * string).

(**
  While traversing, the `navigation`, deconstructed as `(l, r, (pr, in, po))`, gives the contextual
  information for printing rewrites:
    `refine (pr (λ x, ` + (join "(" reverse(l)) + ` x ` + (join ")" r) + `) in (_) po)`
  For example: `maponpaths (λ x, _ ∧ (x ~ _)) (_) @ _` or `transportf (λ x, (x ∨ _) ⊢ _) (_) _`.
*)
Ltac2 Type navigation := {
  left: string list;
  right: string list;
  preinpostfix: (string * string * string)
}.

(** Adds a new step on the inside of the navigation *)
Ltac2 append_navigation
  (n : navigation)
  ((l, r) : string * string)
  : navigation
  := {n with
    left := (l :: n.(left));
    right := (r :: n.(right));
  }.

(** Prints a rewrite with navigation n and identity t (in its string representation) *)
Ltac2 print_refine (n : navigation) (t : string) :=
  let (prefix, infix, postfix) := n.(preinpostfix) in
  Message.print (Message.of_string (
    String.concat "" [
      prefix ;
      "(λ x, " ;
      String.concat "(" (List.rev (n.(left))) ;
      "x" ;
      String.concat ")" (n.(right)) ;
      ")" ;
      infix ;
      "(" ;
      t ;
      ")" ;
      postfix
    ]
  )).

Ltac2 traverse_subterm
  (traverse : (t_traversal list) option -> navigation -> (t_traversal list) option)
  (n : navigation)
  (t : t_traversal)
  (l : t_traversal list)
  : (t_traversal list) option
  := try_opt (fun () =>
      let c := t.(c) () in
      refine '(maponpaths $c _);
      focus 2 2 (fun () =>
        Option.get_bt (Option.map
          (fun (x : t_traversal list) => ({t with t := Some x}) :: l)
          (traverse (t.(t)) (append_navigation n (t.(s)))))
      )
    ).

(**
  At each subterm of the left hand side of the goal, executes `preorder`, then recurses, and then
  executes `postorder`. If either preorder or postorder returns true, stops executing and returns
  the remaining traversals at each level.
*)
Ltac2 rec traverse
  (traversals : t_traversal list)
  (preorder :  navigation -> bool)
  (postorder : navigation -> bool)
  (first_traversals : (t_traversal list) option)
  (n : navigation)
  : (t_traversal list) option
  := if preorder n then Some traversals else
    match iterate_until
      (traverse_subterm (traverse traversals preorder postorder) n)
      (Option.default traversals first_traversals)
    with
    | Some x => Some x
    | _ => if postorder n then Some [] else None
    end.

(** Tries to rewrite any subterm of the left hand side of the goal, from the top level downwards *)
Ltac2 simplify_component
  (traversals : t_traversal list)
  (rewrites : t_rewrite list)
  : (t_traversal list) option -> navigation -> (t_traversal list) option
  := traverse
      traversals
      (fun n => List.fold_left (fun b (p, c, t) =>
          if b then true else
            match (try_opt (fun () =>
              match! goal with
              | [ |- $pattern:p = _ ] =>
                refine (c ());
                print_refine n t
              end
            )) with
            | Some _ => true
            | None => false
            end
        ) false rewrites
      )
      (fun _ => false).

(**
  Uses `top_traversals` to get a goal of the form `[term] = _`, and tries to repeatedly rewrite the
  highest rewritable subterm of the left hand side of that goal.
*)
Ltac2 simplify
  (traversals : t_traversal list)
  (rewrites : (int * t_rewrite) list)
  (top_traversals : ((unit -> unit) * navigation) list)
  (rewrite_level : int option)
  : unit
  :=
  let filtered_rewrites :=
    List.map
      (fun (_, r) => r)
      (match rewrite_level with
      | None => rewrites
      | Some n =>
        (List.filter
          (fun (i, _) => Int.le i n)
          rewrites)
      end) in
  List.iter (fun (m, n) =>
    try (
      m ();
      focus 2 2 (fun () =>
        repeat_while
        (fun (l : t_traversal list) =>
          try_opt (fun () =>
            refine '(_ @ _);
            focus 2 2 (fun () => Option.get_bt (simplify_component traversals filtered_rewrites (Some l) n))
          )
        )
        traversals;
        reflexivity
      )
    )
  ) top_traversals.
