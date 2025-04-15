(**

  A Generic Tactic for Simplification

  A tactic which can be instantiated for various theories to perform simplification:
  - The tactic uses a list of "top level traversals" to split the goal into subgoals.
  - For every subgoal, it uses a list of "traversals" to recursively traverse "suitable" subterms of
    the subgoals
  - At every step, it uses a list of "rewrites" to see if the current subterm can be rewritten into
    "something simpler".
  - After a rewrite, an equivalent rewrite statement is printed to the output and the tactic starts
    from the top of the subgoal again.

  The tactic can be used to propagate explicit substitution through a term in an untyped lambda
  calculus or propagate substitution through a formula in a (first order) hyperdoctrine.

  Contents
  1. Some supporting types and definitions [t_traversal] [t_rewrite] [navigation]
  2. The traversal tactic [traverse]
  3. The simplification tactic [simplify]

 *)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Tactics.Utilities.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Notations.

(** * 1. Some supporting types and definitions *)

(**
  A traversal consists of
  - A tactic that tries to match the goal to some pattern, and if it matches, steps into a subgoal.
  - A pair of strings, describing the left and right hand side of the goal around the subgoal.
  - An optional list of traversals that should be used for the subgoal, instead of the "standard"
    list of sugboals. This is to keep track of the state of the algorithm, and should be None at the
    start.
  For example:
    `(make_traversal (fun () => match! goal with | [|- (?a ∨ _ ) = _ ] => '(λ x, $a ∨ x ) end) "_ ∨ " "")`
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
  - A (thunked) term `t` of an identity type, describing the rewrite;
  - A string representation of `t`.
  For example:
    `(pn:((_ ∨ _)[_]), (fun () => '(disj_subst _ _ _)), "disj_subst _ _ _")`
*)
Ltac2 Type t_rewrite := (pattern * (unit -> constr) * string).

(**
  While traversing, the `navigation`, deconstructed as `(l, r, (pre, in, post))`, gives the
  contextual information for printing rewrites `rew`:
    `refine (pre (λ x, ` + (join "(" reverse(l)) + ` x ` + (join ")" r) + `) in (rew) post)`
  For example: `maponpaths (λ x, _ ∧ (x ~ _)) (_) @ _` or `transportf (λ x, (x ∨ _) ⊢ _) (_) _`.
*)
Ltac2 Type navigation := {
  left: string list;
  right: string list;
  preinpostfix: (string * string * string);
  print: bool;
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
  if n.(print) then
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
      ))
  else ().

(** * 2. The traversal tactic *)

(** Steps into a subterm, described by the traversal `t`, of the current goal. In this subterm,
  execute `traverse`, with `first_traversals` set to the list `t.(t)`.
  If the result of this is `Some x` (presumed to be the "remaining traversals" in the subterm),
  returns the remaining traversals at this level. Else, the combination of `try_opt` and
  `Option.get_bt` resets the goal to what it was at the start of the function. *)
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
  At this level, uses `first_traversals` if it has a value, and else uses `traversals`.
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

(** * 3. The simplification tactic *)

(** Tries to rewrite any subterm of the left hand side of the goal, from the top level downwards *)
Ltac2 simplify_component
  (traversals : t_traversal list)
  (rewrites : t_rewrite list)
  : (t_traversal list) option -> navigation -> (t_traversal list) option
  := traverse
      traversals
      (fun n => match
        (iterate_until
          (fun (p, c, t) _ => try_opt (fun () =>
            match! goal with
            | [ |- $pattern:p = _ ] =>
              refine (c ());
              print_refine n t
            end
          ))
          rewrites)
        with
        | Some _ => true
        | None => false
        end)
      (fun _ => false).

(**
  Uses `top_traversals` to get a goals of the form `[term] = _`, and tries to repeatedly rewrite the
  highest rewritable subterm of the left hand side of those goals.

  If `rewrite_level` is supplied, the provided rewrites are first filtered, keeping only the
  rewrites `(i, r)` where `i ≤ rewrite_level`. The rationale being that rewrites with a higher `i`
  are more rarely used, or more complex.
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
