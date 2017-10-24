(** Author: Michael A. Warren (maw@mawarren.net) in consultation with Vladimir Voevodsky.*)
(** Date: Spring - Summer 2015.*)
(** Description: Some tactics for natural numbers. *)

(** Tactics for natural numbers.*)
(** by Michael A. Warren, April - June 2015.*)

(** ADD: Disclaimer regarding connection with other tactics files.*)

Unset Automatic Introduction.

Require Import
        UniMath.Foundations.NaturalNumbers
        UniMath.Tactics.Utilities
        UniMath.Tactics.Abmonoids_Tactics.

Local Open Scope nat_scope.

(** * Basic definitions and hints. *)

Definition natneqtwist n (p : ¬ (0 = n)) : ¬ (n = 0) :=
  λ f, p (pathsinv0 f).

Definition nat_plus_perm021 :
  ∏ n0 n1 n2,
    n0 + n1 + n2 = n0 + n2 + n1 :=
  λ n0 n1 n2,
    pathscomp0
      (pathscomp0
         (natplusassoc n0 n1 n2)
         (maponpaths (λ z, n0 + z) (natpluscomm n1 n2)))
      (pathsinv0 (natplusassoc n0 n2 n1)).

Definition nat_plus_perm102 :
  ∏ n0 n1 n2,
    n0 + n1 + n2 = n1 + n0 + n2 :=
  λ n0 n1 n2, maponpaths (λ z, z + n2) (natpluscomm n0 n1).

Definition nat_plus_perm120 :
  ∏ n0 n1 n2,
    n0 + n1 + n2 = n2 + n0 + n1 :=
  λ n0 n1 n2,
    pathscomp0 (natpluscomm (n0 + n1) n2) (pathsinv0 (natplusassoc n2 n0 n1)).

Definition nat_plus_perm201 :
  ∏ n0 n1 n2,
    n0 + n1 + n2 = n1 + n2 + n0 :=
  λ n0 n1 n2,
    pathscomp0 (natplusassoc n0 n1 n2) (natpluscomm n0 (n1 + n2)).

Definition nat_plus_perm210 :
  ∏ n0 n1 n2,
    n0 + n1 + n2 = n2 + n1 + n0 :=
  λ n0 n1 n2,
    pathscomp0 (nat_plus_perm102 n0 n1 n2) (nat_plus_perm120 n1 n0 n2).

Definition nat_mult_perm021 :
  ∏ n0 n1 n2,
    n0 * n1 * n2 = n0 * n2 * n1 :=
  λ n0 n1 n2,
    pathscomp0
      (pathscomp0
         (natmultassoc n0 n1 n2)
         (maponpaths (λ z, n0 * z) (natmultcomm n1 n2)))
      (pathsinv0 (natmultassoc n0 n2 n1)).

Definition nat_mult_perm102 :
  ∏ n0 n1 n2,
    n0 * n1 * n2 = n1 * n0 * n2 :=
  λ n0 n1 n2, maponpaths (λ z, z * n2) (natmultcomm n0 n1).

Definition nat_mult_perm120 :
  ∏ n0 n1 n2,
    n0 * n1 * n2 = n2 * n0 * n1 :=
  λ n0 n1 n2,
    pathscomp0 (natmultcomm (n0 * n1) n2) (pathsinv0 (natmultassoc n2 n0 n1)).

Definition nat_mult_perm201 :
  ∏ n0 n1 n2,
    n0 * n1 * n2 = n1 * n2 * n0 :=
  λ n0 n1 n2,
    pathscomp0 (natmultassoc n0 n1 n2) (natmultcomm n0 (n1 * n2)).

Definition nat_mult_perm210 :
  ∏ n0 n1 n2,
    n0 * n1 * n2 = n2 * n1 * n0 :=
  λ n0 n1 n2,
    pathscomp0 (nat_mult_perm102 n0 n1 n2) (nat_mult_perm120 n1 n0 n2).

Definition minus0r : ∏ n, n - 0 = n :=
  λ n, match n with
             | 0 => (idpath _)
             | S _ => (idpath _)
           end.

Definition minusnn0 n : n - n = 0.
Proof.
  intro n. induction n as [|n IHn]; [exact (idpath 0) | exact IHn].
Defined.

(** minus0l and Lemma minussn1 n : (S n) - 1 change to n - 0 should be changed in tactics.*)

Definition minusgeh n m : n >= (n - m).
Proof.
  intro n. induction n as [|n IHn]; intros. apply isreflnatgeh.
  destruct m. rewrite minus0r. apply isreflnatgeh.
  apply (istransnatgeh _ n _). apply natgthtogeh. apply natgthsnn.
  apply IHn.
Defined.

(** * Tactics for rearranging subterms of goals and hypotheses.*)

(** ** Tactics for performing ternary permutations of words written in [+] and [*].*)

(** TACTIC: [nat_plus_ternary_perm]

    SUMMARY: [nat_plus_ternary_perm] permutes words of length 3 in [+].

    USAGE: Provided that the current [goal] is of the form [lhs = rhs], [nat_plus_ternary_perm x y z] will permute a subterm of [lhs] so that it now appears in the form [x + y + z].

    EXAMPLE: If the current goal is [x + y + z = y + z + x], then [nat_plus_ternary_perm y z x] will change the goal to [y + z + x = y + z + x].*)
Ltac nat_plus_ternary_perm s t u :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context[t + s + u] =>
          rewrite (nat_plus_perm102 t s u); idtac
        | context[t + u + s] =>
          rewrite (nat_plus_perm120 t u s); idtac
        | context[u + s + t] =>
          rewrite (nat_plus_perm201 u s t); idtac
        | context[u + t + s] =>
          rewrite (nat_plus_perm210 u t s); idtac
        | context[s + u + t] =>
          rewrite (nat_plus_perm021 s u t); idtac
        | context[?x + t + s + u] =>
          rewrite (natplusassoc x t s); rewrite (natplusassoc x (t + s) u);
          rewrite (nat_plus_perm102 t s u);
          rewrite <- (natplusassoc x (s + t) u);
          rewrite <- (natplusassoc x s t); idtac
        | context[?x + t + u + s] =>
          rewrite (natplusassoc x t u); rewrite (natplusassoc x (t + u) s);
          rewrite (nat_plus_perm120 t u s);
          rewrite <- (natplusassoc x (s + t) u);
          rewrite <- (natplusassoc x s t); idtac
        | context[?x + u + s + t] =>
          rewrite (natplusassoc x u s); rewrite (natplusassoc x (u + s) t);
          rewrite (nat_plus_perm201 u s t);
          rewrite <- (natplusassoc x (s + t) u);
          rewrite <- (natplusassoc x s t); idtac
        | context[?x + u + t + s] =>
          rewrite (natplusassoc x u t); rewrite (natplusassoc x (u + t) s);
          rewrite (nat_plus_perm210 u t s);
          rewrite <- (natplusassoc x (s + t) u);
          rewrite <- (natplusassoc x s t); idtac
        | context[?x + s + u + t] =>
          rewrite (natplusassoc x s u); rewrite (natplusassoc x (s + u) t);
          rewrite (nat_plus_perm021 s u t);
          rewrite <- (natplusassoc x (s + t) u);
          rewrite <- (natplusassoc x s t); idtac
      end
  end.

(** TACTIC: [nat_mult_ternary_perm]

    SUMMARY: [nat_mult_ternary_perm] permutes words of length 3 in [*].

    USAGE: See [nat_plus_ternary_perm] above.*)
Ltac nat_mult_ternary_perm s t u :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context[t * s * u] =>
          rewrite (nat_mult_perm102 t s u); idtac
        | context[t * u * s] =>
          rewrite (nat_mult_perm120 t u s); idtac
        | context[u * s * t] =>
          rewrite (nat_mult_perm201 u s t); idtac
        | context[u * t * s] =>
          rewrite (nat_mult_perm210 u t s); idtac
        | context[s * u * t] =>
          rewrite (nat_mult_perm021 s u t); idtac
        | context[?x * t * s * u] =>
          rewrite (natmultassoc x t s); rewrite (natmultassoc x (t * s) u);
          rewrite (nat_mult_perm102 t s u);
          rewrite <- (natmultassoc x (s * t) u);
          rewrite <- (natmultassoc x s t); idtac
        | context[?x * t * u * s] =>
          rewrite (natmultassoc x t u); rewrite (natmultassoc x (t * u) s);
          rewrite (nat_mult_perm120 t u s);
          rewrite <- (natmultassoc x (s * t) u);
          rewrite <- (natmultassoc x s t); idtac
        | context[?x * u * s * t] =>
          rewrite (natmultassoc x u s); rewrite (natmultassoc x (u * s) t);
          rewrite (nat_mult_perm201 u s t);
          rewrite <- (natmultassoc x (s * t) u);
          rewrite <- (natmultassoc x s t); idtac
        | context[?x * u * t * s] =>
          rewrite (natmultassoc x u t); rewrite (natmultassoc x (u * t) s);
          rewrite (nat_mult_perm210 u t s);
          rewrite <- (natmultassoc x (s * t) u);
          rewrite <- (natmultassoc x s t); idtac
        | context[?x * s * u * t] =>
          rewrite (natmultassoc x s u); rewrite (natmultassoc x (s * u) t);
          rewrite (nat_mult_perm021 s u t);
          rewrite <- (natmultassoc x (s * t) u);
          rewrite <- (natmultassoc x s t); idtac
      end
  end.


(** ** Tactics for grouping pairs of terms appearing in words written in [+] and [*].*)

(** *** Helper tactics (which should not be considered as part of the public interface for these tactics).*)

Ltac nat_plus_not_word s :=
  match s with
    | ?x + ?y => fail 1
    | _ => idtac
  end.

Ltac nat_plus_not_at_front t s :=
  match t with
    | s => fail 1
    | context[s + ?x] => fail 1
    | _ => idtac
  end.

Ltac nat_plus_not_at_back t s :=
  match t with
    | s => fail 1 "A"
    | ?x + s => fail 1 "B"
    | _ => idtac
  end.

Ltac nat_plus_move_to_back s :=
  repeat
    let lhs := get_current_lhs in
    nat_plus_not_at_back lhs s;
      match lhs with
        | s + ?x => rewrite (natpluscomm s x)
        | context[?x + s + ?y] =>
          rewrite (nat_plus_perm021 x s y)
        | context[s + ?x + ?y] =>
          rewrite (nat_plus_perm201 s x y)
      end.

Ltac nat_plus_move_to_back_in H s :=
  repeat
    let lhs := get_current_lhs_in H in
    nat_plus_not_at_back lhs s;
      match lhs with
        | s + ?x => rewrite (natpluscomm s x) in H
        | context[?x + s + ?y] =>
          rewrite (nat_plus_perm021 x s y) in H
        | context[s + ?x + ?y] =>
          rewrite (nat_plus_perm201 s x y) in H
      end.

Ltac nat_plus_move_to_front s :=
  repeat
    let lhs := get_current_lhs in
    nat_plus_not_at_front lhs s;
      match lhs with
        | context[?x + s] =>
          nat_plus_not_word x; rewrite (natpluscomm x s)
        | context[?x + ?y + s] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x y s)
      end.

Ltac nat_plus_move_to_front_in H s :=
  repeat
    let lhs := get_current_lhs_in H in
    nat_plus_not_at_front lhs s;
      match lhs with
        | context[?x + s] =>
          nat_plus_not_word x; rewrite (natpluscomm x s) in H
        | context[?x + ?y + s] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x y s) in H
      end.

Ltac nat_plus_move_to_front_goal s :=
  repeat
    let rhs := get_current_rhs in
    nat_plus_not_at_front rhs s;
      match rhs with
        | context[?x + s] =>
          nat_plus_not_word x; rewrite (natpluscomm x s)
        | context[?x + ?y + s] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x y s)
      end.

Ltac nat_plus_move_to_front_both_in H s :=
  repeat
    let rhs := get_current_rhs_in H in
    nat_plus_not_at_front rhs s;
      match rhs with
        | context[?x + s] =>
          nat_plus_not_word x; rewrite (natpluscomm x s) in H
        | context[?x + ?y + s] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x y s) in H
      end.

Ltac nat_plus_move_to_back_goal s :=
  repeat
    let rhs := get_current_rhs in
    nat_plus_not_at_back rhs s;
      match rhs with
        | context [s + ?x] => rewrite (natpluscomm s x)
        | context[?x + s + ?y] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x s y)
        | context[s + ?x + ?y] =>
          nat_plus_not_word x; nat_plus_not_word y;
          rewrite (nat_plus_perm201 s x y)
      end.

Ltac nat_plus_move_to_back_both_in H s :=
  repeat
    let rhs := get_current_rhs_in H in
    nat_plus_not_at_back rhs s;
      match rhs with
        | context [s + ?x] => rewrite (natpluscomm s x)
        | context[?x + s + ?y] => nat_plus_not_word y;
            rewrite (nat_plus_perm021 x s y) in H
        | context[s + ?x + ?y] =>
          nat_plus_not_word x; nat_plus_not_word y;
          rewrite (nat_plus_perm201 s x y) in H
      end.

Ltac nat_mult_not_word s :=
  match s with
    | ?x * ?y => fail 1
    | _ => idtac
  end.

Ltac nat_mult_not_at_front t s :=
  match t with
    | s => fail 1
    | context[s * ?x] => fail 1
    | _ => idtac
  end.

Ltac nat_mult_not_at_back t s :=
  match t with
    | s => fail 1 "A"
    | ?x * s => fail 1 "B"
    | _ => idtac
  end.

Ltac nat_mult_move_to_back s :=
  repeat
    let lhs := get_current_lhs in
    nat_mult_not_at_back lhs s;
      match lhs with
        | s * ?x => rewrite (natmultcomm s x)
        | context[?x * s * ?y] =>
          rewrite (nat_mult_perm021 x s y)
        | context[s * ?x * ?y] =>
          rewrite (nat_mult_perm201 s x y)
      end.

Ltac nat_mult_move_to_back_in H s :=
  repeat
    let lhs := get_current_lhs_in H in
    nat_mult_not_at_back lhs s;
      match lhs with
        | s * ?x => rewrite (natmultcomm s x) in H
        | context[?x * s * ?y] =>
          rewrite (nat_mult_perm021 x s y) in H
        | context[s * ?x * ?y] =>
          rewrite (nat_mult_perm201 s x y) in H
      end.

Ltac nat_mult_move_to_front s :=
  repeat
    let lhs := get_current_lhs in
    nat_mult_not_at_front lhs s;
      match lhs with
        | context[?x * s] =>
          nat_mult_not_word x; rewrite (natmultcomm x s)
        | context[?x * ?y * s] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x y s)
      end.

Ltac nat_mult_move_to_front_in H s :=
  repeat
    let lhs := get_current_lhs_in H in
    nat_mult_not_at_front lhs s;
      match lhs with
        | context[?x * s] =>
          nat_mult_not_word x; rewrite (natmultcomm x s) in H
        | context[?x * ?y * s] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x y s) in H
      end.

Ltac nat_mult_move_to_front_goal s :=
  repeat
    let rhs := get_current_rhs in
    nat_mult_not_at_front rhs s;
      match rhs with
        | context[?x * s] =>
          nat_mult_not_word x; rewrite (natmultcomm x s)
        | context[?x * ?y * s] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x y s)
      end.

Ltac nat_mult_move_to_front_both_in H s :=
  repeat
    let rhs := get_current_rhs_in H in
    nat_mult_not_at_front rhs s;
      match rhs with
        | context[?x * s] =>
          nat_mult_not_word x; rewrite (natmultcomm x s) in H
        | context[?x * ?y * s] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x y s) in H
      end.

Ltac nat_mult_move_to_back_goal s :=
  repeat
    let rhs := get_current_rhs in
    nat_mult_not_at_back rhs s;
      match rhs with
        | context [s * ?x] => rewrite (natmultcomm s x)
        | context[?x * s * ?y] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x s y)
        | context[s * ?x * ?y] =>
          nat_mult_not_word x; nat_mult_not_word y;
          rewrite (nat_mult_perm201 s x y)
      end.

Ltac nat_mult_move_to_back_both_in H s :=
  repeat
    let rhs := get_current_rhs_in H in
    nat_mult_not_at_back rhs s;
      match rhs with
        | context [s * ?x] => rewrite (natmultcomm s x)
        | context[?x * s * ?y] => nat_mult_not_word y;
            rewrite (nat_mult_perm021 x s y) in H
        | context[s * ?x * ?y] =>
          nat_mult_not_word x; nat_mult_not_word y;
          rewrite (nat_mult_perm201 s x y) in H
      end.

(** *** The tactics.*)

(** We employ the following naming conventions.  By default a tactics given pertain only to equations and operate by default on the left-hand side of equations.  Those that operate on both left- and right-hand sides of the goal are suffixed with [_goal].  Tactics that operate on the left-hand side of equations occurring as hypotheses are suffixed with [_in].  Those that operate on both left- and right-hand sides of equations occurring as hypotheses are suffixed with [_both_in].  Those that opexrate on all sides of goals and hypotheses are suffixeD with [_all].*)

Ltac nat_plus_group s t :=
  nat_plus_move_to_front t; nat_plus_move_to_front s.

Ltac nat_plus_group_goal s t :=
  nat_plus_move_to_front_goal t; nat_plus_move_to_front_goal s.

Ltac nat_plus_group_in H s t :=
  nat_plus_move_to_front_in H t; nat_plus_move_to_front_in H s.

Ltac nat_plus_group_both_in H s t :=
  nat_plus_move_to_front_both_in H t; nat_plus_move_to_front_both_in H s.

Ltac nat_plus_group_all s t :=
  nat_plus_group_goal s t;
  repeat
    match goal with
      | H : _ |- _ => nat_plus_group_both_in H s t
    end.

(** [t] is a term of type [nat] and [nat_plus_group_as] attempts to reorganize the [lhs] of the [goal] to include as a subterm [t].*)
Ltac nat_plus_group_as t :=
  match t with
    | ?x + ?y =>
      nat_plus_not_word y; nat_plus_move_to_front y;
      nat_plus_group_as x
    | ?x => nat_plus_not_word x; nat_plus_move_to_front x
  end.

(** t is a term of type x = y for x, y : nat and nat_plus_group_from attempts to reogranize the lhs of the goal to include as a subterm x.*)
Ltac nat_plus_group_from t :=
  let T := type of t in
  match T with
    | ?lhs = ?rhs => nat_plus_group_as lhs
  end.

Ltac nat_mult_group s t :=
  nat_mult_move_to_front t; nat_mult_move_to_front s.

Ltac nat_mult_group_goal s t :=
  nat_mult_move_to_front_goal t; nat_mult_move_to_front_goal s.

Ltac nat_mult_group_in H s t :=
  nat_mult_move_to_front_in H t; nat_mult_move_to_front_in H s.

Ltac nat_mult_group_both_in H s t :=
  nat_mult_move_to_front_both_in H t; nat_mult_move_to_front_both_in H s.

Ltac nat_mult_group_all s t :=
  nat_mult_group_goal s t;
  repeat
    match goal with
      | H : _ |- _ => nat_mult_group_both_in H s t
    end.

(** [t] is a term of type [nat] and [nat_mult_group_as] attempts to reorganize the [lhs] of the [goal] to include as a subterm [t].*)
Ltac nat_mult_group_as t :=
  match t with
    | ?x + ?y =>
      nat_mult_not_word y; nat_mult_move_to_front y;
      nat_mult_group_as x
    | ?x => nat_mult_not_word x; nat_mult_move_to_front x
  end.

(** [t] is a term of type [x = y] for [x y : nat] and [nat_mult_group_from] attempts to reogranize the [lhs] of the [goal] to include as a subterm [x].*)
Ltac nat_mult_group_from t :=
  let T := type of t in
  match T with
    | ?lhs = ?rhs => nat_mult_group_as lhs
  end.


(** * Tactics pertaining to inequalities.*)

(** ** Preprocessing of the ambient goal and hypotheses.*)

(** *** Helper tactics (which should not be considered as part of the public interface for these tactics).*)
Ltac does_not_have_gth x y :=
  match goal with
    | _ : hProptoType (x > y) |- _ => fail 1
    | |- _ => idtac
  end.

Ltac does_not_have_geh x y :=
  match goal with
    | _ : hProptoType (x >= y) |- _ => fail 1
    | |- _ => idtac
  end.

(** It is convenient to have to only work with either [hzgth]/[hzgeh] or [hzlth]/[hzleh].  We choose the former and the following tactics replace instances of [hzlth]/[hzleh] with the corresponding inequalities involving [hzgth]/[hzgeh].*)
Ltac reverse_lth :=
  repeat
    match goal with
      | H : hProptoType (?y < ?u) |- _ =>
        does_not_have_gth u y; assert (natgth u y); [apply H | ]
    end.

Ltac reverse_leh :=
  repeat
    match goal with
      | H : hProptoType (?y <= ?u) |- _ =>
        does_not_have_geh u y; assert (natgeh u y); [apply H | ]
    end.

Ltac gth_to_geh :=
  repeat
    match goal with
      | H : hProptoType (?x > ?y) |- _ =>
        does_not_have_geh x y; assert (natgeh x y);
        [apply natgthtogeh; assumption |]
    end.

(** Clean the hypotheses in preparation for searching.*)
Ltac nat_dfs_clean := reverse_lth; reverse_leh; gth_to_geh.

(** ** Tactics for solving inequalities involving natural numbers.*)

(** *** Tactics for solving very simple inequalities using known lemmas.*)

(** The following tactic allows immediate solution of common goals involving [natgth] provided that the appropriate hypotheses are available.  We probably want to eventually add additional "hints" here.*)
Ltac natgth_simple :=
  match goal with
    | _ : hProptoType (?x > ?y) |- hProptoType (?x > ?y) => assumption
    | P : hProptoType ((S ?x) > (S ?y)) |- hProptoType (?x > ?y) => apply P
    | |- hProptoType ((S ?x) > ?x) => apply (natgthsnn x)
    | |- hProptoType ((S ?x) > 0) => apply (natgthsn0 x)
    | P : hProptoType (?x > ?y) |- hProptoType ((S ?x) > (S ?y)) => apply P
    | P : hProptoType (?x ≠ 0)%nat |- hProptoType (?x > 0) =>
      apply (natneq0togth0 x P)
    | P : hProptoType (0 ≠ ?x)%nat |- hProptoType (?x > 0) =>
      apply (natneq0togth0 x (natneqtwist x P))
    | P : (?x = 0) -> empty |- hProptoType (?x > 0) =>
      apply (natneq0togth0 x P)
    | P : (0 = ?x) -> empty |- hProptoType (?x > 0) =>
      apply (natneq0togth0 x (natneqtwist x P))
    | |- hProptoType ((S ?x) > ?x) => apply (natgthsnn x)
    | P : hProptoType (?x > ?y) |- hProptoType ((S ?x) > ?y) =>
      apply (natgthtogths x y P)
    | P : hProptoType (?x >= ?y) |- hProptoType ((S ?x) > ?y) =>
      apply (natgehtogthsn x y P)
    | P : hProptoType (?x > ?y),
          Q : hProptoType (?y > ?z) |- hProptoType (?x > ?z) =>
      apply (istransnatgth x y z P Q)
    | P : hProptoType (?x > ?y),
          Q : hProptoType (?y >= ?z) |- hProptoType (?x > ?z) =>
      apply (natgthgehtrans x y z P Q)
    | P : hProptoType (?x >= ?y),
          Q : hProptoType (?y > ?z) |- hProptoType (?x > ?z) =>
      apply (natgehgthtrans x y z P Q)
  end.

Ltac natgeh_simple :=
  match goal with
    | _ : hProptoType (?x >= ?y) |- hProptoType (?x >= ?y) => assumption
    | P : hProptoType (?x >= ?y) |- hProptoType ((S ?x) >= (S ?y)) => apply P
    | P : hProptoType ((S ?x) >= (S ?y)) |- hProptoType (?x >= ?y) =>
      apply P
    | |- hProptoType (?x >= ?x) => apply isreflnatgeh
    | |- hProptoType (?x >= 0) => apply natgehn0
    | |- hProptoType ((S ?x) >= ?x) => apply (natgehsnn x)
    | |- hProptoType (?x >= ?x - ?y) => apply (minusgeh x y)
    | H : hProptoType (?x > ?y) |- hProptoType (?x >= ?y) =>
      apply (natgthtogeh x y H)
    | P : hProptoType (?x >= ?y),
          Q : hProptoType (?y >= ?z) |- hProptoType (?x >= ?z) =>
      apply (istransnatgeh x y z P Q)
    | P : hProptoType ((S ?x) > ?y) |- hProptoType (?x >= ?y) =>
      apply (natgthsntogeh x y P)
  end.

(** *** General tactics for solving inequalities by depth-first search.*)

(** The approach taken here for solving inequalities is to construct from the given collection of hypotheses HH a corresponding directed graph and then to perform a depth-first search of the graph.*)

(** Although we will often employ our search method in order to traverse an acyclic graph, when we are proving that the hypotheses imply [empty] we are forced to consider the cyclic case.  In these cases it may be possible to become trapped in a cycle.  To prevent this from happening we must build helper functions that will allow us to check that the next goal we move to is not one we have previously considered.*)
Ltac make_gth_check x y :=
  let f T :=
      match T with
        | hProptoType (x > y) => fail 1
        | _ => idtac
      end
  in f.

Ltac make_geh_check x y :=
  let f T :=
      match T with
        | hProptoType (x >= y) => fail 1
        | _ => idtac
      end
  in f.

(** Perform depth first search of the graph corresponding to the hypotheses.  In standard continuation passing style we allow a helper ltac function [f] which is admitted to perform certain checks (or which can be ignored as in nat_dfs below).*)

(** TODO: Try instead change.  Think about strengthening clauses.*)
Ltac nat_dfs_body f :=
  natgth_simple
    || natgeh_simple
    || match goal with
         | |- hProptoType (?x < ?y) =>
           let X := fresh "X" in
           assert (natgth y x) as X; [nat_dfs_body f | apply X]
         | |- hProptoType (?x <= ?y) =>
           let X := fresh "X" in
           assert (natgeh y x) as X; [nat_dfs_body f | apply X]
         | _ : hProptoType (?u > ?y) |- hProptoType (?x > ?y) =>
           f (hProptoType (x >= u));
             let g := make_geh_check x u in
             let h := check_cons g f in
             apply (natgehgthtrans x u y); [nat_dfs_body h | assumption]
         | |- hProptoType (?x >= ?y) => f (hProptoType(x >= y));
             let g := make_geh_check x y in
             let h := check_cons g f in
             apply (natgthtogeh x y); nat_dfs_body h
         | _ : hProptoType (?u >= ?y) |- hProptoType (?x >= ?y) =>
           f (hProptoType (x >= u));
             let g := make_geh_check x u in
             let h := check_cons g f in
             apply (istransnatgeh x u y); [nat_dfs_body h | assumption]
         | _ : hProptoType (?x >= ?u) |- hProptoType (?x > ?y) =>
           f (hProptoType (u > y));
             let g := make_gth_check u y in
             let h := check_cons g f in
             apply (natgehgthtrans x u y); [assumption | nat_dfs_body h]
         | _ : hProptoType (?u >= ?y) |- hProptoType (?x > ?y) =>
           f (hProptoType (x > u));
             let g := make_gth_check x u in
             let h := check_cons g f in
             apply (natgthgehtrans x u y); [nat_dfs_body h | assumption]
         | |- hProptoType (?x >= S ?y) =>
           apply natgthtogehsn; nat_dfs_body f
         | |- hProptoType ((S ?x) > ?y) =>
           let g := make_geh_check x y in
           let h := check_cons g f in
           (apply (natgthgehtrans _ x _); [apply natlthnsn | nat_dfs_body h])

         | |- hProptoType (?x > ?y - ?z) =>
           let g := make_gth_check x (y - z) in
           let h := check_cons g f in
           apply (natgthgehtrans x y (y - z));
             [nat_dfs_body h | apply minusgeh]
       end.

Ltac nat_dfs := nat_dfs_clean; nat_dfs_body id_check.

(** * Tactics for deriving contradictions.*)
Ltac nat_eq_contr :=
  let f X := assert empty; [apply X; assumption | contradiction] in
  let i X := assert empty; [apply X; apply idpath | contradiction] in
  match goal with
    | H : ?x = ?y -> empty, _ : ?x = ?y |- _ => f H
    | H : neg (?x = ?y), _ : ?x = ?y |- _ => f H
    | H : ?x = ?x -> empty |- _ => i H
    | H : neg (?x = ?x) |- _ => i H
    | H : hProptoType (?x ≠ ?y)%nat, _ : ?x = ?y |- _ => f H
    | H : hProptoType (?x ≠ ?x)%nat |- _ => i H
    | H : hProptoType (?x ≠ ?y)%nat, _ : ?x = ?y |- _ => f H
    | H : hProptoType (?x ≠ ?x)%nat |- _ => i H
  end.

Ltac nat_simple_contr :=
  assert empty; [
    match goal with
      | H : hProptoType (?x < 0) |- _ => exact (negnatlthn0 x H)
      | H : hProptoType (0 > ?x) |- _ => exact (negnatgth0n x H)
      | H : hProptoType ((S ?x) <= 0) |- _ => exact (negnatlehsn0 x H)
      | H : hProptoType (0 >= (S ?x)) |- _ => exact (negnatgeh0sn x H)
      | H : S ?x = 0 |- _ => exact (negpathssx0 x H)
    end | contradiction].

(** Note that the following tactic may not halt. SHOULD halt now.*)
Ltac nat_ineq_contr_isirrefl :=
  nat_dfs_clean;
  assert empty; [
    match goal with
      | _ : hProptoType (?x > ?x) |- _ => apply (isirreflnatgth x); assumption
      | N : nat |- _ =>
        let f := make_gth_check N N in
        apply (isirreflnatgth N); nat_dfs_body ltac:(f)
    end
  | contradiction].

Ltac nat_absurd :=
  (nat_simple_contr || nat_eq_contr || nat_ineq_contr_isirrefl).

Ltac nat_preclean_1 :=
  repeat
    match goal with
      | |- context [0 - ?n] => change (0 - n) with 0
      | |- context [(S ?n) - 1] => change ((S n) - 1) with (n - 0)
      | |- context[S ?x - S ?y] => change (S x - S y) with (x - y)
    end.

Ltac nat_preclean_2 :=
  repeat rewrite multsnm; repeat rewrite multnsm;
  repeat rewrite natldistr; repeat rewrite natrdistr;
  repeat rewrite natmultn0; repeat rewrite natmult0n;
  repeat rewrite natplusl0; repeat rewrite natplusr0;
  repeat rewrite natminuseqn; repeat rewrite natmultl1;
  repeat rewrite natmultr1; repeat rewrite <- natplusassoc;
  repeat rewrite <- natmultassoc; repeat rewrite minus0r;
  repeat rewrite minusnn0.

Ltac nat_clean := nat_preclean_1; nat_preclean_2.

Ltac nat_preclean_1_in H :=
  repeat
    let T := type of H in
    match T with
      | context [0 - ?n] => change (0 - n) with 0 in H
      | context [(S ?n) - 1] => change ((S n) - 1) with (n - 0) in H
      | context[S ?x - S ?y] => change (S x - S y) with (x - y) in H
    end.

Ltac nat_preclean_2_in H :=
  repeat rewrite multsnm in H; repeat rewrite multnsm in H;
  repeat rewrite natldistr in H; repeat rewrite natrdistr in H;
  repeat rewrite natmultn0 in H; repeat rewrite natmult0n in H;
  repeat rewrite natplusl0 in H; repeat rewrite natplusr0 in H;
  repeat rewrite natminuseqn in H; repeat rewrite natmultl1 in H;
  repeat rewrite natmultr1 in H; repeat rewrite <- natplusassoc in H;
  repeat rewrite <- natmultassoc in H; repeat rewrite minus0r in H;
  repeat rewrite minusnn0 in H.

Ltac nat_clean_in H := nat_preclean_1_in H; nat_preclean_2_in H.

Ltac nat_clean_all :=
  nat_clean;
  repeat
    match goal with
      | H : _ |- _ => nat_clean_in H
    end.

(** * Several somewhat devious experimental tactics.*)

Ltac nat_devious_ineq :=
  match goal with
    | |- hProptoType (?x > ?y) =>
      destruct (natgthorleh x y); [assumption | nat_absurd]
    | |- hProptoType (?x >= ?y) =>
      destruct (natlthorgeh x y); [nat_absurd | assumption]
    | |- hProptoType (?x < ?y) =>
      destruct (natlthorgeh x y); [assumption | nat_absurd]
    | |- hProptoType (?x <= ?y) =>
      destruct (natgthorleh x y); [nat_absurd | assumption]
  end.

(** * Tactics for solving equations.*)

(** ** Helper tactics.*)
Ltac make_check T :=
  let f S :=
      match S with
        | T => fail 1
      end
  in f.

Ltac nat_plus_strip :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context [?x] =>
          match rhs with
            | context [x] => nat_plus_move_to_back_goal x;
                apply (ap (λ v, v + x))
          end
      end
  end.

Ltac nat_mult_strip :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context [?x] =>
          match rhs with
            | context [x] => nat_mult_move_to_back_goal x;
                apply (ap (λ v, v * x))
          end
      end
  end.

(** ** Some simple solver tactics which are concerned exclusively with equations involving _only_ [+] or _only_ [*].*)
Ltac nat_plus_prezap_body f :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | rhs => apply idpath
        | 0 => apply pathsinv0; nat_plus_prezap_body f
        | ?x + ?y =>
          match rhs with
            | y + x => apply (natpluscomm x y)
          end
        | _ => (nat_plus_strip; nat_plus_prezap_body f)
      end
    | E : ?l = ?r |- ?lhs = ?rhs => f E;
        let g := make_hyp_check E in
        let h := check_cons g f in
        nat_plus_group_from E; matched_rewrite E; nat_plus_prezap_body h
  end.

Ltac nat_plus_prezap := nat_clean_all; nat_plus_prezap_body id_check.

Ltac nat_mult_prezap_body f :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | rhs => apply idpath
        | 0 => apply pathsinv0; nat_mult_prezap_body f
        | ?x * ?y =>
          match rhs with
            | y * x => apply (natmultcomm x y)
          end
        | _ => (nat_mult_strip; nat_mult_prezap_body f)
      end
    | E : ?l = ?r |- ?lhs = ?rhs => f E;
        let g := make_hyp_check E in
        let h := check_cons g f in
        nat_mult_group_from E; matched_rewrite E; nat_mult_prezap_body h
  end.

Ltac nat_mult_prezap := nat_clean_all; nat_mult_prezap_body id_check.

(** ** A simple solver tactic for mixed [+] [*] equations.*)

Ltac nat_plus_zap_body f :=
  match goal with
    | |- ?lhs = ?rhs =>
      match rhs with
        | ?x + ?y => nat_plus_not_word y;
            match lhs with
              | ?u + ?v =>
                (nat_plus_not_word v;
                 let F := fresh in
                 assert (v = y) as F;
                 [ nat_mult_prezap
                 | rewrite F; apply (ap (λ v, v + y));
                   nat_plus_zap_body f
                 ])
                  || (let l := get_current_lhs in
                      let g := make_check l in
                      let h := check_cons f g in
                      nat_plus_move_to_front v; nat_plus_zap_body h)
            end
        | ?x => nat_plus_not_word x;
            match lhs with
              | ?v => nat_plus_not_word v; nat_mult_prezap
            end
      end
  end.

Ltac nat_plus_zap := nat_plus_zap_body id_check.

(** * Combined tactics for solving equations and inequalities of natural numbers.*)

Ltac nat_simple :=
  match goal with
    | H : hProptoType (?n <= 0) |- ?n = 0 => apply (natleh0tois0 n H)
    | H : hProptoType (0 >= ?n) |- ?n = 0 => apply (nat0gehtois0 n H)
    | H : hProptoType (?n <= 0) |- 0 = ?n =>
      apply pathsinv0; apply (natleh0tois0 n H)
    | H : hProptoType (0 >= ?n) |- 0 = ?n =>
      apply pathsinv0; apply (nat0gehtois0 n H)
    | |- ?x + ?y = ?y + ?x => apply natpluscomm
  end.

Ltac nat_intros :=
  repeat match goal with
           | |- ?x -> ?y => intro
           | |- ∏ _, _ => intro
         end.

Ltac nat_try :=
  repeat
    match goal with
      | H : _ |- _ =>
        let T := type of H in
        match T with
          | nat => fail 1
          | _ => idtac "About to try " H; apply H
        end
    end.

Ltac nat_basic_destruct N := destruct N; nat_intros; nat_clean;
                             (auto || assumption || nat_simple || nat_absurd
                                   || nat_dfs ).

Ltac nat_basic_induction N := induction N; nat_intros; nat_clean;
                              (auto || assumption || nat_simple || nat_absurd
                                    || nat_dfs || nat_try ).

Ltac nat_zap :=
  nat_clean_all;
  try (auto || assumption || nat_simple || nat_absurd || nat_dfs
            || nat_plus_zap || nat_try);
  match goal with
    | N : nat |- _ =>
      nat_basic_destruct N || nat_basic_induction N
  end.

Close Scope nat_scope.
(** * TESTS *)
(*
Unset Ltac Debug.

Section Tests.
  Open Scope nat_scope.

  Hypothesis x y z u v w x' y' z' u' v' w' : nat.

  (** Note that [nat_devious_ineq] also correctly solves all of the tests designed for [nat_dfs].*)

  Lemma test_nat_dfs_0 (i1 : natgth x y) (i2 : natgeh y z)
        (i3 : natgth z u) (i4 : natgeh u v) (i5 : natgeh v w) : natgth x w.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_1 (i1 : natgth x y) (i2 : natgth y z)
        (i3 : natlth u z) (i4 : natgth w u) (i5 : natgth z x') : natgth x x'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_2 (i1 : natgth x y) (i2 : natlth z y)
        (i3 : natgth u z) : natgth x z.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_3 (i1 : natgth x y) (i2 : natlth z y)
        (i3 : natlth z u) : natgth x z.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_4 (i1 : natgth x y) (i2 : natgth y z)
        (i3 : natlth z u) (i4 : natlth v z) (i5 : natgth v x')
        (i6 : natlth v w) (i7 : natlth z' x') (i8 : natlth u' z')
        (i9 : natgth u y') : natgth x u'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_5 (i1 : natlth x y) (i2 : natlth y z)
        (i3 : natgth z u) (i4 : natgth v z) (i5 : natlth v x')
        (i6 : natgth v w) (i7 : natgth z' x') (i8 : natgth u' z')
        (i9 : natlth u y') : natlth x u'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_6 (i1 : natgeh x y) (i2 : natgth y z)
        (i3 : natleh z u) (i4 : natlth v z) (i5 : natgth v x')
        (i6 : natleh v w) (i7 : natlth z' x') (i8 : natlth u' z')
        (i9 : natgeh u y') : natgeh x u'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_7 (i1 : natleh x y) (i2 : natlth y z)
        (i3 : natgeh z u) (i4 : natgth v z) (i5 : natlth v x')
        (i6 : natgeh v w) (i7 : natgth z' x') (i8 : natgth u' z')
        (i9 : natleh u y') : natleh x u'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_8 (i1 : natleh x y) (i2 : natlth y z)
        (i3 : natgeh z u) (i4 : natgth v z) (i5 : natlth v x')
        (i6 : natgeh v w) (i7 : natgth z' x') (i8 : natgth u' z')
        (i9 : natleh u y') : natleh x u'.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_10 (i1 : x ≠ 0)%nat (i2 : natgeh x 0) :
    natgth x 0.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_11 (i2 : 0 ≠ x)%nat (i2 : natgeh x 0) :
    natgth x 0.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_12 (i1 : 0 = x -> empty) (i2 : natgeh x 0) :
    natgth x 0.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_dfs_13 (i : natleh y x) (l : natgth y x) : natlth x x.
  Proof.
    intros. nat_dfs.
  Qed.

  Lemma test_nat_absurd_1 (i : natleh x y) (j : natgth x (S z))
        (k : natleh y z) : natgth u v.
  Proof.
    intros. nat_absurd.
  Qed.

  Lemma test_nat_absurd_2 (i : natlth x y) (j : natgeh x (S z))
        (k : natlth y z) : natgth u v.
  Proof.
    intros. nat_absurd.
  Qed.

  Lemma test_nat_absurd_3 x y z u v w (i1 : natgth x y) (i2 : natgeh y z)
        (i3 : natgth z u) (i4 : natgeh u v) (i5 : natgeh v w)
        (i6 : natgeh w x) : natgth x w.
  Proof.
    intros. nat_absurd.
  Qed.

  Lemma test_nat_absurd_4 (i1 : natgth x y) (i2 : natlth z y)
        (i3 : natgth u z) (i4 : natleh x z ) : natgth x z.
  Proof.
    intros. nat_absurd.
  Qed.

  Lemma test_nat_plus_ternary_perm  n m k l : n + m + k + l = l + m + n + k.
  Proof.
    intros. nat_plus_ternary_perm l m k. nat_plus_ternary_perm l m n.
    apply idpath.
  Qed.

  Lemma test_nat_mult_ternary_perm  n m k l : n * m * k * l = k * l * n * m.
  Proof.
    intros. nat_mult_ternary_perm k n m. nat_mult_ternary_perm l n m.
    apply idpath.
  Qed.

  Lemma test_nat_plus_group n m k l : n + m + k + l = k + n + m + l.
  Proof.
    intros. nat_plus_group k n. apply idpath.
  Qed.

  Lemma test_nat_mult_group n m k l : n * m * k * l = k * n * m * l.
  Proof.
    intros. nat_mult_group k n. apply idpath.
  Qed.

  Close Scope nat_scope.

End Tests.
 *)
