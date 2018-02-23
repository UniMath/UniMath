(** Author: Michael A. Warren.*)
(** Date: Spring 2015.*)
(** Description: Some tactics for abelian monoids.*)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.Tactics.Utilities
               UniMath.Tactics.Monoids_Tactics.

(** * I. Definitions.*)

(** Because rewrite seems to have handling the two scopes multmonoid and addmonoid, the following definitions are for arbitrary commutative operations.*)

Definition isabsemigrop {X : hSet} (opp : binop X) :=
  (isassoc opp) ** (iscomm opp).

Definition abmonoid_to_absemigr (M : abmonoid) : isabsemigrop (@op M) :=
  dirprodpair (@assocax M) (@commax M).

Definition absemigr_perm021 :
  ∏ X : hSet, ∏ opp : binop X, ∏ is : isabsemigrop opp,
  ∏ n0 n1 n2,
    opp (opp n0 n1) n2 = opp (opp n0 n2) n1 :=
  λ X opp is n0 n1 n2,
    pathscomp0
      (pathscomp0
         ((pr1 is) n0 n1 n2)
         (maponpaths (λ z, opp n0 z) ((pr2 is) n1 n2)))
      (pathsinv0 ((pr1 is) n0 n2 n1)).

Definition abmonoid_perm021 :=
  λ M : abmonoid, absemigr_perm021 M (@op M) (abmonoid_to_absemigr M).

Definition absemigr_perm102 :
  ∏ X : hSet, ∏ opp : binop X, ∏ is : isabsemigrop opp,
  ∏ n0 n1 n2,
    opp (opp n0 n1) n2 = opp (opp n1 n0) n2 :=
  λ X opp is n0 n1 n2, maponpaths (λ z, opp z n2) ((pr2 is) n0 n1).

Definition abmonoid_perm102 :=
  λ M : abmonoid, absemigr_perm102 M (@op M) (abmonoid_to_absemigr M).

Definition absemigr_perm120 :
  ∏ X : hSet, ∏ opp : binop X, ∏ is : isabsemigrop opp,
  ∏ n0 n1 n2,
    opp (opp n0 n1) n2 = opp (opp n2 n0) n1 :=
  λ X opp is n0 n1 n2,
    pathscomp0 ((pr2 is) (opp n0 n1) n2) (pathsinv0 ((pr1 is) n2 n0 n1)).

Definition abmonoid_perm120 :=
  λ M : abmonoid, absemigr_perm120 M (@op M) (abmonoid_to_absemigr M).

Definition absemigr_perm201 :
  ∏ X : hSet, ∏ opp : binop X, ∏ is : isabsemigrop opp,
  ∏ n0 n1 n2,
    opp (opp n0 n1) n2 = opp (opp n1 n2) n0 :=
  λ X opp is n0 n1 n2,
    pathscomp0 ((pr1 is) n0 n1 n2) ((pr2 is) n0 (opp n1 n2)).

Definition abmonoid_perm201 :=
  λ M : abmonoid, absemigr_perm201 M (@op M) (abmonoid_to_absemigr M).

Definition absemigr_perm210 :
  ∏ X : hSet, ∏ opp : binop X, ∏ is : isabsemigrop opp,
  ∏ n0 n1 n2,
    opp (opp n0 n1) n2 = opp (opp n2 n1) n0 :=
  λ X opp is n0 n1 n2,
    pathscomp0 (absemigr_perm102 X opp is n0 n1 n2)
               (absemigr_perm120 X opp is n1 n0 n2).

Definition abmonoid_perm210 :=
  λ M : abmonoid, absemigr_perm210 M (@op M) (abmonoid_to_absemigr M).

(** * II. Tactics for rearranging words.*)

(** We employ the following naming conventions.  By default a tactics given pertain only to equations and operate by default on the left-hand side of equations.  Those that operate on both left- and right-hand sides of the goal are suffixed with [_goal].  Tactics that operate on the left-hand side of equations occurring as hypotheses are suffixed with [_in].  Those that operate on both left- and right-hand sides of equations occurring as hypotheses are suffixed with [_both_in].  Those that opexrate on all sides of goals and hypotheses are suffixed with [_all].*)

(** TODO: More general version.*)
Ltac absemigr_ternary_perm X opp is s t u :=
  let f := eval hnf in opp in
      match goal with
        | |- ?lhs = ?rhs =>
          match lhs with
            | context[f (f t s) u] =>
              rewrite (absemigr_perm102 X f is t s u); idtac
            | context[f (f t u) s] =>
              rewrite (absemigr_perm120 X f is t u s); idtac
            | context[f (f u s) t] =>
              rewrite (absemigr_perm201 X f is u s t); idtac
            | context[f (f u t) s] =>
              rewrite (absemigr_perm210 X f is u t s); idtac
            | context[f (f s u) t] =>
              rewrite (absemigr_perm021 X f is s u t); idtac
            | context[f (f (f ?x t) s) u] =>
              rewrite (pr1 is x t s); rewrite (pr1 is x (f t s) u);
              rewrite (absemigr_perm102 X f is t s u);
              rewrite <- (pr1 is x (f s t) u);
              rewrite <- (pr1 is x s t); idtac
            | context[f (f (f ?x t) u) s] =>
              rewrite (pr1 is x t u); rewrite (pr1 is x (f t u) s);
              rewrite (absemigr_perm120 X f is t u s);
              rewrite <- (pr1 is x (f s t) u);
              rewrite <- (pr1 is x s t); idtac
            | context[f (f (f ?x u) s) t] =>
              rewrite (pr1 is x u s); rewrite (pr1 is x (f u s) t);
              rewrite (absemigr_perm201 X f is u s t);
              rewrite <- (pr1 is x (f s t) u);
              rewrite <- (pr1 is x s t); idtac
            | context[f (f (f ?x u) t) s] =>
              rewrite (pr1 is x u t); rewrite (pr1 is x (f u t) s);
              rewrite (absemigr_perm210 X f is u t s);
              rewrite <- (pr1 is x (f s t) u);
              rewrite <- (pr1 is x s t); idtac
            | context[f (f (f ?x s) u) t] =>
              rewrite (pr1 is x s u); rewrite (pr1 is x (f s u) t);
              rewrite (absemigr_perm021 X f is s u t);
              rewrite <- (pr1 is x (f s t) u);
              rewrite <- (pr1 is x s t); idtac
          end
      end.

Ltac abmonoid_ternary_perm M :=
  absemigr_ternary_perm M (@op M) (abmonoid_to_absemigr M).

Open Scope addmonoid.

Ltac abmonoid_not_word M s :=
  match s with
    | ?x + ?y => fail 1
    | _ => idtac
  end.

Ltac abmonoid_not_at_front M t s :=
  match t with
    | s => fail 1
    | context[s + ?x] => fail 1
    | _ => idtac
  end.

Ltac abmonoid_not_at_back M t s :=
  match t with
    | s => fail 1
    | ?x + s => fail 1
    | _ => idtac
  end.

Ltac abmonoid_move_to_back M s :=
  repeat
    let lhs := get_current_lhs in
    abmonoid_not_at_back M lhs s;
      match lhs with
        | s + ?x => rewrite (commax M s x)
        | context[?x + s + ?y] =>
          rewrite (abmonoid_perm021 M x s y)
        | context[s + ?x + ?y] =>
          rewrite (abmonoid_perm201 M s x y)
      end.

Ltac abmonoid_move_to_back_in M H s :=
  repeat
    let lhs := get_current_lhs_in H in
    abmonoid_not_at_back M lhs s;
      match lhs with
        | s + ?x => rewrite (commax M s x) in H
        | context[?x + s + ?y] =>
          rewrite (abmonoid_perm021 M x s y) in H
        | context[s + ?x + ?y] =>
          rewrite (abmonoid_perm201 M s x y) in H
      end.

Ltac abmonoid_move_to_front M s :=
  repeat
    let lhs := get_current_lhs in
    abmonoid_not_at_front M lhs s;
      match lhs with
        | context[?x + s] =>
          abmonoid_not_word M x; rewrite (commax M x s)
        | context[?x + ?y + s] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x y s)
      end.

Ltac abmonoid_move_to_front_in M H s :=
  repeat
    let lhs := get_current_lhs_in H in
    abmonoid_not_at_front M lhs s;
      match lhs with
        | context[?x + s] =>
          abmonoid_not_word M x; rewrite (commax M x s) in H
        | context[?x + ?y + s] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x y s) in H
      end.

Ltac abmonoid_move_to_front_goal M s :=
  repeat
    let rhs := get_current_rhs in
    abmonoid_not_at_front M rhs s;
      match rhs with
        | context[?x + s] =>
          abmonoid_not_word M x; rewrite (commax M x s)
        | context[?x + ?y + s] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x y s)
      end.

Ltac abmonoid_move_to_front_both_in M H s :=
  repeat
    let rhs := get_current_rhs_in H in
    abmonoid_not_at_front M rhs s;
      match rhs with
        | context[?x + s] =>
          abmonoid_not_word M x; rewrite (commax M x s) in H
        | context[?x + ?y + s] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x y s) in H
      end.

Ltac abmonoid_move_to_back_goal M s :=
  repeat
    let rhs := get_current_rhs in
    abmonoid_not_at_back M rhs s;
      match rhs with
        | context [s + ?x] => rewrite (commax M s x)
        | context[?x + s + ?y] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x s y)
        | context[s + ?x + ?y] =>
          abmonoid_not_word M x; abmonoid_not_word M y;
          rewrite (abmonoid_perm201 M s x y)
      end.

Ltac abmonoid_move_to_back_both_in M H s :=
  repeat
    let rhs := get_current_rhs_in H in
    abmonoid_not_at_back M rhs s;
      match rhs with
        | context [s + ?x] => rewrite (commax M s x)
        | context[?x + s + ?y] => abmonoid_not_word M y;
            rewrite (abmonoid_perm021 M x s y) in H
        | context[s + ?x + ?y] =>
          abmonoid_not_word M x; abmonoid_not_word M y;
          rewrite (abmonoid_perm201 M s x y) in H
      end.

Ltac abmonoid_group M s t :=
  abmonoid_move_to_front M t; abmonoid_move_to_front M s.

Ltac abmonoid_group_goal M s t :=
  abmonoid_move_to_front_goal M t; abmonoid_move_to_front_goal M s.

Ltac abmonoid_group_in M H s t :=
  abmonoid_move_to_front_in M H t; abmonoid_move_to_front_in M H s.

Ltac abmonoid_group_both_in M H s t :=
  abmonoid_move_to_front_both_in M H t; abmonoid_move_to_front_both_in M H s.

Ltac abmonoid_group_all M s t :=
  abmonoid_group_goal M s t;
  repeat
    match goal with
      | H : _ |- _ => abmonoid_group_both_in M H s t
    end.


(** t is a term of type M and abmonoid_group_as attempts to reorganize the lhs of the goal to include as a subterm t.*)
Ltac abmonoid_group_as M t :=
  match t with
    | ?x + ?y =>
      abmonoid_not_word M y; abmonoid_move_to_front M y;
      abmonoid_group_as M x
    | ?x => abmonoid_not_word M x; abmonoid_move_to_front M x
  end.

(** t is a term of type x = y for x, y : M and abmonoid_group_from attempts to reogranize the lhs of the goal to include as a subterm x.*)
Ltac abmonoid_group_from M t :=
  let T := type of t in
  match T with
    | ?lhs = ?rhs => abmonoid_group_as M lhs
  end.

Ltac abmonoid_op_strip M :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context [?x] =>
          match rhs with
            | context [x] => abmonoid_move_to_back_goal M x;
                apply (ap (λ v, v + x))
          end
      end
  end.

Ltac abmonoid_zap_body M f :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | rhs => apply idpath
        | 0 => apply pathsinv0; abmonoid_zap_body M f
        | ?x + ?y =>
          match rhs with
            | y + x => apply (commax M x y)
          end
        | _ => (abmonoid_op_strip M; abmonoid_zap_body M f)
      end
    | E : ?l = ?r |- ?lhs = ?rhs => f E;
        let g := make_hyp_check E in
        let h := check_cons g f in
        abmonoid_group_from M E; matched_rewrite E; abmonoid_zap_body M h
  end.

Ltac abmonoid_zap M := monoid_clean_all M; abmonoid_zap_body M id_check.

(** * TESTS *)
(*
Unset Ltac Debug.

Section Tests.
  Hypothesis M : abmonoid.

  Hypothesis x y z u v w : M.

  Lemma test_abmonoid_zap_1 (is : w = v): x + (y + w) = x + (v + y).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_2 (is : w = v):  x + (y + w) = v + (x + y).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_3 (t : x + (y + (u + z)) = (v + w) + u) :
    (((x + y) + z) + u) + w = v + (w + (u + w)).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_4 (t : x + (u + (z + y)) = (u + w) + v) :
    (((x + y) + z) + u) + w = (w + (u + w)) + v.
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_5 (t : x + ((u + z) + y) = (v + w) + u) :
    ((x + (y + z)) + u) + w = v + (w + (u + w)).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_6 (t : x + (y + (z + u)) = (v + w) + u) :
    ((u + (z + y)) + x) + w = w + (u + (w + v)).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_monoid_zap_7 : x + y + x = x + x + y.
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Lemma test_abmonoid_zap_8 (t : x + y = y + x) (i : z + x = @unel M) :
    x + (y + z) = y + (x + z).
  Proof.
    intros. abmonoid_zap M.
  Qed.

  Close Scope addmonoid.
End Tests.
*)
