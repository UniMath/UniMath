(** Author: Michael A. Warren.*)
(** Date: Spring 2015.*)
(** Description: Some tactics for monoids.*)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.Tactics.Utilities.

Ltac op_strip f :=
  repeat
    match goal with
      | |- f ?x ?y = f ?x ?z =>
        apply (ap (λ v, f x v))
      | |- f ?y ?x = f ?z ?x =>
        apply (ap (λ v, f v x))
  end.

Ltac assocop_clean M f :=
  repeat rewrite <- (assocax M).

Ltac assocop_clean_in M f t :=
  repeat rewrite <- (assocax M) in t.

Ltac assocop_clean_all M f :=
  assocop_clean M f;
  repeat
    match goal with
      | H : context[f ?x (f ?y ?z)] |- _ => assocop_clean_in M f H
    end.

Ltac assocop_trivial M f :=
  try (assocop_clean_all M f; op_strip f; apply idpath).

Ltac assocop_group_in M f x s t :=
  let T := type of x in
  match T with
    | context[f s t] => idtac
    | context [f (f ?u s) t] => rewrite (assocax M u s t) in x
    | context [f s (f t ?u)] => rewrite <- (assocax M s t u) in x
  end.

Ltac assocop_group M f s t :=
  match goal with
    | |- context [f s t] => idtac
    | |- context [f (f ?u s) t] => rewrite (assocax M u s t)
    | |- context [f s (f t ?u)] => rewrite <- (assocax M s t u)
  end.

Ltac monoid_clean M :=
  repeat rewrite (lunax M); repeat rewrite (runax M); assocop_clean M (@op M).

Ltac monoid_clean_in M t :=
  repeat rewrite (lunax M) in t; repeat rewrite (runax M) in t;
  assocop_clean_in M (@op M) t.

Ltac monoid_clean_all M :=
  monoid_clean M;
  repeat
    match goal with
      | H : _ |- _ => monoid_clean_in M H
    end.

Ltac monoid_declean M :=
  repeat rewrite (assocax M).

Ltac monoid_op_strip_left M :=
  (monoid_declean M;
   match goal with
     | |- (@op M) ?x ?y = (@op M) ?x ?z =>
       apply (ap (λ v, (@op M) x v))
     | |- (?x * ?y = ?x * ?z)%multmonoid => apply (ap (λ v, x * v))%multmonoid
   end;
   monoid_clean M).

(** Some error handling should be added (e.g., to check that lhs, rhs are of type M; that they are words in M, etc.).*)
Ltac monoid_zap_body M f :=
  match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | rhs => apply idpath
        | (@unel M) => apply pathsinv0; monoid_zap_body M f
        | _ => (monoid_op_strip_left M; monoid_zap_body M f)
      end
    | E : ?l = ?r |- ?lhs = ?rhs => f E;
        let g := make_hyp_check E in
        let h := check_cons g f in
        matched_rewrite E; monoid_zap_body M h
  end.

Ltac monoid_zap M := monoid_clean_all M; monoid_zap_body M id_check.

(** * TESTS *)
(*
Unset Ltac Debug.

Section Tests.
  Open Scope multmonoid.

  Hypothesis M : monoid.

  Hypothesis x y z u v w : M.

  Lemma test_op_strip_1 (is : w = v): x * (y * w) = x * (y * v).
  Proof.
    intros. op_strip (@op M). assumption.
  Qed.

  Lemma test_assocop_clean_1 (is : w = v):  x * (y * w) = (x * y) * v.
  Proof.
    intros. assocop_clean M (@op M). op_strip (@op M). assumption.
  Qed.

  Lemma test_assocop_clean_in_1 (t : x * (y * (z * u)) = (v * w) * u) :
    (((x * y) * z) * u) * w = v * (w * (u * w)).
  Proof.
    intros. assocop_clean_in M (@op M) t. assocop_clean M (@op M).
    rewrite t. op_strip (@op M). apply idpath.
  Qed.

  Lemma test_assocop_clean_all_1 (t : x * (y * (z * u)) = (v * w) * u) :
    (((x * y) * z) * u) * w = v * (w * (u * w)).
  Proof.
    intros. assocop_clean_all M (@op M). rewrite t. op_strip (@op M).
    apply idpath.
  Qed.

  Lemma test_assocop_group_1 (t : x * (y * (z * u)) = (v * w) * u) :
    ((x * (y * z)) * u) * w = v * (w * (u * w)).
  Proof.
    intros. assocop_group_in M (@op M) t w u.
    assocop_group M (@op M) w u. assocop_group M (@op M) v (w * u).
    rewrite <- t. assocop_trivial M (@op M).
  Qed.

  Lemma test_monoid_zap_1 (t : x * (y * (z * u)) = (v * w) * u) :
    ((x * (y * z)) * u) * w = v * (w * (u * w)).
  Proof.
    intros. monoid_zap M.
  Qed.

  Lemma test_monoid_zap_2 (t : x * y = y * x) : x * y * x = x * x * y.
  Proof.
    intros. monoid_zap M.
  Qed.

  Lemma test_monoid_zap_3 (t : x * y = y * x) (i : x * z = @unel M) :
    x * (y * z) = y * (x * z).
  Proof.
    intros. monoid_zap M.
  Qed.

  Close Scope multmonoid.
End Tests.
 *)
