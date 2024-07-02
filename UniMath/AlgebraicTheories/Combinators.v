(**************************************************************************************************

  λ-calculus combinators

  There is a lot of `basic' terms that are often used when working with the λ-calculus. This
  file contains definitions for some of these, as well as some lemmas about their interaction with
  substitution and with each other. The file also contains two tactics that assist in proving
  equalities of terms.

  Contents
  1. The tactics [propagate_subst] [generate_refine]
  2. Compose
  3. Pair
  4. Pair arrow
  5. Pair projections [π1] [π2]
  6. Union arrow ('match')
  7. Union injections [ι1] [ι2]
  8. Evaluation of a curried function [ev]
  9. Curry
  10. Uncurry
  11. An alternative form of curry, swapping the arguments

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Require Import Ltac2.Ltac2.

Local Open Scope vec.
Local Open Scope stn.
Local Open Scope algebraic_theories.
Local Open Scope lambda_calculus.

(** * 1. The tactics *)

Ltac2 Type state := {
  left : string list;
  right : string list;
  side : int;
}.

Ltac2 print_refine (s : state) (t : string) :=
  let (short: bool) := match s.(left), s.(right) with
    | [], [] => true
    | _, _ => false
  end in
  let (beginning, ending) := match (s.(side)), short with
    | 0, true => ("refine '(", " @ _).")
    | 0, false => ("refine '(maponpaths (λ x, ", ") @ _).")
    | _, true => ("refine '(_ @ !", ").")
    | _, false => ("refine '(_ @ !maponpaths (λ x, ", ")).")
  end in
  let navigation := match short with
    | true => []
    | false => [
        String.concat "" (List.rev (s.(left))) ;
        "x" ;
        String.concat "" (s.(right)) ;
        ") ("
      ]
  end in
  Message.print (Message.of_string (String.concat "" [
    beginning ;
    String.concat "" navigation ;
    t ;
    ending
  ])).

Ltac2 mutable traversals () : ((unit -> unit) * string * string) list := [].

Ltac2 rec traverse_left (s : state) (t : state -> unit) () :=
  t s;
  List.iter (
    fun (m, l, r) =>
    try (m () ; Control.focus 2 2 (
      traverse_left {
        s with
        left := (l :: "(" :: s.(left));
        right := (r :: ")" :: s.(right))
      } t
    ))) (List.rev (traversals ()));
  apply idpath.

Ltac2 traverse (t : state -> unit) :=
  refine '(_ @ !_);
  Control.focus 2 2 (traverse_left {
    side := 0;
    left := [];
    right := [];
  } t);
  refine '(_ @ !_);
  Control.focus 2 2 (traverse_left {
    side := 1;
    left := [];
    right := [];
  } t).

Ltac2 generate_refine' (p : pattern) (t : string) := traverse
  (fun s => match! goal with
  | [ |- $pattern:p = _] => print_refine s t
  | [ |- _ = _ ] => ()
  end).

Ltac2 Notation "generate_refine" p(pattern) := generate_refine' p.

Ltac2 mutable rewrites () : ((unit -> unit) * string) list := [].

Ltac2 propagate_subst () := repeat (progress (traverse (fun s =>
  List.iter (fun (r, t) => try (r (); print_refine s t)) (List.rev (rewrites ()))
))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- abs _ = _ ] => refine '(maponpaths abs _ @ _) end),
    "abs ",
    ""
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- app _ _ = _ ] => refine '(maponpaths (λ x, app x _) _ @ _) end),
    "app ",
    " _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- app _ _ = _ ] => refine '(maponpaths (λ x, app _ x) _ @ _) end),
    "app _ ",
    ""
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- _ • _ = _ ] => refine '(maponpaths (λ x, x • _) _ @ _) end),
    "",
    " • _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- inflate _ = _ ] => refine '(maponpaths inflate _ @ _) end),
    "inflate ",
    ""
  ) :: traversals0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (var ?a) • ?b = _] => refine '(var_subst _ $a $b)
  end), "var_subst _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (abs ?a) • ?b = _] => refine '(subst_abs _ $a $b)
  end), "subst_abs _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (app ?a ?b) • ?c = _] => refine '(subst_app _ $a $b $c)
  end), "subst_app _ _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (?a • ?b) • ?c = _] => refine '(subst_subst _ $a $b $c)
  end), "subst_subst _ _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- app (abs ?a) ?b = _] => refine '(beta_equality _ _ $a $b); assumption
  end), "beta_equality _ Lβ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate ?a • ?b = _] => refine '(subst_inflate _ $a $b)
  end), "subst_inflate _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (var ?a) = _] => refine '(inflate_var _ $a)
  end), "inflate_var _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (abs ?a) = _] => refine '(inflate_abs _ $a)
  end), "inflate_abs _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (app ?a ?b) = _] => refine '(inflate_app _ $a $b)
  end), "inflate_app _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (?a • ?b) = _] => refine '(inflate_subst _ $a $b)
  end), "inflate_subst _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- extend_tuple ?a ?b (_ (inl ?c)) = _] => refine '(extend_tuple_inl $a $b $c)
  end), "extend_tuple_inl _ _ _") :: rewrites0 ().

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- extend_tuple ?a ?b (_ (inr ?c)) = _] => refine '(extend_tuple_inr $a $b $c)
  end), "extend_tuple_inr _ _ _") :: rewrites0 ().

(** * 2. Compose *)

Definition compose
  {L : lambda_theory}
  {n : nat}
  (a b : L n)
  : L n
  := abs
    (app
      (inflate a)
      (app
        (inflate b)
        (var (stnweq (inr tt))))).

Notation "a ∘ b" :=
  (compose a b)
  (at level 40, left associativity)
  : lambda_calculus.

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- _ ∘ _ = _ ] => refine '(maponpaths (λ x, x ∘ _) _ @ _) end),
    "",
    " ∘ _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- _ ∘ _ = _ ] => refine '(maponpaths (λ x, _ ∘ x) _ @ _) end),
    "_ ∘ ",
    ""
  ) :: traversals0 ().

Lemma subst_compose
  (L : lambda_theory)
  {m n : nat}
  (a b : L m)
  (c : stn m → L n)
  : subst (a ∘ b) c = compose (subst a c) (subst b c).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (app x _))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (inflate_subst _ _ _)).
  refine '(
    maponpaths (λ x, abs (app (_ x) _)) _ @
    maponpaths (λ x, abs (app _ (app (_ x) _))) _
  );
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (?a ∘ ?b) • ?c = _] => refine '(subst_compose _ $a $b $c)
  end), "subst_compose _ _ _ _") :: rewrites0 ().

Definition inflate_compose
  (L : lambda_theory)
  {n : nat}
  (a b : L n)
  : inflate (a ∘ b) = inflate a ∘ inflate b
  := subst_compose L _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (?a ∘ ?b) = _] => refine '(inflate_compose _ $a $b)
  end), "inflate_compose _ _ _") :: rewrites0 ().

Lemma app_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (a ∘ b) c = app a (app b c).
Proof.
  refine '(_ @ (_
    : subst (app (compose (var (● 0 : stn 3)) (var (● 1 : stn 3))) (var (● 2 : stn 3))) (weqvecfun _ [(a ; b ; c)])
    = subst (app (var (● 0 : stn 3)) (app (var (● 1 : stn 3)) (var (● 2 : stn 3)))) (weqvecfun _ [(a ; b ; c)]))
  @ _).
  - refine '(_ @ !subst_app _ _ _ _).
    refine '(_ @ !maponpaths (λ x, (app x _)) (subst_compose _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (app _ x)) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (app (x ∘ _) _)) (var_subst _ _ _)).
    exact (!maponpaths (λ x, (app (_ ∘ x) _)) (var_subst _ _ _)).
  - apply (maponpaths (λ x, subst x _)).
    refine '(beta_equality _ Lβ _ _ @ _).
    refine '(subst_app _ _ _ _ @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (subst_app _ _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app x _))) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app _ x))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (extend_tuple_inl _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app x _))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app _ x))) (extend_tuple_inr _ _ _) @ _).
    exact (maponpaths (λ x, (app _ (app x _))) (extend_tuple_inl _ _ _)).
  - refine '(subst_app L (var _) _ _ @ _).
    refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (subst_app _ _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app x _))) (var_subst _ _ _) @ _).
    exact (maponpaths (λ x, (app _ (app _ x))) (var_subst _ _ _)).
Qed.

Lemma compose_abs
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L n)
  (b : L (S n))
  : a ∘ abs b = abs (app (inflate a) b).
Proof.
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_subst L b _ _) @ _).
  apply (maponpaths (λ x, abs (app _ x))).
  refine '(_ @ subst_var _ b).
  apply maponpaths.
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inr _ _ _).
Qed.

Lemma abs_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L (S n))
  (b : L n)
  : abs a ∘ b
  = abs
    (subst
      a
      (extend_tuple
        (λ i, var (stnweq (inl i)))
        (app
          (inflate b)
          (var (stnweq (inr tt)))))).
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, _ (_ • x)) (!_)).
  apply extend_tuple_eq.
  - intro i.
    refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _)).
    refine '(_ @ !var_subst _ _ _).
    exact (!extend_tuple_inl _ _ _).
  - refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _)).
    refine '(_ @ !var_subst _ _ _).
    exact (!extend_tuple_inr _ _ _).
Qed.

Lemma compose_assoc
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : a ∘ (b ∘ c) = a ∘ b ∘ c.
Proof.
  set (f := weqvecfun _ [(a ; b ; c)]).
  refine '(_ @ (_
    : subst (var (● 0 : stn 3) ∘ (var (● 1 : stn 3) ∘ var (● 2 : stn 3))) f
    = subst (var (● 0 : stn 3) ∘ var (● 1 : stn 3) ∘ var (● 2 : stn 3)) f
  ) @ _).
  - refine '(_ @ !subst_compose _ _ _ _).
    refine '(_ @ !maponpaths (λ x, (x ∘ _)) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (_ ∘ x)) (subst_compose _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (_ ∘ (x ∘ _))) (var_subst _ _ _)).
    exact (!maponpaths (λ x, (_ ∘ (_ ∘ x))) (var_subst _ _ _)).
  - apply (maponpaths (λ x, x • f)).
    refine '(maponpaths (λ x, (abs (app x _))) (inflate_var _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app x _)))) (inflate_abs _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ x))) (beta_equality _ Lβ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ x))) (subst_subst _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app x _)))) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (subst_app _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app x _)))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ x))))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (x • _) _)))) (extend_tuple_inl _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (x • _)))))) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app x _)))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app (x • _) _))))) (extend_tuple_inl _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ x))))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app x _)))) (extend_tuple_inl _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ x))))) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (extend_tuple_inl _ _ _) @ _).
    refine '(_ @ !maponpaths (λ x, (abs (app x _))) (inflate_abs _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (inflate_var _ _)).
    refine '(_ @ !maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs x)) (subst_subst _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs x)) (subst_app _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app x _))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (subst_inflate _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ x)))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app (x • _) _))) (extend_tuple_inl _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (x • _))))) (extend_tuple_inr _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app x _))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app (x • _) _)))) (extend_tuple_inl _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ x)))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app x _))) (extend_tuple_inl _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (var_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ x)))) (extend_tuple_inr _ _ _)).
    exact (!maponpaths (λ x, (abs (app _ (app x _)))) (extend_tuple_inl _ _ _)).
  - refine '(subst_compose _ (_ ∘ _) _ _ @ _).
    refine '(maponpaths (λ x, (x ∘ _)) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (_ ∘ x)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, ((x ∘ _) ∘ _)) (var_subst _ _ _) @ _).
    exact (maponpaths (λ x, ((_ ∘ x) ∘ _)) (var_subst _ _ _)).
Qed.

(** * 3. Pair *)

Definition pair
  {L : lambda_theory}
  {n : nat}
  (a b : L n)
  : L n
  := abs
    (app
      (app
        (var (stnweq (inr tt)))
        (inflate a))
      (inflate b)).

Notation "⟨ a , b ⟩" :=
  (pair a b)
  : lambda_calculus.

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- ⟨_, _⟩ = _ ] => refine '(maponpaths (λ x, ⟨x, _⟩) _ @ _) end),
    "⟨",
    ", _⟩"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- ⟨_, _⟩ = _ ] => refine '(maponpaths (λ x, ⟨_, x⟩) _ @ _) end),
    "⟨_, ",
    "⟩"
  ) :: traversals0 ().

Lemma subst_pair
  (L : lambda_theory)
  {m n : nat}
  (a b : L m)
  (c : stn m → L n)
  : subst (⟨a, b⟩) c = (⟨subst a c, subst b c⟩).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ x) _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (app (app _ x) _))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (inflate_subst _ _ _)).
  refine '(
    maponpaths (λ x, abs (app (app _ (_ x)) _)) _ @
    maponpaths (λ x, abs (app _ (_ x))) _
  );
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (⟨?a , ?b⟩) • ?c = _] => refine '(subst_pair _ $a $b $c)
  end), "subst_pair _ _ _ _") :: rewrites0 ().

Definition inflate_pair
  (L : lambda_theory)
  {n : nat}
  (a b : L n)
  : inflate (⟨a, b⟩) = ⟨inflate a, inflate b⟩
  := subst_pair _ _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (⟨?a , ?b⟩) = _] => refine '(inflate_pair _ $a $b)
  end), "inflate_pair _ _ _") :: rewrites0 ().

(** * 4. Pair arrow *)

Definition pair_arrow
  {L : lambda_theory}
  {n : nat}
  (a b : L n)
  : L n
  := abs
    (pair
      (app
        (inflate a)
        (var (stnweq (inr tt))))
      (app
        (inflate b)
        (var (stnweq (inr tt))))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- pair_arrow _ _ = _ ] => refine '(maponpaths (λ x, pair_arrow x _) _ @ _) end),
    "pair_arrow ",
    " _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- pair_arrow _ _ = _ ] => refine '(maponpaths (λ x, pair_arrow _ x) _ @ _) end),
    "pair_arrow _ ",
    ""
  ) :: traversals0 ().

Lemma subst_pair_arrow
  (L : lambda_theory)
  {m n : nat}
  (a b : L m)
  (c : stn m → L n)
  : (pair_arrow a b) • c = pair_arrow (a • c) (b • c).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨x, _⟩))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, x⟩))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app x _), _⟩))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app x _), _⟩))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (inflate_subst _ _ _)).
  refine '(maponpaths (λ x, abs (⟨ app (_ • x) _ , _ ⟩)) _ @ maponpaths (λ x, abs (⟨ _ , app (_ • x) _ ⟩)) _);
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (pair_arrow ?a ?b) • ?c = _] => refine '(subst_pair_arrow _ $a $b $c)
  end), "subst_pair_arrow _ _ _ _") :: rewrites0 ().

Definition inflate_pair_arrow
  (L : lambda_theory)
  {n : nat}
  (a b : L n)
  : inflate (pair_arrow a b) = pair_arrow (inflate a) (inflate b)
  := subst_pair_arrow _ _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (pair_arrow ?a ?b) = _] => refine '(inflate_pair_arrow _ $a $b)
  end), "inflate_pair_arrow _ _ _") :: rewrites0 ().

Lemma app_pair_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (pair_arrow a b) c = (⟨app a c, app b c⟩).
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_pair _ _ _ _ @ _).
  refine '(maponpaths (λ x, (⟨x, _⟩)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨_, x⟩)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨(app x _), _⟩)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨(app _ x), _⟩)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨_, (app x _)⟩)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨_, (app _ x)⟩)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨(app _ x), _⟩)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨_, (app _ x)⟩)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (⟨ app x c , _ ⟩)) _ @ maponpaths (λ x, (⟨ _ , app x c ⟩)) _);
    refine '(_ @ subst_var _ (_ c));
    apply maponpaths;
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Lemma pair_arrow_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : (pair_arrow a b) ∘ c = pair_arrow (a ∘ c) (b ∘ c).
Proof.
  refine '(abs_compose _ Lβ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨x, _⟩))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, x⟩))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app x _), _⟩))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app x _), _⟩))) (inflate_compose _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (inflate_compose _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨x, _⟩))) (app_compose _ Lβ _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, x⟩))) (app_compose _ Lβ _ _ _)).
  refine '(maponpaths (λ x, abs (⟨ app (_ • x) _ , _ ⟩)) _ @ maponpaths (λ x, abs (⟨ _ , app (_ • x) _ ⟩)) _);
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

(** * 5. Pair projections *)

Definition π1
  {L : lambda_theory}
  {n : nat}
  : L n
  := abs
    (app
      (var (stnweq (inr tt)))
      (abs
        (abs
          (var (stnweq (inl (stnweq (inr tt)))))))).

Lemma subst_π1
  (L : lambda_theory)
  {m n : nat}
  (t : stn m → L n)
  : subst π1 t = π1.
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs x)))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs (abs x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs (abs x))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs (abs (inflate x)))))) (extend_tuple_inr _ _ _) @ _).
  exact (maponpaths (λ x, (abs (app _ (abs (abs x))))) (inflate_var _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- π1 • ?a = _] => refine '(subst_π1 _ $a)
  end), "subst_π1 _ _") :: rewrites0 ().

Definition inflate_π1
  (L : lambda_theory)
  {n : nat}
  : inflate (π1 : L n) = π1
  := subst_π1 _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate π1 = _] => refine '(inflate_π1 _)
  end), "inflate_π1 _") :: rewrites0 ().

Lemma π1_pair
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : app π1 (⟨a, b⟩) = a.
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (abs x))) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_subst _ (_ • _) _ (extend_tuple _ _) @ _).
  refine '(subst_subst _ (var _) _ _ @ _).
  refine '(var_subst _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
  refine '(subst_inflate _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
  refine '(var_subst _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
  refine '(subst_inflate _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
  refine '(subst_subst _ a _ _ @ _).
  refine '(_ @ subst_var _ a).
  apply maponpaths.
  apply funextfun.
  intro i.
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
  refine '(var_subst _ _ _ @ _).
  exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- app π1 (⟨?a , ?b⟩) = _] => refine '(π1_pair _ _ $a $b); assumption
  end), "π1_pair _ Lβ _ _") :: rewrites0 ().

Lemma π1_pair_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L (S n))
  (b : L n)
  : π1 ∘ (pair_arrow (abs a) b) = abs a.
Proof.
  refine '(compose_abs _ Lβ _ _ @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_π1 _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨(app x _), _⟩)))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, abs x) (π1_pair _ Lβ _ _) @ _).
  refine '(_ @ maponpaths abs (subst_var L a)).
  apply (maponpaths (λ x, abs (a • x))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inr _ _ _).
Qed.

Lemma π1_pair_arrow'
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : π1 ∘ pair_arrow a b = abs (app (inflate a) (var (stnweq (inr tt)))).
Proof.
  refine '(_ @ π1_pair_arrow _ Lβ _ b).
  apply maponpaths.
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app x _), _⟩))) (inflate_abs _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨x, _⟩))) (beta_equality _ Lβ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨x, _⟩))) (subst_subst _ _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨x, _⟩))) (subst_app _ _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app x _), _⟩))) (subst_inflate _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app _ (x • _)), _⟩))) (extend_tuple_inr _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (var_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨(app _ x), _⟩))) (extend_tuple_inr _ _ _)).
  apply (maponpaths (λ x, (abs (⟨(app (a • x) _), _⟩)))).
  apply funextfun.
  intro i.
  refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _)).
  refine '(_ @ !var_subst _ _ _).
  exact (!extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- π1 ∘ (pair_arrow ?a ?b) = _] => refine '(π1_pair_arrow _ _ _ $b); assumption
  end), "π1_pair_arrow _ Lβ _ _") :: rewrites0 ().


Definition π2
  {L : lambda_theory}
  {n : nat}
  : L n
  := abs
    (app
      (var (stnweq (inr tt)))
      (abs
        (abs
          (var (stnweq (inr tt)))))).

Lemma subst_π2
  (L : lambda_theory)
  {m n : nat}
  (t : stn m → L n)
  : subst π2 t = π2.
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs x)))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (abs (abs x))))) (var_subst _ _ _) @ _).
  exact (maponpaths (λ x, (abs (app _ (abs (abs x))))) (extend_tuple_inr _ _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- π2 • ?c = _] => refine '(subst_π2 _ $c)
  end), "subst_π2 _ _") :: rewrites0 ().

Definition inflate_π2
  (L : lambda_theory)
  {n : nat}
  : inflate (π2 : L n) = π2
  := subst_π2 _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate π2 = _] => refine '(inflate_π2 _)
  end), "inflate_π2 _") :: rewrites0 ().

Lemma π2_pair
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : app π2 (⟨a, b⟩) = b.
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (abs x))) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_subst _ (_ • _) _ (extend_tuple _ _) @ _).
  refine '(subst_subst _ (var _) _ _ @ _).
  refine '(var_subst _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
  refine '(var_subst _ _ _ @ _).
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
  refine '(var_subst _ _ _ @ _).
  refine '(extend_tuple_inr _ _ _ @ _).
  refine '(_ @ subst_var _ b).
  apply maponpaths.
  apply funextfun.
  intro i.
  exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- app π2 (⟨?a , ?b⟩) = _] => refine '(π2_pair _ _ $a $b); assumption
  end), "π2_pair _ Lβ _ _") :: rewrites0 ().

Lemma π2_pair_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L n)
  (b : L (S n))
  : π2 ∘ (pair_arrow a (abs b)) = abs b.
Proof.
  refine '(compose_abs _ Lβ _ _ @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_π2 _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, (app x _)⟩)))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (π2_pair _ Lβ _ _) @ _).
  refine '(_ @ maponpaths abs (subst_var L b)).
  apply (maponpaths (λ x, abs (b • x))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inr _ _ _).
Qed.

Lemma π2_pair_arrow'
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : π2 ∘ pair_arrow a b = abs (app (inflate b) (var (stnweq (inr tt)))).
Proof.
  refine '(_ @ π2_pair_arrow _ Lβ a _).
  apply maponpaths.
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (inflate_abs _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, x⟩))) (beta_equality _ Lβ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, x⟩))) (subst_subst _ _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, x⟩))) (subst_app _ _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app x _)⟩))) (subst_inflate _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app _ (x • _))⟩))) (extend_tuple_inr _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (var_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (⟨_, (app _ x)⟩))) (extend_tuple_inr _ _ _)).
  apply (maponpaths (λ x, (abs (⟨_, (app (b • x) _)⟩)))).
  apply funextfun.
  intro i.
  refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _)).
  refine '(_ @ !var_subst _ _ _).
  exact (!extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- π2 ∘ (pair_arrow ?a ?b) = _] => refine '(π2_pair_arrow _ _ $a _); assumption
  end), "π2_pair_arrow _ Lβ _ _") :: rewrites0 ().

(** * 6. Union arrow ('match') *)

Definition union_arrow
  {L : lambda_theory}
  {n : nat}
  (a b : L n)
  : L n
  := abs
    (app
      (app
        (var (stnweq (inr tt)))
        (inflate a))
      (inflate b)).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- union_arrow _ _ = _ ] => refine '(maponpaths (λ x, union_arrow x _) _ @ _) end),
    "union_arrow ",
    " _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- union_arrow _ _ = _ ] => refine '(maponpaths (λ x, union_arrow _ x) _ @ _) end),
    "union_arrow _ ",
    ""
  ) :: traversals0 ().

Lemma subst_union_arrow
  (L : lambda_theory)
  {n m : nat}
  (a b : L n)
  (c : stn n → L m)
  : union_arrow a b • c = union_arrow (a • c) (b • c).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ x) _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (app (app _ x) _))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (inflate_subst _ _ _)).
  refine '(maponpaths (λ x, (abs (app (app _ (_ • x)) _))) _ @ maponpaths (λ x, (abs (app _ (_ • x)))) _);
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- union_arrow ?a ?b • ?c = _] => refine '(subst_union_arrow _ $a $b $c)
  end), "subst_union_arrow _ _ _ _") :: rewrites0 ().

Definition inflate_union_arrow
  (L : lambda_theory)
  {n : nat}
  (a b : L n)
  : inflate (union_arrow a b) = union_arrow (inflate a) (inflate b)
  := subst_union_arrow _ _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (union_arrow ?a ?b) = _] => refine '(inflate_union_arrow _ $a $b)
  end), "inflate_union_arrow _ _ _") :: rewrites0 ().

Lemma app_union_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (union_arrow a b) c = app (app c a) b.
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, (app (app _ x) _)) (subst_var _ _)).
  refine '(_ @ maponpaths (λ x, (app _ x)) (subst_var _ _)).
  refine '(maponpaths (λ x, (app (app _ (_ • x)) _)) _ @ maponpaths (λ x, (app _ (_ • x))) _);
    apply funextfun;
    intro i;
    apply extend_tuple_inl.
Qed.

(** * 7. Union injections *)

Definition ι1
  {L : lambda_theory}
  {n : nat}
  : L n
  := abs (abs (abs
    (app
      (var (stnweq (inl (stnweq (inr tt)))))
      (var (stnweq (inl (stnweq (inl (stnweq (inr tt))))))))
      )).

Lemma subst_ι1
  (L : lambda_theory)
  {n m : nat}
  (a : stn n → L m)
  : ι1 • a = ι1.
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs x)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app x _))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app x _))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ x))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app (inflate x) _))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate x)))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app x _))))) (inflate_var _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate (inflate x))))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate x)))))) (inflate_var _ _) @ _).
  exact (maponpaths (λ x, (abs (abs (abs (app _ x))))) (inflate_var _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- ι1 • ?a = _] => refine '(subst_ι1 _ $a)
  end), "subst_ι1 _ _") :: rewrites0 ().

Definition inflate_ι1
  (L : lambda_theory)
  {n : nat}
  : inflate (ι1 : L n) = ι1
  := subst_ι1 _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate ι1 = _] => refine '(inflate_ι1 _)
  end), "inflate_ι1 _") :: rewrites0 ().

Lemma app_ι1
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (app (app ι1 a) b) c = app b a.
Proof.
  refine '(maponpaths (λ x, (app (app x _) _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_subst _ (app _ _) _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (x • _) _)) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app ((x • _) • _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ ((x • _) • _))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (x • _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, app x _) (subst_var _ _)).
  refine '(_ @ maponpaths (λ x, app _ x) (subst_var _ _)).
  refine '(maponpaths (λ x, app (_ • x) _) _ @ maponpaths (λ x, app _ (_ • x)) _);
    apply funextfun;
    intro i.
  - apply extend_tuple_inl.
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
Qed.

Lemma union_arrow_ι1
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L (S n))
  (b : L n)
  : union_arrow (abs a) b ∘ ι1 = abs a.
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_union_arrow _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (inflate_ι1 _) @ _).
  refine '(maponpaths _ (app_union_arrow _ Lβ _ _ _) @ _).
  refine '(maponpaths _ (app_ι1 _ Lβ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
  refine '(_ @ maponpaths abs (subst_var _ _)).
  apply (maponpaths (λ x, abs (a • x))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    apply extend_tuple_inl.
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    apply extend_tuple_inr.
Qed.


Definition ι2
  {L : lambda_theory}
  {n : nat}
  : L n
  := abs (abs (abs
    (app
      (var (stnweq (inr tt)))
      (var (stnweq (inl (stnweq (inl (stnweq (inr tt))))))))
      )).

Lemma subst_ι2
  (L : lambda_theory)
  {n m : nat}
  (a : stn n → L m)
  : ι2 • a = ι2.
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs x)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app x _))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app x _))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ x))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate x)))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate (inflate x))))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (abs (app _ (inflate x)))))) (inflate_var _ _) @ _).
  exact (maponpaths (λ x, (abs (abs (abs (app _ x))))) (inflate_var _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- ι2 • ?a = _] => refine '(subst_ι2 _ $a)
  end), "subst_ι2 _ _") :: rewrites0 ().

Definition inflate_ι2
  (L : lambda_theory)
  {n : nat}
  : inflate (ι2 : L n) = ι2
  := subst_ι2 _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate ι2 = _] => refine '(inflate_ι2 _)
  end), "inflate_ι2 _") :: rewrites0 ().

Lemma app_ι2
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (app (app ι2 a) b) c = app c a.
Proof.
  refine '(maponpaths (λ x, (app (app x _) _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_abs _ _ _) @ _).
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_subst _ (app _ _) _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (x • _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app x _)) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ ((x • _) • _))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, app _ x) (subst_var _ _)).
  refine '(maponpaths (λ x, app _ (_ • x)) _).
  apply funextfun.
  intro i.
  refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
  refine '(var_subst _ _ _ @ _).
  exact (extend_tuple_inl _ _ _).
Qed.

Lemma union_arrow_ι2
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L n)
  (b : L (S n))
  : union_arrow a (abs b) ∘ ι2 = abs b.
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_union_arrow _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (inflate_ι2 _) @ _).
  refine '(maponpaths _ (app_union_arrow _ Lβ _ _ _) @ _).
  refine '(maponpaths _ (app_ι2 _ Lβ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
  refine '(_ @ maponpaths abs (subst_var _ _)).
  apply (maponpaths (λ x, abs (b • x))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    apply extend_tuple_inl.
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    apply extend_tuple_inr.
Qed.

(** * 8. Evaluation of a curried function *)

Definition ev
  {L : lambda_theory}
  {m : nat}
  (a b : L m)
  : L m
  := abs
    (app
      (inflate a)
      (app
        (app
          π2
          (var (stnweq (inr tt))))
        (app
          (inflate b)
          (app
            π1
            (var (stnweq (inr tt))))))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- ev _ _ = _ ] => refine '(maponpaths (λ x, ev x _) _ @ _) end),
    "ev ",
    " _"
  ) :: traversals0 ().

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- ev _ _ = _ ] => refine '(maponpaths (λ x, ev _ x) _ @ _) end),
    "ev _ ",
    ""
  ) :: traversals0 ().

Lemma subst_ev
  (L : lambda_theory)
  {m m' : nat}
  (a b : L m)
  (c : stn m → L m')
  : (ev a b) • c = ev (a • c) (b • c).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app (app x _) _)))) (subst_π2 _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app (app _ x) _)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app _ x))))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app (app _ x) _)))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ x)))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ x)))))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (app x _))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app x _))))) (inflate_subst _ _ _)).
  refine '(maponpaths (λ x, abs (app (_ • x) _)) _ @ maponpaths (λ x, abs (app _ (app _ (app (_ • x) _)))) _);
    apply funextfun;
    intro i;
    exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (ev ?a ?b) • ?c = _] => refine '(subst_ev _ $a $b $c)
  end), "subst_ev _ _ _ _") :: rewrites0 ().

Definition inflate_ev
  (L : lambda_theory)
  {n : nat}
  (a b : L n)
  : inflate (ev a b) = ev (inflate a) (inflate b)
  := subst_ev _ _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (ev ?a ?b) = _] => refine '(inflate_ev _ $a $b)
  end), "inflate_ev _ _ _") :: rewrites0 ().

Lemma app_ev
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a b c : L m)
  : app (ev a b) c
  = app
    a
    (app
      (app
        π2
        c)
      (app
        b
        (app
          π1
          c))).
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app x _))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app (app x _) _))) (subst_π2 _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app (app _ x) _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app _ x)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app (app _ x) _))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app _ (app x _))))) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app _ (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app _ (app _ x))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, app x _) _ @ maponpaths (λ x, app _ (app _ (app x _))) _).
  - refine '(_ @ subst_var L a).
    apply maponpaths.
    apply funextfun.
    intro i.
    exact (extend_tuple_inl _ _ _).
  - refine '(_ @ subst_var L b).
    apply maponpaths.
    apply funextfun.
    intro i.
    exact (extend_tuple_inl _ _ _).
Qed.

Lemma app_ev_pair
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a b c d : L m)
  : app (ev a b) (⟨c, d⟩)
  = app
      a
      (app
        d
        (app
          b
          c)).
Proof.
  refine '(app_ev _ Lβ _ _ _ @ _).
  refine '(maponpaths (λ x, (app _ (app _ (app _ x)))) (π1_pair _ Lβ _ _) @ _).
  exact (maponpaths (λ x, (app _ (app x _))) (π2_pair _ Lβ _ _)).
Qed.

Lemma ev_compose_pair_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a b c d : L m)
  : ev a b ∘ (pair_arrow c d)
  = abs
    (app
      (inflate a)
      (app
        (app
          (inflate d)
          (var (stnweq (inr tt))))
        (app
          (inflate b)
          (app
            (inflate c)
            (var (stnweq (inr tt))))))).
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_ev _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (inflate_pair_arrow _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (app_pair_arrow _ Lβ _ _ _) @ _).
  exact (maponpaths (λ x, (abs x)) (app_ev_pair _ Lβ _ _ _ _)).
Qed.

(** * 9. Curry *)

Definition curry
  {L : lambda_theory}
  {m : nat}
  (a : L m)
  : L m
  := abs
    (abs
      (app
        (inflate (inflate a))
        (⟨
          var (stnweq (inl (stnweq (inr tt)))),
          var (stnweq (inr tt))
        ⟩))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- curry _ = _ ] => refine '(maponpaths (λ x, curry x) _ @ _) end),
    "curry ",
    ""
  ) :: traversals0 ().

Lemma subst_curry
  (L : lambda_theory)
  {m m' : nat}
  (a : L m)
  (b : stn m → L m')
  : curry a • b = curry (a • b).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨(inflate x), _⟩))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (inflate_var _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_subst _ _ _)).
  apply (maponpaths (λ x, abs (abs (app (a • x) _)))).
  apply funextfun.
  intro i.
  refine '(extend_tuple_inl _ _ _ @ _).
  exact (maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (curry ?a) • ?b = _] => refine '(subst_curry _ $a $b)
  end), "subst_curry _ _ _") :: rewrites0 ().

Definition inflate_curry
  (L : lambda_theory)
  {n : nat}
  (a : L n)
  : inflate (curry a) = curry (inflate a)
  := subst_curry _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (curry ?a) = _] => refine '(inflate_curry _ $a)
  end), "inflate_curry _ _") :: rewrites0 ().

Lemma app_curry
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a b : L m)
  : app (curry a) b
  = abs
    (app
      (inflate a)
      (⟨ inflate b,
      var (stnweq (inr tt))⟩)).
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨(inflate x), _⟩)))) (extend_tuple_inr _ _ _) @ _).
  apply (maponpaths (λ x, abs (app (a • x) _))).
  apply funextfun.
  intro i.
  refine '(extend_tuple_inl _ _ _ @ _).
  refine '(maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _) @ _).
  exact (inflate_var _ _).
Qed.

Lemma curry_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a : L (S m))
  (b : L m)
  : curry b ∘ abs a
  = abs (abs
    (app
      (inflate (inflate b))
      (⟨
        inflate a,
        var (stnweq (inr tt))
      ⟩))).
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_curry _ _) @ _).
  refine '(maponpaths abs (app_curry _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (inflate_app _ _ _ : app (inflate _) _ • _ = _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨(app (inflate x) _), _⟩))))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨(app _ x), _⟩))))) (inflate_var _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨(app x _), _⟩))))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (beta_equality _ Lβ _ _) @ _).
  do 2 (refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (subst_subst _ _ _ _) @ _)).
  apply (maponpaths (λ x, abs (abs (app _ (⟨a • x, _⟩))))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inr _ _ _).
Qed.

(** * 10. Uncurry *)

Definition uncurry
  {L : lambda_theory}
  {m : nat}
  (a : L m)
  : L m
  := abs
    (app
      (app
        (inflate a)
        (app
          π1
          (var (stnweq (inr tt)))))
      (app
          π2
          (var (stnweq (inr tt))))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- uncurry _ = _ ] => refine '(maponpaths (λ x, uncurry x) _ @ _) end),
    "uncurry ",
    ""
  ) :: traversals0 ().

Lemma subst_uncurry
  (L : lambda_theory)
  {m m' : nat}
  (a : L m)
  (b : stn m → L m')
  : uncurry a • b = uncurry (a • b).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ x) _))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app x _)))) (subst_π2 _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ (app x _)) _))) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ (app _ x)) _))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ (app _ x)) _))) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (app (app x _) _))) (inflate_subst _ _ _)).
  refine '(maponpaths (λ x, (abs (app (app (_ • x) _) _))) _).
  apply funextfun.
  intro i.
  exact (extend_tuple_inl _ _ _).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (uncurry ?a) • ?b = _] => refine '(subst_uncurry _ $a $b)
  end), "subst_uncurry _ _ _") :: rewrites0 ().

Definition inflate_uncurry
  (L : lambda_theory)
  {n : nat}
  (a : L n)
  : inflate (uncurry a) = uncurry (inflate a)
  := subst_uncurry _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (uncurry ?a) = _] => refine '(inflate_uncurry _ $a)
  end), "inflate_uncurry _ _") :: rewrites0 ().

Lemma app_uncurry
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : app (uncurry a) b
  = app
      (app
        a
        (app π1 b))
      (app π2 b).
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app x _))) (subst_π2 _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ x))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ (app x _)) _)) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ (app _ x)) _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ (app _ x))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ (app _ x)) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, (app (app x _) _)) (subst_var _ _)).
  refine '(maponpaths (λ x, (app (app (_ • x) _) _)) _).
  apply funextfun.
  intro i.
  exact (extend_tuple_inl _ _ _).
Qed.

Lemma app_uncurry_pair
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (uncurry a) (⟨b, c⟩)
  = app
      (app
        a
        b)
      c.
Proof.
  refine '(app_uncurry _ Lβ _ _ @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (π1_pair _ Lβ _ _) @ _).
  exact (maponpaths (λ x, (app _ x)) (π2_pair _ Lβ _ _)).
Qed.

Lemma uncurry_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b : L n)
  : uncurry a ∘ b
  = abs
    (app
      (app
        (inflate a)
        (app
          π1
          (app
            (inflate b)
            (var (stnweq (inr tt))))))
      (app
        π2
        (app
          (inflate b)
          (var (stnweq (inr tt)))))).
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_uncurry _ _) @ _).
  exact (maponpaths (λ x, (abs x)) (app_uncurry _ Lβ _ _)).
Qed.

Lemma uncurry_compose_pair_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : uncurry a ∘ (pair_arrow b c)
  = abs
    (app
      (app
        (inflate a)
        (app
          (inflate b)
          (var (stnweq (inr tt)))))
      (app
        (inflate c)
        (var (stnweq (inr tt))))).
Proof.
  refine '(uncurry_compose _ Lβ _ _ @ _).
  refine '(maponpaths (λ x, (abs (app (app _ (app _ (app x _))) _))) (inflate_pair_arrow _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (inflate_pair_arrow _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ (app _ x)) _))) (app_pair_arrow _ Lβ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (app_pair_arrow _ Lβ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app (app _ x) _))) (π1_pair _ Lβ _ _) @ _).
  exact (maponpaths (λ x, (abs (app _ x))) (π2_pair _ Lβ _ _)).
Qed.

Lemma curry_uncurry
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L (S (S n)))
  : curry (uncurry (abs (abs a))) = abs (abs a).
Proof.
  refine '(maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app (app x _) _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app (app _ x) _)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_π2 _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app (app x _) _)))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app (app _ (app x _)) _)))) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app (app _ (app _ x)) _)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app _ (x • _)))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_subst _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app _ (x • _)))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_subst _ _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, abs (abs x)) (subst_var _ _)).
  apply (maponpaths (λ x, abs (abs (a • x)))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(subst_inflate _ _ _ @ _).
    refine '(subst_subst _ (extend_tuple _ _ i') _ _ @ _).
    rewrite <- (homotweqinvweq stnweq i').
    induction (invmap stnweq i') as [i'' | i''].
    + refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
      refine '(subst_inflate _ _ _ @ _).
      refine '(subst_subst _ (extend_tuple _ _ _) _ _ @ _).
      refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
      refine '(var_subst _ _ _ @ _).
      refine '(maponpaths (λ x, ((x • _) • _)) (extend_tuple_inl _ _ _) @ _).
      refine '(subst_subst _ (var _) _ _ @ _).
      refine '(var_subst _ _ _ @ _).
      refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
      refine '(var_subst _ _ _ @ _).
      refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
      refine '(var_subst _ _ _ @ _).
      exact (extend_tuple_inl _ _ _).
    + refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
      refine '(var_subst _ _ _ @ _).
      refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
      refine '(subst_app _ _ _ _ @ _).
      refine '(maponpaths (λ x, (app x _)) (subst_π1 _ _) @ _).
      refine '(maponpaths (λ x, (app _ x)) (subst_subst _ _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inr _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ ((x • _) • _))) (extend_tuple_inr _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ x)) (subst_subst _ _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inr _ _ _) @ _).
      refine '(maponpaths (λ x, (app _ x)) (subst_pair _ _ _ _) @ _).
      refine '(π1_pair _ Lβ _ _ @ _).
      refine '(var_subst _ _ _ @ _).
      refine '(extend_tuple_inl _ _ _ @ _).
      now induction i''.
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    refine '(extend_tuple_inr _ _ _ @ _).
    refine '(maponpaths (λ x, (app _ x)) (extend_tuple_inr _ _ _) @ _).
    exact (π2_pair _ Lβ _ _).
Qed.

Lemma uncurry_curry
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a : L n)
  : uncurry (curry a) = a ∘ (pair_arrow π1 π2).
Proof.
  refine '(maponpaths (λ x, (abs (app (app x _) _))) (inflate_curry _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (app_curry _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨(app x _), _⟩)))) (subst_π1 _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨(app _ x), _⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨(app _ x), _⟩)))) (extend_tuple_inl _ _ _) @ _).
  refine '(_ @ !compose_abs _ Lβ _ _).
  refine '(_ @ !maponpaths (λ x, (abs (app _ (⟨(app x _), _⟩)))) (inflate_π1 _)).
  refine '(_ @ !maponpaths (λ x, (abs (app _ (⟨_, (app x _)⟩)))) (inflate_π2 _)).
  apply   (maponpaths (λ x, (abs (app (a • x) _)))).
  apply funextfun.
  intro i.
  apply extend_tuple_inl.
Qed.

(** * 11. An alternative form of curry, swapping the arguments *)

Definition curry'
  {L : lambda_theory}
  {m : nat}
  (a : L m)
  : L m
  := abs
    (abs
      (app
        (inflate (inflate a))
        (⟨
          var (stnweq (inr tt)),
          var (stnweq (inl (stnweq (inr tt))))
        ⟩))).

Ltac2 Set traversals as traversals0 := fun _ => (
    (fun () => match! goal with | [ |- curry' _ = _ ] => refine '(maponpaths (λ x, curry' x) _ @ _) end),
    "curry' ",
    ""
  ) :: traversals0 ().

Lemma subst_curry'
  (L : lambda_theory)
  {m m' : nat}
  (a : L m)
  (b : stn m → L m')
  : curry' a • b = curry' (a • b).
Proof.
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs x))) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (inflate x)⟩))))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (inflate_var _ _) @ _).
  refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_subst _ _ _)).
  refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_subst _ _ _)).
  apply (maponpaths (λ x, abs (abs (app (a • x) _)))).
  apply funextfun.
  intro i.
  refine '(extend_tuple_inl _ _ _ @ _).
  exact (maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _)).
Qed.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- (curry' ?a) • ?b = _] => refine '(subst_curry' _ $a $b)
  end), "subst_curry' _ _ _") :: rewrites0 ().

Definition inflate_curry'
  (L : lambda_theory)
  {n : nat}
  (a : L n)
  : inflate (curry' a) = curry' (inflate a)
  := subst_curry' _ _ _.

Ltac2 Set rewrites as rewrites0 := fun () =>
  ((fun () => match! goal with
  | [ |- inflate (curry' ?a) = _] => refine '(inflate_curry' _ $a)
  end), "inflate_curry' _ _") :: rewrites0 ().

Lemma app_curry'
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a b : L m)
  : app (curry' a) b
  = abs
    (app
      (inflate a)
      (⟨
        var (stnweq (inr tt)),
        inflate b
      ⟩)).
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_abs _ _ _ @ _).
  refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ x))) (subst_pair _ _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app x _))) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨x, _⟩)))) (extend_tuple_inr _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, x⟩)))) (extend_tuple_inl _ _ _) @ _).
  refine '(maponpaths (λ x, (abs (app _ (⟨_, (inflate x)⟩)))) (extend_tuple_inr _ _ _) @ _).
  apply (maponpaths (λ x, abs (app (a • x) _))).
  apply funextfun.
  intro i.
  refine '(extend_tuple_inl _ _ _ @ _).
  refine '(maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _) @ _).
  exact (inflate_var _ _).
Qed.

Lemma curry'_compose
  (L : lambda_theory)
  (Lβ : has_β L)
  {m : nat}
  (a : L (S m))
  (b : L m)
  : curry' b ∘ abs a
  = abs (abs
    (app
      (inflate (inflate b))
      (⟨
        var (stnweq (inr tt)),
        inflate a
      ⟩))).
Proof.
  refine '(maponpaths (λ x, (abs (app x _))) (inflate_curry' _ _) @ _).
  refine '(maponpaths abs (app_curry' _ Lβ _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (inflate_app _ _ _ : app (inflate _) _ • _ = _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (app (inflate x) _)⟩))))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (app _ x)⟩))))) (inflate_var _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (app x _)⟩))))) (inflate_abs _ _) @ _).
  refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (beta_equality _ Lβ _ _) @ _).
  do 2 (refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (subst_subst _ _ _ _) @ _)).
  apply (maponpaths (λ x, abs (abs (app _ (⟨_, a • x⟩))))).
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inl _ _ _).
  - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
    refine '(var_subst _ _ _ @ _).
    exact (extend_tuple_inr _ _ _).
Qed.
