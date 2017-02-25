(** First steps toward the Univalent Foundations *)

(* convenient notations *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

Definition UU := Type.

(** We define the type [empty] by induction, with no constructors. *)

Inductive empty : UU := .

Notation "∅" := empty.

(** We define the identity type [paths] by induction. *)

Inductive paths {A:Type} (a:A) : A -> UU :=
    | idpath : paths a a.

Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.

Inductive coprod (A B:UU) : UU :=
    | ii1 : A -> coprod A B
    | ii2 : B -> coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation "X ⨿ Y" := (coprod X Y) (at level 50, left associativity).
  (* to input: type "\union" with Agda input method and select it from the menu
     or use C-X 8 RET AMALGAMATION OR COPRODUCT

     should be changed to X ∐ Y :
     to input: type "\union" or "\smallamalg" or "\amalg" or "\coprod" with Agda input method *)

(** Sums, or Σ-types *)

Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* to input: type "\union" or "\sum" with Agda input method *)

Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).

(** *** Pairwise direct products *)

Definition dirprod (X Y : UU) := ∑ x:X, Y.

Notation "A × B" := (dirprod A B) (at level 75, right associativity) : type_scope.

Definition dirprod_pr1 {X Y : UU} := pr1 : X × Y -> X.
Definition dirprod_pr2 {X Y : UU} := pr2 : X × Y -> Y.

Definition dirprodpair {X Y : UU} := tpair (fun x : X => Y).

(** *** Negation *)

Definition neg (X : UU) : UU := X -> empty.

Notation "'¬' X" := (neg X) (at level 35, right associativity).
(* to input: type "\neg" or "\lnot" with Agda input method *)

Notation "x != y" := (neg (x = y)) (at level 70).

(** Functions *)

Definition idfun (T : UU) := λ t:T, t.

Definition funcomp {X Y : UU} {Z:Y->UU} (f : X -> Y) (g : ∏ y:Y, Z y) := λ x, g (f x).

Delimit Scope functions with functions.

Open Scope functions.

Notation "g ∘ f" := (funcomp f g) (at level 50, left associativity) : functions.

(** *** Associativity of function composition and mutual invertibility of curry/uncurry  *)

(** While the paths in two of the three following lemmas are trivial, having them as
lemmas turns out to be convenient in some future proofs. They are used to apply a particular
definitional equalities to modify the syntactic form of the goal in order to make the
next tactic, which uses the syntactic form of the goal to guess how to proceed, to work.

The same applies to other lemmas below whose proof is by immediate "reflexivity" or
"idpath". *)

Lemma funcomp_assoc {X Y Z W : UU} (f : X -> Y) (g : Y -> Z) (h : Z -> W)
  : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  reflexivity.
Defined.

(** *** Composition of paths and inverse paths *)

Definition pathscomp0 {X : UU} {a b c : X} : a = b -> b = c -> a = c.
Proof.
  intros p q. induction p. exact q.
Defined.

Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Definition pathscomp0rid {X : UU} {a b : X} (p : a = b) : p @ idpath b = p.
(** Note that we do not introduce [ pathscomp0lid ] since the corresponding
    two terms are convertible to each other due to our definition of
    [ pathscomp0 ]. If we defined it by inductioning [ e2 ] and
    applying [ e1 ] then [ pathscomp0rid ] would be trivial but
    [ pathscomp0lid ] would require a proof. Similarly we do not introduce a
    lemma to connect [ pathsinv0 (idpath _) ] to [ idpath ].
 *)
Proof.
  induction p. simpl. reflexivity.
Defined.

Definition pathsinv0 {X : UU} {a b : X} : a = b -> b = a.
Proof.
  intros p. induction p. reflexivity.
Defined.

Notation "! p " := (pathsinv0 p) (at level 50).

(** ** First fundamental notions *)

(** *** Contractibility - h-level 0 *)

Definition iscontr (T:UU) : UU := ∑ cntr:T, ∏ t:T, t=cntr.

Definition iscontrpr1 {T : UU} : iscontr T -> T := pr1.

Notation "'∃!' x .. y , P"
  := (iscontr (∑ x, .. (∑ y, P) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
(* to input: type "\exists" or "\ex" with Agda input method *)

(** *** h-levels of types *)

Definition isofhlevel (n : nat) : UU -> UU.
Proof.
  induction n as [|n IH].
  - intros X. exact (iscontr X).
  - intros X. exact (∏ (x x':X), IH (x = x')).
Defined.

(** *** Propositions -- h-level 1 *)

Definition isaprop := isofhlevel 1.

Goal ∏ (X : UU), isaprop X = (∏ x x' : X, iscontr (x = x')).
Proof. reflexivity. Qed.

Definition isProofIrrelevant (X:UU) := ∏ x y:X, x = y.

Lemma proofirrelevance (X : UU) : isaprop X -> isProofIrrelevant X.
Proof.
  intros is. intros x x'. unfold isaprop in is. unfold isofhlevel in is.
  apply iscontrpr1. apply is.
Defined.

(** *** Sets -- h-level 2 *)

Definition isaset := isofhlevel 2.

Goal ∏ (X : UU), isaset X = (∏ x x' : X, isaprop (x = x')).
Proof. reflexivity. Qed.
