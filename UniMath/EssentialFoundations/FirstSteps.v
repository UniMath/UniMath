(** * First steps toward the Univalent Foundations *)

(** ** Product and function notation *)

(** Introduce the conventional notations for the product type and for function construction. *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* to input: type "\prod" with Agda input method *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* to input: type "\Gl" or "\lambda" or "\lamda" with Agda input method *)

(** ** The universe *)

(** Introduce a fixed universe and call it [UU].  Currently we run Coq with the command line option
    [-type-in-type], which defeats universe consistency checking.  Eventually we hope to be
    able to implement judgmental "resizing" axioms in Coq and turn universe consistency checking back on.

    We prepare for that day by declaring everything to occupy a single universe, [UU], which
    is pinned down by the following definition.

    *)

Definition UU := Type.

(** ** The empty type *)

(** Define the empty type [empty] by induction, with no constructors. *)

Inductive empty : UU := .

Notation "∅" := empty.

(** *** Canonical function from the empty type *)

Definition fromempty {X:UU} : empty -> X.
Proof.
  intros n.
  induction n.
Defined.

(** ** Negation *)

Definition neg (X : UU) : UU := X -> empty.

Notation "'¬' X" := (neg X) (at level 35, right associativity).
(** to input: type "\neg" or "\lnot" with Agda input method *)

(** ** The unit type *)

Inductive unit : UU :=  tt : unit.

(** *** Canonical functions to [unit] *)

Definition tounit {X : UU} : X -> unit.
Proof.
  intros x.
  exact tt.
Defined.

(** *** Functions from [unit] corresponding to terms *)

Definition termfun {X:UU} (x:X) : unit -> X := λ t, x.

(** ** The coproduct of two types *)

Inductive coprod (A B:UU) : UU :=
    | ii1 : A -> coprod A B
    | ii2 : B -> coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation "X ⨿ Y" := (coprod X Y) (at level 50, left associativity).
  (** to input: type "\union" with Agda input method and select it from the menu
     or use C-X 8 RET AMALGAMATION OR COPRODUCT

     should be changed to X ∐ Y :
     to input: type "\union" or "\smallamalg" or "\amalg" or "\coprod" with Agda input method *)

(** ** Sums, or ∑-types *)

Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (** to input: type "\union" or "\sum" with Agda input method *)

Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).

(** ** Identity type *)

(** Define the identity type [paths] by induction. *)

Inductive paths {A:Type} (a:A) : A -> UU :=
    | idpath : paths a a.

Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.

Notation "x != y" := (¬ (x = y)) (at level 70).

(** ** Binary direct product *)

Definition dirprod (X Y : UU) := ∑ x:X, Y.

Notation "A × B" := (dirprod A B) (at level 75, right associativity) : type_scope.

Definition dirprod_pr1 {X Y : UU} := pr1 : X × Y -> X.

Definition dirprod_pr2 {X Y : UU} := pr2 : X × Y -> Y.

Definition dirprodpair {X Y : UU} := tpair (fun x : X => Y).

(** ** Functions *)

Definition idfun (T : UU) := λ t:T, t.

Definition funcomp {X Y : UU} {Z:Y->UU} (f : X -> Y) (g : ∏ y:Y, Z y) := λ x, g (f x).

Delimit Scope functions with functions.

Open Scope functions.

Notation "g ∘ f" := (funcomp f g) (at level 50, left associativity) : functions.

(** *** Associativity of function composition *)

Lemma funcomp_assoc {X Y Z W : UU} (f : X -> Y) (g : Y -> Z) (h : Z -> W)
  : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  exact (idpath _).
Defined.

(** While the path in the proof above is trivial, the lemma turns out to be convenient in future
proofs, to apply a particular definitional equality to modify the syntactic form of the goal in
order to make the next tactic, which uses the syntactic form of the goal to guess how to proceed,
succeed.

The same remark applies to other lemmas below whose proof is by a term of the form [idpath _].
Such terms are also produced by the tactic [reflexivity]. *)

(** ** Paths *)

(** *** Path composition *)

Definition pathscomp0 {X : UU} {a b c : X} : a = b -> b = c -> a = c.
Proof.
  intros p q. induction p. exact q.
Defined.

(** The proof above is by induction on the path [p], which reduces the goal to the
    special case where the path [p] is of the form [idpath _].  The next few proofs
    follow the same pattern. *)

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

Definition path_assoc {X} {a b c d:X} (f : a = b) (g : b = c) (h : c = d)
  : f @ (g @ h) = (f @ g) @ h.
Proof.
  induction f.
  reflexivity.
Defined.

(** *** Inverse path *)

Definition pathsinv0 {X : UU} {a b : X} : a = b -> b = a.
Proof.
  intros p. induction p. reflexivity.
Defined.

Notation "! p " := (pathsinv0 p) (at level 50).

Definition pathsinv0l {X : UU} {a b : X} (p : a = b) : !p @ p = idpath _.
Proof.
  induction p. reflexivity.
Defined.

Definition pathsinv0r {X : UU} {a b : X} (p : a = b) : p @ !p = idpath _.
Proof.
  induction p. reflexivity.
Defined.

Definition pathsinv0inv0 {X : UU} {x x' : X} (p : x = x') : !(!p) = p.
Proof.
  induction p. reflexivity.
Defined.

(** *** Applying a function to a path *)

(** The function [maponpaths] takes a functino [f : X -> Y] and a path [p : x = x'] between
    two points of [X] and produces a path between [f x] and [f x']. *)

Definition maponpaths {X Y : UU} (f : X -> Y) {x x':X} (p: x = x') : f x = f x'.
Proof.
  induction p. reflexivity.
Defined.

(** The function [maponpaths] is compatible with the operations on paths defined above. *)

Definition maponpathscomp0 {X Y : UU} {x1 x2 x3 : X}
           (f : X -> Y) (p : x1 = x2) (q : x2 = x3) :
  maponpaths f (p @ q) = maponpaths f p @ maponpaths f q.
Proof.
  induction p. induction q. apply idpath.
Defined.

Definition maponpathsinv0 {X Y : UU} (f : X -> Y) {x1 x2 : X} (p : x1 = x2) :
  maponpaths f (! p) = ! maponpaths f p.
Proof.
  induction p. apply idpath.
Defined.

(** The function [maponpaths] is compatible with the operations on functions. *)

Lemma maponpathsidfun {X : UU} {x x' : X}
      (p : x = x') : maponpaths (idfun _) p = p.
Proof.
  induction p. apply idpath.
Defined.

Lemma maponpathscomp {X Y Z : UU} {x x' : X} (f : X -> Y) (g : Y -> Z)
      (p : x = x') : maponpaths g (maponpaths f p) = maponpaths (g ∘ f) p.
Proof.
  induction p. apply idpath.
Defined.

(** ** h-level *)

(** In this subsection we introduce the fundamental notion of "h-level", which reveals a hierarchy
    of types.  The types of h-level 0 are the types with a unique element, and the types of h-level
    n+1 are the types whose identity types are of h-level n.

    We interpret the propositions of mathematics as the types of h-level 1, and we interpret the
    sets of mathematics as the types of h-level 2.  The type of objects of a "univalent" category
    will be of h-level 3, and in general, one expects the type of objects of a "univalent"
    n-category to be of h-level n+2.

  *)

(** *** Contractibility - h-level 0 *)

(** A type is contractible if it has exactly one element. *)

Definition iscontr (X:UU) : UU := ∑ cntr:X, ∏ t:X, t=cntr.

Definition iscontrpr1 {X : UU} : iscontr X -> X := pr1.

Notation "'∃!' x .. y , P"
  := (iscontr (∑ x, .. (∑ y, P) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
(** to input: type "\exists" or "\ex" with Agda input method *)

(** **** Contractibility of [unit]  *)

Theorem iscontrunit: iscontr unit.
Proof.
  exists tt.
  intro t.
  induction t.
  reflexivity.
Defined.

(** *** h-levels of types *)

Definition isofhlevel (n : nat) : UU -> UU.
Proof.
  induction n as [|n previous_hlevel].
  - intros X. exact (iscontr X).
  - intros X. exact (∏ (x x':X), previous_hlevel (x = x')).
Defined.

(** *** Propositions -- types of h-level 1 *)

Definition isaprop := isofhlevel 1.

Goal ∏ (X : UU), isaprop X = (∏ x x' : X, iscontr (x = x')).
Proof. reflexivity. Qed.

(** **** Proof irrelevance *)

(** A type is called _proof irrelevant_ if its elements (proofs) are equal. *)

Definition isProofIrrelevant (X:UU) := ∏ x y:X, x = y.

(** A proposition is proof irrelevant.  Later, we will prove the converse. *)

Lemma proofirrelevance (X : UU) : isaprop X -> isProofIrrelevant X.
Proof.
  intros i. intros x x'. unfold isaprop in i. unfold isofhlevel in i.
  apply iscontrpr1. apply i.
Defined.

(** *** Sets -- types of h-level 2 *)

Definition isaset := isofhlevel 2.

(** A set is a type whose identity types are propositions, and that's what makes them
    analogous to the sets of set theory. *)

Goal ∏ (X : UU), isaset X = (∏ x x' : X, isaprop (x = x')).
Proof. reflexivity. Qed.

(** ** Homotopy fibers of maps  *)

Definition hfiber {X Y : UU} (f : X -> Y) (y : Y) : UU := ∑ x : X, f x = y.

(** ** Equivalences *)

(** A function is a weak equivalence if its fibers are contractible, i.e., have exactly
    one element. *)

Definition isweq {X Y : UU} (f : X -> Y) : UU :=
  ∏ y : Y, iscontr (hfiber f y).

(** A weak equivalence is a function [f] together with a proof of [isweq f]. *)

Definition weq (X Y : UU) : UU := ∑ f:X->Y, isweq f.

Notation "X ≃ Y" := (weq X Y) (at level 80, no associativity) : type_scope.
(** to input: type "\simeq" or "\~-" or "\eq" with Agda input method *)

(** An identity function is a weak equivlanece. *)

Lemma idisweq (X : UU) : isweq (idfun X).
Proof.
  intros. unfold isweq. intros y.
  unfold iscontr.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact y.
    + simpl. reflexivity.
  - simpl. intro w. induction w as [x p].
    unfold idfun in p.
    induction p.
    reflexivity.
Defined.

Definition idweq (X : UU) : X ≃ X := (idfun X,,idisweq X).

(** ** Paths in the universe *)

(** A path in the universe between two types gives a weak equivalence between the two types,
    i.e., equal types are equivalent. *)

Definition eqweqmap { X Y : UU } : X = Y -> X ≃ Y.
Proof.
  intro p.
  induction p.
  apply idweq.
Defined.

(** The univalence axiom will assert that the map in the definition above is a weak
    equivalence from [X=Y] to [X≃Y]. *)
