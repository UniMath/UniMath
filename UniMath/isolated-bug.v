(* File reduced by coq-bug-finder from original input, then from 3183 lines to 48 lines *)
(* coqc version 8.5beta3 (November 2015) compiled on Nov 5 2015 18:3:10 with OCaml 4.02.3
   coqtop version 8.5beta3 (November 2015) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Definition UU := Type.
Inductive paths {A:Type} (a:A) : A -> Type := paths_refl : paths a a.
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Set Primitive Projections.
    Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.
    Arguments pr1 {_ _} _.
Notation "'Σ'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
Definition iscontr (T:UU) : UU := Σ cntr:T, ∀ t:T, t=cntr.
Definition hfiber {X Y : UU}  (f : X -> Y) (y : Y) : UU := Σ x:X, f x = y.
Definition hfiberpr1 {X Y : UU} (f : X -> Y) (y : Y) : hfiber f y -> X := pr1.
Fixpoint isofhlevel (n:nat) (X:UU): UU:=
match n with
O => iscontr X |
S m => forall x:X, forall x':X, (isofhlevel m (paths x x'))
end.
Definition isofhlevelf ( n : nat ) { X Y : UU } ( f : X -> Y ) : UU := forall y:Y, isofhlevel n (hfiber  f y).
Corollary isofhlevelfhfiberpr1 ( n : nat ) { X Y : UU }  ( f : X -> Y ) ( y : Y ) ( is : isofhlevel (S n) Y ) : isofhlevelf n ( hfiberpr1 f y ) .
admit.
Defined.
Definition isaprop  := isofhlevel 1 .
Definition isincl { X Y : UU } (f : X -> Y ) := isofhlevelf 1 f .
Definition isaset ( X : UU ) : UU := forall x x' : X , isaprop ( paths x x' ) .
Theorem isinclfromhfiber { X Y : UU } (f: X -> Y) (is : isaset Y) ( y: Y ) : @isincl (hfiber  f y) X ( @pr1 _ _  ).
Proof.
intros.
apply isofhlevelfhfiberpr1.
