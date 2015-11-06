(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011

This is the first in the group of files which contain the (current state of) the mathematical library for the proof assistant Coq based on the Univalent Foundations.
It contains some new notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)




(** Preamble. *)

Unset Automatic Introduction.  (** This line has to be removed for the file to compile with Coq8.2 *)

(** Universe structure *)

Notation UUU := Set .

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.


(** Empty type.  The empty type is introduced in Coq.Init.Datatypes by the line:

[ Inductive Empty_set : Set := . ]

*)

Notation empty := Empty_set.
Notation empty_rect := Empty_set_rect.

(** Identity Types. Identity types are introduced in Coq.Init.Datatypes by the lines :

[ Inductive identity ( A : Type ) ( a : A ) : A -> Type := identity_refl : identity _ a a .

Hint Resolve identity_refl : core . ]

*)

Inductive paths {A:Type} (a:A) : A -> Type := paths_refl : paths a a.
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl .

(* Remark: all of the uu0.v now uses only paths_rect and not the direct "match" construction
on paths. By adding a constantin paths for the computation rule for paths_rect and then making
both this constant and paths_rect itself opaque it is possible to check which of the
constructions of the uu0 can be done with the weakened version of the Martin-Lof Type Theory
that is interpreted by the Bezm-Coquand-Huber cubical set model of 2014. *)




(** Coproducts .

The coproduct of two types is introduced in Coq.Init.Datatypes by the lines:

[ Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B. ]
*)

Notation coprod := sum .

Notation ii1fun := inl .
Notation ii2fun := inr .

Notation ii1 := inl .
Notation ii2 := inr .
Implicit Arguments ii1 [ A B ] .
Implicit Arguments ii2 [ A B ] .

Notation coprod_rect := sum_rect.

Notation "X ⨿ Y" := (coprod X Y) (at level 50, left associativity) : type_scope.
  (* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)


Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \forall *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

(** Dependent sums.

One can not use a new record each time one needs it because the general theorems about this
construction would not apply to new instances of "Record" due to the "generativity" of inductive
definitions in Coq.

We use "Inductive" instead of "Record" here.

Using "Record" which is equivalent to "Structure" would allow us later to use the mechanism of
canonical structures with total2.
By using "Structure", we could also get eta for dependent pairs, by adding the option
"Set Primitive Projections.".

However, the use of "Inductive" allows us to obtain proof terms that are expressed in terms of
the eliminator total2_rect that, unlike the "match" construct that would appear in the proof terms
if we used "Record", has a known interpretation in the framework of the univalent model.

*)

Set Primitive Projections.

(* two alternatives: *)
(* total2 as a record with primitive projections: *)
    Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.
    Arguments tpair {T} _ _ _.
    Arguments pr1 {_ _} _.
    Arguments pr2 {_ _} _.
(* or total2 as an inductive type:  *)
    (* Inductive total2 { T: Type } ( P: T -> Type ) := tpair : forall ( t : T ) ( p : P t ) , total2 P . *)
    (* Definition pr1 { T : Type } { P : T -> Type } ( t : total2 P ) : T . *)
    (* Proof . intros .  induction t as [ t p ] . exact t . Defined. *)
    (* Definition pr2 { T : Type } { P : T -> Type } ( t : total2 P ) : P ( pr1 t ) . *)
    (* Proof . intros .  induction t as [ t p ] . exact p . Defined. *)
(* end of two alternatives *)

Notation "'Σ'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \Sigma *)

Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity). (* looser than '+' *)
(* Example: *)
Goal Σ (_:nat) (_:nat) (_:nat) (_:nat), nat. exact (2,,3,,4,,5,,6). Defined.

Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Definition rewrite_pr1_tpair {X} {P:X->UU} x p : pr1 (tpair P x p) = x.
reflexivity. Defined.

Definition rewrite_pr2_tpair {X} {P:X->UU} x p : pr2 (tpair P x p) = p.
reflexivity. Defined.

(*

(** The phantom type family ( following George Gonthier ) *)

Inductive Phant ( T : Type ) := phant : Phant T .


*)



(** The following command checks whether the flag [-indices-matter] which modifies the universe level assignment for inductive types has been set. With the flag it returns [ paths 0 0 : UUU ] . Without the flag it returns [ paths 0 0 : Prop ]. *)

Check (O = O) .

(* notation *)

Notation "X <- Y" := (Y -> X) (at level 90, only parsing, left associativity) : type_scope.

(* exhibit some aspects of addition on [nat] *)
(* parsing is left associative: *)
Goal ∀ i j k, i+j+k = (i+j)+k. reflexivity. Defined.
Goal ∀ n, 1+n = S n. reflexivity. Defined.
Goal ∀ n, n+1 = S n. try reflexivity. Abort.

(* confirm and repair some aspects of multiplication on [nat] *)
(* parsing is left associative: *)
Goal ∀ i j k, i*j*k = (i*j)*k. reflexivity. Defined.
Goal ∀ n, 0*n = 0.     reflexivity. Defined.

(* one of these should have worked: *)
Goal ∀ n, n*1 = n. try reflexivity. Abort.
Goal ∀ n, 1*n = n. try reflexivity. Abort.

(* here we see the problem: *)
Goal ∀ n, 1*n = n+0. reflexivity. Defined.
Goal ∀ n, 4*n = n+(n+(n+(n+0))). reflexivity. Defined.

(* not that 0+n reduces to n: *)
Goal ∀ n, 0+n = n. reflexivity. Defined.

(* so we do it the other way around: *)
Definition mul : nat -> nat -> nat.
Proof.
  intros n m.
  induction n as [|p pm].
  - exact O.
  - exact (pm + m).
Defined.
Notation mult := mul.           (* this overrides the notation "mult" defined in Coq's Peano.v *)
Notation "n * m" := (mul n m) : nat_scope.

(* confirm: *)
Goal ∀ n, 0*n = 0.             reflexivity. Defined.
Goal ∀ n m, S n * m = n*m + m. reflexivity. Defined.
Goal ∀ n, 1*n = n.             reflexivity. Defined.
Goal ∀ n, 4*n = n+n+n+n.       reflexivity. Defined.
