(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011

This is the first in the group of files which contain the (current state of) the mathematical
library for the proof assistant Coq based on the Univalent Foundations.  It contains some new
notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)




(** Preamble. *)

Unset Automatic Introduction.

(** Universe structure *)

Notation UUU := Set .

Notation UU  := Type.

Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.
Global Unset Universe Minimization ToSet.

(** Empty type.  The empty type is introduced in Coq.Init.Datatypes by the line:

[ Inductive Empty_set : Set := . ]

*)


Inductive empty : UU :=.  (* make it polymorphic; needed due to Coq bug? *)

Notation "∅" := empty.

(** Identity Types. Identity types are introduced in Coq.Init.Datatypes by the lines :

[ Inductive identity ( A : Type ) ( a : A ) : A -> Type := identity_refl : identity _ a a .

Hint Resolve identity_refl : core . ]

*)

Inductive paths {A:Type} (a:A) : A -> Type := paths_refl : paths a a.
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl .

(* When the goal is displayed as x=y and the types of x and y are hard to discern,
   use this tactic -- it will add the type to the context in simplified form. *)
Ltac show_id_type := match goal with |- @paths ?ID _ _ => set (TYPE := ID); simpl in TYPE end.

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

(* Notation coprod := sum . *)
(* Notation coprod_rect := sum_rect. *)

Inductive coprod (__A__ __B__:Type) : Type :=
  | inl : __A__ -> coprod __A__ __B__
  | inr : __B__ -> coprod __A__ __B__.
(* Do not use "induction" on an element of this type without specifying names; seeing __A__ or __B__
   will indicate that you did that. *)

Arguments coprod_rect {_ _} _ _ _ _.

Notation ii1fun := inl .
Notation ii2fun := inr .

Notation ii1 := inl .
Notation ii2 := inr .
Arguments ii1 {A B} _ : rename.
Arguments ii2 {A B} _ : rename.

Notation "X ⨿ Y" := (coprod X Y) (at level 50, left associativity).
  (* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

Definition coprod_rect_compute_1
           (A B : UU) (P : A ⨿ B -> UU)
           (f : ∏ (a : A), P (ii1 a))
           (g : ∏ (b : B), P (ii2 b)) (a:A) :
  coprod_rect P f g (ii1 a) = f a.
Proof. reflexivity. Defined.

Definition coprod_rect_compute_2
           (A B : UU) (P : A ⨿ B -> UU)
           (f : ∏ a : A, P (ii1 a))
           (g : ∏ b : B, P (ii2 b)) (b:B) :
  coprod_rect P f g (ii2 b) = g b.
Proof. reflexivity. Defined.

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

(* two alternatives: *)
(* total2 as a record with primitive projections: *)

    (* Set Primitive Projections. *)

    (* Set Nonrecursive Elimination Schemes. *)

    (* Record total2@{i} { T: Type@{i} } ( P: T -> Type@{i} ) := tpair { pr1 : T; pr2 : P pr1 }. *)

(* or total2 as an inductive type:  *)

    Inductive total2@{i} { T: Type@{i} } ( P: T -> Type@{i} ) : Type@{i} := tpair : ∏ (__t__:T) (__p__:P __t__), total2 P.

    (* Do not use "induction" without specifying names; seeing __t__ or __p__ will indicate that you *)
    (*    did that.  This will prepare for the use of primitive projections, when the names will be pr1 *)
    (*    and pr2. *)

    Definition pr1@{i} { T : Type@{i} } { P : T -> Type@{i} } ( t : total2@{i} P ) : T .
    Proof . intros .  induction t as [ t p ] . exact t . Defined.

    Definition pr2@{i} { T : Type@{i} } { P : T -> Type@{i} } ( t : total2@{i} P ) : P ( pr1 t ) .
    Proof . intros .  induction t as [ t p ] . exact p . Defined.

(* end of two alternatives *)

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

(* Now prepare tactics for writing proofs in two ways, depending on whether projections are primitive *)
Ltac primitive_projections :=
  unify (fun (w : total2 (fun _:nat => nat)) => tpair _ (pr1 w) (pr2 w))
        (fun (w : total2 (fun _:nat => nat)) => w).
(* Use like this: [ tryif primitive_projections then ... else ... . ] *)

Definition whether_primitive_projections : bool.
Proof.
  tryif primitive_projections then exact true else exact false.
Defined.

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity). (* looser than '+' *)

Ltac mkpair := (simple refine (tpair _ _ _ ) ; [| cbn]).

Goal ∏ X (Y : X -> UU) (x : X) (y : Y x), ∑ x, Y x.
  intros X Y x y.
  mkpair.
  - apply x.
  - apply y.
Defined.

(* print out this theorem to see whether "induction" compiles to "match" *)
Goal ∏ X (Y:X->UU) (w:∑ x, Y x), X.
  intros.
  induction w as [x y].
  exact x.
Defined.

(* Step through this proof to demonstrate eta expansion for pairs, if primitive
   projections are on: *)
Goal ∏ X (Y:X->UU) (w:∑ x, Y x), w = (pr1 w,, pr2 w).
Proof. try reflexivity. Abort.

Definition rewrite_pr1_tpair {X} {P:X->UU} x p : pr1 (tpair P x p) = x.
reflexivity. Defined.

Definition rewrite_pr2_tpair {X} {P:X->UU} x p : pr2 (tpair P x p) = p.
reflexivity. Defined.

(*

(** The phantom type family ( following George Gonthier ) *)

Inductive Phant ( T : Type ) := phant : Phant T .


*)



(** The following command checks whether the flag [-indices-matter] which modifies the universe
level assignment for inductive types has been set. With the flag it returns [ paths 0 0 : UUU
]. Without the flag it returns [ paths 0 0 : Prop ]. *)

Check (O = O) .

(* notation *)

Notation "X <- Y" := (Y -> X) (at level 90, only parsing, left associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
(* written \to or \r- in Agda input method *)
(* the level comes from sub/coq/theories/Unicode/Utf8_core.v *)

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



(** A few tactics, thanks go to Jason Gross *)

Ltac simple_rapply p :=
  simple refine p ||
  simple refine (p _) ||
  simple refine (p _ _) ||
  simple refine (p _ _ _) ||
  simple refine (p _ _ _ _) ||
  simple refine (p _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Tactic Notation "use" uconstr(p) := simple_rapply p.

Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let name := (_ : type) in _).

(** reserve notations for later use: *)

Reserved Notation "∅".

Reserved Notation "a --> b" (at level 50).

Reserved Notation "C ⟦ a , b ⟧" (at level 50).
(* ⟦   to input: type "\[[" or "\(" with Agda input method
   ⟧   to input: type "\]]" or "\)" with Agda input method *)

Reserved Notation "f ;; g"  (at level 50, left associativity, only parsing). (* deprecated *)

Reserved Notation "f · g"  (at level 50, format "f  ·  g", left associativity).
(* to input: type "\centerdot" or "\cdot" with Agda input method *)

Reserved Notation "g ∘ f"  (at level 50, left associativity).
(* agda input \circ *)

(* conflict:
    Reserved Notation "# F"  (at level 3).
    Reserved Notation "p # x" (right associativity, at level 65, only parsing).
*)

Reserved Notation "p #' x" (right associativity, at level 65, only parsing).

Reserved Notation "C '^op'" (at level 3, format "C ^op").

Reserved Notation "a <-- b" (at level 50).

Reserved Notation "[ C , D ]" .

Reserved Notation "C [ a , b ]"  (at level 50).

Reserved Notation "X ⟶ Y"  (at level 39).
(* to input: type "\-->" with Agda input method *)

Reserved Notation "X ⟹ Y"  (at level 39).
(* same parsing level as ⟶ *)
(* to input: type "\==>" with Agda input method *)

Reserved Notation "F ∙ G" (at level 35).
(* to input: type "\." with Agda input method *)
(* the old notation had the arguments in the opposite order *)

(* conflict:
    Reserved Notation "s □ x" (at level 64, left associativity).
    Reserved Notation "G □ F" (at level 35).
    (* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)
*)

Reserved Notation "F ◾ b"  (at level 40, left associativity).
(* to input: type "\sqb" or "\sq" with Agda input method *)

Reserved Notation "F ▭ f"  (at level 40, left associativity). (* \rew1 *)
(* to input: type "\rew" or "\re" with Agda input method *)

(* conflict:
    Reserved Notation "A ⇒ B" (at level 95, no associativity).
    Reserved Notation "c ⇒ X" (at level 50).
    (* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with Agda input method *)
*)

Reserved Notation "X ⇐ c"   (at level 50).
(* to input: type "\Leftarrow" or "\Longleftarrow" or "\l=" or "\l" with Agda input method *)

Reserved Notation "x ⟲ f"  (at level 50, left associativity).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "q ⟳ x"  (at level 50, left associativity).
(* to input: type "\r" and select from the menu, row 4, spot 3, with Agda input method *)

Reserved Notation "p ◽ b"  (at level 40).
(* to input: type "\sqw" or "\sq" with Agda input method *)

Reserved Notation "xe ⟲⟲ p"  (at level 50).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "r \\ x"  (at level 50, left associativity).

Reserved Notation "x // r"  (at level 50, left associativity).
