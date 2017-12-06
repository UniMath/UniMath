(** * Univalent Foundations, Part A

Vladimir Voevodsky.
Feb. 2010 - Sep. 2011.


This file is based on the first part of the original uu0 file.

The uu0 file contained the basic results of the univalent foundations
that required the use of only one universe.

Eventually the requirement concerning one universe was removed because of the
general uncertainty in what does it mean for a construction to require only one universe.
For example, [ boolsumfun ], when written in terms of the eliminatior [ bool_rect ]
instead of the  [ match ], requires application of [ bool_rect ] to an argument that is
not a member of the base universe [ UU ]. This would be different if the universe management
in Coq was constructed differently. Due to this uncertainty we do not consider any more the
single universe requirement as a defining one when selecting results for the inclusion in Foundations.

Part A was created as a separate file on Dec. 3, 2014.

Together with Part B it contains those results that do not require any axioms.

This file was edited and expanded by Benedikt Ahrens 2014-2016, Dan Grayson 2014-2016,
Vladimir Voevodsky 2014-2016, Alex Kavvos 2014, Peter LeFanu Lumsdaine 2016 and
Tomi Pannila 2016.
*)

(** ** Contents
- Preamble
 - Settings
 - Imports

- Some standard constructions not using identity types (paths)
 - Canonical functions from [ empty ] and to [unit ]
 - Identity functions and function composition, curry and uncurry
 - Iteration of an endomorphism
 - Basic constructions related to the adjoint evaluation function [ X -> ((X -> Y) -> Y) ]
 - Pairwise direct products
 - Negation and double negation
 - Logical equivalence

- Paths and operations on paths
 - Associativity of function composition and mutual invertibility of curry/uncurry
 - Composition of paths and inverse paths
 - Direct product of paths
 - The function [ maponpaths ] between paths types defined by a function between ambient types
 - [ maponpaths ] for the identity functions and compositions of functions
 - Homotopy between functions
 - Equality between functions defines a homotopy
 - [ maponpaths ] for a function homotopic to the identity
 - [ maponpaths ] in the case of a projection p with a section s
 - Fibrations and paths - the transport functions
 - A series of lemmas about paths and [ total2 ]
 - Lemmas about transport adapted from the HoTT library and the HoTT book
 - Homotopies between families and the total spaces

- First fundamental notions
 - Contractibility [ iscontr ]
 - Homotopy fibers [ hfiber ]
 - The functions between the hfibers of homotopic functions over the same point
 - Paths in homotopy fibers
 - Coconuses: spaces of paths that begin (coconusfromt) or end (coconustot) at a given point
 - The total paths space of a type - two definitions
 - Coconus of a function: the total space of the family of h-fibers

- Weak equivalences
 - Basics - [ isweq ] and [ weq ]
 - Weak equivalences and paths spaces (more results in further sections)
 - Adjointness property of a weak equivalence and its inverse
 - Transport functions are weak equivalences
 - Weak equivalences between contractible types (one implication)
 - Unit and contractibility
 - Homotopy equivalence is a weak equivalence
 - Some weak equivalences
 - 2-out-of-3 property  of weak equivalences
 - Any function between contractible types is a weak equivalence
 - Composition of weak equivalences
 - 2-out-of-6 property  of weak equivalences
 - Pairwise direct products of weak equivalences
 - Weak equivalence of a type and its direct product with the unit
 - Associativity of total2 as a weak equivalence
 - Associativity and commutativity of direct products as weak equivalences

- Binary coproducts and their basic properties
 - Distributivity of coproducts and direct products as a weak equivalence
 - Total space of a family over a coproduct
 - Pairwise sum of functions, coproduct associativity and commutativity
 - Coproduct with a "negative" type
 - Coproduct of two functions
 - The [ equality_cases ] construction and four applications to [ ii1 ] and [ ii2 ]
 - Bool as coproduct
 - Pairwise coproducts as dependent sums of families over [ bool ]
 - Splitting of [ X ] into a coproduct defined by a function [ X -> Y ⨿ Z ]
 - Some properties of bool
 - Fibrations with only one non-empty fiber

- Basics about fibration sequences
 - The structures of a complex and of a fibration sequence on a composable pair of functions
 - Construction of the derived fibration sequence
 - Explicit description of the first map in the second derived sequence
 - Fibration sequences based on [ tpair P z ] and [ pr1 : total2 P -> Z ] ( the "pr1-case" )
 - Fibration sequences based on [ hfiberpr1 : hfiber g z -> Y ] and [ g : Y -> Z ] (the "g-case")
 - Fibration sequence of h-fibers defined by a composable pair of functions (the "hf-case")

- Functions between total spaces of families
 - Function [ totalfun ] between total spaces from a family of functions between the fibers
 - Function [ fpmap ] between the total spaces from a function between the bases
 - Homotopy fibers of [ fpmap ]
 - The [ fpmap ] from a weak equivalence is a weak equivalence
 - Total spaces of families over a contractible base
 - Function on the total spaces from functions between the bases and between the fibers

- Homotopy fiber squares
 - Homotopy commutative squares
 - Short complexes and homotopy commutative squares
 - Homotopy fiber products
 - Homotopy fiber products and homotopy fibers
 - Homotopy fiber squares
 - Fiber sequences and homotopy fiber squares
 *)






(** ** Preamble *)

(** *** Settings *)

Unset Automatic Introduction.
(* The above line has to be removed for the file to compile with Coq8.2 *)


(** *** Imports *)

Require Export UniMath.Foundations.Preamble.

(* end of "Preamble" *)


(** ** Some standard constructions not using identity types (paths) *)

(** *** Canonical functions from [ empty ] and to [ unit ] *)

Definition fromempty  : ∏ X : UU , empty -> X. (* type this in emacs in agda-input method
with \prod *)
Proof.
  intro X.
  intro H.
  induction H.
Defined.

Arguments fromempty { X } _.

Definition tounit {X : UU} : X -> unit := λ _, tt.

(** *** Functions from [ unit ] corresponding to terms *)

Definition termfun {X : UU} (x : X) : unit -> X := λ _, x.

(** *** Identity functions and function composition, curry and uncurry *)

Definition idfun (T : UU) := λ t:T, t.

Definition funcomp {X Y : UU} {Z:Y->UU} (f : X -> Y) (g : ∏ y:Y, Z y) := λ x, g (f x).

Delimit Scope functions with functions.

Open Scope functions.

Notation "g ∘ f" := (funcomp f g) (at level 50, left associativity) : functions.

(** back and forth between functions of pairs and functions returning
  functions *)

Definition curry {X Z : UU} {Y : X -> UU} (f : (∑ x : X, Y x) -> Z) :
  ∏ x, Y x -> Z.
Proof.
  intros ? ? ? ? ? y.
  exact (f (x,,y)).
Defined.

Definition uncurry {X Z : UU} {Y : X -> UU} (g : ∏ x : X, Y x -> Z) :
  (∑ x, Y x) -> Z.
Proof.
  intros ? ? ? ? xy.
  exact (g (pr1 xy) (pr2 xy)).
Defined.

(** *** Definition of binary operation *)

Definition binop (X : UU) : UU := X -> X -> X.

(** *** Iteration of an endomorphism *)

Definition iteration {T : UU} (f : T -> T) (n : nat) : T -> T.
Proof.
  intros T f n.
  induction n as [ | n IHn ].
  + exact (idfun T).
  + exact (f ∘ IHn).
Defined.

(** *** Basic constructions related to the adjoint evaluation function [ X -> ((X -> Y) -> Y) ] *)

Definition adjev {X Y : UU} (x : X) (f : X -> Y) : Y := f x.

Definition adjev2 {X Y : UU} (phi : ((X -> Y) -> Y) -> Y) : X -> Y :=
  λ x, phi (λ f, f x).

(** *** Pairwise direct products *)

Definition dirprod (X Y : UU) := ∑ x:X, Y.

Notation "A × B" := (dirprod A B) (at level 75, right associativity) : type_scope.

Definition dirprod_pr1 {X Y : UU} := pr1 : X × Y -> X.
Definition dirprod_pr2 {X Y : UU} := pr2 : X × Y -> Y.

Definition dirprodpair {X Y : UU} (x:X) (y:Y) : X × Y := x,,y.

Definition dirprodadj {X Y Z : UU} (f : X × Y -> Z) : X -> Y -> Z :=
  λ x y, f (x,,y).

Definition dirprodf {X Y X' Y' : UU}
           (f : X -> Y) (f' : X' -> Y') (xx' : X × X')  : Y × Y' :=
  dirprodpair (f (pr1 xx')) (f' (pr2 xx')).

Definition ddualand {X Y P : UU}
           (xp : (X -> P) -> P) (yp : (Y -> P) -> P) : (X × Y -> P) -> P.
Proof.
  intros X Y P xp yp X0.
  apply xp. intro x.
  apply yp. intro y.
  apply (X0 (dirprodpair x y)).
Defined.

(** *** Negation and double negation *)

Definition neg (X : UU) : UU := X -> empty.

Notation "'¬' X" := (neg X) (at level 35, right associativity).
(* type this in emacs in agda-input method with \neg *)

Notation "x != y" := (neg (x = y)) (at level 70).

Definition negf {X Y : UU} (f : X -> Y) : ¬ Y -> ¬ X := λ phi x, phi (f x).

Definition dneg (X : UU) : UU := ¬ ¬ X.

Notation "'¬¬' X" := (dneg X) (at level 35, right associativity).
(* type this in emacs in agda-input method with \neg twice *)


Definition dnegf {X Y : UU} (f : X -> Y) : dneg X -> dneg Y :=
  negf (negf f).

Definition todneg (X : UU) : X -> dneg X := adjev.

Definition dnegnegtoneg {X : UU} : ¬¬ ¬ X -> ¬ X := adjev2.

Lemma dneganddnegl1 {X Y : UU} (dnx : ¬¬ X) (dny : ¬¬ Y) : ¬ (X -> ¬ Y).
Proof.
  intros.
  intros X2.
  apply (dnegf X2).
  + apply dnx.
  + apply dny.
Defined.

Definition dneganddnegimpldneg {X Y : UU}
           (dnx : ¬¬ X) (dny : ¬¬ Y) : ¬¬ (X × Y) := ddualand dnx dny.

(** *** Logical equivalence *)

Definition logeq (X Y : UU) := (X -> Y) × (Y -> X).
Notation " X <-> Y " := (logeq X Y) : type_scope.

Lemma isrefl_logeq (X : UU) : X <-> X.
Proof.
  intros. split; apply idfun.
Defined.

Lemma issymm_logeq (X Y : UU) : (X <-> Y) -> (Y <-> X).
Proof.
  intros ? ? e.
  exact (pr2 e,,pr1 e).
Defined.

Definition logeqnegs {X Y : UU} (l : X <-> Y) : (¬ X) <-> (¬ Y) :=
  dirprodpair (negf (pr2 l)) (negf (pr1 l)).

Definition logeq_both_true {X Y : UU} : X -> Y -> (X <-> Y).
Proof.
  intros ? ? x y.
  split.
  - intros x'. exact y.
  - intros y'. exact x.
Defined.

Definition logeq_both_false {X Y : UU} : ¬X -> ¬Y -> (X <-> Y).
Proof.
  intros ? ? nx ny.
  split.
  - intros x. induction (nx x).
  - intros y. induction (ny y).
Defined.

Definition logeq_trans {X Y Z : UU} : (X <-> Y) -> (Y <-> Z) -> (X <-> Z).
Proof.
  intros ? ? ? i j. exact (pr1 j ∘ pr1 i,, pr2 i ∘ pr2 j).
Defined.

(* end of "Some standard constructions not using identity types (paths)". *)


(** ** Paths and operations on [ paths ] *)

(** *** Associativity of function composition and mutual invertibility of curry/uncurry  *)

(** While the paths in two of the three following lemmas are trivial, having them as
lemmas turns out to be convenient in some future proofs. They are used to apply a particular
definitional equality to modify the syntactic form of the goal in order to make the
next tactic, which uses the syntactic form of the goal to guess how to proceed, to work.

The same applies to other lemmas below whose proof is by immediate "reflexivity" or
"idpath". *)

Lemma funcomp_assoc {X Y Z W : UU} (f : X -> Y) (g : Y -> Z) (h : Z -> W)
: h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  intros .
  apply idpath.
Defined.

Lemma uncurry_curry {X Z : UU} {Y : X -> UU} (f : (∑ x : X, Y x) -> Z) :
  ∏ p, uncurry (curry f) p = f p.
Proof.
  intros. induction p as [x y]. apply idpath.
Defined.

Lemma curry_uncurry {X Z : UU} {Y : X -> UU} (g : ∏ x : X, Y x -> Z) :
  ∏ x y, curry (uncurry g) x y = g x y.
Proof.
  intros. apply idpath.
Defined.


(** *** Composition of paths and inverse paths *)

Definition pathscomp0 {X : UU} {a b c : X} (e1 : a = b) (e2 : b = c) : a = c.
Proof.
  intros. induction e1. apply e2.
Defined.

Hint Resolve @pathscomp0 : pathshints.

Ltac intermediate_path x := apply (pathscomp0 (b := x)).
Ltac etrans := eapply pathscomp0.

(** Notation [p @ q] added by B.A., oct 2014 *)

Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


Definition pathscomp0rid {X : UU} {a b : X} (e1 : a = b) : e1 @ idpath b = e1.
Proof.
  intros. induction e1. simpl. apply idpath.
Defined.

(** Note that we do not introduce [ pathscomp0lid ] since the corresponding
    two terms are convertible to each other due to our definition of
    [ pathscomp0 ]. If we defined it by inductioning [ e2 ] and
    applying [ e1 ] then [ pathscomp0rid ] would be trivial but
    [ pathscomp0lid ] would require a proof. Similarly we do not introduce a
    lemma to connect [ pathsinv0 (idpath _) ] to [ idpath ].
 *)

Definition pathsinv0 {X : UU} {a b : X} (e : a = b) : b = a.
Proof.
  intros. induction e. apply idpath.
Defined.

Hint Resolve @pathsinv0 : pathshints.

Definition path_assoc {X} {a b c d:X}
           (f : a = b) (g : b = c) (h : c = d)
  : f @ (g @ h) = (f @ g) @ h.
Proof.
  intros. induction f. apply idpath.
Defined.

(** Notation [! p] added by B.A., oct 2014 *)

Notation "! p " := (pathsinv0 p) (at level 50).


Definition pathsinv0l {X : UU} {a b : X} (e : a = b) : !e @ e = idpath _.
Proof.
  intros. induction e. apply idpath.
Defined.

Definition pathsinv0r {X : UU} {a b : X} (e : a = b) : e @ !e = idpath _.
Proof.
  intros. induction e. apply idpath.
Defined.

Definition pathsinv0inv0 {X : UU} {x x' : X} (e : x = x') : !(!e) = e.
Proof.
  intros. induction e. apply idpath.
Defined.

Lemma pathscomp_cancel_left {X : UU} {x y z : X} (p : x = y) (r s : y = z) :
  p @ r= p @ s -> r = s.
Proof.
  intros ? ? ? ? ? ? ? e. induction p. exact e.
Defined.

Lemma pathscomp_cancel_right {X : UU} {x y z : X} (p q : x = y) (s : y = z) :
  p @ s = q @ s -> p = q.
Proof.
  intros ? ? ? ? ? ? ? e. induction s. refine (_ @ e @ _).
  - apply pathsinv0, pathscomp0rid.
  - apply pathscomp0rid.
Defined.

Lemma pathscomp_inv {X : UU} {x y z : X} (p : x = y) (q : y = z)
  : !(p @ q) = !q @ !p.
Proof.
  intros ? ? ? ? p q. induction p. induction q.
  apply idpath.
Defined.

(** *** Direct product of paths  *)


Definition pathsdirprod {X Y : UU} {x1 x2 : X} {y1 y2 : Y}
           (ex : x1 = x2) (ey : y1 = y2) :
  dirprodpair x1 y1 = dirprodpair x2 y2.
Proof.
  intros. induction ex. induction ey. apply idpath.
Defined.

Lemma dirprodeq (A B : UU) (ab ab' : A × B) :
  pr1 ab = pr1 ab' -> pr2 ab = pr2 ab' -> ab = ab'.
Proof.
  intros A B ab ab' H H'.
  induction ab as [a b].
  induction ab' as [a' b']; simpl in *.
  induction H.
  induction H'.
  apply idpath.
Defined.


(** *** The function [ maponpaths ] between paths types defined by a function between ambient types

and its behavior relative to [ @ ] and [ ! ] *)

Definition maponpaths {T1 T2 : UU} (f : T1 -> T2) {t1 t2 : T1}
           (e: t1 = t2) : f t1 = f t2.
Proof.
  intros. induction e. apply idpath.
Defined.

(* useful with apply, to save typing *)
Definition map_on_two_paths {X Y Z : UU} (f : X -> Y -> Z) {x x' y y'} (ex : x = x') (ey: y = y') :
  f x y = f x' y'.
Proof.
  intros. induction ex. induction ey. apply idpath.
Defined.


Definition maponpathscomp0 {X Y : UU} {x1 x2 x3 : X}
           (f : X -> Y) (e1 : x1 = x2) (e2 : x2 = x3) :
  maponpaths f (e1 @ e2) = maponpaths f e1 @ maponpaths f e2.
Proof.
  intros. induction e1. induction e2. apply idpath.
Defined.

Definition maponpathsinv0 {X Y : UU} (f : X -> Y)
           {x1 x2 : X} (e : x1 = x2) : maponpaths f (! e) = ! (maponpaths f e).
Proof.
  intros. induction e. apply idpath.
Defined.


(** *** [ maponpaths ] for the identity functions and compositions of functions *)

Lemma maponpathsidfun {X : UU} {x x' : X}
      (e : x = x') : maponpaths (idfun _) e = e.
Proof.
  intros. induction e. apply idpath.
Defined.

Lemma maponpathscomp {X Y Z : UU} {x x' : X} (f : X -> Y) (g : Y -> Z)
      (e : x = x') : maponpaths g (maponpaths f e) = maponpaths (g ∘ f) e.
Proof.
  intros. induction e. apply idpath.
Defined.

(** *** Homotopy between sections *)

Definition homot {X : UU} {P : X -> UU} (f g : ∏ x : X, P x) := ∏ x : X , f x = g x.

Notation "f ~ g" := (homot f g) (at level 70, no associativity).

Definition homotrefl {X : UU} {P : X -> UU} (f: ∏ x : X, P x) : f ~ f.
Proof.
  intros ? ? ? x. apply idpath.
Defined.

Definition homotcomp {X:UU} {Y:X->UU} {f f' f'' : ∏ x : X, Y x}
           (h : f ~ f') (h' : f' ~ f'') : f ~ f'' := λ x, h x @ h' x.

Definition invhomot {X:UU} {Y:X->UU} {f f' : ∏ x : X, Y x}
           (h : f ~ f') : f' ~ f := λ x, !(h x).

Definition funhomot {X Y Z:UU} (f : X -> Y) {g g' : Y -> Z}
           (h : g ~ g') : g ∘ f ~ g' ∘ f := λ x, h (f x).

Definition funhomotsec {X Y:UU} {Z:Y->UU} (f : X -> Y) {g g' : ∏ y:Y, Z y}
           (h : g ~ g') : g ∘ f ~ g' ∘ f := λ x, h (f x).

Definition homotfun {X Y Z : UU} {f f' : X -> Y} (h : f ~ f')
           (g : Y -> Z) : g ∘ f ~ g ∘ f' := λ x, maponpaths g (h x).

(** *** Equality between functions defines a homotopy *)

Definition toforallpaths {T:UU} (P:T->UU) (f g:∏ t:T, P t) : f = g -> f ~ g.
Proof.
  intros ? ? ? ? h t. induction h.  apply (idpath _).
Defined.

Definition eqtohomot     {T:UU} {P:T->UU} {f g:∏ t:T, P t} : f = g -> f ~ g.
(* the same as toforallpaths, but with different implicit arguments *)
Proof.
  intros ? ? ? ? e t. induction e. apply idpath.
Defined.

(** *** [ maponpaths ] for a function homotopic to the identity

The following three statements show that [ maponpaths ] defined by
a function f which is homotopic to the identity is
"surjective". It is later used to show that the maponpaths defined
by a function which is a weak equivalence is itself a weak
equivalence. *)

(** Note that the type of the assumption h below can equivalently be written as
[ homot f ( idfun X ) ] *)

Definition maponpathshomidinv {X : UU} (f : X -> X)
           (h : ∏ x : X, f x = x) (x x' : X) (e : f x = f x') :
  x = x' := ! (h x) @ e @ (h x').

Lemma maponpathshomid1 {X : UU} (f : X -> X) (h: ∏ x : X, f x = x)
      {x x' : X} (e : x = x') : maponpaths f e = (h x) @ e @ (! h x').
Proof.
  intros. induction e. simpl.
  apply pathsinv0.
  apply pathsinv0r.
Defined.

Lemma maponpathshomid2 {X : UU} (f : X -> X) (h : ∏ x : X, f x = x)
      (x x' : X) (e: f x = f x') :
  maponpaths f (maponpathshomidinv f h _ _ e) = e.
Proof.
  intros.
  unfold maponpathshomidinv.
  apply (pathscomp0 (maponpathshomid1 f h (! h x @ e @ h x'))).

  assert (l : ∏ (X : UU) (a b c d : X) (p : a = b) (q : a = c) (r : c = d),
              p @ (!p @ q @ r) @ !r = q).
  { intros. induction p. induction q. induction r. apply idpath. }

  apply (l _ _ _ _ _ (h x) e (h x')).
Defined.


(** *** [ maponpaths ] in the case of a projection p with a section s *)

(** Note that the type of the assumption eps below can equivalently be written as
[ homot ( funcomp s p ) ( idfun X ) ] *)

Definition pathssec1 {X Y : UU} (s : X -> Y) (p : Y -> X)
           (eps : ∏ (x : X) , p (s x) = x)
           (x : X) (y : Y) (e : s x = y) : x = p y.
Proof.
  intros.
  apply (pathscomp0 (! eps x)).
  apply (maponpaths p e).
Defined.

Definition pathssec2 {X Y : UU} (s : X -> Y) (p : Y -> X)
           (eps : ∏ (x : X), p (s x) = x)
           (x x' : X) (e : s x = s x') : x = x'.
Proof.
  intros.
  set (e' := pathssec1 s p eps _ _ e).
  apply (e' @ (eps x')).
Defined.

Definition pathssec2id {X Y : UU} (s : X -> Y) (p : Y -> X)
           (eps : ∏ x : X, p (s x) = x)
           (x : X) : pathssec2 s p eps _ _ (idpath (s x)) = idpath x.
Proof.
  intros.
  unfold pathssec2. unfold pathssec1. simpl.
  assert (e : ∏ X : UU, ∏ a b : X,
                                ∏ p : a = b, (! p @ idpath _) @ p = idpath _).
  { intros. induction p0. simpl. apply idpath. }
  apply e.
Defined.

Definition pathssec3 {X Y : UU} (s : X -> Y) (p : Y -> X)
           (eps : ∏ x : X, p (s x) = x) {x x' : X} (e : x = x') :
  pathssec2 s p eps  _ _ (maponpaths s e) = e.
Proof.
  intros. induction e. simpl.
  apply pathssec2id.
Defined.



(** *** Fibrations and paths - the transport functions *)

Definition constr1 {X : UU} (P : X -> UU) {x x' : X} (e : x = x') :
  ∑ (f : P x -> P x'),
  ∑ (ee : ∏ p : P x, tpair _ x p = tpair _ x' (f p)),
  ∏ (pp : P x), maponpaths pr1 (ee pp) = e.
Proof.
  intros. induction e.
  split with (idfun (P x)).
  split with (λ p, idpath _).
  unfold maponpaths. simpl.
  intro. apply idpath.
Defined.

Definition transportf {X : UU} (P : X -> UU) {x x' : X}
           (e : x = x') : P x -> P x' := pr1 (constr1 P e).

Definition transportf_eq {X : UU} (P : X -> UU) {x x' : X} (e : x = x') ( p : P x ) :
  tpair _ x p = tpair  _ x' ( transportf P e p ) := ( pr1 ( pr2 ( constr1 P e ))) p .

Definition transportb {X : UU} (P : X -> UU) {x x' : X}
           (e : x = x') : P x' -> P x := transportf P (!e).

Notation "p # x" := (transportf _ p x)
  (right associativity, at level 65, only parsing) : transport.
Notation "p #' x" := (transportb _ p x)
  (right associativity, at level 65, only parsing) : transport.
Delimit Scope transport with transport.

Definition idpath_transportf {X : UU} (P : X -> UU) {x : X} (p : P x) :
  transportf P (idpath x) p = p.
Proof.
  intros. apply idpath.
Defined.

Lemma functtransportf {X Y : UU} (f : X -> Y) (P : Y -> UU) {x x' : X}
      (e : x = x') (p : P (f x)) :
  transportf (λ x, P (f x)) e p = transportf P (maponpaths f e) p.
Proof.
  intros. induction e. apply idpath.
Defined.

Lemma functtransportb {X Y : UU} (f : X -> Y) (P : Y -> UU) {x x' : X}
      (e : x' = x) (p : P (f x)) :
  transportb (λ x, P (f x)) e p = transportb P (maponpaths f e) p.
Proof.
  intros. induction e. apply idpath.
Defined.

Definition transport_f_b {X : UU} (P : X ->UU) {x y z : X} (e : y = x)
           (e' : y = z) (p : P x) :
  transportf P e' (transportb P e p) = transportf P (!e @ e') p.
Proof.
  intros. induction e'. induction e. apply idpath.
Defined.

Definition transport_b_f {X : UU} (P : X ->UU) {x y z : X} (e : x = y)
           (e' : z = y) (p : P x) :
  transportb P e' (transportf P e p) = transportf P (e @ !e') p.
Proof.
  intros. induction e'. induction e. apply idpath.
Defined.

Definition transport_f_f {X : UU} (P : X ->UU) {x y z : X} (e : x = y)
           (e' : y = z) (p : P x) :
  transportf P e' (transportf P e p) = transportf P (e @ e') p.
Proof.
  intros. induction e'. induction e. apply idpath.
Defined.

Definition transport_b_b {X : UU} (P : X ->UU) {x y z : X} (e : x = y)
           (e' : y = z) (p : P z) :
  transportb P e (transportb P e' p) = transportb P (e @ e') p.
Proof.
  intros. induction e'. induction e. apply idpath.
Defined.

Definition transport_map {X : UU} {P Q : X -> UU} (f : ∏ x, P x -> Q x)
           {x : X} {y : X} (e : x = y) (p : P x) :
  transportf Q e (f x p) = f y (transportf P e p).
Proof.
  intros. induction e. apply idpath.
Defined.

Definition transport_section {X : UU} {P:X -> UU} (f : ∏ x, P x)
           {x : X} {y : X} (e : x = y) :
  transportf P e (f x) = f y.
Proof.
  intros. exact (transport_map (P:= λ _,unit) (λ x _,f x) e tt).
Defined.

Definition transportf_fun {X Y : UU}(P : X -> UU)
           {x1 x2 : X}(e : x1 = x2)(f : P x1 -> Y) :
  transportf (λ x, (P x -> Y)) e f = f ∘ transportb P e .
Proof.
  intros. induction e. apply idpath .
Defined.

Lemma transportb_fun' {X:UU} {P:X->UU} {Z:UU}
      {x x':X} (f:P x'->Z) (p:x=x') (y:P x) :
  f (transportf P p y) = transportb (λ x, P x->Z) p f y.
Proof.
  intros. induction p. apply idpath.
Defined.

Definition transportf_const {X : UU}{x1 x2 : X}(e : x1 = x2)(Y : UU) :
  transportf (λ x, Y) e = idfun Y.
Proof.
  intros. induction e. apply idpath.
Defined.

Definition transportb_const {X : UU}{x1 x2 : X}(e : x1 = x2)(Y : UU) :
  transportb (λ x, Y) e = idfun Y.
Proof.
  intros. induction e. apply idpath.
Defined.

Lemma transportf_paths {X : UU} (P : X -> UU) {x1 x2 : X} {e1 e2 : x1 = x2} (e : e1 = e2)
      (p : P x1) : transportf P e1 p = transportf P e2 p.
Proof.
  intros X P x1 x2 e1 e2 e p. induction e. apply idpath.
Defined.
Opaque transportf_paths.

Local Open Scope transport.

Definition transportbfinv {T} (P:T->Type) {t u:T} (e:t = u) (p:P t) : e#'e#p = p.
Proof.
  intros. induction e. apply idpath.
Defined.

Definition transportfbinv {T} (P:T->Type) {t u:T} (e:t = u) (p:P u) : e#e#'p = p.
Proof.
  intros. induction e. apply idpath.
Defined.

Close Scope transport.

(** *** A series of lemmas about paths and [ total2 ]

    Some lemmas are adapted from the HoTT library http://github.com/HoTT/HoTT *)

Lemma base_paths {A : UU} {B : A -> UU}
      (a b : total2 B) : a = b -> pr1 a = pr1 b.
Proof.
  intros.
  apply maponpaths; assumption.
Defined.

Lemma two_arg_paths {A B C:UU} {f : A -> B -> C} {a1 b1 a2 b2} (p : a1 = a2)
      (q : b1 = b2) : f a1 b1 = f a2 b2.
(* This lemma is an analogue of [maponpaths] for functions of two arguments. *)
Proof.
  intros. induction p. induction q. apply idpath.
Defined.

Lemma two_arg_paths_f {A : UU} {B : A -> UU} {C:UU} {f : ∏ a, B a -> C} {a1 b1 a2  b2}
      (p : a1 = a2) (q : transportf B p b1 = b2) : f a1 b1 = f a2 b2.
(* This lemma is a replacement for and a generalization of [total2_paths2_f], formerly called
   [total2_paths2], which does not refer to [total2].  The lemma [total2_paths2_f] can be obtained
   as the special case [f := tpair _], and Coq can often infer the value for [f], which is declared
   as an implicit argument. *)
Proof.
  intros. induction p. induction q. apply idpath.
Defined.

Lemma two_arg_paths_b {A : UU} {B : A -> UU} {C:UU} {f : ∏ a, B a -> C} {a1 b1 a2 b2}
      (p : a1 = a2) (q : b1 = transportb B p b2) : f a1 b1 = f a2 b2.
(* This lemma is a replacement for and a generalization of [total2_paths2_b], which does not refer
   to [total2].  The lemma [total2_paths2_b] can be obtained as the special case [f := tpair _],
   and Coq can often infer the value for [f], which is declared as an implicit argument. *)
Proof.
  intros. induction p. change _ with (b1 = b2) in q. induction q. apply idpath.
Defined.

Lemma dirprod_paths {A : UU} {B :  UU} {s s' : A × B}
      (p : pr1 s = pr1 s') (q : pr2 s = pr2 s') : s = s'.
Proof.
  intros.
  induction s as [a b]; induction s' as [a' b']; simpl in *.
  exact (two_arg_paths p q).
Defined.

Lemma total2_paths_f {A : UU} {B : A -> UU} {s s' : ∑ x, B x}
      (p : pr1 s = pr1 s')
      (q : transportf B p (pr2 s) = pr2 s') : s = s'.
Proof.
  intros.
  induction s as [a b]; induction s' as [a' b']; simpl in *.
  exact (two_arg_paths_f p q).
Defined.

Lemma total2_paths_b {A : UU} {B : A -> UU} {s s' : ∑ x, B x}
      (p : pr1 s = pr1 s')
      (q : pr2 s = transportb B p (pr2 s')) : s = s'.
Proof.
  intros.
  induction s as [a b]; induction s' as [a' b']; simpl in *.
  exact (two_arg_paths_b p q).
Defined.

Lemma total2_paths2 {A : UU} {B : UU} {a1 a2:A} {b1 b2:B}
      (p : a1 = a2) (q : b1 = b2) : a1,,b1 = a2,,b2.
Proof.
  intros. exact (two_arg_paths p q).
Defined.

Lemma total2_paths2_f {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1}
      {a2 : A} {b2 : B a2} (p : a1 = a2)
      (q : transportf B p b1 = b2) : a1,,b1 = a2,,b2.
Proof.
  intros. exact (two_arg_paths_f p q).
Defined.

Lemma total2_paths2_b {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1}
  {a2 : A} {b2 : B a2} (p : a1 = a2)
  (q : b1 = transportb B p b2) : a1,,b1 = a2,,b2.
Proof.
  intros. exact (two_arg_paths_b p q).
Defined.

Definition pair_path_in2 {X : UU} (P : X -> UU) {x : X} {p q : P x} (e : p = q) :
  x,,p = x,,q.
(* this function can often replaced by [maponpaths _] or by [maponpaths (tpair _ _)],
   except when the pairs in the goal have not been simplified enough to make the
   equality of their first parts evident, in which case this can be useful *)
Proof.
  intros. apply maponpaths. exact e.
Defined.

Definition fiber_paths {A : UU} {B : A -> UU} {u v : ∑ x, B x} (p : u = v) :
  transportf (λ x, B x) (base_paths _ _ p) (pr2 u) = pr2 v.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma total2_fiber_paths {A : UU} {B : A -> UU} {x y : ∑ x, B x} (p : x = y) :
  total2_paths_f  _ (fiber_paths p) = p.
Proof.
  induction p.
  induction x.
  apply idpath.
Defined.

Lemma base_total2_paths {A : UU} {B : A -> UU} {x y : ∑ x, B x}
      {p : pr1 x = pr1 y} (q : transportf _ p (pr2 x) = pr2 y) :
  (base_paths _ _ (total2_paths_f _ q)) = p.
Proof.
  induction x as [x H].
  induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.


Lemma transportf_fiber_total2_paths {A : UU} (B : A -> UU)
      (x y : ∑ x, B x)
      (p : pr1 x = pr1 y) (q : transportf _ p (pr2 x) = pr2 y) :
  transportf (λ p' : pr1 x = pr1 y, transportf _ p' (pr2 x) = pr2 y)
             (base_total2_paths q)  (fiber_paths (total2_paths_f _ q)) = q.
Proof.
  induction x as [x H].
  induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition total2_base_map {S T:UU} {P: T -> UU} (f : S->T) : (∑ i, P(f i)) -> (∑ j, P j).
Proof.
  intros ? ? ? ? x.
  exact (f(pr1 x),,pr2 x).
Defined.

Lemma total2_section_path {X:UU} {Y:X->UU} (a:X) (b:Y a) (e:∏ x, Y x) : (a,,e a) = (a,,b) -> e a = b.
(* this is called "Voldemort's theorem" by David McAllester, https://arxiv.org/pdf/1407.7274.pdf *)
Proof.
  intros ? ? ? ? ? p. simple refine (_ @ fiber_paths p). unfold base_paths. simpl.
  apply pathsinv0, transport_section.
Defined.

(** *** Lemmas about transport adapted from the HoTT library and the HoTT book *)

Definition transportD {A : UU} (B : A -> UU) (C : ∏ a : A, B a -> UU)
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y) :
  C x2 (transportf _ p y).
Proof.
  intros.
  induction p.
  exact z.
Defined.


Definition transportf_total2 {A : UU} {B : A -> UU} {C : ∏ a:A, B a -> UU}
           {x1 x2 : A} (p : x1 = x2) (yz : ∑ y : B x1, C x1 y) :
  transportf (λ x, ∑ y : B x, C x y) p yz =
  tpair (λ y, C x2 y) (transportf _ p  (pr1 yz))
        (transportD _ _ p (pr1 yz) (pr2 yz)).
Proof.
  intros.
  induction p.
  induction yz.
  apply idpath.
Defined.

Definition transportf_dirprod (A : UU) (B B' : A -> UU)
           (x x' : ∑ a, B a × B' a) (p : pr1 x = pr1 x') :
  transportf (λ a, B a × B' a) p (pr2 x) =
  dirprodpair (transportf (λ a, B a) p (pr1 (pr2 x)))
              (transportf (λ a, B' a) p (pr2 (pr2 x))).
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportb_dirprod (A : UU) (B B' : A -> UU)
  (x x' : ∑ a,  B a × B' a)  (p : pr1 x = pr1 x') :
  transportb (λ a, B a × B' a) p (pr2 x') =
    dirprodpair (transportb (λ a, B a) p (pr1 (pr2 x')))
                (transportb (λ a, B' a) p (pr2 (pr2 x'))).
Proof.
  intros.
  apply transportf_dirprod.
Defined.

Definition transportf_id1 {A : UU} {a x1 x2 : A}
           (p : x1 = x2) (q : a = x1) :
  transportf (λ (x : A), a = x) p q = q @ p.
Proof.
  intros. induction p. induction q. apply idpath.
Defined.

Definition transportf_id2 {A : UU} {a x1 x2 : A}
           (p : x1 = x2) (q : x1 = a) :
  transportf (λ (x : A), x = a) p q = !p @ q.
Proof.
  intros. induction p. induction q. apply idpath.
Defined.

Definition transportf_id3 {A : UU} {x1 x2 : A}
           (p : x1 = x2) (q : x1 = x1) :
  transportf (λ (x : A), x = x) p q = !p @ q @ p.
Proof.
  intros. induction p. simpl. apply pathsinv0. apply pathscomp0rid.
Defined.


(** *** Homotopies between families and the total spaces *)

Definition famhomotfun {X : UU} {P Q : X -> UU}
           (h : P ~ Q) (xp : total2 P) : total2 Q.
Proof.
  intros.
  induction xp as [ x p ].
  split with x.
  induction (h x).
  apply p.
Defined.

Definition famhomothomothomot {X : UU} {P Q : X -> UU} (h1 h2 : P ~ Q)
           (H : h1 ~ h2) : famhomotfun h1 ~ famhomotfun h2.
Proof.
  intros.
  intro xp.
  induction xp as [x p].
  simpl.
  apply (maponpaths (λ q, tpair Q x q)).
  induction (H x).
  apply idpath.
Defined.


(** ** First fundamental notions *)

(** *** Contractibility [ iscontr ] *)

Definition iscontr (T:UU) : UU := ∑ cntr:T, ∏ t:T, t=cntr.

Notation "'∃!' x .. y , P"
  := (iscontr (∑ x, .. (∑ y, P) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
(* type this in emacs in agda-input method with \ex ! *)

Definition iscontrpair {T : UU} : ∏ x : T, (∏ t : T, t = x) -> iscontr T
  := tpair _.

Definition iscontrpr1 {T : UU} : iscontr T -> T := pr1.

Definition iscontr_uniqueness {T} (i:iscontr T) (t:T) : t = iscontrpr1 i
  := pr2 i t.

Lemma iscontrretract {X Y : UU} (p : X -> Y) (s : Y -> X)
      (eps : ∏ y : Y, p (s y) = y) (is : iscontr X) : iscontr Y.
Proof.
  intros. set (x := iscontrpr1 is). set (fe := pr2 is). split with (p x).
  intro t. apply (! (eps t) @ maponpaths p (fe (s t))).
Defined.

Lemma proofirrelevancecontr {X : UU} (is : iscontr X) (x x' : X) : x = x'.
Proof.
  intros.
  induction is as [y fe].
  apply (fe x @ !(fe x')).
Defined.

Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : ∃! a, B a)
      (a : A) (p : B a) : a = pr1 (pr1 isc).
Proof.
  intros A B isc a p.
  set (Hi := tpair _ a p).
  apply (maponpaths pr1 (pr2 isc Hi)).
Defined.


(** *** Homotopy fibers [ hfiber ] *)

Definition hfiber {X Y : UU} (f : X -> Y) (y : Y) : UU := ∑ x : X, f x = y.

Definition hfiberpair {X Y : UU} (f : X -> Y) {y : Y}
           (x : X) (e : f x = y) : hfiber f y :=
  tpair _ x e.

Definition hfiberpr1 {X Y : UU} (f : X -> Y) (y : Y) : hfiber f y -> X := pr1.

Definition hfiberpr2 {X Y : UU} (f : X -> Y) (y : Y) (y' : hfiber f y) : f (hfiberpr1 f y y') = y :=
  pr2 y'.

(** *** The functions between the hfibers of homotopic functions over the same point *)

Lemma hfibershomotftog {X Y : UU} (f g : X -> Y)
      (h : f ~ g) (y : Y) : hfiber f y -> hfiber g y.
Proof.
  intros X Y f g h y xe.
  induction xe as [x e].
  split with x.
  apply (!(h x) @ e).
Defined.

Lemma hfibershomotgtof {X Y : UU} (f g : X -> Y)
      (h : f ~ g) (y : Y) : hfiber g y -> hfiber f y.
Proof.
  intros X Y f g h y xe.
  induction xe as [x e].
  split with x.
  apply (h x @ e).
Defined.

(** *** Paths in homotopy fibers *)

Lemma hfibertriangle1 {X Y : UU} (f : X -> Y) {y : Y} {xe1 xe2 : hfiber f y}
      (e : xe1 = xe2) :
  pr2 xe1 = maponpaths f (maponpaths pr1 e) @ pr2 xe2.
Proof.
  intros. induction e. simpl. apply idpath.
Defined.

Corollary hfibertriangle1' {X Y : UU} (f : X -> Y) {x : X} {xe1: hfiber f (f x)}
          (e : xe1 = (x,,idpath (f x))) :
  pr2 xe1 = maponpaths f (maponpaths pr1 e).
Proof.
  intros.
  intermediate_path (maponpaths f (maponpaths pr1 e) @ idpath (f x)).
  - apply hfibertriangle1.
  - apply pathscomp0rid.
Defined.

Lemma hfibertriangle1inv0 {X Y : UU} (f : X -> Y) {y : Y} {xe1 xe2: hfiber f y}
      (e : xe1 = xe2) :
  maponpaths f (! (maponpaths pr1 e)) @ (pr2 xe1) = pr2 xe2.
Proof.
  intros. induction e. apply idpath.
Defined.

Corollary hfibertriangle1inv0' {X Y : UU} (f : X -> Y) {x : X}
          {xe2: hfiber f (f x)} (e : (x,,idpath (f x)) = xe2) :
  maponpaths f (! (maponpaths pr1 e)) = pr2 xe2.
Proof.
  intros.
  intermediate_path (maponpaths f (! (maponpaths pr1 e)) @ idpath (f x)).
  - apply pathsinv0, pathscomp0rid.
  - apply hfibertriangle1inv0.
Defined.

Lemma hfibertriangle2 {X Y : UU} (f : X -> Y) {y : Y} (xe1 xe2: hfiber f y)
      (ee: pr1 xe1 = pr1 xe2) (eee: pr2 xe1 = maponpaths f ee @ (pr2 xe2)) :
  xe1 = xe2.
Proof.
  intros.
  induction xe1 as [t e1].
  induction xe2 as [t' e2].
  simpl in *.
  fold (hfiberpair f t e1).
  fold (hfiberpair f t' e2).
  induction ee.
  simpl in eee.
  apply (maponpaths (λ e, hfiberpair f t e) eee).
Defined.


(** *** Coconuses: spaces of paths that begin [ coconusfromt ] or end [ coconustot ] at a given point *)

Definition coconusfromt (T : UU) (t : T) := ∑ t' : T, t = t'.

Definition coconusfromtpair (T : UU) {t t' : T} (e: t = t') : coconusfromt T t
  := tpair _ t' e.

Definition coconusfromtpr1 (T : UU) (t : T) : coconusfromt T t -> T := pr1.

Definition coconustot (T : UU) (t : T) := ∑ t' : T, t' = t.

Definition coconustotpair (T : UU) {t t' : T} (e: t' = t) : coconustot T t
  := tpair _ t' e.

Definition coconustotpr1 (T : UU) (t : T) : coconustot T t -> T := pr1.

(* There is a path between any two points in a coconus. As we always have a point
in a coconus, namely the one that is given by the pair of t and the path that
starts at t and ends at t, the coconuses are contractible. *)

Lemma connectedcoconustot {T : UU} {t : T} (c1 c2 : coconustot T t) : c1 = c2.
Proof.
  intros.
  induction c1 as [x0 x].
  induction x.
  induction c2 as [x1 y].
  induction y.
  apply idpath.
Defined.

Lemma iscontrcoconustot (T : UU) (t : T) : iscontr (coconustot T t).
Proof.
  intros.
  unfold iscontr.
  split with (coconustotpair T (idpath t)).
  intros.
  apply connectedcoconustot.
Defined.

Lemma connectedcoconusfromt {T : UU} {t : T} (c1 c2 : coconusfromt T t) :
  c1 = c2.
Proof.
  intros.
  induction c1 as [x0 x].
  induction x.
  induction c2 as [x1 y].
  induction y.
  apply idpath.
Defined.

Lemma iscontrcoconusfromt (T : UU) (t : T) : iscontr (coconusfromt T t).
Proof.
  intros. unfold iscontr.
  split with (coconusfromtpair T (idpath t)).
  intros.
  apply connectedcoconusfromt.
Defined.

(** *** The total paths space of a type - two definitions

The definitions differ by the (non) associativity of the [ total2 ].  *)

Definition pathsspace (T : UU) := ∑ t:T, coconusfromt T t.

Definition pathsspacetriple (T : UU) {t1 t2 : T}
           (e : t1 = t2) : pathsspace T := tpair _ t1 (coconusfromtpair T e).

Definition deltap (T : UU) : T -> pathsspace T :=
  λ (t : T), pathsspacetriple T (idpath t).

Definition pathsspace' (T : UU) := ∑ xy : T × T, pr1 xy = pr2 xy.


(** *** Coconus of a function: the total space of the family of h-fibers *)

Definition coconusf {X Y : UU} (f : X -> Y) := ∑ y:Y, hfiber f y.

Definition fromcoconusf {X Y : UU} (f : X -> Y) : coconusf f -> X :=
  λ yxe, pr1 (pr2 yxe).

Definition tococonusf {X Y : UU} (f : X -> Y) : X -> coconusf f :=
  λ x, tpair _ (f x) (hfiberpair f x (idpath _)).

Lemma homottofromcoconusf {X Y : UU} (f : X -> Y) :
  ∏ yxe : coconusf f, tococonusf f (fromcoconusf f yxe) = yxe.
Proof.
  intros.
  induction yxe as [y xe].
  induction xe as [x e].
  unfold fromcoconusf.
  unfold tococonusf.
  simpl.
  induction e.
  apply idpath.
Defined.

Lemma homotfromtococonusf {X Y : UU} (f : X -> Y) :
  ∏ x : X, fromcoconusf f (tococonusf f x) = x.
Proof.
  intros.
  unfold fromcoconusf.
  unfold tococonusf.
  simpl.
  apply idpath.
Defined.


(** ** Weak equivalences *)

(** *** Basics - [ isweq ] and [ weq ] *)

Definition isweq {X Y : UU} (f : X -> Y) : UU :=
  ∏ y : Y, iscontr (hfiber f y).

Lemma idisweq (T : UU) : isweq (idfun T).
Proof.
  intros. unfold isweq. intro y.
  unfold iscontr.
  split with (hfiberpair (idfun T) y (idpath y)).
  intro t.
  induction t as [x e].
  induction e.
  apply idpath.
Defined.

Definition weq (X Y : UU) : UU := ∑ f:X->Y, isweq f.

Notation "X ≃ Y" := (weq X Y) (at level 80, no associativity) : type_scope.
(* written \~- or \simeq in Agda input method *)

Definition pr1weq {X Y : UU} := pr1 : X ≃ Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass.

Definition weqproperty {X Y} (f:X≃Y) : isweq f := pr2 f.

Definition weqccontrhfiber {X Y : UU} (w : X ≃ Y) (y : Y) : hfiber w y.
Proof.
  intros. apply (iscontrpr1 (weqproperty w y)).
Defined.

Definition weqccontrhfiber2 {X Y : UU} (w : X ≃ Y) (y : Y) :
  ∏ x : hfiber w y, x = weqccontrhfiber w y.
Proof.
  intros. unfold weqccontrhfiber. apply (pr2 (pr2 w y)).
Defined.

Definition weqpair {X Y : UU} (f : X -> Y) (is: isweq f) : X ≃ Y :=
  tpair (λ f : X -> Y, isweq f) f is.

Definition idweq (X : UU) : X ≃ X :=
  tpair (λ f : X -> X, isweq f) (λ (x : X), x) (idisweq X).

Definition isweqtoempty {X : UU} (f : X -> ∅) : isweq f.
Proof.
  intros. intro y. apply (fromempty y).
Defined.

Definition weqtoempty {X : UU} (f : X -> ∅) : X ≃ ∅ :=
  weqpair _ (isweqtoempty f).

Lemma isweqtoempty2 {X Y : UU} (f : X -> Y) (is : ¬ Y) : isweq f.
Proof.
  intros. intro y. induction (is y).
Defined.

Definition weqtoempty2 {X Y : UU} (f : X -> Y) (is : ¬ Y) : X ≃ Y
  := weqpair _ (isweqtoempty2 f is).

Definition weqempty {X Y : UU} : ¬X → ¬Y → X≃Y.
Proof.
  intros ? ? nx ny.
  use weqpair.
  - intro x. apply fromempty, nx. exact x.
  - intro y. apply fromempty, ny. exact y.
Defined.

Definition invmap {X Y : UU} (w : X ≃ Y) : Y -> X :=
  λ (y : Y), hfiberpr1 _ _ (weqccontrhfiber w y).

(** *** Weak equivalences and paths spaces (more results in further sections) *)

(** We now define different homotopies and maps between the paths
    spaces corresponding to a weak equivalence. What may look like
    unnecessary complexity in the definition of [ homotinvweqweq ] is due to the
    fact that the "naive" definition needs to be
    corrected in order for lemma [ homotweqinvweqweq ] to hold. *)

Definition homotweqinvweq {X Y : UU} (w : X ≃ Y) :
  ∏ y : Y, w (invmap w y) = y.
Proof.
  intros.
  unfold invmap.
  apply (pr2 (weqccontrhfiber w y)).
Defined.

Definition homotinvweqweq0 {X Y : UU} (w : X ≃ Y) :
  ∏ x : X, x = invmap w (w x).
Proof.
  intros.
  unfold invmap.
  set (xe1 := weqccontrhfiber w (w x)).
  set (xe2 := hfiberpair w x (idpath (w x))).
  set (p := weqccontrhfiber2 w (w x) xe2).
  apply (maponpaths pr1 p).
Defined.

Definition homotinvweqweq {X Y : UU} (w : X ≃ Y) :
  ∏ x : X, invmap w (w x) = x
  := λ (x : X), ! (homotinvweqweq0 w x).

Definition invmaponpathsweq {X Y : UU} (w : X ≃ Y) (x x' : X) :
  w x = w x' -> x = x'
  := pathssec2 w (invmap w) (homotinvweqweq w) x x'.

Definition invmaponpathsweqid {X Y : UU} (w : X ≃ Y) (x : X) :
  invmaponpathsweq w _ _ (idpath (w x)) = idpath x
  := pathssec2id w (invmap w) (homotinvweqweq w) x.

Definition pathsweq1 {X Y : UU} (w : X ≃ Y) (x : X) (y : Y) :
  w x = y -> x = invmap w y
  := λ e, maponpaths pr1 (pr2 (weqproperty w y) (x,,e)).

Definition pathsweq1' {X Y : UU} (w : X ≃ Y) (x : X) (y : Y) :
  x = invmap w y -> w x = y
  := λ e, maponpaths w e @ homotweqinvweq w y.

Definition pathsweq3 {X Y : UU} (w : X ≃ Y) {x x' : X}
           (e : x = x') : invmaponpathsweq w x x' (maponpaths w e) = e
  := pathssec3 w (invmap w) (homotinvweqweq w) _.

Definition pathsweq4 {X Y : UU} (w : X ≃ Y) (x x' : X)
           (e : w x = w x') : maponpaths w (invmaponpathsweq w x x' e) = e.
Proof.
  intros.
  induction w as [f is1].
  set (w := weqpair f is1).
  set (g := invmap w).
  set (ee := maponpaths g e).
  simpl in *.
  set (eee := maponpathshomidinv (g ∘ f) (homotinvweqweq w) x x' ee).

  assert (e1 : maponpaths f eee = e).
  {
    assert (e2 : maponpaths (g ∘ f) eee = ee).
    { apply maponpathshomid2. }
    assert (e3 : maponpaths g (maponpaths f eee) = maponpaths g e).
    { apply (maponpathscomp f g eee @ e2). }
    set (s := @maponpaths _ _ g (f x) (f x')).
    set (p := @pathssec2 _ _ g f (homotweqinvweq w) (f x) (f x')).
    set (eps := @pathssec3 _ _ g f (homotweqinvweq w) (f x) (f x')).
    apply (pathssec2 s p eps _ _ e3).
  }

  assert (e4:
            maponpaths f  (invmaponpathsweq w x x' (maponpaths f eee)) =
            maponpaths f (invmaponpathsweq w x x' e)).
  {
    apply (maponpaths (λ e0: f x = f x',
                         maponpaths f (invmaponpathsweq w x x' e0))
                      e1).
  }

  assert (X0 : invmaponpathsweq w x x' (maponpaths f eee) = eee).
  { apply (pathsweq3 w). }

  assert (e5: maponpaths f (invmaponpathsweq w x x' (maponpaths f eee))
              = maponpaths f eee).
  { apply (maponpaths (λ eee0: x = x', maponpaths f eee0) X0). }

  apply (! e4 @ e5 @ e1).
Defined.

Lemma homotweqinv  {X Y Z} (f:X->Z) (w:X≃Y) (g:Y->Z) : f ~ g ∘ w -> f ∘ invmap w ~ g.
Proof.
  intros ? ? ? ? ? ? p y.
  simple refine (p (invmap w y) @ _); clear p.
  unfold funcomp. apply maponpaths. apply homotweqinvweq.
Defined.

Lemma homotweqinv' {X Y Z} (f:X->Z) (w:X≃Y) (g:Y->Z) : f ~ g ∘ w <- f ∘ invmap w ~ g.
Proof.
  intros ? ? ? ? ? ? q x.
  simple refine (_ @ q (w x)).
  unfold funcomp. apply maponpaths, pathsinv0. apply homotinvweqweq.
Defined.

Definition isinjinvmap {X Y} (v w:X≃Y) : invmap v ~ invmap w -> v ~ w.
Proof.
  intros ? ? ? ? h x.
  intermediate_path (w ((invmap w) (v x))).
  { apply pathsinv0. apply homotweqinvweq. }
  rewrite <- h. rewrite homotinvweqweq. apply idpath.
Defined.

Definition isinjinvmap' {X Y} (v w:X->Y) (v' w':Y->X) : w ∘ w' ~ idfun Y -> v' ∘ v ~ idfun X -> v' ~ w' -> v ~ w.
Proof.
  intros ? ? ? ? ? ? p q h x .
  intermediate_path (w (w' (v x))).
  { apply pathsinv0. apply p. }
  apply maponpaths. rewrite <- h. apply q.
Defined.

(** *** Adjointness property of a weak equivalence and its inverse *)

Lemma diaglemma2 {X Y : UU} (f : X -> Y) {x x' : X}
      (e1 : x = x') (e2 : f x' = f x)
      (ee : idpath (f x) = maponpaths f e1 @ e2) : maponpaths f (! e1) = e2.
Proof.
  intros. induction e1. simpl in *. exact ee.
Defined.

(* this is the adjointness relation for w and its homotopy inverse: *)
Definition homotweqinvweqweq {X Y : UU} (w : X ≃ Y) (x : X) :
  maponpaths w (homotinvweqweq w x) = homotweqinvweq w (w x).
Proof.
  intros.
  unfold homotinvweqweq.
  unfold homotinvweqweq0.
  set (hfid := hfiberpair w x (idpath (w x))).
  set (hfcc := weqccontrhfiber w (w x)).
  unfold homotweqinvweq.
  apply diaglemma2.
  apply (@hfibertriangle1 _ _ w _ hfid hfcc (weqccontrhfiber2 w (w x) hfid)).
Defined.

(* another way the adjointness relation may occur (added by D. Grayson, Oct. 2015): *)
Definition weq_transportf_adjointness {X Y : UU} (w : X ≃ Y) (P : Y -> UU)
           (x : X) (p : P (w x)) :
  transportf (P ∘ w) (! homotinvweqweq w x) p
  = transportf P (! homotweqinvweq w (w x)) p.
Proof.
  intros. refine (functtransportf w P (!homotinvweqweq w x) p @ _).
  apply (maponpaths (λ e, transportf P e p)).
  rewrite maponpathsinv0. apply maponpaths. apply homotweqinvweqweq.
Defined.

Definition weq_transportb_adjointness {X Y : UU} (w : X ≃ Y) (P : Y -> UU)
           (x : X) (p : P (w x)) :
  transportb (P ∘ w) (homotinvweqweq w x) p
  = transportb P (homotweqinvweq w (w x)) p.
Proof.
  intros.
  refine (functtransportb w P (homotinvweqweq w x) p @ _).
  apply (maponpaths (λ e, transportb P e p)).
  apply homotweqinvweqweq.
Defined.

(** *** Transport functions are weak equivalences *)

Lemma isweqtransportf {X : UU} (P : X -> UU) {x x' : X}
      (e : x = x') : isweq (transportf P e).
Proof.
  intros. induction e. unfold transportf. simpl. apply idisweq.
Defined.

Lemma isweqtransportb {X : UU} (P : X -> UU) {x x' : X}
      (e : x = x') : isweq (transportb P e).
Proof.
  intros. apply (isweqtransportf _ (pathsinv0 e)).
Defined.

(** *** Weak equivalences between contractible types (one implication) *)

Lemma iscontrweqb {X Y : UU} (w : X ≃ Y) (is : iscontr Y) : iscontr X.
Proof.
  intros. apply (iscontrretract (invmap w) w (homotinvweqweq w) is).
Defined.

(** *** [ unit ] and contractibility *)

(** [ unit ] is contractible (recall that [ tt ] is the name of the
    canonical term of the type [ unit ]). *)

Lemma isProofIrrelevantUnit : ∏ x x' : unit, x = x'.
Proof.
  intros. induction x. induction x'. apply idpath.
Defined.

Lemma unitl0 : tt = tt -> coconustot _ tt.
Proof.
  intros e. apply (coconustotpair unit e).
Defined.

Lemma unitl1: coconustot _ tt -> tt = tt.
Proof.
  intro cp. induction cp as [x t]. induction x. exact t.
Defined.

Lemma unitl2: ∏ e : tt = tt, unitl1 (unitl0 e) = e.
Proof.
  intros. unfold unitl0. simpl. apply idpath.
Defined.

Lemma unitl3: ∏ e : tt = tt, e = idpath tt.
Proof.
  intros.

  assert (e0 : unitl0 (idpath tt) = unitl0 e).
  { apply connectedcoconustot. }

  set (e1 := maponpaths unitl1 e0).

  apply (! (unitl2 e) @ (! e1) @ (unitl2 (idpath _))).
Defined.

Theorem iscontrunit: iscontr (unit).
Proof.
  split with tt. intros t. apply (isProofIrrelevantUnit t tt).
Defined.

(** [ paths ] in [ unit ] are contractible. *)

Theorem iscontrpathsinunit (x x' : unit) : iscontr (x = x').
Proof.
  intros.
  split with (isProofIrrelevantUnit x x').
  intros e'.
  induction x.
  induction x'.
  simpl.
  apply unitl3.
Defined.

(** A type [ T : UU ] is contractible if and only if [ T -> unit ] is
    a weak equivalence. *)

Lemma ifcontrthenunitl0 (e1 e2 : tt = tt) : e1 = e2.
Proof.
  intros.
  apply proofirrelevancecontr.
  apply (iscontrpathsinunit tt tt).
Defined.

Lemma isweqcontrtounit {T : UU} (is : iscontr T) : isweq (λ (_ : T), tt).
Proof.
  intros. unfold isweq. intro y. induction y.
  induction is as [c h].
  set (hc := hfiberpair _ c (idpath tt)).
  split with hc.
  intros ha.
  induction ha as [x e].
  unfold hc. unfold hfiberpair. unfold isProofIrrelevantUnit.
  simpl.
  apply (λ q, two_arg_paths_f (h x) q).
  apply ifcontrthenunitl0.
Defined.

Definition weqcontrtounit {T : UU} (is : iscontr T) : T ≃ unit :=
  weqpair _ (isweqcontrtounit is).

Theorem iscontrifweqtounit {X : UU} (w : X ≃ unit) : iscontr X.
Proof.
  intros.
  apply (iscontrweqb w).
  apply iscontrunit.
Defined.

(** *** Homotopy equivalence is a weak equivalence *)

Definition hfibersgftog {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (xe : hfiber (g ∘ f) z) : hfiber g z :=
  hfiberpair g (f (pr1 xe)) (pr2 xe).

Lemma constr2 {X Y : UU} (f : X -> Y) (g : Y -> X)
      (efg: ∏ y : Y, f (g y) = y) (x0 : X) (xe : hfiber g x0) :
  ∑ xe' : hfiber (g ∘ f) x0, xe = hfibersgftog f g x0 xe'.
Proof.
  intros.
  induction xe as [y0 e].
  set (eint := pathssec1 _ _ efg _ _ e).
  set (ee := ! (maponpaths g eint) @ e).
  split with (hfiberpair (g ∘ f) x0 ee).
  unfold hfibersgftog.
  unfold hfiberpair.
  simpl.
  apply (two_arg_paths_f eint).
  induction eint.
  apply idpath.
Defined.

Lemma iscontrhfiberl1 {X Y : UU} (f : X -> Y) (g : Y -> X)
      (efg: ∏ y : Y, f (g y) = y) (x0 : X)
      (is : iscontr (hfiber (g ∘ f) x0)) : iscontr (hfiber g x0).
Proof.
  intros.
  set (f1 := hfibersgftog f g x0).
  set (g1 := λ (xe : hfiber g x0), pr1 (constr2 f g efg x0 xe)).
  set (efg1 := λ (xe : hfiber g x0), ! (pr2 (constr2 f g efg x0 xe))).
  apply (iscontrretract f1 g1 efg1).
  apply is.
Defined.

Definition homothfiber1 {X Y : UU} (f g : X -> Y)
           (h : f ~ g) (y : Y) (xe : hfiber f y) : hfiber g y.
Proof.
  intros.
  set (x := pr1 xe).
  set (e := pr2 xe).
  apply (hfiberpair g x (!(h x) @ e)).
Defined.

Definition homothfiber2 {X Y : UU} (f g : X -> Y)
           (h : f ~ g) (y : Y) (xe : hfiber g y) : hfiber f y.
Proof.
  intros.
  set (x := pr1 xe).
  set (e := pr2 xe).
  apply (hfiberpair f x (h x @ e)).
Defined.

Definition homothfiberretr {X Y : UU} (f g : X -> Y)
           (h : f ~ g) (y : Y) (xe : hfiber g y) :
  homothfiber1 f g h y (homothfiber2 f g h y xe) = xe.
Proof.
  intros.
  induction xe as [x e].
  simpl.
  fold (hfiberpair g x e).
  set (xe1 := hfiberpair g x (! h x @ h x @ e)).
  set (xe2 := hfiberpair g x e).
  apply (hfibertriangle2 g xe1 xe2 (idpath _)).
  simpl.

  (* A little lemma: *)
  assert (ee : ∏ a b c : Y, ∏ p : a = b, ∏ q : b = c,
                                               !p @ (p @ q) = q).
  { intros. induction p. induction q. apply idpath. }

  apply ee.
Defined.

Lemma iscontrhfiberl2 {X Y : UU} (f g : X -> Y)
      (h : f ~ g) (y : Y) (is : iscontr (hfiber f y)) : iscontr (hfiber g y).
Proof.
  intros.
  set (a := homothfiber1 f g h y).
  set (b := homothfiber2 f g h y).
  set (eab := homothfiberretr f g h y).
  apply (iscontrretract a b eab is).
Defined.

Corollary isweqhomot {X Y : UU} (f1 f2 : X -> Y)
          (h : f1 ~ f2) : isweq f1 -> isweq f2.
Proof.
  intros X Y f1 f2 h x0.
  unfold isweq.
  intro y.
  apply (iscontrhfiberl2 f1 f2 h).
  apply x0.
Defined.

Corollary remakeweq {X Y : UU} {f:X≃Y} {g:X->Y} : f ~ g -> X≃Y.
(* this lemma may be used to replace an equivalence by one whose forward map has a simpler definition,
   keeping the same inverse map, judgmentally *)
Proof.
  intros ? ? ? ? e.
  exact (g ,, isweqhomot f g e (weqproperty f)).
Defined.

Lemma remakeweq_eq {X Y : UU} (f1:X≃Y) (f2:X->Y) (e:f1~f2) : pr1weq (remakeweq e) = f2.
(* check the claim in the comment above *)
Proof.
  intros. apply idpath.
Defined.

Lemma remakeweq_eq' {X Y : UU} (f1:X≃Y) (f2:X->Y) (e:f1~f2) : invmap (remakeweq e) = invmap f1.
(* check the claim in the comment above *)
Proof.
  intros. apply idpath.
Defined.

Lemma iscontr_move_point {X} : X -> iscontr X -> iscontr X.
Proof.
  intros ? x i.
  exists x.
  intro y.
  apply proofirrelevancecontr.
  exact i.
Defined.

Lemma iscontr_move_point_eq {X} (x:X) (i:iscontr X) : iscontrpr1 (iscontr_move_point x i) = x.
Proof.
  intros. apply idpath.
Defined.

Corollary remakeweqinv {X Y : UU} {f:X≃Y} {h:Y->X} : invmap f ~ h -> X≃Y.
(* this lemma may be used to replace an equivalence by one whose inverse map is simpler,
   leaving the forward map the same, judgmentally *)
Proof.
  intros ? ? ? ? e. exists f. intro y.
  assert (p : hfiber f y).
  { exists (h y). apply pathsweq1', pathsinv0. apply e. }
  exact (iscontr_move_point p (weqproperty f y)).
Defined.

Lemma remakeweqinv_eq {X Y : UU} (f:X≃Y) (h:Y->X) (e:invmap f ~ h) : pr1weq (remakeweqinv e) = pr1weq f.
(* check the claim in the comment above *)
Proof.
  intros. apply idpath.
Defined.

Lemma remakeweqinv_eq' {X Y : UU} (f:X≃Y) (h:Y->X) (e:invmap f ~ h) : invmap (remakeweqinv e) = h.
(* check the claim in the comment above *)
Proof.
  intros. apply idpath.
Defined.

Corollary remakeweqboth {X Y : UU} {f:X≃Y} {g:X->Y} {h:Y->X} : f ~ g -> invmap f ~ h -> X≃Y.
(* this lemma may be used to replace an equivalence by one whose two maps are simpler *)
Proof.
  intros ? ? ? ? ? r s.
  use (remakeweqinv (f := remakeweq r) s).
Defined.

Lemma remakeweqboth_eq {X Y : UU} (f:X≃Y) (g:X->Y) (h:Y->X) (r:f~g) (s:invmap f ~ h) :
  pr1weq (remakeweqboth r s) = g.
Proof.
  intros. apply idpath.
Defined.

Lemma remakeweqboth_eq' {X Y : UU} (f:X≃Y) (g:X->Y) (h:Y->X) (r:f~g) (s:invmap f ~ h) :
  invmap (remakeweqboth r s) = h.
Proof.
  intros. apply idpath.
Defined.

Corollary isweqhomot_iff {X Y : UU} (f1 f2 : X -> Y)
          (h : f1 ~ f2) : isweq f1 <-> isweq f2.
Proof.
  intros. split.
  - apply isweqhomot; assumption.
  - apply isweqhomot, invhomot; assumption.
Defined.

Lemma isweq_to_isweq_unit {X:UU} (f g:X->unit) : isweq f -> isweq g.
Proof.
  intros ? ? ? i.
  assert (h : f ~ g).
  { intros t. apply isProofIrrelevantUnit. }
  exact (isweqhomot f g h i).
Defined.

Theorem gradth {X Y : UU} (f : X -> Y) (g : Y -> X)
        (egf: ∏ x : X, g (f x) = x)
        (efg: ∏ y : Y, f (g y) = y) : isweq f.
Proof.
  intros.
  unfold isweq.
  intro y.
  assert (X0 : iscontr (hfiber (f ∘ g) y)).
  assert (efg' : ∏ y : Y, y = f (g y)).
  { intro y0.
    apply pathsinv0.
    apply (efg y0). }
  apply (iscontrhfiberl2 (idfun _) (f ∘ g) efg' y (idisweq Y y)).
  apply (iscontrhfiberl1 g f egf y).
  apply X0.
Defined.

Definition weqgradth {X Y : UU} (f : X -> Y) (g : Y -> X)
           (egf: ∏ x : X, g (f x) = x)
           (efg: ∏ y : Y, f (g y) = y) : X ≃ Y :=
  weqpair _ (gradth _ _ egf efg).

Definition UniqueConstruction {X Y:UU} (f:X->Y) :=
  (∏ y, ∑ x, f x = y) × (∏ x x', f x = f x' -> x = x').

Corollary UniqueConstruction_to_weq {X Y:UU} (f:X->Y) : UniqueConstruction f -> isweq f.

Proof.
  intros ? ? ? bij. assert (sur := pr1 bij). assert (inj := pr2 bij).
  use (gradth f).
  - intros y. exact (pr1 (sur y)).
  - intros. simpl. simpl in inj. apply inj. exact (pr2 (sur (f x))).
  - intros. simpl. exact (pr2 (sur y)).
Defined.

(** *** Some weak equivalences *)

(* ### *)

Corollary isweqinvmap {X Y : UU} (w : X ≃ Y) : isweq (invmap w).
Proof.
  intros.
  assert (efg : ∏ (y : Y), w (invmap w y) = y).
  apply homotweqinvweq.
  assert (egf : ∏ (x : X), invmap w (w x) = x).
  apply homotinvweqweq.
  apply (gradth _ _ efg egf).
Defined.

Definition invweq {X Y : UU} (w : X ≃ Y) : Y ≃ X :=
  weqpair (invmap w) (isweqinvmap w).

Lemma invinv {X Y : UU} (w : X ≃ Y) (x : X) :
  invmap (invweq w) x = w x.
Proof.
  intros. apply idpath.
Defined.

Lemma pr1_invweq {X Y : UU} (w : X ≃ Y) : pr1weq (invweq w) = invmap w.
(* useful for rewriting *)
Proof.
  intros. apply idpath.
Defined.

Corollary iscontrweqf {X Y : UU} (w : X ≃ Y) (is : iscontr X) : iscontr Y.
Proof.
  intros. apply (iscontrweqb (invweq w) is).
Defined.

(** Equality between pairs is equivalent to pairs of equalities
    between components. Theorem adapted from HoTT library
    http://github.com/HoTT/HoTT.
 *)

Definition PathPair {A : UU} {B : A -> UU} (x y : ∑ x, B x) :=
  ∑ p : pr1 x = pr1 y, transportf _ p (pr2 x) = pr2 y.

Notation "a ╝ b" := (PathPair a b) (at level 70, no associativity) : type_scope.
(* the two horizontal lines represent an equality in the base and
   the two vertical lines represent an equality in the fiber *)
(* in agda input mode use \--= and select the 6-th one in the first set,
   or use \chimney *)

Theorem total2_paths_equiv {A : UU} (B : A -> UU) (x y : ∑ x, B x) :
  x = y  ≃  x ╝ y.
Proof.
  intros.
  exists (λ r : x = y,
            tpair (λ p : pr1 x = pr1 y, transportf _ p (pr2 x) = pr2 y)
                  (base_paths _ _ r) (fiber_paths r)).
  apply (gradth _ (λ pq, total2_paths_f (pr1 pq) (pr2 pq))).
  - intro p.
    apply total2_fiber_paths.
  - intros [p q]. simpl.
    apply (two_arg_paths_f (base_total2_paths q)).
    apply transportf_fiber_total2_paths.
Defined.

(** The standard weak equivalence from [ unit ] to a contractible type *)

Definition wequnittocontr {X : UU} (is : iscontr X) : unit ≃ X.
Proof.
  intros.
  set (f := λ (_ : unit), pr1 is).
  set (g := λ (_ : X), tt).
  split with f.
  assert (egf : ∏ t : unit, g (f t) = t).
  { intro. induction t. apply idpath. }
  assert (efg : ∏ x : X, f (g x) = x).
  { intro. apply (! (pr2 is x)). }
  apply (gradth _ _ egf efg).
Defined.

(** A weak equivalence between types defines weak equivalences on the
    corresponding [ paths ] types. *)

Corollary isweqmaponpaths {X Y : UU} (w : X ≃ Y) (x x' : X) :
  isweq (@maponpaths _ _ w x x').
Proof.
  intros.
  apply (gradth (@maponpaths _ _ w x x')
                (@invmaponpathsweq _ _ w x x')
                (@pathsweq3 _ _ w x x')
                (@pathsweq4 _ _ w x x')).
Defined.

Definition weqonpaths {X Y : UU} (w : X ≃ Y) (x x' : X) : x = x' ≃ w x = w x'
  := weqpair _ (isweqmaponpaths w x x').

(** The inverse path and the composition with a path functions are weak equivalences *)

Corollary isweqpathsinv0 {X : UU} (x x' : X) : isweq (@pathsinv0 _ x x').
Proof.
  intros.
  apply (gradth (@pathsinv0 _ x x')
                (@pathsinv0 _ x' x)
                (@pathsinv0inv0 _ _ _)
                (@pathsinv0inv0 _ _ _)).
Defined.

Definition weqpathsinv0 {X : UU} (x x' : X) : x = x' ≃ x' = x
  := weqpair _ (isweqpathsinv0 x x').

Corollary isweqpathscomp0r {X : UU} (x : X) {x' x'' : X} (e' : x' = x'') :
  isweq (λ e : x = x', e @ e').
Proof.
  intros.
  set (f := λ e : x = x', e @ e').
  set (g := λ e'' : x = x'', e'' @ (! e')).
  assert (egf : ∏ e : _, g (f e) = e).
  { intro e. induction e. induction e'. apply idpath. }
  assert (efg : ∏ e : _, f (g e) = e).
  { intro e. induction e. induction e'. apply idpath. }
  apply (gradth f g egf efg).
Defined.

(** Weak equivalences to and from coconuses and total path spaces *)

Corollary isweqtococonusf {X Y : UU} (f : X -> Y) : isweq (tococonusf f).
Proof.
  intros.
  apply (gradth _ _ (homotfromtococonusf f) (homottofromcoconusf f)).
Defined.

Definition weqtococonusf {X Y : UU} (f : X -> Y) : X ≃ coconusf f :=
  weqpair _ (isweqtococonusf f).

Corollary isweqfromcoconusf {X Y : UU} (f : X -> Y) : isweq (fromcoconusf f).
Proof.
  intros.
  apply (gradth _ _ (homottofromcoconusf f) (homotfromtococonusf f)).
Defined.

Definition weqfromcoconusf {X Y : UU} (f : X -> Y) : coconusf f ≃ X :=
  weqpair _ (isweqfromcoconusf f).

Corollary isweqdeltap (T : UU) : isweq (deltap T).
Proof.
  intros.
  set (ff := deltap T). set (gg := λ (z : pathsspace T), pr1 z).
  assert (egf : ∏ t : T, gg (ff t) = t).
  { intro. apply idpath. }
  assert (efg : ∏ (tte : _), ff (gg tte) = tte).
  { intro tte. induction tte as [t c].
    induction c as [x e]. induction e.
    apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.

Corollary isweqpr1pr1 (T : UU) :
  isweq (λ (a : pathsspace' T), pr1 (pr1 a)).
Proof.
  intros.
  set (f := λ (a : pathsspace' T), pr1 (pr1 a)).
  set (g := λ (t : T),
              tpair _ (dirprodpair t t) (idpath t) : pathsspace' T).
  assert (efg : ∏ t : T, f (g t) = t).
  { intros t. unfold f. unfold g. simpl. apply idpath. }
  assert (egf : ∏ a : _, g (f a) = a).
  { intros a. induction a as [xy e].
    induction xy as [x y]. simpl in e.
    induction e. unfold f. unfold g.
    apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.

(** The weak equivalence between hfibers of homotopic functions *)

Theorem weqhfibershomot {X Y : UU} (f g : X -> Y)
        (h : f ~ g) (y : Y) : hfiber f y ≃ hfiber g y.
Proof.
  intros.
  set (ff := hfibershomotftog f g h y).
  set (gg := hfibershomotgtof f g h y).

  split with ff.

  assert (effgg : ∏ xe : _, ff (gg xe) = xe).
  {
    intro xe.
    induction xe as [x e].
    simpl.
    assert (eee : ! h x @ h x @ e = maponpaths g (idpath x) @ e).
    { simpl.  induction e. induction (h x). apply idpath. }
    set (xe1 := hfiberpair g x (! h x @ h x @ e)).
    set (xe2 := hfiberpair g x e).
    apply (hfibertriangle2 g xe1 xe2 (idpath x) eee).
  }

  assert (eggff : ∏ xe : _, gg (ff xe) = xe).
  {
    intro xe.
    induction xe as [x e].
    simpl.
    assert (eee :  h x @ !h x @ e = maponpaths f (idpath x) @ e).
    { simpl.  induction e. induction (h x). apply idpath. }
    set (xe1 := hfiberpair f x (h x @ ! h x @ e)).
    set (xe2 := hfiberpair f x e).
    apply (hfibertriangle2 f xe1 xe2 (idpath x) eee).
  }

  apply (gradth _ _ eggff effgg).
Defined.

(** *** The 2-out-of-3 property of weak equivalences

    Theorems showing that if any two of three functions f, g, gf are
    weak equivalences then so is the third - the 2-out-of-3 property.
 *)

Theorem twooutof3a {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isgf: isweq (g ∘ f)) (isg: isweq g) : isweq f.
Proof.
  intros.
  set (gw := weqpair g isg).
  set (gfw := weqpair (g ∘ f) isgf).
  set (invg := invmap gw).
  set (invgf := invmap gfw).

  set (invf := invgf ∘ g).

  assert (efinvf : ∏ y : Y, f (invf y) = y).
  {
    intro y.
    assert (int1 : g (f (invf y)) = g y).
    { unfold invf. apply (homotweqinvweq gfw (g y)). }
    apply (invmaponpathsweq gw _ _  int1).
  }

  assert (einvff: ∏ x : X, invf (f x) = x).
  { intro. unfold invf. apply (homotinvweqweq gfw x). }

  apply (gradth f invf einvff efinvf).
Defined.

Theorem twooutof3b {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isgf : isweq (g ∘ f)) : isweq g.
Proof.
  intros.
  set (wf := weqpair f isf).
  set (wgf := weqpair (g ∘ f) isgf).
  set (invf := invmap wf).
  set (invgf := invmap wgf).

  set (invg := f ∘ invgf).

  assert (eginvg : ∏ z : Z, g (invg z) = z).
  { intro. unfold invg. apply (homotweqinvweq wgf z). }

  assert (einvgg : ∏ y : Y, invg (g y) = y).
  { intro. unfold invg.

    assert (isinvf: isweq invf).
    { apply isweqinvmap. }
    assert (isinvgf: isweq invgf).
    { apply isweqinvmap. }

    assert (int1 : g y = (g ∘ f) (invf y)).
    apply (maponpaths g (! homotweqinvweq wf y)).

    assert (int2 : (g ∘ f) (invgf (g y)) = (g ∘ f) (invf y)).
    {
      assert (int3: (g ∘ f) (invgf (g y)) = g y).
      { apply (homotweqinvweq wgf). }
      induction int1.
      apply int3.
    }

    assert (int4: (invgf (g y)) = (invf y)).
    { apply (invmaponpathsweq wgf). apply int2. }

    assert (int5: (invf (f (invgf (g y)))) = (invgf (g y))).
    { apply (homotinvweqweq wf). }

    assert (int6: (invf (f (invgf (g (y))))) = (invf y)).
    { induction int4. apply int5. }

    apply (invmaponpathsweq (weqpair invf isinvf)).
    simpl.
    apply int6.
  }

  apply (gradth g invg einvgg eginvg).
Defined.

Lemma isweql3 {X Y : UU} (f : X -> Y) (g : Y -> X)
      (egf : ∏ x : X, g (f x) = x) : isweq f -> isweq g.
Proof.
  intros ? ? ? ? ? w.
  assert (int1 : isweq (g ∘ f)).
  {
    apply (isweqhomot (idfun X) (g ∘ f) (λ (x : X), ! (egf x))).
    apply idisweq.
  }
  apply (twooutof3b f g w int1).
Defined.

Theorem twooutof3c {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Proof.
  intros.
  set (wf := weqpair f isf).
  set (wg := weqpair g isg).
  set (invf := invmap wf).
  set (invg := invmap wg).

  set (gf := g ∘ f).
  set (invgf := invf ∘ invg).

  assert (egfinvgf : ∏ x : X, invgf (gf x) = x).
  {
    intros x.
    assert (int1 : invf (invg (g (f x))) = invf (f x)).
    { apply (maponpaths invf (homotinvweqweq wg (f x))). }
    assert (int2 : invf (f x) = x).
    { apply (homotinvweqweq wf x). }
    induction int1.
    apply int2.
  }

  assert (einvgfgf : ∏ z : Z, gf (invgf z) = z).
  {
    intros z.
    assert (int1 : g (f (invgf z)) = g (invg z)).
    {
      unfold invgf.
      apply (maponpaths g (homotweqinvweq wf (invg z))).
    }
    assert (int2 : g (invg z) = z).
    { apply (homotweqinvweq wg z). }
    induction int1.
    apply int2.
  }

  apply (gradth gf invgf egfinvgf einvgfgf).
Defined.

Corollary twooutof3c_iff_2 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) :
  isweq f -> (isweq g <-> isweq (g ∘ f)).
Proof.
  intros ? ? ? ? ? i. split.
  - intro j. exact (twooutof3c f g i j).
  - intro j. exact (twooutof3b f g i j).
Defined.

Corollary twooutof3c_iff_1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) :
  isweq g -> (isweq f <-> isweq (g ∘ f)).
Proof.
  intros ? ? ? ? ? i. split.
  - intro j. exact (twooutof3c f g j i).
  - intro j. exact (twooutof3a f g j i).
Defined.

Corollary twooutof3c_iff_1_homot {X Y Z : UU}
          (f : X -> Y) (g : Y -> Z) (h : X -> Z) :
  g ∘ f ~ h  -> isweq g -> (isweq f <-> isweq h).
Proof.
  intros ? ? ? ? ? ? r i.
  apply (logeq_trans (Y := isweq (g ∘ f))).
  - apply twooutof3c_iff_1; assumption.
  - apply isweqhomot_iff; assumption.
Defined.

Corollary twooutof3c_iff_2_homot {X Y Z : UU}
          (f : X -> Y) (g : Y -> Z) (h : X -> Z) :
  g ∘ f ~ h  -> isweq f -> (isweq g <-> isweq h).
Proof.
  intros ? ? ? ? ? ? r i.
  apply (logeq_trans (Y := isweq (g ∘ f))).
  - apply twooutof3c_iff_2; assumption.
  - apply isweqhomot_iff; assumption.
Defined.

(** *** Any function between contractible types is a weak equivalence *)

Corollary isweqcontrcontr {X Y : UU} (f : X -> Y)
          (isx : iscontr X) (isy: iscontr Y): isweq f.
Proof.
  intros.
  set (py := λ (y : Y), tt).
  apply (twooutof3a f py (isweqcontrtounit isx) (isweqcontrtounit isy)).
Defined.

Definition weqcontrcontr {X Y : UU} (isx : iscontr X) (isy : iscontr Y) :=
  weqpair _ (isweqcontrcontr (λ (_ : X), pr1 isy) isx isy).

(** *** Composition of weak equivalences *)

Definition weqcomp {X Y Z : UU} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z :=
  weqpair (λ (x : X), w2 (w1 x)) (twooutof3c w1 w2 (pr2 w1) (pr2 w2)).

Notation "g ∘ f" := (weqcomp f g) (at level 50, left associativity) : weq_scope.

Delimit Scope weq_scope with weq.

Ltac intermediate_weq Y' := apply (weqcomp (Y := Y')).

Definition weqcomp_to_funcomp_app {X Y Z : UU} {x : X} {f : X ≃ Y} {g : Y ≃ Z} :
  (weqcomp f g) x = pr1weq g (pr1weq f x).
Proof.
  intros. apply idpath.
Defined.

Definition weqcomp_to_funcomp {X Y Z : UU} {f : X ≃ Y} {g : Y ≃ Z} :
  pr1weq (weqcomp f g) = pr1weq g ∘ pr1weq f.
Proof.
  intros. apply idpath.
Defined.

Definition invmap_weqcomp_expand {X Y Z : UU} {f : X ≃ Y} {g : Y ≃ Z} :
  invmap (weqcomp f g) = invmap f ∘ invmap g.
Proof.
  intros. apply idpath.
Defined.

(** *** The 2-out-of-6 (two-out-of-six) property of weak equivalences *)

Theorem twooutofsixu {X Y Z K : UU} {u : X -> Y} {v : Y -> Z} {w : Z -> K}
        (isuv : isweq (funcomp u v)) (isvw : isweq (funcomp v w)) : isweq u.
Proof.
  intros.

  set (invuv := invmap (weqpair _ isuv)).
  set (pu := funcomp v invuv).
  set (hupu := homotinvweqweq (weqpair _ isuv)
               : homot (funcomp u pu) (idfun X)).

  set (invvw := invmap (weqpair _ isvw)).
  set (pv := funcomp w invvw).
  set (hvpv := homotinvweqweq (weqpair _ isvw)
               : homot (funcomp v pv) (idfun Y)).

  set (h0 := funhomot v (homotweqinvweq (weqpair _ isuv))).
  set (h1 := funhomot (funcomp pu u) (invhomot hvpv)).
  set (h2 := homotfun h0 pv).

  set (hpuu := homotcomp (homotcomp h1 h2) hvpv).

  exact (gradth u pu hupu hpuu).
Defined.

Theorem twooutofsixv {X Y Z K : UU} {u : X -> Y} {v : Y -> Z} {w : Z -> K}
        (isuv : isweq (funcomp u v))(isvw : isweq (funcomp v w)) : isweq v.
Proof.
  intros. exact (twooutof3b _ _ (twooutofsixu isuv isvw) isuv).
Defined.

Theorem twooutofsixw {X Y Z K : UU} {u : X -> Y} {v : Y -> Z} {w : Z -> K}
        (isuv : isweq (funcomp u v))(isvw : isweq (funcomp v w)) : isweq w.
Proof.
  intros. exact (twooutof3b _ _ (twooutofsixv isuv isvw) isvw).
Defined.

(** *** Pairwise direct products of weak equivalences *)

Theorem isweqdirprodf {X Y X' Y' : UU} (w : X ≃ Y) (w' : X' ≃ Y') :
  isweq (dirprodf w w').
Proof.
  intros.
  set (f := dirprodf w w'). set (g := dirprodf (invweq w) (invweq w')).
  assert (egf : ∏ a : _, (g (f a)) = a).
  intro a. induction a as [ x x' ].  simpl. apply pathsdirprod.
  apply (homotinvweqweq w x).  apply (homotinvweqweq w' x').
  assert (efg : ∏ a : _, (f (g a)) = a).
  intro a. induction a as [ x x' ].  simpl. apply pathsdirprod.
  apply (homotweqinvweq w x). apply (homotweqinvweq w' x').
  apply (gradth _ _ egf efg).
Defined.

Definition weqdirprodf {X Y X' Y' : UU} (w : X ≃ Y) (w' : X' ≃ Y') : X × X' ≃ Y × Y'
  := weqpair _ (isweqdirprodf w w').

(** *** Weak equivalence of a type and its direct product with the unit *)

Definition weqtodirprodwithunit (X : UU): X ≃ X × unit.
Proof.
  intros.
  set (f := λ x : X, dirprodpair x tt).
  split with f.
  set (g := λ xu : X × unit, pr1 xu).
  assert (egf : ∏ x : X, (g (f x)) = x). intro. apply idpath.
  assert (efg : ∏ xu : _, (f (g xu)) = xu). intro. induction xu as [ t x ].
  induction x. apply idpath.
  apply (gradth f g egf efg).
Defined.


(** *** Associativity of [ total2 ] as a weak equivalence *)

Lemma total2asstor {X : UU} (P : X -> UU) (Q : total2 P -> UU) :
  total2 Q ->  ∑ x:X, ∑ p : P x, Q (tpair P x p).
Proof.
  intros X P Q xpq.
  exists (pr1 (pr1 xpq)).
  exists (pr2 (pr1 xpq)).
  induction xpq as [ xp q ].
  induction xp as [ x p ].
  assumption.
Defined.

Lemma total2asstol {X : UU} (P : X -> UU) (Q : total2 P -> UU) :
  (∑ x : X, ∑ p : P x, Q (tpair P x p)) -> total2 Q.
Proof.
  intros X P Q xpq.
  use tpair.
  - use tpair.
    + apply (pr1 xpq).
    + apply (pr1 (pr2 xpq)).
  - induction xpq as [ x pq ].
    induction pq as [ p q ].
    assumption.
Defined.


Theorem weqtotal2asstor {X : UU} (P : X -> UU) (Q : total2 P -> UU) :
  total2 Q ≃ ∑ x : X, ∑ p : P x, Q (tpair P x p).
Proof.
  intros.
  set (f := total2asstor P Q). set (g:= total2asstol P Q).
  split with f.
  assert (egf : ∏ xpq : _ , (g (f xpq)) = xpq).
  intro. induction xpq as [ xp q ]. induction xp as [ x p ]. apply idpath.
  assert (efg : ∏ xpq : _ , (f (g xpq)) = xpq).
  intro. induction xpq as [ x pq ]. induction pq as [ p q ]. apply idpath.
  apply (gradth _ _ egf efg).
Defined.

Definition weqtotal2asstol {X : UU} (P : X -> UU) (Q : total2 P -> UU) :
  (∑ x : X, ∑ p : P x, Q (tpair P x p)) ≃ total2 Q
  := invweq (weqtotal2asstor P Q).

(** *** Associativity and commutativity of direct products as weak equivalences *)

Definition weqdirprodasstor (X Y Z : UU) : (X × Y) × Z ≃ X × (Y × Z).
Proof.
  intros. apply weqtotal2asstor.
Defined.

Definition weqdirprodasstol (X Y Z : UU) : X × (Y × Z) ≃ (X × Y) × Z
  := invweq (weqdirprodasstor X Y Z).

Definition weqdirprodcomm (X Y : UU) : X × Y ≃ Y × X.
Proof.
  intros.
  set (f := λ xy : X × Y, dirprodpair (pr2 xy) (pr1 xy)).
  set (g := λ yx : Y × X, dirprodpair (pr2 yx) (pr1 yx)).
  assert (egf : ∏ xy : _, (g (f xy)) = xy).
  intro. induction xy. apply idpath.
  assert (efg : ∏ yx : _, (f (g yx)) = yx).
  intro. induction yx. apply idpath.
  split with f. apply (gradth _ _ egf efg).
Defined.

Definition weqtotal2dirprodcomm {X Y : UU} (P : X × Y -> UU) :
  (∑ xy : X × Y, P xy) ≃ (∑ xy : Y × X, P (weqdirprodcomm _ _ xy)).
Proof.
  intros.
  use weqgradth.
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    exact ((y,,x),,p).
  - intros yxp. induction yxp as [yx p]. induction yx as [y x].
    exact ((x,,y),,p).
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    apply idpath.
  - intros yxp. induction yxp as [yx p]. induction yx as [y x].
    apply idpath.
Defined.

Definition weqtotal2dirprodassoc  {X Y : UU} (P : X × Y -> UU) :
  (∑ xy : X × Y, P xy) ≃ (∑ (x : X) (y : Y), P (x,,y)).
  intros.
  use weqgradth.
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    exact (x,,y,,p).
  - intros xyp. induction xyp as [x yp]. induction yp as [y p].
    exact ((x,,y),,p).
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    apply idpath.
  - intros xyp. induction xyp as [x yp]. induction yp as [y p].
    apply idpath.
Defined.

Definition weqtotal2dirprodassoc' {X Y : UU} (P : X × Y -> UU) :
  (∑ xy : X × Y, P xy) ≃ (∑ (y : Y) (x : X), P (x,,y)).
Proof.
  intros.
  use weqgradth.
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    exact (y,,x,,p).
  - intros yxp. induction yxp as [x yp]. induction yp as [y p].
    exact ((y,,x),,p).
  - intros xyp. induction xyp as [xy p]. induction xy as [x y].
    apply idpath.
  - intros yxp. induction yxp as [x yp]. induction yp as [y p].
    apply idpath.
Defined.

Definition weqtotal2comm12 {X} (P Q : X -> UU) :
  (∑ (w : ∑ x, P x), Q (pr1 w)) ≃ (∑ (w : ∑ x, Q x), P (pr1 w)).
Proof.
  intros.
  use weqgradth.
  - intros [[x p] q]. exact ((x,,q),,p).
  - intros [[x q] p]. exact ((x,,p),,q).
  - intros [[x p] q]. apply idpath.
  - intros [[x q] p]. apply idpath.
Defined.

(** ** Binary coproducts and their basic properties *)

(** Binary coproducts have not been introduced or used earlier except for the
lines in the Preamble.v that define [ coprod ] and [ ⨿ ] as a notation for
the inductive type family [ sum ] that is defined in Coq.Init. *)

(** *** Distributivity of coproducts and direct products as a weak equivalence *)

Definition rdistrtocoprod (X Y Z : UU) :
  X × (Y ⨿ Z) -> (X × Y) ⨿ (X × Z).
Proof.
  intros X Y Z X0.
  induction X0 as [ t x ]. induction x as [ y | z ].
  apply (ii1 (dirprodpair t y)).
  apply (ii2 (dirprodpair t z)).
Defined.


Definition rdistrtoprod (X Y Z : UU) : (X × Y) ⨿ (X × Z) -> X × (Y ⨿ Z).
Proof.
  intros X Y Z X0.
  induction X0 as [ d | d ]. induction d as [ t x ].
  apply (dirprodpair t (ii1 x)).
  induction d as [ t x ]. apply (dirprodpair t (ii2 x)).
Defined.


Theorem isweqrdistrtoprod (X Y Z : UU) : isweq (rdistrtoprod X Y Z).
Proof.
  intros.
  set (f := rdistrtoprod X Y Z). set (g := rdistrtocoprod X Y Z).

  assert (egf: ∏ a, (g (f a)) = a).
  intro. induction a as [ d | d ]. induction d. apply idpath. induction d.
  apply idpath.

  assert (efg: ∏ a, (f (g a)) = a). intro. induction a as [ t x ].
  induction x. apply idpath. apply idpath.

  apply (gradth f g egf efg).
Defined.

Definition weqrdistrtoprod (X Y Z : UU) := weqpair _ (isweqrdistrtoprod X Y Z).

Corollary isweqrdistrtocoprod (X Y Z : UU) : isweq (rdistrtocoprod X Y Z).
Proof.
  intros. apply (isweqinvmap (weqrdistrtoprod X Y Z)).
Defined.

Definition weqrdistrtocoprod (X Y Z : UU)
  := weqpair _ (isweqrdistrtocoprod X Y Z).


(** *** Total space of a family over a coproduct *)

Definition fromtotal2overcoprod {X Y : UU} (P : X ⨿ Y -> UU) (xyp : total2 P) :
  coprod (∑ x : X, P (ii1 x)) (∑ y : Y, P (ii2 y)).
Proof.
  intros.
  set (PX := λ x : X, P (ii1 x)). set (PY := λ y : Y, P (ii2 y)).
  induction xyp as [ xy p ]. induction xy as [ x | y ].
  apply (ii1 (tpair PX x p)). apply (ii2 (tpair PY y p)).
Defined.

Definition tototal2overcoprod {X Y : UU} (P : X ⨿ Y -> UU)
           (xpyp : coprod (∑ x : X, P (ii1 x)) (∑ y : Y, P (ii2 y))) : total2 P.
Proof.
  intros.
  induction xpyp as [ xp | yp ]. induction xp as [ x p ].
  apply (tpair P (ii1 x) p).
  induction yp as [ y p ]. apply (tpair P (ii2 y) p).
Defined.

Theorem weqtotal2overcoprod {X Y : UU} (P : X ⨿ Y -> UU) :
  (∑ xy, P xy) ≃ (∑ x : X, P (ii1 x)) ⨿ (∑ y : Y, P (ii2 y)).
Proof.
  intros.
  set (f := fromtotal2overcoprod P). set (g := tototal2overcoprod P).
  split with f.
  assert (egf : ∏ a : _ , (g (f a)) = a).
  { intro a.
    induction a as [ xy p ].
    induction xy as [ x | y ].
    simpl.
    apply idpath.
    simpl.
    apply idpath. }
  assert (efg : ∏ a : _ , (f (g a)) = a).
  { intro a.
    induction a as [ xp | yp ].
    induction xp as [ x p ].
    simpl.
    apply idpath.
    induction yp as [ y p ].
    apply idpath. }
  apply (gradth _ _ egf efg).
Defined.

(** *** Pairwise sum of functions, coproduct associativity and commutativity  *)

Definition sumofmaps {X Y Z : UU} (fx : X -> Z)(fy : Y -> Z) :
  (X ⨿ Y) -> Z := λ xy : _, match xy with ii1 x => fx x | ii2 y => fy y end.

Definition coprodasstor (X Y Z : UU) : (X ⨿ Y) ⨿ Z -> X ⨿ (Y ⨿ Z).
Proof.
  intros X Y Z X0.
  induction X0 as [ c | z ]. induction c as [ x | y ].
  apply (ii1 x). apply (ii2 (ii1 y)). apply (ii2 (ii2 z)).
Defined.

Definition coprodasstol (X Y Z : UU): X ⨿ (Y ⨿ Z) -> (X ⨿ Y) ⨿ Z.
Proof.
  intros X Y Z X0.
  induction X0 as [ x | c ]. apply (ii1 (ii1 x)). induction c as [ y | z ].
  apply (ii1 (ii2 y)). apply (ii2 z).
Defined.

Definition sumofmaps_assoc_left {X Y Z T : UU} (f : X -> T) (g : Y -> T)
           (h : Z -> T) :
  sumofmaps (sumofmaps f g) h ∘ coprodasstol _ _ _ ~ sumofmaps f (sumofmaps g h).
Proof.
  intros. intros [x|[y|z]]; apply idpath.
Defined.

Definition sumofmaps_assoc_right {X Y Z T : UU} (f : X -> T) (g : Y -> T)
           (h : Z -> T) :
  sumofmaps f (sumofmaps g h) ∘ coprodasstor _ _ _ ~ sumofmaps (sumofmaps f g) h.
Proof.
  intros. intros [[x|y]|z]; apply idpath.
Defined.

Theorem isweqcoprodasstor (X Y Z : UU): isweq (coprodasstor X Y Z).
Proof.
  intros. set (f := coprodasstor X Y Z). set (g := coprodasstol X Y Z).
  assert (egf : ∏ xyz, (g (f xyz)) = xyz).
  intro xyz. induction xyz as [ c | z ].  induction c.
  apply idpath. apply idpath. apply idpath.
  assert (efg : ∏ xyz, (f (g xyz)) = xyz). intro xyz.
  induction xyz as [ x | c ].  apply idpath. induction c.
  apply idpath. apply idpath.
  apply (gradth f g egf efg).
Defined.

Definition weqcoprodasstor (X Y Z : UU) := weqpair _ (isweqcoprodasstor X Y Z).

Corollary isweqcoprodasstol (X Y Z : UU) : isweq (coprodasstol X Y Z).
Proof.
  intros. apply (isweqinvmap (weqcoprodasstor X Y Z)).
Defined.

Definition weqcoprodasstol (X Y Z : UU) := weqpair _ (isweqcoprodasstol X Y Z).

Definition coprodcomm (X Y : UU) : X ⨿ Y -> Y ⨿ X
  := λ xy : _, match xy with ii1 x => ii2 x | ii2 y => ii1 y end.

Theorem isweqcoprodcomm (X Y : UU) : isweq (coprodcomm X Y).
Proof.
  intros.
  set (f := coprodcomm X Y). set (g := coprodcomm Y X).
  assert (egf : ∏ xy : _, (g (f xy)) = xy). intro.
  induction xy. apply idpath. apply idpath.
  assert (efg : ∏ yx : _, (f (g yx)) = yx). intro.
  induction yx. apply idpath. apply idpath.
  apply (gradth f g egf efg).
Defined.

Definition weqcoprodcomm (X Y : UU) := weqpair _ (isweqcoprodcomm X Y).

(** *** Coproduct with a "negative" type *)

Theorem isweqii1withneg (X : UU) {Y : UU} (nf : Y -> empty) : isweq (@ii1 X Y).
Proof.
  intros.
  set (f := @ii1 X Y).
  set (g := λ xy : X ⨿ Y, match xy with
                          | ii1 x => x
                          | ii2 y => fromempty (nf y)
                          end).
  assert (egf : ∏ x : X, (g (f x)) = x). intro. apply idpath.
  assert (efg : ∏ xy : X ⨿ Y, (f (g xy)) = xy). intro.
  induction xy as [ x | y ]. apply idpath. apply (fromempty (nf y)).
  apply (gradth f g egf efg).
Defined.

Definition weqii1withneg (X : UU) {Y : UU} (nf : ¬ Y)
  := weqpair _ (isweqii1withneg X nf).

Theorem isweqii2withneg {X : UU} (Y : UU) (nf : X -> empty) : isweq (@ii2 X Y).
Proof.
  intros.
  set (f:= @ii2 X Y).
  set (g:= λ xy : X ⨿ Y, match xy with
                         | ii1 x => fromempty (nf x)
                         | ii2 y => y
                         end).
  assert (egf : ∏ y : Y, (g (f y)) = y). intro. apply idpath.
  assert (efg : ∏ xy : X ⨿ Y, (f (g xy)) = xy). intro.
  induction xy as [ x | y ]. apply (fromempty (nf x)). apply idpath.
  apply (gradth f g egf efg).
Defined.

Definition weqii2withneg {X : UU} (Y : UU) (nf : ¬ X)
  := weqpair _ (isweqii2withneg Y nf).

(** *** Coproduct of two functions *)

Definition coprodf {X Y X' Y' : UU} (f : X -> X') (g : Y-> Y') : X ⨿ Y -> X' ⨿ Y'
  := λ xy: X ⨿ Y,
           match xy with
           | ii1 x => ii1 (f x)
           | ii2 y => ii2 (g y)
           end.

Definition coprodf1 {X Y X' : UU} : (X -> X') -> X ⨿ Y -> X' ⨿ Y.
Proof.
  intros ? ? ? f. exact (coprodf f (idfun Y)).
Defined.

Definition coprodf2 {X Y Y' : UU} : (Y -> Y') -> X ⨿ Y -> X ⨿ Y'.
Proof.
  intros ? ? ? g. exact (coprodf (idfun X) g).
Defined.

Definition homotcoprodfcomp {X X' Y Y' Z Z' : UU} (f : X -> Y)
           (f' : X' -> Y') (g : Y -> Z) (g' : Y' -> Z') :
  homot (funcomp (coprodf f f') (coprodf g g'))
        (coprodf (funcomp f g) (funcomp f' g')).
Proof.
  intros. intro xx'. induction xx' as [ x | x' ].
  apply idpath. apply idpath.
Defined.


Definition homotcoprodfhomot {X X' Y Y' : UU} (f g : X -> Y)
           (f' g' : X' -> Y') (h : homot f g) (h' : homot f' g') :
  homot (coprodf f f') (coprodf g g')
  := λ xx' : _, match xx' with
                    | ii1 x  => maponpaths (@ii1 _ _) (h x)
                    | ii2 x' => maponpaths (@ii2 _ _) (h' x')
                    end.


Theorem isweqcoprodf {X Y X' Y' : UU} (w : X ≃ X') (w' : Y ≃ Y') :
  isweq (coprodf w w').
Proof.
  intros.
  set (finv := invmap w). set (ginv := invmap w').
  set (ff := coprodf w w'). set (gg := coprodf finv ginv).
  assert (egf : ∏ xy : X ⨿ Y, (gg (ff xy)) = xy).
  intro. induction xy as [ x | y ]. simpl.
  apply (maponpaths (@ii1 X Y) (homotinvweqweq w x)).
  apply (maponpaths (@ii2 X Y) (homotinvweqweq w' y)).
  assert (efg : ∏ xy' : coprod X' Y', (ff (gg xy')) = xy').
  intro. induction xy' as [ x | y ]. simpl.
  apply (maponpaths (@ii1 X' Y') (homotweqinvweq w x)).
  apply (maponpaths (@ii2 X' Y') (homotweqinvweq w' y)).
  apply (gradth ff gg egf efg).
Defined.

Definition weqcoprodf {X Y X' Y' : UU} : X ≃ X' -> Y ≃ Y' -> X ⨿ Y ≃ X' ⨿ Y'.
Proof.
  intros ? ? ? ? w1 w2. exact (weqpair _ (isweqcoprodf w1 w2)).
Defined.

Definition weqcoprodf1 {X Y X' : UU} : X ≃ X' -> X ⨿ Y ≃ X' ⨿ Y.
Proof.
  intros ? ? ? w. exact (weqcoprodf w (idweq Y)).
Defined.

Definition weqcoprodf2 {X Y Y' : UU} : Y ≃ Y' -> X ⨿ Y ≃ X ⨿ Y'.
Proof.
  intros ? ? ? w. exact (weqcoprodf (idweq X) w).
Defined.

(** *** The [ equality_cases ] construction and four applications to [ ii1 ] and [ ii2 ] *)

(* Added by D. Grayson, Nov. 2015 *)

Definition equality_cases {P Q : UU} (x x' : P ⨿ Q) : UU.
Proof.
                           (* "codes" *)
  intros. induction x as [p|q].
  - induction x' as [p'|q'].
    + exact (p = p').
    + exact empty.
  - induction x' as [p'|q'].
    + exact empty.
    + exact (q = q').
Defined.

Definition equality_by_case {P Q : UU} {x x' : P ⨿ Q} :
  x = x'-> equality_cases x x'.
Proof.
  intros ? ? ? ? e. induction x as [p|q].
  - induction x' as [p'|q'].
    + simpl.
      exact (maponpaths (@coprod_rect P Q (λ _, P) (λ p, p) (λ _, p)) e).
    + simpl.
      exact (transportf (@coprod_rect P Q (λ _, UU) (λ _, unit) (λ _, empty))
                        e tt).
  - induction x' as [p'|q'].
    + simpl.
      exact (transportb (@coprod_rect P Q (λ _, UU) (λ _, unit) (λ _, empty))
                        e tt).
    + simpl.
      exact (maponpaths (@coprod_rect P Q (λ _,Q) (λ _, q) (λ q, q)) e).
Defined.

Definition inv_equality_by_case {P Q : UU} {x x' : P ⨿ Q} :
  equality_cases x x' -> x = x'.
Proof.
  intros ? ? ? ? e.
  induction x as [p|q].
  - induction x' as [p'|q'].
    + exact (maponpaths (@ii1 P Q) e).
    + induction e.
  - induction x' as [p'|q'].
    + induction e.
    + exact (maponpaths (@ii2 P Q) e).
Defined.

(* the same proof proves 4 lemmas: *)

Lemma ii1_injectivity {P Q : UU} (p p' : P) :
  ii1 (B := Q) p = ii1 (B := Q) p' -> p = p'.
Proof.
  intros ? ? ? ?. exact equality_by_case.
Defined.

Lemma ii2_injectivity {P Q : UU} (q q' : Q) :
  ii2 (A := P) q = ii2 (A := P) q' -> q = q'.
Proof.
  intros ? ? ? ?. exact equality_by_case.
Defined.

Lemma negpathsii1ii2 {X Y : UU} (x : X) (y : Y) : ii1 x != ii2 y.
Proof.
  intros ? ? ? ?. exact equality_by_case.
Defined.

Lemma negpathsii2ii1 {X Y : UU} (x : X) (y : Y) : ii2 y != ii1 x.
Proof.
  intros ? ? ? ?. exact equality_by_case.
Defined.


(** *** Bool as coproduct *)

Definition boolascoprod: unit ⨿ unit ≃ bool.
Proof.
  set (f := λ xx : coprod unit unit,
                   match xx with ii1 t => true | ii2 t => false end).
  split with f.
  set (g := λ t:bool, match t with true => ii1 tt | false => ii2 tt end).

  assert (egf : ∏ xx : _, g (f xx) = xx).
  intro xx. induction xx as [ u | u ]. induction u. apply idpath.
  induction u. apply idpath.

  assert (efg : ∏ t : _, f (g t) = t). induction t. apply idpath.
  apply idpath.

  apply (gradth f g egf efg).
Defined.


(** *** Pairwise coproducts as dependent sums of families over [ bool ] *)

Definition coprodtobool {X Y : UU} (xy : X ⨿ Y) : bool
  := match xy with
     | ii1 x => true
     | ii2 y => false
     end.

Definition boolsumfun (X Y : UU) : bool -> UU
  := λ t : _, match t with
                  | true => X
                  | false => Y
                  end.

Definition coprodtoboolsum (X Y : UU) : X ⨿ Y -> total2 (boolsumfun X Y)
  := λ xy : _, match xy with
                   | ii1 x => tpair (boolsumfun X Y) true x
                   | ii2 y => tpair (boolsumfun X Y) false y
                   end.

Definition boolsumtocoprod (X Y : UU): (total2 (boolsumfun X Y)) -> X ⨿ Y
  := λ xy, match xy with
           | tpair _ true x => ii1 x
           | tpair _ false y => ii2 y
           end.

Theorem isweqcoprodtoboolsum (X Y : UU) : isweq (coprodtoboolsum X Y).
Proof.
  intros.
  set (f := coprodtoboolsum X Y). set (g := boolsumtocoprod X Y).
  assert (egf : ∏ xy : X ⨿ Y , (g (f xy)) = xy).
  induction xy. apply idpath. apply idpath.
  assert (efg : ∏ xy : total2 (boolsumfun X Y), (f (g xy)) = xy).
  intro. induction xy as [ t x ]. induction t. apply idpath. apply idpath.
  apply (gradth f g egf efg).
Defined.

Definition weqcoprodtoboolsum (X Y : UU) := weqpair _ (isweqcoprodtoboolsum X Y).

Corollary isweqboolsumtocoprod (X Y : UU): isweq (boolsumtocoprod X Y).
Proof.
  intros. apply (isweqinvmap (weqcoprodtoboolsum X Y)).
Defined.

Definition weqboolsumtocoprod (X Y : UU) := weqpair _ (isweqboolsumtocoprod X Y).


(** *** Splitting of [ X ] into a coproduct defined by a function [ X -> Y ⨿ Z ] *)

Definition weqcoprodsplit {X Y Z : UU} (f : X -> coprod Y Z) :
  X ≃ (∑ y : Y, hfiber f (ii1 y)) ⨿ (∑ z : Z, hfiber f (ii2 z)).
Proof.
  intros.
  set (w1 := weqtococonusf f).
  set (w2 := weqtotal2overcoprod (λ yz : coprod Y Z, hfiber f yz)).
  apply (weqcomp w1 w2).
Defined.


(** *** Some properties of [ bool ] *)

Definition boolchoice (x : bool) : (x = true) ⨿ (x = false).
Proof.
  intro. induction x. apply (ii1 (idpath _)). apply (ii2 (idpath _)).
Defined.

Definition bool_to_type : bool -> UU.
Proof.
  intros b. induction b as [|]. { exact unit. } { exact empty. }
Defined.

Theorem nopathstruetofalse : true = false -> empty.
Proof.
  intro X. apply (transportf bool_to_type X tt).
Defined.

Corollary nopathsfalsetotrue : false = true -> empty.
Proof.
  intro X. apply (transportb bool_to_type X tt).
Defined.

Definition truetonegfalse (x : bool) : x = true -> x != false.
Proof.
  intros x e. rewrite e. unfold neg. apply nopathstruetofalse.
Defined.

Definition falsetonegtrue (x : bool) : x = false -> x != true.
Proof.
  intros x e. rewrite e. unfold neg. apply nopathsfalsetotrue.
Defined.

Definition negtruetofalse (x : bool) : x != true -> x = false.
Proof.
  intros x ne. induction (boolchoice x) as [t | f]. induction (ne t). apply f.
Defined.

Definition negfalsetotrue (x : bool) : x != false -> x = true.
Proof.
  intros x ne. induction (boolchoice x) as [t | f]. apply t. induction (ne f).
Defined.


(** *** Fibrations with only one non-empty fiber

Theorem saying that if a fibration has only one non-empty fiber then the total
space is weakly equivalent to this fiber. *)

(* The current proof added by P. L. Lumsdaine, 2016 *)

Theorem onefiber {X : UU} (P : X -> UU) (x : X)
        (c : ∏ x' : X, (x = x') ⨿ ¬ P x') : isweq (λ p, tpair P x p).
Proof.
  intros.
  set (f := λ p : P x, tpair _ x p).
  set (cx := c x).
  transparent assert (cnew : (∏ x' : X, (x = x') ⨿ ¬ P x')).
  { intro x'. refine (coprod_rect (λ _, _) _ _ (cx)).
    - intro x0. refine (coprod_rect (λ _, _) _ _ (c x')).
      + intro ee. apply ii1; exact (pathscomp0 (pathsinv0 x0) ee).
      + intro phi. apply ii2, phi.
    - intro phi. exact (c x'). }


  set (g := λ pp : total2 P,
              match (cnew (pr1 pp)) with
              | ii1 e => transportb P e (pr2 pp)
              | ii2 phi => fromempty (phi (pr2 pp))
              end).


  assert (efg : ∏ pp : total2 P, (f (g pp)) = pp).
  intro. induction pp as [ t x0 ]. set (cnewt := cnew t).
  unfold g. unfold f. simpl. change (cnew t) with cnewt.
  induction cnewt as [ x1 | y ].
  apply (pathsinv0 (pr1 (pr2 (constr1 P (pathsinv0 x1))) x0)).
  induction (y x0).

  set (cnewx := cnew x).
  assert (e1 : (cnew x) = cnewx). apply idpath.
  unfold cnew in cnewx. change (c x) with cx in cnewx.
  induction cx as [ x0 | e0 ].
  assert (e : (cnewx) = (ii1  (idpath x))).
  apply (maponpaths (@ii1 (x = x) (P x -> empty)) (pathsinv0l x0)).

  assert (egf : ∏ p: P x, (g (f p)) = p). intro. simpl in g.
  unfold g. unfold f. simpl.

  set (ff := λ cc:(x = x) ⨿ (P x -> empty),
               match cc with
               | ii1 e0 => transportb P e0 p
               | ii2 phi => fromempty  (phi p)
               end).
  assert (ee : (ff (cnewx)) = (ff (@ii1 (x = x) (P x -> empty) (idpath x)))).
  apply (maponpaths ff e).
  assert (eee : (ff (@ii1 (x = x) (P x -> empty) (idpath x))) = p). apply idpath.
  fold (ff (cnew x)).
  assert (e2 : (ff (cnew x)) = (ff cnewx)). apply (maponpaths ff e1).
  apply (pathscomp0 (pathscomp0 e2 ee) eee).
  apply (gradth f g egf efg).

  unfold isweq. intro y0. induction (e0 (g y0)).
Defined.




(** ** Basics about fibration sequences. *)



(** *** Fibrations sequences and their first "left shifts"

The group of constructions related to fibration sequences forms one of the most
important computational toolboxes of homotopy theory.

Given a pair of functions [ (f : X -> Y) (g : Y -> Z) ] and a point [ z : Z ] ,
a structure of the complex on such a triple is a homotopy from the composition
[ funcomp f g ] to the constant function [ X -> Z ] corresponding to [ z ] i.e.
a term [ ez : ∏ x : X, (g (f x)) = z ]. Specifing such a structure is
essentially equivalent to specifing a structure of the form
[ ezmap : X -> hfiber g z ]. The mapping in one direction is given in the
definition of [ ezmap ] below. The mapping in another is given by
[ f := λ x : X, pr1 (ezmap x) ] and [ ez := λ x : X, pr2 (ezmap x) ].

A complex is called a fibration sequence if [ ezmap ] is a weak equivalence.
Correspondingly, the structure of a fibration sequence on [ f g z ] is a pair
[ (ez , is) ] where [ is : isweq (ezmap f g z ez) ]. For a fibration sequence
[ f g z fs ]  where [ fs : fibseqstr f g z ] and any [ y : Y ] there is defined
a function [ diff1 : (g y) = z -> X ] and a structure of the fibration
sequence [ fibseqdiff1 ] on the triple [ diff1 g y ]. This new fibration
sequence is called the derived fibration sequence of the original one.

The first function of the second derived of [ f g z fs ] corresponding to
[ (y : Y) (x : X) ]  is of the form [ (f x) = y -> (g y) = z ] and it is
homotopic to the function defined by
[ e => pathscomp0 (maponpaths g (pathsinv0 e)) (ez x) ]. The first function of
the third derived of [ f g z fs ] corresponding to
[ (y : Y) (x : X) (e : (g y) = z) ] is of the form
[ (diff1 e) = x -> (f x) = y ]. Therefore, the third derived of a sequence based
on [ X Y Z ] is based entirely on types = of [ X ], [ Y ] and [ Z ]. When this
construction is applied to types of finite h-level (see below) and combined with
the fact that the h-level of a path type is strictly lower than the h-level of
the ambient type it leads to the possibility of building proofs about types by
induction on h-level.

There are three important special cases in which fibration sequences arise:

( pr1 - case ) The fibration sequence [ fibseqpr1 P z ] defined by family
[ P : Z -> UU ] and a term [ z : Z ]. It is based on the sequence of functions
[ (tpair P z : P z -> total2 P) (pr1 : total2 P -> Z) ]. The corresponding
[ ezmap ] is defined by an obvious rule and the fact that it is a weak
equivalence is proved in [ isweqfibertohfiber ].

( g - case ) The fibration sequence [ fibseqg g z ]  defined by a function
[ g : Y -> Z ] and a term [ z : Z ]. It is based on the sequence of functions
[ (hfiberpr1 : hfiber g z -> Y) (g : Y -> Z) ] and the corresponding [ ezmap ]
is the function which takes a term [ ye : hfiber ] to
[ hfiberpair g (pr1 ye) (pr2 ye) ].   We now have eta-coercion for dependent
sums, so it is the identity function,
which is sufficient to ensure that it is a weak equivalence. The first derived
of [ fibseqg g z ] corresponding to [ y : Y ] coincides with
[ fibseqpr1 (λ y' : Y , (g y') = z) y ].

( hf -case ) The fibration sequence of homotopy fibers defined for any pair of
functions [ (f : X -> Y) (g : Y -> Z) ] and any terms
[ (z : Z) (ye : hfiber g z) ]. It is based on functions
[ hfiberftogf : hfiber f (pr1 ye) -> hfiber (funcomp f g) z ] and
[ hfibergftog : hfiber (funcomp f g) z -> hfiber g z ] which are defined below.
 *)

(** *** The structures of a complex and of a fibration sequence on a composable pair of functions *)

(** The structure of a complex on a composable pair of functions
  [ (f : X -> Y) (g : Y -> Z) ] relative to a term [ z : Z ]. *)

Definition complxstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
  := ∏ x : X, (g (f x)) = z.


(** The structure of a fibration sequence on a complex. *)

Definition ezmap {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ez : complxstr f g z) :
  X -> hfiber g z := λ x : X, hfiberpair g (f x) (ez x).

Definition isfibseq {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ez : complxstr f g z) := isweq (ezmap f g z ez).

Definition fibseqstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
  := ∑ ez : complxstr f g z, isfibseq f g z ez.
Definition fibseqstrpair {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
  := tpair (λ ez : complxstr f g z, isfibseq f g z ez).
Definition fibseqstrtocomplxstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z) :
  fibseqstr f g z -> complxstr f g z
  := @pr1 _ (λ ez : complxstr f g z, isfibseq f g z ez).
Coercion fibseqstrtocomplxstr : fibseqstr >-> complxstr.

Definition ezweq {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) : X ≃ hfiber g z
  := weqpair _ (pr2 fs).



(** *** Construction of the derived fibration sequence *)


Definition d1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) : (g y) = z -> X
  := λ e : _, invmap (ezweq f g z fs) (hfiberpair g y e).

Definition ezmap1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) (e : (g y) = z) : hfiber f y.
Proof.
  intros.
  split with (d1 f g z fs y e).
  unfold d1.
  change (f (invmap (ezweq f g z fs) (hfiberpair g y e)))
  with (hfiberpr1 _ _ (ezweq f g z fs (invmap (ezweq f g z fs)
                                              (hfiberpair g y e)))).
  apply (maponpaths (hfiberpr1 g z)
                    (homotweqinvweq (ezweq f g z fs) (hfiberpair g y e))).
Defined.

Definition invezmap1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ez : complxstr f g z) (y : Y) : hfiber f y -> (g y) = z
  := λ xe: hfiber f y,
           match xe with
             tpair _ x e => pathscomp0 (maponpaths g (pathsinv0 e)) (ez x)
           end.

Theorem isweqezmap1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (fs : fibseqstr f g z) (y : Y) : isweq (ezmap1 f g z fs y).
Proof.
  intros.
  set (ff := ezmap1 f g z fs y). set (gg := invezmap1 f g z (pr1 fs) y).
  assert (egf : ∏ e : _, (gg (ff e)) = e).
  intro. simpl.
  apply (hfibertriangle1inv0 g (homotweqinvweq (ezweq f g z fs)
                                               (hfiberpair g y e))).
  assert (efg : ∏ xe : _, (ff (gg xe)) = xe).
  intro. induction xe as [ x e ]. induction e. simpl.
  unfold ff. unfold ezmap1. unfold d1.
  change (hfiberpair g (f x) (pr1 fs x)) with (ezmap f g z fs x).
  apply (hfibertriangle2
           f (hfiberpair f (invmap (ezweq f g z fs) (ezmap f g z fs x)) _)
           (hfiberpair f x (idpath _))
           (homotinvweqweq (ezweq f g z fs) x)).
  simpl.
  set (e1 := pathsinv0 (pathscomp0rid (maponpaths f (homotinvweqweq
                                                       (ezweq f g z fs) x)))).
  assert (e2 : (maponpaths (hfiberpr1 g z)
                           (homotweqinvweq (ezweq f g z fs)
                                           ((ezmap f g z fs) x)))
               = (maponpaths f (homotinvweqweq (ezweq f g z fs) x))).
  set (e3 := maponpaths (λ e : _, maponpaths (hfiberpr1 g z) e)
                        (pathsinv0 (homotweqinvweqweq (ezweq f g z fs) x))).
  simpl in e3.
  set (e4 := maponpathscomp (ezmap f g z (pr1 fs)) (hfiberpr1 g z)
                            (homotinvweqweq (ezweq f g z fs) x)).
  simpl in e4. apply (pathscomp0 e3 e4). apply (pathscomp0 e2 e1).
  apply (gradth _ _ egf efg).
Defined.

Definition ezweq1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) := weqpair _ (isweqezmap1 f g z fs y).

Definition fibseq1 {X Y Z : UU} (f :X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) : fibseqstr (d1 f g z fs y) f y
  := fibseqstrpair _ _ _ _ (isweqezmap1 f g z fs y).



(** *** Explicit description of the first map in the second derived sequence *)

Definition d2 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) (x : X) (e : (f x) = y) :
  (g y) = z := pathscomp0 (maponpaths g (pathsinv0 e)) ((pr1 fs) x).
Definition ezweq2 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) (x : X) :
  f x = y  ≃  hfiber (d1 f g z fs y) x
  := ezweq1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x.
Definition fibseq2 {X Y Z : UU} (f : X -> Y) (g : Y->Z) (z : Z)
           (fs : fibseqstr f g z) (y : Y) (x : X) :
  fibseqstr (d2 f g z fs y x) (d1 f g z fs y) x
  := fibseqstrpair _ _ _ _
                   (isweqezmap1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x).



(** *** Fibration sequences based on [ tpair P z ] and [ pr1 : total2 P -> Z ] ( the "pr1-case" ) *)


(** Construction of the fibration sequence. *)

Definition ezmappr1 {Z : UU} (P : Z -> UU) (z : Z) :
  P z -> hfiber (@pr1 Z P) z
  := λ p : P z, tpair _ (tpair _  z p) (idpath z).

Definition invezmappr1 {Z : UU} (P : Z -> UU) (z : Z) :
  hfiber (@pr1 Z P) z -> P z
  := λ te, transportf P (pr2 te) (pr2 (pr1 te)).

Definition isweqezmappr1 {Z : UU} (P : Z -> UU) (z : Z) :
  isweq (ezmappr1 P z).
Proof.
  intros.
  assert (egf : ∏ x: P z , (invezmappr1 _ z ((ezmappr1 P z) x)) = x).
  intro. unfold ezmappr1. unfold invezmappr1. simpl. apply idpath.
  assert (efg : ∏ x: hfiber (@pr1 Z P) z ,
                     (ezmappr1 _ z (invezmappr1 P z x)) = x).
  intros. induction x as [ x t0 ]. induction t0. simpl in x. simpl.
  induction x. simpl. unfold transportf. unfold ezmappr1. apply idpath.
  apply (gradth _ _ egf efg).
Defined.

Definition ezweqpr1 {Z : UU} (P : Z -> UU) (z : Z)
  := weqpair _ (isweqezmappr1 P z).

Lemma isfibseqpr1 {Z : UU} (P : Z -> UU) (z : Z) :
  isfibseq (λ p : P z, tpair _ z p) (@pr1 Z P) z (λ p : P z, idpath z).
Proof.
  intros. unfold isfibseq. unfold ezmap. apply isweqezmappr1.
Defined.

Definition fibseqpr1 {Z : UU} (P : Z -> UU) (z : Z) :
  fibseqstr (λ p : P z, tpair _ z p) (@pr1 Z P) z
  := fibseqstrpair _ _ _ _ (isfibseqpr1 P z).


(** The main weak equivalence defined by the first derived of [ fibseqpr1 ]. *)

Definition ezweq1pr1 {Z : UU} (P : Z -> UU) (z : Z) (zp : total2 P) :
  pr1 zp = z  ≃  hfiber (tpair P z) zp
  := ezweq1 _ _ z (fibseqpr1 P z) zp.







(** *** Fibration sequences based on [ hfiberpr1 : hfiber g z -> Y ] and [ g : Y -> Z ] (the "g-case") *)


Theorem isfibseqg {Y Z : UU} (g : Y -> Z) (z : Z) :
  isfibseq (hfiberpr1 g z) g z (λ ye: _, pr2 ye).
Proof.
  intros.
  simple refine (isweqhomot _ _ _ (idisweq _)).
  - intro. apply idpath.
Defined.

Definition ezweqg {Y Z : UU} (g : Y -> Z) (z : Z) := weqpair _ (isfibseqg g z).
Definition fibseqg {Y Z : UU} (g : Y -> Z) (z : Z)
  : fibseqstr (hfiberpr1 g z) g z := fibseqstrpair _ _ _ _ (isfibseqg g z).


(** The first derived of [ fibseqg ]. *)

Definition d1g {Y Z : UU} (g : Y -> Z) (z : Z) (y : Y) :
  (g y) = z -> hfiber g z := hfiberpair g y.

(** note that [ d1g ] coincides with [ d1 _ _ _ (fibseqg g z) ] which makes
  the following two definitions possible. *)

Definition ezweq1g {Y Z : UU} (g : Y -> Z) (z : Z) (y : Y) :
  g y = z ≃  hfiber (hfiberpr1 g z) y
  := weqpair _ (isweqezmap1 (hfiberpr1  g z) g z (fibseqg g z) y).
Definition fibseq1g {Y Z : UU} (g : Y -> Z) (z : Z) (y : Y) :
  fibseqstr (d1g g z y) (hfiberpr1 g z) y
  := fibseqstrpair _ _ _ _ (isweqezmap1 (hfiberpr1 g z) g z (fibseqg g z) y).


(** The second derived of [ fibseqg ]. *)

Definition d2g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z)
           (e: (pr1 ye') = y) : (g y) = z
  := pathscomp0 (maponpaths g (pathsinv0 e)) (pr2  ye').

(** note that [ d2g ] coincides with [ d2 _ _ _ (fibseqg g z) ] which makes
  the following two definitions possible. *)

Definition ezweq2g
           {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z) :
  (pr1 ye') = y  ≃  hfiber (hfiberpair g y) ye'
  := ezweq2 _ _ _ (fibseqg g z) _ _.
Definition fibseq2g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z) :
  fibseqstr (d2g g y ye') (hfiberpair g y) ye'
  := fibseq2 _ _ _ (fibseqg g z) _ _.


(** The third derived of [ fibseqg ] and an explicit description of the
  corresponding first map. *)

Definition d3g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z)
           (e : (g y) = z) : (hfiberpair g y e) = ye' -> (pr1 ye') = y
  := d2 (d1g  g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e.

Lemma homotd3g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z)
      (e : (g y) = z) (ee : (hfiberpair g y e) = ye') :
  (d3g g y ye' e ee) = (maponpaths (@pr1 _ _) (pathsinv0 ee)).
Proof.
  intros. unfold d3g. unfold d2. simpl. apply pathscomp0rid.
Defined.

Definition ezweq3g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z)
           (e : (g y) = z)
  := ezweq2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e.
Definition fibseq3g {Y Z : UU} (g : Y -> Z) {z : Z} (y : Y) (ye' : hfiber g z)
           (e : (g y) = z)
  := fibseq2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e.



(** *** Fibration sequence of h-fibers defined by a composable pair of functions (the "hf-case")

  We construct a fibration sequence based on [ hfibersftogf f g z ye : hfiber f (pr1 ye) -> hfiber gf z) ]
  and [ hfibersgftog f g z : hfiber gf z -> hfiber g z) ].

*)




Definition hfibersftogf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) (xe : hfiber f (pr1 ye)) : hfiber (funcomp f g) z.
Proof.
  intros.
  split with (pr1 xe).
  apply (pathscomp0 (maponpaths g (pr2 xe)) (pr2 ye)).
Defined.



Definition ezmaphf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) (xe : hfiber f (pr1 ye)) :
  hfiber (hfibersgftog f g z) ye.
Proof.
  intros.
  split with (hfibersftogf f g z ye xe). simpl.
  apply (hfibertriangle2
           g (hfiberpair g (f (pr1 xe)) (pathscomp0 (maponpaths g (pr2 xe))
                                                    (pr2 ye))) ye (pr2 xe)).
  simpl. apply idpath.
Defined.

Definition invezmaphf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) (xee' : hfiber (hfibersgftog f g z) ye) :
  hfiber f (pr1 ye).
Proof.
  intros.
  split with (pr1 (pr1 xee')).
  apply (maponpaths (hfiberpr1 _ _) (pr2 xee')).
Defined.

Definition ffgg {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) (xee' : hfiber (hfibersgftog f g z) ye) :
  hfiber (hfibersgftog f g z) ye.
Proof.
  intros.
  induction ye as [ y e ]. induction e. unfold hfibersgftog.
  unfold hfibersgftog in xee'.
  induction xee' as [ xe e' ]. induction xe as [ x e ].
  set (e'' := (maponpaths g (maponpaths (hfiberpr1 g (g y)) e'))).
  simpl in e'.
  split with (hfiberpair (funcomp f g) x (pathscomp0 e'' (idpath (g y)))).
  simpl.
  apply (hfibertriangle2 _ (hfiberpair g (f x) (pathscomp0 e'' (idpath (g y))))
                         (hfiberpair g y (idpath _))
                         (maponpaths (hfiberpr1 _ _) e') (idpath _)).
Defined.

Definition homotffggid {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) (xee' : hfiber (hfibersgftog f g z) ye) :
  (ffgg f g z ye xee') = xee'.
Proof.
  intros.
  induction ye as [ y e ]. induction e.
  induction xee' as [ xe e' ]. induction e'.
  induction xe as [ x e ]. induction e.
  simpl. apply idpath.
Defined.

Theorem isweqezmaphf {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (z : Z) (ye : hfiber g z) : isweq (ezmaphf f g z ye).
Proof.
  intros.
  set (ff := ezmaphf f g z ye). set (gg := invezmaphf f g z ye).
  assert (egf : ∏ xe : _ , (gg (ff xe)) = xe).
  induction ye as [ y e ]. induction e. intro xe.
  apply (hfibertriangle2 f (gg (ff xe)) xe (idpath (pr1 xe))).
  induction xe as [ x ex ]. simpl in ex. induction ex. simpl. apply idpath.
  assert (efg : ∏ xee' : _ , (ff (gg xee')) = xee').
  induction ye as [ y e ]. induction e. intro xee'.
  assert (hint : (ff (gg xee'))
                 = (ffgg f g (g y) (hfiberpair g y (idpath _)) xee')).
  induction xee' as [ xe e' ]. induction xe as [ x e ]. apply idpath.
  apply (pathscomp0 hint (homotffggid _ _ _ _ xee')).
  apply (gradth _ _ egf efg).
Defined.


Definition ezweqhf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) :
  hfiber f (pr1 ye) ≃ hfiber (hfibersgftog f g z) ye
  := weqpair _ (isweqezmaphf f g z ye).

Definition fibseqhf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) :
  fibseqstr (hfibersftogf f g z ye) (hfibersgftog f g z) ye
  := fibseqstrpair _ _ _ _ (isweqezmaphf f g z ye).

Definition isweqinvezmaphf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
           (ye : hfiber g z) :
  isweq (invezmaphf f g z ye) := pr2 (invweq (ezweqhf f g z ye)).


Corollary weqhfibersgwtog {X Y Z : UU} (w : X ≃ Y) (g : Y -> Z) (z : Z) :
  hfiber (funcomp w g) z ≃ hfiber g z.
Proof.
  intros.
  split with (hfibersgftog w g z).
  intro ye.
  apply (iscontrweqf (ezweqhf w g z ye) ((pr2 w) (pr1 ye))).
Defined.



(** ** Functions between total spaces of families


(** *** Function [ totalfun ] between total spaces from a family of functions between the fibers

Including theorems saying that a fiber-wise morphism between total spaces is a weak
equivalence if and only if all the morphisms between the fibers are weak
equivalences. *)

*)

Definition totalfun {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
  := (λ z: total2 P, tpair Q (pr1 z) (f (pr1 z) (pr2 z))).


Theorem isweqtotaltofib {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x):
  isweq (totalfun _ _ f) -> ∏ x : X, isweq (f x).
Proof.
  intros X P Q f X0 x.
  set (totp := total2 P). set (totq := total2 Q).
  set (totf := (totalfun _ _ f)).
  set (pip := λ z: totp, pr1  z). set (piq:= λ z: totq, pr1  z).
  set (hfx := hfibersgftog totf piq x). simpl in hfx.
  assert (H : isweq hfx). unfold isweq. intro y.
  set (int := invezmaphf totf piq x y).
  assert (X1 : isweq int). apply (isweqinvezmaphf totf piq x y).
  induction y as [ t e ].
  assert (is1 : iscontr (hfiber totf t)).
  apply (X0 t). apply (iscontrweqb (weqpair int X1) is1).
  set (ip := ezmappr1 P x). set (iq := ezmappr1 Q x).
  set (h := λ p: P x, hfx (ip p)).
  assert (is2 : isweq h).
  apply (twooutof3c ip hfx (isweqezmappr1 P x) H).
  set (h':= λ p: P x, iq ((f x) p)).
  assert (ee : ∏ p:P x, (h p) = (h' p)). intro. apply idpath.
  assert (X2 : isweq h'). apply (isweqhomot h h' ee is2).
  apply (twooutof3a (f x) iq X2).
  apply (isweqezmappr1 Q x).
Defined.


Definition weqtotaltofib {X : UU} (P Q : X -> UU) (f : ∏ x : X , P x -> Q x)
           (is : isweq (totalfun _ _ f)) (x : X) : P x ≃ Q x
  := weqpair _ (isweqtotaltofib P Q f is x).


Theorem isweqfibtototal {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x ≃ Q x) :
  isweq (totalfun _ _ f).
Proof.
  intros X P Q f.
  set (fpq := totalfun P Q f). set (pr1p := λ z : total2 P, pr1 z).
  set (pr1q := λ z : total2 Q, pr1  z).
  unfold isweq. intro xq.
  set (x:= pr1q xq).
  set (xqe:= hfiberpair pr1q xq (idpath _)).
  set (hfpqx:= hfibersgftog fpq pr1q x).

  assert (isint : iscontr (hfiber hfpqx xqe)).
  assert (isint1 : isweq hfpqx).
  set (ipx := ezmappr1 P x). set (iqx := ezmappr1 Q x).
  set (diag := λ p : P x, (iqx ((f x) p))).
  assert (is2: isweq diag).
  apply (twooutof3c (f x) iqx (pr2 (f x)) (isweqezmappr1 Q x)).
  apply (twooutof3b ipx hfpqx (isweqezmappr1 P x) is2).
  unfold isweq in isint1. apply (isint1 xqe).
  set (intmap := invezmaphf fpq pr1q x xqe).
  apply (iscontrweqf (weqpair intmap (isweqinvezmaphf fpq pr1q x xqe)) isint).
Defined.

Definition weqfibtototal {X : UU} (P Q : X -> UU) (f : ∏ x, P x ≃ Q x) :
  (∑ x, P x) ≃ (∑ x, Q x) := weqpair _ (isweqfibtototal P Q f).


(** *** Function [ fpmap ] between the total spaces from a function between the bases

Given [ X Y ] in [ UU ], [ P:Y -> UU ] and [ f: X -> Y ] we get a function
[ fpmap: total2 X (P f) -> total2 Y P ]. The main theorem of this section
asserts that the homotopy fiber of fpmap over [ yp:total Y P ] is naturally
weakly equivalent to the homotopy fiber of [ f ] over [ pr1 yp ]. In
particular, if  [ f ] is a weak equivalence then so is [ fpmap ]. *)


Definition fpmap {X Y : UU} (f : X -> Y) (P : Y -> UU) :
  (∑ x, P (f x)) -> (∑ y, P y) := λ z, tpair P (f (pr1 z)) (pr2 z).

Definition hffpmap2 {X Y : UU} (f : X -> Y) (P : Y -> UU) :
  (∑ x, P (f x)) -> ∑ u : total2 P, hfiber f (pr1 u).
Proof.
  intros X Y f P X0.
  set (u:= fpmap f P X0).
  split with u.
  set (x:= pr1  X0).
  split with x.
  simpl. apply idpath.
Defined.

Lemma centralfiber {X : UU} (P : X -> UU) (x : X) :
  isweq (λ p : P x, tpair (λ u : coconusfromt X x, P (pr1 u))
                              (coconusfromtpair X (idpath x)) p).
Proof.
  intros.
  set (f := λ p: P x, tpair (λ u: coconusfromt X x, P(pr1 u))
                                (coconusfromtpair X (idpath x)) p).
  set (g := λ z: total2 (λ u: coconusfromt X x, P (pr1 u)),
            transportf P (pathsinv0 (pr2 (pr1 z))) (pr2 z)).

  assert (efg : ∏ z : total2 (λ u : coconusfromt X x, P (pr1 u)),
                      (f (g z)) = z).
  intro.
  induction z as [ t x0 ]. induction t as [ t x1 ].
  simpl. induction x1. simpl. apply idpath.

  assert (egf : ∏ p : P x , (g (f p)) = p). intro. apply idpath.

  apply (gradth f g egf efg).
Defined.


Lemma isweqhff {X Y : UU} (f : X -> Y) (P : Y -> UU) : isweq (hffpmap2 f P).
Proof.
  intros.
  set (int := total2 (λ x : X, total2 (λ u : coconusfromt Y (f x),
                                             P (pr1  u)))).
  set (intpair := tpair (λ x:X, total2 (λ u : coconusfromt Y (f x),
                                              P (pr1  u)))).
  set (toint :=
         λ z : (total2 (λ u : total2 P, hfiber f (pr1 u))),
               intpair (pr1 (pr2 z))
                       (tpair (fun u: coconusfromt Y (f (pr1 (pr2 z))) => P (pr1 u))
                              (coconusfromtpair _ (pr2 (pr2 z))) (pr2 (pr1 z)))).
  set (fromint := λ z : int,
                        tpair (λ u : total2 P, hfiber f (pr1 u))
                              (tpair P (pr1 (pr1 (pr2 z))) (pr2 (pr2 z)))
                              (hfiberpair f (pr1 z) (pr2 (pr1 (pr2 z))))).

  assert (fromto : ∏ u : (total2 (λ u : total2 P, hfiber f (pr1 u))),
                         (fromint (toint u)) = u).
  simpl in toint. simpl in fromint. simpl.
  intro u. induction u as [ t x ]. induction x. induction t as [ p0 p1 ].
  simpl. unfold toint. unfold fromint. simpl. apply idpath.

  assert (tofrom : ∏ u : int, (toint (fromint u)) = u).
  intro. induction u as [ t x ]. induction x as [ t0 x ]. induction t0.
  simpl in x. simpl. unfold fromint. unfold toint. simpl. apply idpath.

  assert (is : isweq toint). apply (gradth toint fromint fromto tofrom).

  clear tofrom. clear fromto. clear fromint.
  set (h := λ u : total2 (λ x : X, P (f x)), toint ((hffpmap2 f P) u)).
  simpl in h.

  assert (l1 : ∏ x : X, isweq (λ p: P (f x),
                                 tpair (λ u : coconusfromt _ (f x), P (pr1 u))
                                       (coconusfromtpair _ (idpath (f x))) p)).
  intro. apply (centralfiber P (f x)).

  assert (X0 : isweq h).
  apply (isweqfibtototal
           (λ x : X, P (f x))
           (λ x : X, total2 (λ u : coconusfromt _ (f x), P (pr1 u)))
           (λ x : X, weqpair _ (l1 x))).

  apply (twooutof3a (hffpmap2 f P) toint X0 is).
Defined.

(** *** Homotopy fibers of [ fpmap ] *)

Definition hfiberfpmap {X Y : UU} (f : X -> Y) (P : Y -> UU) (yp : total2 P) :
  hfiber (fpmap f P) yp -> hfiber f (pr1 yp).
Proof.
  intros X Y f P yp X0.
  set (int1:= hfibersgftog (hffpmap2 f P)
                           (λ u : (∑ u : total2 P, hfiber f (pr1  u)),
                                  (pr1 u)) yp).
  set (phi := invezmappr1 (λ u:total2 P, hfiber f (pr1 u)) yp).
  apply (phi (int1 X0)).
Defined.


Theorem isweqhfiberfp {X Y : UU} (f : X -> Y) (P : Y -> UU) (yp : total2 P) :
  isweq (hfiberfpmap f P yp).
Proof.
  intros.

  set (int1 := hfibersgftog
                 (hffpmap2  f P)
                 (λ u : (total2 (λ u : total2 P, hfiber f (pr1 u))), (pr1 u))
                 yp).
  assert (is1 : isweq int1). simpl in int1.
  apply (pr2 (weqhfibersgwtog
                (weqpair _ (isweqhff f P))
                (λ u : total2 (λ u : total2 P, hfiber f (pr1 u)), pr1 u) yp)).

  set (phi := invezmappr1 (λ u : total2 P, hfiber f (pr1 u)) yp).
  assert (is2 : isweq phi).
  apply (pr2 (invweq (ezweqpr1 (λ u : total2 P, hfiber f (pr1 u)) yp))).

  apply (twooutof3c int1 phi is1 is2).
Defined.

(** *** The [ fpmap ] from a weak equivalence is a weak equivalence *)

Corollary isweqfpmap {X Y : UU} (w : X ≃ Y)(P : Y -> UU) : isweq (fpmap w P).
Proof.
  intros.
  unfold isweq. intro y. set (h := hfiberfpmap w P y).
  assert (X1 : isweq h). apply isweqhfiberfp.
  assert (is : iscontr (hfiber w (pr1 y))). apply (pr2 w).
  apply (iscontrweqb (weqpair h X1) is).
Defined.

Definition weqfp_map {X Y : UU} (w : X ≃ Y) (P : Y -> UU) :
  (∑ x, P(w x)) -> (∑ y, P y).
Proof.
  intros ? ? ? ? xp. exact (w (pr1 xp),,pr2 xp).
Defined.

Definition weqfp_invmap {X Y : UU} (w : X ≃ Y) (P : Y -> UU) :
  (∑ y, P y) -> (∑ x, P(w x)).
Proof.
  intros ? ? ? ? yp.
  exact (invmap w (pr1 yp),,
                transportf P (! homotweqinvweq w (pr1 yp)) (pr2 yp)).
Defined.

Definition weqfp {X Y : UU} (w : X ≃ Y) (P : Y -> UU) :
  (∑ x : X, P (w x)) ≃ (∑ y, P y).
Proof.
  intros.
  exists (weqfp_map w P).
  refine (gradth _ (weqfp_invmap w P) _ _).
  { intros xp. use total2_paths_f.
    { simpl. apply homotinvweqweq. }
    simpl. rewrite <- weq_transportf_adjointness.
    rewrite transport_f_f. rewrite pathsinv0l.
    apply idpath. }
  { intros yp. simple refine (total2_paths_f _ _).
    { simpl. apply homotweqinvweq. }
    simpl. rewrite transport_f_f. rewrite pathsinv0l. apply idpath. }
Defined.

Definition weqfp_compute_1 {X Y : UU} (w : X ≃ Y) (P : Y -> UU) :
  weqfp w P ~ weqfp_map w P.
Proof.
  intros. intros xp. apply idpath.
Defined.

Definition weqfp_compute_2 {X Y : UU} (w : X ≃ Y) (P : Y -> UU) :
  invmap (weqfp w P) ~ weqfp_invmap w P.
Proof.
  intros. intros yp. apply idpath.
Defined.

Definition weqtotal2overcoprod' {W X Y : UU} (P : W -> UU) (f : X ⨿ Y ≃ W) :
  (∑ w, P w) ≃ (∑ x : X, P (f (ii1 x))) ⨿ (∑ y : Y, P (f (ii2 y))).
Proof.
  intros.
  exact (weqcomp (invweq (weqfp f _)) (weqtotal2overcoprod (P ∘ f))).
Defined.

(** *** Total spaces of families over a contractible base *)

Definition fromtotal2overunit (P : unit -> UU) (tp : total2 P) : P tt.
Proof.
  intros. induction tp as [ t p ]. induction t. apply p.
Defined.

Definition tototal2overunit (P : unit -> UU) (p : P tt) : total2 P
  := tpair P tt p.

Theorem weqtotal2overunit (P : unit -> UU) : (∑ u, P u) ≃ P tt.
Proof.
  intro.
  set (f := fromtotal2overunit P). set (g := tototal2overunit P).
  split with f.
  assert (egf : ∏ a : _ , (g (f a)) = a).
  intro a. induction a as [ t p ]. induction t. apply idpath.
  assert (efg : ∏ a : _ , (f (g a)) = a).
  intro a. apply idpath. apply (gradth _ _ egf efg).
Defined.

(** *** The function on the total spaces from functions on the bases and on the fibers *)

Definition bandfmap {X Y : UU} (f : X -> Y) (P : X -> UU) (Q : Y -> UU)
           (fm : ∏ x : X, P x -> (Q (f x))) :
  (∑ x, P x) -> (∑ x, Q x) := λ xp, f (pr1 xp) ,, fm (pr1 xp) (pr2 xp).

Theorem isweqbandfmap {X Y : UU} (w : X ≃ Y) (P : X -> UU) (Q : Y -> UU)
        (fw : ∏ x : X, P x ≃ Q (w x)) : isweq (bandfmap  _ P Q fw).
Proof.
  intros.
  set (f1 := totalfun P _ fw).
  set (is1 := isweqfibtototal P (λ x:X, Q (w x)) fw).
  set (f2:= fpmap w Q).
  set (is2:= isweqfpmap w Q).
  assert (h: ∏ xp: total2 P, (f2 (f1 xp)) = (bandfmap w P Q fw xp)).
  intro. induction xp. apply idpath.
  apply (isweqhomot _ _ h (twooutof3c f1 f2 is1 is2)).
Defined.

Definition weqbandf {X Y : UU} (w : X ≃ Y) (P : X -> UU) (Q : Y -> UU)
           (fw : ∏ x : X, P x ≃ Q (w x))
  := weqpair _ (isweqbandfmap w P Q fw).



(** ** Homotopy fiber squares *)

(** *** Homotopy commutative squares *)

Definition commsqstr {X X' Y Z : UU} (g' : Z -> X') (f' : X' -> Y) (g : Z -> X)
           (f : X -> Y) := ∏ (z : Z), (f' (g' z)) = (f (g z)).

Definition hfibersgtof' {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y) (g : Z -> X)
           (g' : Z -> X') (h : commsqstr g' f' g f) (x : X) (ze : hfiber g x) :
  hfiber f' (f x).
Proof.
  intros.
  induction ze as [ z e ].
  split with (g' z).
  apply (pathscomp0 (h z) (maponpaths f e)).
Defined.

Definition hfibersg'tof {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f) (x' : X')
           (ze : hfiber g' x') : hfiber f (f' x').
Proof.
  intros.
  induction ze as [ z e ].
  split with (g z).
  apply (pathscomp0 (pathsinv0 (h z)) (maponpaths f' e)).
Defined.

Definition transposcommsqstr {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') :
  commsqstr g' f' g f -> commsqstr g f g' f'
  := λ h : _, λ z : Z, (pathsinv0 (h z)).


(** *** Short complexes and homotopy commutative squares *)

Lemma complxstrtocommsqstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
      (h : complxstr f g z) :
  commsqstr f g (λ x : X, tt) (λ t : unit, z).
Proof.
  intros. assumption.
Defined.


Lemma commsqstrtocomplxstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
      (h : commsqstr f g (λ x : X, tt) (λ t : unit, z)) :
  complxstr f g z.
Proof.
  intros. assumption.
Defined.


(** *** Homotopy fiber products *)



Definition hfp {X X' Y : UU} (f : X -> Y) (f' : X' -> Y)
  := total2 (λ xx' : X × X', (f' (pr2 xx')) = (f (pr1 xx'))).
Definition hfpg {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) :
  hfp f f' -> X := λ xx'e, (pr1 (pr1 xx'e)).
Definition hfpg' {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) :
  hfp f f' -> X' := λ xx'e, (pr2 (pr1 xx'e)).

Definition commsqZtohfp {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f) :
  Z -> hfp f f' := λ z : _, tpair _ (dirprodpair (g z) (g' z)) (h z).

Definition commsqZtohfphomot {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f) :
  ∏ z : Z, (hfpg _ _ (commsqZtohfp _ _ _ _ h z)) = (g z)
  := λ z : _, idpath _.

Definition commsqZtohfphomot' {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f) :
  ∏ z : Z, (hfpg' _ _ (commsqZtohfp _ _ _ _ h z)) = (g' z)
  := λ z : _, idpath _.


Definition hfpoverX {X X' Y : UU} (f : X -> Y) (f' : X' -> Y)
  := total2 (λ x : X, hfiber f' (f x)).
Definition hfpoverX' {X X' Y : UU} (f : X -> Y) (f' : X' -> Y)
  := total2 (λ x' : X', hfiber f (f' x')).


Definition weqhfptohfpoverX {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) :
  hfp f f' ≃ hfpoverX f f'.
Proof.
  intros.
  exact (weqtotal2asstor _ (λ xx',  f' (pr2 xx') = f (pr1 xx'))).
Defined.


Definition weqhfptohfpoverX' {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) :
  hfp f f' ≃ hfpoverX' f f'.
Proof.
  intros.
  set (w1 := weqfp (weqdirprodcomm X X')
                   (λ xx' : X' × X , (f' (pr1 xx')) = (f (pr2 xx')))).
  simpl in w1.
  set (w2 := weqfibtototal
               (λ x'x : X' × X, (f' (pr1 x'x)) = (f (pr2 x'x)))
               (λ x'x : X' × X, (f (pr2 x'x)) = (f' (pr1 x'x)))
               (λ x'x : _, weqpathsinv0  (f' (pr1 x'x)) (f (pr2 x'x)))).
  set (w3 := weqtotal2asstor
               (λ x' : X', X)
               (λ x'x : X' × X, (f (pr2 x'x)) = (f' (pr1 x'x)))).
  simpl in w3.
  apply (weqcomp (weqcomp w1 w2) w3).
Defined.


Lemma weqhfpcomm {X X' Y : UU} (f : X -> Y) (f' : X' -> Y):
  hfp f f' ≃ hfp f' f.
Proof.
  intros.
  set (w1 := weqfp (weqdirprodcomm X X')
                   (λ xx' : X' × X, (f' (pr1 xx')) = (f (pr2 xx')))).
  simpl in w1.
  set (w2 := weqfibtototal
               (λ x'x : X' × X, (f' (pr1 x'x)) = (f (pr2 x'x)))
               (λ x'x : X' × X, (f (pr2 x'x)) = (f' (pr1 x'x)))
               (λ x'x : _, weqpathsinv0 (f' (pr1 x'x)) (f (pr2 x'x)))).
  apply (weqcomp w1 w2).
Defined.

Definition commhfp {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) :
  commsqstr (hfpg' f f') f' (hfpg f f') f
  := λ xx'e : hfp f f', pr2 xx'e.


(** *** Homotopy fiber products and homotopy fibers *)

Definition  hfibertohfp {X Y : UU} (f : X -> Y) (y : Y) (xe : hfiber f y) :
  hfp (λ t : unit, y) f := tpair (λ tx : unit × X, (f (pr2 tx)) = y)
                                     (dirprodpair tt (pr1 xe)) (pr2 xe).

Definition hfptohfiber {X Y : UU} (f : X -> Y) (y : Y)
           (hf : hfp (λ t : unit, y) f) : hfiber f y
  := hfiberpair f (pr2 (pr1 hf)) (pr2 hf).

Lemma weqhfibertohfp {X Y : UU} (f : X -> Y) (y : Y) :
  hfiber f y ≃ hfp (λ _:unit, y) f.
Proof.
  intros.
  set (ff := hfibertohfp f y).
  set (gg := hfptohfiber f y).
  split with ff.
  assert (egf : ∏ xe : _, (gg (ff xe)) = xe).
  intro. induction xe. apply idpath.
  assert (efg : ∏ hf : _, (ff (gg hf)) = hf).
  intro.
  induction hf as [ tx e ]. induction tx as [ t x ].
  induction t. apply idpath. apply (gradth _ _ egf efg).
Defined.

Lemma hfp_left {X Y Z : UU} (f : X -> Z) (g : Y -> Z) :
  hfp f g ≃ ∑ x, hfiber g (f x).
Proof.
  intros. apply weqtotal2dirprodassoc.
Defined.

Definition hfp_right {X Y Z : UU} (f : X -> Z) (g : Y -> Z) :
  hfp f g ≃ ∑ y, hfiber f (g y).
Proof.
  intros. use weqgradth.
  - intros [[x y] e]. exact (y,,x,,!e).
  - intros [x [y e]]. exact ((y,,x),,!e).
  - intros [[x y] e]. apply maponpaths, pathsinv0inv0.
  - intros [x [y e]]. apply maponpaths, maponpaths, pathsinv0inv0.
Defined.

Definition hfiber_comm {X Y Z : UU} (f : X -> Z) (g : Y -> Z) :
  (∑ x, hfiber g (f x)) ≃ (∑ y, hfiber f (g y)).
Proof.
  intros. use weqgradth.
  - intros [x [y e]]. exact (y,,x,,!e).
  - intros [y [x e]]. exact (x,,y,,!e).
  - intros [x [y e]]. apply maponpaths, maponpaths, pathsinv0inv0.
  - intros [y [x e]]. apply maponpaths, maponpaths, pathsinv0inv0.
Defined.


(** *** Homotopy fiber squares *)

Definition ishfsq {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f)
  := isweq (commsqZtohfp f f' g g' h).

Definition hfsqstr {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X')
  := total2 (λ h : commsqstr g' f' g f, isweq (commsqZtohfp f f' g g' h)).

Definition hfsqstrpair {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X')
  := tpair (λ h : commsqstr g' f' g f, isweq (commsqZtohfp f f' g g' h)).

Definition hfsqstrtocommsqstr {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') :
  hfsqstr f f' g g' -> commsqstr g' f' g f
  := @pr1 _ (λ h : commsqstr g' f' g f, isweq (commsqZtohfp f f' g g' h)).
Coercion hfsqstrtocommsqstr : hfsqstr >-> commsqstr.

Definition weqZtohfp {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y) (g : Z -> X)
           (g' : Z -> X') (hf : hfsqstr f f' g g') : Z ≃ hfp f f'
  := weqpair _ (pr2 hf).

Lemma isweqhfibersgtof' {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y) (g : Z -> X)
      (g' : Z -> X') (hf : hfsqstr f f' g g') (x : X) :
  isweq (hfibersgtof' f f' g g' hf x).
Proof.
  intros.
  set (is := pr2 hf).
  set (h := pr1 hf).
  set (a := weqtococonusf g).
  set (c := weqpair _ is).
  set (d := weqhfptohfpoverX f f').
  set (b0 := totalfun _ _ (hfibersgtof' f f' g g' h)).

  assert (h1 : ∏ z : Z, (d (c z)) = (b0 (a z))).
  intro. simpl. unfold b0. unfold a. unfold weqtococonusf. unfold tococonusf.
  simpl. unfold totalfun, total2asstor, hfibersgtof'; simpl.
  assert (e : (h z) = (pathscomp0 (h z) (idpath (f (g z))))).
  apply (pathsinv0 (pathscomp0rid _)). induction e. apply idpath.

  assert (is1 : isweq (λ z : _, b0 (a z))).
  apply (isweqhomot _ _ h1). apply (twooutof3c _ _ (pr2 c) (pr2 d)).

  assert (is2 : isweq b0).
  apply (twooutof3b _ _ (pr2 a) is1).

  apply (isweqtotaltofib _ _ _ is2 x).
Defined.

Definition weqhfibersgtof' {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (hf : hfsqstr f f' g g') (x : X)
  := weqpair _ (isweqhfibersgtof' _ _ _ _ hf x).

Lemma ishfsqweqhfibersgtof' {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
      (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f)
      (is : ∏ x : X, isweq (hfibersgtof' f f' g g' h x)) : hfsqstr f f' g g'.
Proof.
  intros. split with h.
  set (a := weqtococonusf g).
  set (c0 := commsqZtohfp f f' g g' h).
  set (d := weqhfptohfpoverX f f').
  set (b := weqfibtototal _ _ (λ x : X, weqpair _ (is x))).

  assert (h1 : ∏ z : Z, (d (c0 z)) = (b (a z))).
  intro. simpl. unfold b. unfold a. unfold weqtococonusf. unfold tococonusf.
  simpl. unfold totalfun, total2asstor, hfibersgtof'; simpl.
  assert (e : (h z) = (pathscomp0 (h z) (idpath (f (g z))))).
  apply (pathsinv0 (pathscomp0rid _)). induction e. apply idpath.

  assert (is1 : isweq (λ z : _, d (c0 z))).
  apply (isweqhomot _ _ (λ z : Z, (pathsinv0 (h1 z)))).
  apply (twooutof3c _ _ (pr2 a) (pr2 b)).

  apply (twooutof3a _ _ is1 (pr2 d)).
Defined.

Lemma isweqhfibersg'tof {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y) (g : Z -> X)
      (g' : Z -> X') (hf : hfsqstr f f' g g') (x' : X') :
  isweq (hfibersg'tof f f' g g' hf x').
Proof.
  intros.
  set (is := pr2 hf).
  set (h := pr1 hf).
  set (a' := weqtococonusf g').
  set (c' := weqpair _ is).
  set (d' := weqhfptohfpoverX' f f').
  set (b0' := totalfun _ _ (hfibersg'tof f f' g g' h)).

  assert (h1 : ∏ z : Z, (d' (c' z)) = (b0' (a' z))).
  intro. unfold b0'. unfold a'. unfold weqtococonusf. unfold tococonusf.
  unfold totalfun, hfibersg'tof; simpl.
  assert (e : (pathsinv0 (h z))
              = (pathscomp0 (pathsinv0 (h z)) (idpath (f' (g' z))))).
  apply (pathsinv0 (pathscomp0rid _)). induction e. apply idpath.

  assert (is1 : isweq (λ z : _, b0'(a' z))).
  apply (isweqhomot _ _ h1). apply (twooutof3c _ _ (pr2 c') (pr2 d')).

  assert (is2 : isweq b0'). apply (twooutof3b _ _ (pr2 a') is1).

  apply (isweqtotaltofib _ _ _ is2 x').
Defined.

Definition weqhfibersg'tof {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
           (g : Z -> X) (g' : Z -> X') (hf : hfsqstr f f' g g') (x' : X')
  := weqpair _ (isweqhfibersg'tof _ _ _ _ hf x').

Lemma ishfsqweqhfibersg'tof {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y)
      (g : Z -> X) (g' : Z -> X') (h : commsqstr g' f' g f)
      (is : ∏ x' : X', isweq (hfibersg'tof f f' g g' h x')) : hfsqstr f f' g g'.
Proof.
  intros.
  split with h.
  set (a' := weqtococonusf g').
  set (c0' := commsqZtohfp f f' g g' h).
  set (d' := weqhfptohfpoverX' f f').
  set (b' := weqfibtototal _ _ (λ x' : X', weqpair _ (is x'))).

  assert (h1 : ∏ z : Z, (d' (c0' z)) = (b' (a' z))).
  intro. simpl. unfold b'. unfold a'. unfold weqtococonusf. unfold tococonusf.
  unfold totalfun, total2asstor, hfibersg'tof; simpl.
  assert (e : (pathsinv0 (h z)) =
              (pathscomp0 (pathsinv0 (h z)) (idpath (f' (g' z))))).
  apply (pathsinv0 (pathscomp0rid _)). induction e. apply idpath.

  assert (is1 : isweq (λ z : _, d' (c0' z))).
  apply (isweqhomot _ _ (λ z : Z, (pathsinv0 (h1 z)))).
  apply (twooutof3c _ _ (pr2 a') (pr2 b')).

  apply (twooutof3a _ _ is1 (pr2 d')).
Defined.

Theorem transposhfpsqstr {X X' Y Z : UU} (f : X -> Y) (f' : X' -> Y) (g : Z -> X)
        (g' : Z -> X') (hf : hfsqstr f f' g g') : hfsqstr f' f g' g.
Proof.
  intros.
  set (is := pr2 hf). set (h := pr1 hf).
  set (th := transposcommsqstr f f' g g' h).
  split with th.
  set (w1 := weqhfpcomm f f').
  assert (h1 : ∏ z : Z, (w1 (commsqZtohfp f f' g g' h z))
                        = (commsqZtohfp f' f g' g th z)).
  intro. unfold commsqZtohfp. simpl. unfold fpmap. unfold totalfun.
  simpl. apply idpath.
  apply (isweqhomot _ _ h1). apply (twooutof3c _ _ is (pr2 w1)).
Defined.


(** *** Fiber sequences and homotopy fiber squares *)

Theorem fibseqstrtohfsqstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (hf : fibseqstr f g z) : hfsqstr (λ t : unit, z) g (λ x : X, tt) f.
Proof.
  intros.
  split with (pr1 hf).
  set (ff := ezweq f g z hf).
  set (ggff := commsqZtohfp (λ t : unit, z) g (λ x : X, tt) f (pr1 hf)).
  set (gg := weqhfibertohfp g z).
  apply (pr2 (weqcomp ff gg)).
Defined.


Theorem hfsqstrtofibseqstr {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (hf : hfsqstr (λ t : unit, z) g (λ x : X, tt) f) : fibseqstr f g z.
Proof.
  intros. split with (pr1 hf).  set (ff := ezmap f g z (pr1 hf)).
  set (ggff := weqZtohfp (λ t : unit, z) g (λ x : X, tt) f hf).
  set (gg := weqhfibertohfp g z).
  apply (twooutof3a ff gg (pr2 ggff) (pr2 gg)).
Defined.

(* End of the file PartA.v *)
