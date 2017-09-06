(** * Generalities on hProp.  Vladimir Voevodsky . May - Sep. 2011 .

In this file we introduce the hProp - an analog of Prop defined based on the
univalent semantics. We further introduce the hProp version of the "inhabited"
construction - i.e. for any [T] in [UU0] we construct an object [ishinh T] and a
function [hinhpr : T -> ishinh T] which plays the role of [inhabits] from the
Coq standard library. The semantic meaning of [hinhpr] is that it is universal
among functions from [T] to objects of hProp. Proving that [ishinh T] is in
[hProp] requires a resizing rule which can be written in the putative notation
for such rules as follows :

Resizing Rule RR1 (U1 U2 : Univ) (X : U1) (is : isaprop X) |- X : U2.

Further in the file we introduce the univalence axiom [hPropUnivalence] for
hProp and a proof of the fact that it is equivalent to a simplier and better
known axiom [propositionalUnivalenceAxiom]. We prove that this axiom implies
that [hProp] satisfies [isaset] i.e. it is a type of h-level 2. This requires
another resizing rule :

Resizing Rule RR2 (U1 U2 : Univ) |- @hProp U1 : U2.

Since resizing rules are not currently implemented in Coq the file does not
compile without a patch provided by Hugo Herbelin which turns off the universe
consistency verification. We do however keep track of universes in our
development "by hand" to ensure that when the resizing rules will become
available the current proofs will verify correctly. To point out which results
require resizing rules in a substantial way we mark the first few of such reults
by (** RR1 *) or (** RR2 *) comment.

One can achieve similar results with a combination of usual axioms which imitate
the resizing rules. However unlike the usual axioms the resizing rules do not
affect the computation/normalization abilities of Coq which makes them the
prefrred choice in this situation.
*)

(** ** Contents
- The type [hProp] of types of h-level 1
- The type [tildehProp] of pairs (P, p : P) where [P : hProp]
- Intuitionistic logic on [hProp]
 - The [hProp] version of the "inhabited" construction.
 - [ishinh] and negation [neg]
 - [ishinh] and [coprod]
- Images and surjectivity for functions between types
 - The two-out-of-three properties of surjections
 - A function between types which is an inclusion and a surjection is a weak
   equivalence
 - Intuitionistic logic on [hProp]
 - Associativity and commutativity of [hdisj] and [hconj] up to logical
   equivalence
 - Proof of the only non-trivial axiom of intuitionistic logic for our
   constructions
 - Negation and quantification
 - Negation and conjunction ("and") and disjunction ("or")
 - Property of being decidable and [hdisj] ("or")
 - The double negation version of [hinhabited] (does not require RR1)
- Decidability
- Univalence for hProp
*)


(** ** Preamble *)

(** Settings *)

(* The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

(** Imports *)

Require Export UniMath.Foundations.PartD.
Require Export UniMath.Foundations.Resizing2.

(** Universe structure *)

(* Definition UU0 := UU. *)

(* end of " Preamble ". *)


(** ** To upstream files *)



(** ** The type [hProp] of types of h-level 1 *)

Definition hProp@{i j} : Type@{j} := total2@{j} isaprop@{i}. (* i < j *)

Definition hProppair@{i j} (X : Type@{i}) (is : isaprop@{i} X) : hProp@{i j}
  := tpair@{j} (isaprop@{i}) X is.

Definition hProptoType@{i j} := @pr1@{j} _ _ : hProp@{i j} -> Type@{i}.

Coercion hProptoType : hProp >-> Sortclass.

Definition propproperty (P : hProp) := pr2 P : isaprop (pr1 P).

(** ** The type [tildehProp] of pairs (P, p : P) where [P : hProp] *)

Definition tildehProp := total2 (fun P : hProp => P).
Definition tildehProppair {P : hProp} (p : P) : tildehProp := tpair _ P p.

Definition negProp_to_hProp {P : UU} (Q : negProp P) : hProp.
Proof. intros. exists (negProp_to_type Q). apply negProp_to_isaprop. Defined.
Coercion negProp_to_hProp : negProp >-> hProp.

(* convenient corollaries of some theorems that take separate isaprop
   arguments: *)

Corollary subtypeInjectivity_prop {A : UU} (B : A -> hProp) :
  ∏ (x y : total2 B), (x = y) ≃ (pr1 x = pr1 y).
Proof. intros. apply subtypeInjectivity. intro. apply propproperty. Defined.

Corollary subtypeEquality_prop {A : UU} {B : A -> hProp}
   {s s' : total2 (fun x => B x)} : pr1 s = pr1 s' -> s = s'.
Proof. intros A B s s'. apply invmap. apply subtypeInjectivity_prop. Defined.

Corollary impred_prop {T : UU} (P : T -> hProp) : isaprop (∏ t : T, P t).
Proof. intros. apply impred; intro. apply propproperty. Defined.

Corollary isaprop_total2 (X : hProp) (Y : X -> hProp) : isaprop (∑ x, Y x).
Proof.
  intros.
  apply (isofhleveltotal2 1).
  - apply propproperty.
  - intro x. apply propproperty.
Defined.

Lemma isaprop_forall_hProp (X : UU) (Y : X -> hProp) : isaprop (∏ x, Y x).
Proof. intros. apply impred_isaprop. intro x. apply propproperty. Defined.

Definition forall_hProp {X : UU} (Y : X -> hProp) : hProp
  := hProppair (∏ x, Y x) (isaprop_forall_hProp X Y).

Notation "∀  x .. y , P"
  := (forall_hProp (fun x => .. (forall_hProp (fun y => P))..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

(** The following re-definitions should make proofs easier in the future when
  the unification algorithms in Coq are improved. At the moment they create more
  complications than they eliminate (e.g. try to prove [isapropishinh] with
  [isaprop] in [hProp]) so for the time being they are commented out.


(** *** Re-definitions of some of the standard constructions of uu0.v which lift these contructions from UU to hProp. *)


Definition iscontr (X : UU) : hProp := hProppair _ (isapropiscontr X).

Definition isweq {X Y : UU} (f : X -> Y) : hProp
:= hProppair _ (isapropisweq f).

Definition isofhlevel (n : nat) (X : UU) : hProp
:= hProppair _ (isapropisofhlevel n X).

Definition isaprop (X : UU) : hProp := hProppair (isaprop X) (isapropisaprop X).

Definition isaset (X : UU) : hProp := hProppair _ (isapropisaset X).

Definition isisolated (X : UU) (x : X) : hProp
:= hProppair _ (isapropisisolated X x).

Definition isdecEq (X : UU) : hProp := hProppair _ (isapropisdeceq X).

*)

(** ** Change of universe level for hProp *)

Section A.

  Universes i j l.
  Constraint i < j.
  Constraint j < l.

  Definition raise_universe_hProp@{} : hProp@{i j} -> hProp@{j l}.
  Proof.
    intro P.
    exact (@tpair Type@{j} isaprop (pr1 P) (pr2 P)).
  Defined.

  Definition lower_universe_hProp@{} : hProp@{i j} <- hProp@{j l}.
  Proof.
    intro P.
    exact (@tpair Type@{i} isaprop (ResizeProp@{i j} (pr1 P) (pr2 P)) (pr2 P)).
  Defined.

  Definition change_universe_hProp@{} : weq@{l} hProp@{i j} hProp@{j l}.
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - exact raise_universe_hProp.
    - exact lower_universe_hProp.
    - reflexivity.
    - reflexivity.
  Defined.

End A.

(** ** Intuitionistic logic on [hProp] *)


(** *** The [hProp] version of the "inhabited" construction. *)

Definition ishinh_UU@{i j} (X : Type@{i}) : Type@{j}           (* i < j *)
  := ∏ P : hProp@{i j}, ((X -> P) -> P).

Lemma isapropishinh_UU@{i j} (X : Type@{i}) : isaprop@{j} (ishinh_UU@{i j} X).
Proof.
  intro. apply impred. intros P. apply impred. intros _. apply propproperty.
Qed.

Definition ishinh_resized@{i j} (X : Type@{i}) : Type@{i}           (* i < j *)
  := ResizeProp@{i j} (ishinh_UU X) (isapropishinh_UU _).

Lemma isapropishinh (X : Type) : isaprop (ishinh_resized X).
Proof.
  intro. unfold ishinh_resized. apply isapropishinh_UU.
Defined.

Definition ishinh@{i j} (X : Type@{i}) : hProp@{i j} := hProppair (ishinh_resized@{i j} X) (isapropishinh@{i j} X).

Notation nonempty := ishinh (only parsing).

Notation "∥ A ∥" := (ishinh A) (at level 20) : type_scope.
(* written \|| in agda-input method *)

Definition hinhpr {X : UU} : X -> ∥ X ∥
  := fun x : X => fun P : hProp => fun f : X -> P => f x.

Definition hinhfun {X Y : UU} (f : X -> Y) : ∥ X ∥ -> ∥ Y ∥ :=
  fun isx : ∥ X ∥ => fun P : _ => fun yp : Y -> P => isx P (fun x : X => yp (f x)).

(** Note that the previous definitions do not require RR1 in an essential way
  (except for the placing of [ishinh] in [hProp UU] - without RR1 it would be
  placed in [hProp UU1]). The first place where RR1 is essentially required is
  in application of [hinhuniv] to a function [X -> ishinh Y] *)

Definition hinhuniv {X : UU} {P : hProp} (f : X -> P) (wit : ∥ X ∥) : P
  := wit P f.

Corollary factor_through_squash {X Q : UU} : isaprop Q -> (X -> Q) -> ∥ X ∥ -> Q.
Proof. intros ? ? i f h. exact (@hinhuniv X (Q,,i) f h). Defined.

Corollary squash_to_prop {X Q : UU} : ∥ X ∥ -> isaprop Q -> (X -> Q) -> Q.
Proof. intros ? ? h i f. exact (@hinhuniv X (Q,,i) f h). Defined.

Definition hinhand {X Y : UU} (inx1 : ∥ X ∥) (iny1 : ∥ Y ∥) : ∥ X × Y ∥
  := fun P : _ => ddualand (inx1 P) (iny1 P).

Definition hinhuniv2 {X Y : UU} {P : hProp} (f : X -> Y -> P)
           (isx : ∥ X ∥) (isy : ∥ Y ∥) : P
  := hinhuniv (fun xy : X × Y => f (pr1 xy) (pr2 xy)) (hinhand isx isy).

Definition hinhfun2 {X Y Z : UU} (f : X -> Y -> Z)
           (isx : ∥ X ∥) (isy : ∥ Y ∥) : ∥ Z ∥
  := hinhfun (fun xy: X × Y => f (pr1 xy) (pr2 xy)) (hinhand isx isy).

Definition hinhunivcor1 (P : hProp) : ∥ P ∥ -> P := hinhuniv (idfun P).
Notation hinhprinv := hinhunivcor1.


(** *** [ishinh] and negation [neg] *)


Lemma weqishinhnegtoneg (X : UU) : ∥ ¬ X ∥ ≃ ¬ X.
Proof.
  intro.
  assert (lg : logeq (ishinh (neg X)) (neg X)).
  {
    split.
    - simpl. apply (@hinhuniv _ (hProppair _ (isapropneg X))).
      simpl. intro nx. apply nx.
    - apply hinhpr.
  }
  apply (weqimplimpl (pr1 lg) (pr2 lg) (pr2 (ishinh _)) (isapropneg X)).
Defined.

Lemma weqnegtonegishinh (X : UU) : ¬ X ≃ ¬ ∥ X ∥.
Proof.
  intro.
  assert (lg : logeq (neg (ishinh X)) (neg X)).
  {
    split.
    - apply (negf (@hinhpr X)).
    - intro nx. unfold neg. simpl.
      apply (@hinhuniv _ (hProppair _ isapropempty)).
      apply nx.
  }
  apply (weqimplimpl (pr2 lg) (pr1 lg) (isapropneg _) (isapropneg _)).
Defined.


(** *** [ishinh] and [coprod] *)


Lemma hinhcoprod (X Y : UU) : ∥ (∥ X ∥ ⨿ ∥ Y ∥) ∥ -> ∥ X ⨿ Y ∥.
Proof.
  intros ? ? is. unfold ishinh. intro P. intro CP.
  set (CPX := fun x : X => CP (ii1 x)).
  set (CPY := fun y : Y => CP (ii2 y)).
  set (is1P := is P).
  assert (f : coprod (ishinh X) (ishinh Y) -> P).
  apply (sumofmaps (hinhuniv CPX) (hinhuniv CPY)).
  apply (is1P f).
Defined.

(** [ishinh] and decidability  *)

Lemma decidable_ishinh {X} : decidable X → decidable(∥X∥).
Proof.
  intros ? d.
  unfold decidable in *.
  induction d as [x|x'].
  - apply ii1. now apply hinhpr.
  - apply ii2. intros p.
    apply (squash_to_prop p).
    + exact isapropempty.
    + exact x'.
Defined.

(** ** Images and surjectivity for functions between types
(both depend only on the behavior of the corresponding function between the sets
of connected components) **)

Definition image {X Y : UU} (f : X -> Y) : UU
  := total2 (fun y : Y => ishinh (hfiber f y)).
Definition imagepair {X Y : UU} (f : X -> Y) :
  ∏ (t : Y), (λ y : Y, ∥ hfiber f y ∥) t → ∑ y : Y, ∥ hfiber f y ∥
  := tpair (fun y : Y => ishinh (hfiber f y)).
Definition pr1image {X Y : UU} (f : X -> Y) :
  (∑ y : Y, ∥ hfiber f y ∥) → Y
  := @pr1 _  (fun y : Y => ishinh (hfiber f y)).

Definition prtoimage {X Y : UU} (f : X -> Y) : X -> image f.
Proof.
  intros X Y f X0.
  apply (imagepair _ (f X0) (hinhpr (hfiberpair f X0 (idpath _)))).
Defined.

Definition issurjective {X Y : UU} (f : X -> Y) := ∏ y : Y, ishinh (hfiber f y).

Lemma isapropissurjective {X Y : UU} (f : X -> Y) : isaprop (issurjective f).
Proof.
  intros. apply impred.
  intro t. apply (pr2 (ishinh (hfiber f t))).
Defined.

Lemma isinclpr1image {X Y : UU} (f : X -> Y): isincl (pr1image f).
Proof.
  intros. refine (isofhlevelfpr1 _ _ _).
  intro. apply (pr2 (ishinh (hfiber f x))).
Defined.

Lemma issurjprtoimage {X Y : UU} (f : X -> Y) : issurjective (prtoimage f).
Proof.
  intros. intro z.
  set (f' := prtoimage f).
  assert (ff: hfiber (funcomp f' (pr1image f)) (pr1 z) -> hfiber f' z)
    by refine (invweq (samehfibers _ _ (isinclpr1image f) z)).
  apply (hinhfun ff).
  exact (pr2 z).
Defined.

(** *** The two-out-of-three properties of surjections *)

Lemma issurjcomp {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
      (isf : issurjective f) (isg : issurjective g) :
  issurjective (funcomp f g).
Proof.
  intros. unfold issurjective.
  intro z. apply (fun ff => hinhuniv ff (isg z)).
  intro ye. apply (hinhfun (hfibersftogf f g z ye)).
  apply (isf).
Defined.

Notation issurjtwooutof3c := issurjcomp.

Lemma issurjtwooutof3b {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
      (isgf : issurjective (funcomp f g)) : issurjective g.
Proof.
  intros. unfold issurjective.
  intro z. apply (hinhfun (hfibersgftog f g z) (isgf z)).
Defined.

(** *** A function between types which is an inclusion and a surjection is a weak equivalence *)

Lemma isweqinclandsurj {X Y : UU} (f : X -> Y) :
  isincl f -> issurjective f -> isweq f.
Proof.
  intros X Y f Hincl Hsurj.
  intro y.
  set (H := hProppair (iscontr (hfiber f y)) (isapropiscontr _)).
  apply (Hsurj y H).
  intro x.
  simpl.
  apply iscontraprop1.
  - apply Hincl.
  - apply x.
Defined.

(** On the other hand, a weak equivalence is surjective *)

Lemma issurjectiveweq (X Y : UU) (f : X -> Y) : isweq f -> issurjective f.
Proof.
  intros X Y f H y.
  apply hinhpr.
  apply (pr1 (H y)).
Defined.




(** *** Intuitionistic logic on [hProp]. *)


Definition htrue : hProp := hProppair unit isapropunit.

Definition hfalse : hProp := hProppair empty isapropempty.

Definition hconj (P Q : hProp) : hProp
  := hProppair (P × Q) (isapropdirprod _ _ (pr2 P) (pr2 Q)).

Notation "A ∧ B" := (hconj A B) (at level 80, right associativity) : type_scope.
  (* precedence same as /\ *)
  (* in agda-input method, type \and or \wedge *)

Definition hdisj (P Q : UU) : hProp := ishinh (coprod P Q).

Notation "X ∨ Y" := (hdisj X Y) (at level 85, right associativity) : type_scope.
  (* in agda-input method, type \or *)
  (* precedence same as ‌\/, whereas ⨿ has the opposite associativity *)

Definition hdisj_in1 {P Q : UU} : P -> P ∨ Q.
Proof. intros. apply hinhpr. now apply ii1. Defined.

Definition hdisj_in2 {P Q : UU} : Q -> P ∨ Q.
Proof. intros. apply hinhpr. now apply ii2. Defined.

Lemma disjoint_disjunction (P Q : hProp) : (P -> Q -> ∅) -> hProp.
Proof.
  intros ? ? n.
  exact (P ⨿ Q,, isapropcoprod P Q (propproperty P) (propproperty Q) n).
Defined.

Definition hneg (P : UU) : hProp := hProppair (¬ P) (isapropneg P).
(* uses funextemptyAxiom *)

(* use scope "logic" for notations that might conflict with others *)

Notation "'¬' X" := (hneg X) (at level 35, right associativity) : logic.
  (* type this in emacs in agda-input method with \neg *)
Delimit Scope logic with logic.

Definition himpl (P : UU) (Q : hProp) : hProp.
Proof. intros. split with (P -> Q). apply impred. intro. apply (pr2 Q). Defined.

Local Notation "A ⇒ B" := (himpl A B) (at level 95, no associativity) : logic.
  (* precedence same as <-> *)
  (* in agda-input method, type \r= or \Rightarrow or \=> *)
  (* can't make it global, because it's defined differently in
     CategoryTheory/UnicodeNotations.v *)
Local Open Scope logic.

Definition hexists {X : UU} (P : X -> UU) := ∥ total2 P ∥.

Notation "'∃' x .. y , P"
  := (ishinh (∑ x ,.. (∑ y , P)..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
  (* in agda-input method, type \ex *)

Definition wittohexists {X : UU} (P : X -> UU) (x : X) (is : P x) : hexists P
  := @hinhpr (total2 P) (tpair _ x is).

Definition total2tohexists {X : UU} (P : X -> UU) : total2 P -> hexists P
  := hinhpr.

Definition weqneghexistsnegtotal2 {X : UU} (P : X -> UU) :
  weq (neg (hexists P)) (neg (total2 P)).
Proof.
  intros.
  assert (lg : (neg (hexists P)) <-> (neg (total2 P))).
  {
    split.
    - apply (negf (total2tohexists P)).
    - intro nt2. unfold neg. change (ishinh_UU (total2 P) -> hfalse).
      apply (hinhuniv). apply nt2.
  }
  apply (weqimplimpl (pr1 lg) (pr2 lg) (isapropneg _) (isapropneg _)).
Defined.


(** *** Associativity and commutativity of [hdisj] and [hconj] up to logical equivalence *)

Lemma islogeqcommhdisj {P Q : hProp} : hdisj P Q <-> hdisj Q P.
Proof.
  intros. split.
  - simpl. apply hinhfun. apply coprodcomm.
  - simpl. apply hinhfun. apply coprodcomm.
Defined.



(** *** Proof of the only non-trivial axiom of intuitionistic logic for our constructions. For the full list of axioms see e.g.  http://plato.stanford.edu/entries/logic-intuitionistic/ *)


Lemma hconjtohdisj (P Q : UU) (R : hProp) : (P ⇒ R) ∧ (Q ⇒ R) -> P ∨ Q ⇒ R.
Proof.
  intros P Q R X0.
  assert (s1: hdisj P Q -> R).
  {
    intro X1.
    assert (s2: coprod P Q -> R).
    {
      intro X2. destruct X2 as [ XP | XQ ].
      - apply X0. apply XP.
      - apply (pr2 X0). apply XQ.
    }
    apply (hinhuniv s2). apply X1.
  }
  unfold himpl. simpl. apply s1.
Defined.

(** *** Negation and quantification.

There are four standard implications in classical logic which can be summarized
as (neg (∏ P)) <-> (exists (neg P)) and (neg (exists P)) <-> (∏ (neg P)). Of
these four implications three are provable in the intuitionistic logic. The
remaining implication (neg (∏ P)) -> (exists (neg P)) is not provable in
general. For a proof in the case of bounded quantification of decidable
predicates on natural numbers see hnat.v. For some other cases when these
implications hold see ???. *)

Lemma hexistsnegtonegforall {X : UU} (F : X -> UU) :
  (∃ x : X, neg (F x)) -> neg (∏ x : X, F x).
Proof.
  intros X F. simpl.
  apply (@hinhuniv _ (hProppair _ (isapropneg (∏ x : X, F x)))).
  simpl. intros t2 f2. destruct t2 as [ x d2 ]. apply (d2 (f2 x)).
Defined.

Lemma forallnegtoneghexists {X : UU} (F : X -> UU) :
  (∏ x : X, neg (F x)) -> neg (∃ x, F x).
Proof.
  intros X F nf.
  change ((ishinh_UU (total2 F)) -> hfalse).
  apply hinhuniv. intro t2. destruct t2 as [ x f ]. apply (nf x f).
Defined.

Lemma neghexisttoforallneg {X : UU} (F : X -> UU) :
  ¬ (∃ x, F x) -> ∏ x : X, ¬ (F x).
Proof.
  intros X F nhe x. intro fx.
  apply (nhe (hinhpr (tpair F x fx))).
Defined.

Definition weqforallnegtonegexists {X : UU} (F : X -> UU) :
  weq (∏ x : X, ¬ F x) (¬ ∃ x, F x).
Proof.
  intros.
  apply (weqimplimpl (forallnegtoneghexists F) (neghexisttoforallneg F)).
  apply impred. intro x. apply isapropneg. apply isapropneg.
Defined.



(** *** Negation and conjunction ("and") and disjunction ("or").

There are four implications in classical logic
((¬ X) and (¬ Y)) <-> (¬ (X or Y)) and ((¬ X) or (¬ Y)) <-> (¬ (X and Y)). Of
these four, three are provable unconditionally in the intuitionistic logic and
the remaining one (¬ (X and Y)) -> ((¬ X) or (¬ Y)) is provable only if one of
the propositions is decidable. These two cases are proved in PartC.v under the
names [fromneganddecx] and [fromneganddecy]. *)

Lemma tonegdirprod {X Y : UU} : ¬ X ∨ ¬ Y -> ¬ (X × Y).
Proof.
  intros X Y. simpl.
  apply (@hinhuniv _ (hProppair _ (isapropneg (X × Y)))).
  intro c. destruct c as [ nx | ny ].
  - simpl. intro xy. apply (nx (pr1 xy)).
  - simpl. intro xy. apply (ny (pr2 xy)).
Defined.

Lemma weak_fromnegdirprod (P Q: hProp) : ¬ (P ∧ Q) -> ¬¬(¬ P ∨ ¬ Q).
(* this is also called a weak deMorgan law *)
Proof.
  intros ? ? npq k.
  assert (e : ¬¬ Q).
  {
    intro n. apply k. now apply hdisj_in2.
  }
  assert (d : ¬¬ P).
  {
    intro n. apply k. now apply hdisj_in1.
  }
  clear k.
  apply d; clear d. intro p. apply e; clear e. intro q.
  refine (npq _). exact (p,,q).
Defined.

Lemma tonegcoprod {X Y : UU} : ¬ X × ¬ Y -> ¬ (X ⨿ Y).
Proof.
  intros ? ? is. intro c. destruct c as [ x | y ].
  - apply (pr1 is x).
  - apply (pr2 is y).
Defined.

Lemma toneghdisj {X Y : UU} : ¬ X × ¬ Y -> ¬ (X ∨ Y).
Proof.
  intros ? ? is. unfold hdisj.
  apply weqnegtonegishinh.
  apply tonegcoprod.
  apply is.
Defined.

Lemma fromnegcoprod {X Y : UU} : ¬ (X ⨿ Y) -> ¬X × ¬Y.
Proof.
  intros ? ? is. split.
  - exact (fun x => is (ii1 x)).
  - exact (fun y => is (ii2 y)).
Defined.

Corollary fromnegcoprod_prop {X Y : hProp} : ¬ (X ∨ Y) -> ¬ X ∧ ¬ Y.
Proof.
  intros ? ? n.
  simpl in *.
  assert (n' := negf hinhpr n); simpl in n'; clear n.
  now apply fromnegcoprod.
Defined.

Lemma hdisjtoimpl {P : UU} {Q : hProp} : P ∨ Q -> ¬ P -> Q.
Proof.
  intros P Q.
  assert (int : isaprop (¬ P -> Q)).
  {
    apply impred. intro.
    apply (pr2 Q).
  }
  simpl. apply (@hinhuniv _ (hProppair _ int)).
  simpl. intro pq. destruct pq as [ p | q ].
  - intro np. destruct (np p).
  - intro np. apply q.
Defined.



(** *** Property of being decidable and [hdisj] ("or").

For being decidable [hconj] see [isdecpropdirprod] in uu0.v  *)

Lemma isdecprophdisj {X Y : UU} (isx : isdecprop X) (isy : isdecprop Y) :
  isdecprop (hdisj X Y).
Proof.
  intros.
  apply isdecpropif. apply (pr2 (hdisj X Y)).
  destruct (pr1 isx) as [ x | nx ].
  - apply (ii1 (hinhpr (ii1 x))).
  - destruct (pr1 isy) as [ y | ny ].
    + apply (ii1 (hinhpr (ii2 y))).
    + apply (ii2 (toneghdisj (dirprodpair nx ny))).
Defined.





(** *** The double negation version of [hinhabited] (does not require RR1). *)


Definition isinhdneg (X : UU) : hProp := hProppair (dneg X) (isapropdneg X).

Definition inhdnegpr (X : UU) : X -> isinhdneg X := todneg X.

Definition inhdnegfun {X Y : UU} (f : X -> Y) : isinhdneg X -> isinhdneg Y
  := dnegf f.

Definition inhdneguniv (X : UU) (P : UU) (is : isweq (todneg P)) :
  (X -> P) -> ((isinhdneg X) -> P)
  := fun xp : _ => fun inx0 : _ => (invmap (weqpair _ is) (dnegf  xp inx0)).

Definition inhdnegand (X Y : UU) (inx0 : isinhdneg X) (iny0 : isinhdneg Y) :
  isinhdneg (X × Y) := dneganddnegimpldneg inx0 iny0.

Definition hinhimplinhdneg (X : UU) (inx1 : ishinh X) : isinhdneg X
  := inx1 hfalse.


(** ** Decidability *)

Definition ComplementaryPair : UU := ∑ (P Q : UU), complementary P Q.
Definition Part1 (C : ComplementaryPair) : UU := pr1 C.
Definition Part2 (C : ComplementaryPair) : UU := pr1 (pr2 C).
Definition pair_contradiction (C : ComplementaryPair) : Part1 C -> Part2 C -> ∅
  := pr1 (pr2 (pr2 C)).
Definition chooser (C : ComplementaryPair) : Part1 C ⨿ Part2 C
  := pr2 (pr2 (pr2 C)).

Definition isTrue (C : ComplementaryPair)
  := hfiber (@ii1 (Part1 C) (Part2 C)) (chooser C).
Definition isFalse (C : ComplementaryPair)
  := hfiber (@ii2 (Part1 C) (Part2 C)) (chooser C).

Definition  trueWitness {C : ComplementaryPair} : isTrue  C -> Part1 C := pr1.
Definition falseWitness {C : ComplementaryPair} : isFalse C -> Part2 C := pr1.

Coercion  trueWitness : isTrue  >-> Part1.
Coercion falseWitness : isFalse >-> Part2.

Lemma complementaryDecisions (C : ComplementaryPair) :
  iscontr (isTrue C ⨿ isFalse C).
Proof.
  (* the idea of this proof is to show that [isTrue C ⨿ isFalse C] is the same
     as the decomposition provided by [weqcoprodsplit] *)
  intros.
  apply iscontrifweqtounit. assert (w := weqcoprodsplit (λ _:unit, chooser C)).
  apply invweq. apply (weqcomp w). apply weqcoprodf; apply weqhfiberunit.
Defined.

Lemma isaprop_isTrue (C : ComplementaryPair) : isaprop (isTrue C).
(* No axioms are used. *)
Proof.
  intros.
  apply (isapropcomponent1 (isTrue C) (isFalse C)).
  apply isapropifcontr.
  apply complementaryDecisions.
Defined.

Lemma isaprop_isFalse (C : ComplementaryPair) : isaprop (isFalse C).
(* No axioms are used. *)
(* By contrast, to prove [¬P] is a proposition requires the use of functional
   extensionality. *)
Proof.
  intros.
  apply (isapropcomponent2 (isTrue C) (isFalse C)).
  apply isapropifcontr.
  apply complementaryDecisions.
Defined.

Ltac unpack_pair C P Q con c := induction C as [P Qc]; induction Qc as [Q c];
                                induction c as [con c]; simpl in c, P, Q.

Lemma pair_truth (C : ComplementaryPair) : Part1 C -> isTrue C.
Proof.
  intros ? p.
  unpack_pair C P Q con c;
    unfold isTrue, hfiber, Part1, Part2, chooser in *; simpl in *.
  induction c as [p'|q].
  - now exists p'.
  - apply fromempty. contradicts (con p) q.
Defined.

Lemma pair_falsehood (C : ComplementaryPair) : Part2 C -> isFalse C.
Proof.
  intros ? q.
  unpack_pair C P Q con c;
    unfold isFalse, hfiber, Part1, Part2, chooser in *; simpl in *.
  induction c as [p|q'].
  - apply fromempty. contradicts (con p) q.
  - now exists q'.
Defined.

Definition to_ComplementaryPair {P : UU} (c : P ⨿ neg P) : ComplementaryPair
  (* By using [isTrue _] instead, we're effectively replacing P by a
     propositional subtype of it: *)
  (* the part connected to the element of [P ⨿ ¬P]. *)
  (* Similarly, by using [isFalse _] instead, we're effectively replacing [¬P]
     by a propositional subtype of it.  *)
  (* Both are proved to be propositions without [funextemptyAxiom] *)
  := (P,,neg P,,(λ p n, n p),,c).

(* Relate isolated points to complementary pairs *)

Definition isolation {X : UU} (x : X) (is : isisolated X x) (y : X) : UU
  := isFalse (to_ComplementaryPair (is y)).

Definition isaprop_isolation {X : UU} (x : X) (is : isisolated X x) (y : X) :
  isaprop (isolation x is y) := isaprop_isFalse _.

Definition isolation_to_inequality {X : UU} (x : X) (is : isisolated X x)
           (y : X) :
  isolation x is y -> x != y := falseWitness.

Definition inequality_to_isolation {X : UU} (x : X) (i : isisolated X x)
           (y : X) :
  x != y -> isolation x i y := pair_falsehood (to_ComplementaryPair (i y)).

(* operations on complementary pairs *)

Definition pairNegation (C : ComplementaryPair) : ComplementaryPair
  := Part2 C,, Part1 C ,, (λ q p, pair_contradiction C p q),,
           coprodcomm _ _ (chooser C).

Definition pairConjunction (C C' : ComplementaryPair) : ComplementaryPair.
Proof.
  intros. unpack_pair C P Q con c; unpack_pair C' P' Q' con' c'; simpl in *.
  unfold ComplementaryPair. exists (P × P'); exists (Q ⨿ Q'). split.
  - simpl. intros a b. induction a as [p p']. induction b as [b|b].
    + induction c' as [_|q'].
      * contradicts (con p) b.
      * contradicts (con p) b.
    + contradicts (con' p') b.
  - simpl. induction c as [p|q].
    + induction c' as [p'|q'].
      * apply ii1. exact (p,,p').
      * apply ii2, ii2. exact q'.
    + induction c' as [p'|q'].
      * apply ii2, ii1. exact q.
      * apply ii2, ii2. exact q'.
Defined.

Definition pairDisjunction (C C' : ComplementaryPair) : ComplementaryPair.
Proof.
  intros.
  exact (pairNegation (pairConjunction (pairNegation C) (pairNegation C'))).
Defined.

Definition dnegelim {P Q : UU} : complementary P Q -> ¬¬ P -> P.
Proof.
  intros ? ? c nnp. induction c as [n c].
  induction c as [p|q].
  - assumption.
  - contradicts nnp (λ p, n p q).
Defined.

(* Law of Excluded Middle

   We don't state LEM as an axiom, because we want to force it
   to be a hypothesis of any corollaries of any theorems that
   appeal to it. *)
Definition LEM : UU := ∏ P : hProp, decidable P.

Lemma LEM_for_sets (X : UU) : LEM -> isaset X -> isdeceq X.
Proof. intros X lem is x y. exact (lem (hProppair (x = y) (is x y))). Defined.

Lemma isaprop_LEM : isaprop LEM.
Proof.
  unfold LEM. apply impred_isaprop; intro P. apply isapropdec. apply propproperty.
Defined.

Lemma dneg_LEM (P : hProp) : LEM -> ¬¬ P -> P.
Proof. intros P lem. exact (dnegelim ((λ p np, np p),,lem P)). Defined.

Corollary reversal_LEM (P Q : hProp) : LEM -> (¬ P -> Q) -> (¬ Q -> P).
Proof.
  intros ? ? lem f n.
  assert (g := negf f); clear f.
  assert (h := g n); clear g n.
  apply (dneg_LEM _ lem).
  exact h.
Defined.

(* all of this will be redone: *)

Definition DecidableProposition : UU := ∑ X : UU, isdecprop X.

Definition isdecprop_to_DecidableProposition {X : UU} (i : isdecprop X) :
  DecidableProposition := X,,i.

Definition decidable_to_isdecprop {X : hProp} : decidable X -> isdecprop X.
Proof.
  intros ? dec. apply isdecpropif.
  - apply propproperty.
  - exact dec.
Defined.

Definition decidable_to_isdecprop_2 {X : UU} :
  isaprop X -> X ⨿ ¬ X -> isdecprop X.
Proof.
  intros ? i dec. apply isdecpropif.
  - exact i.
  - exact dec.
Defined.

Definition decidable_to_DecidableProposition {X : hProp} :
  decidable X -> DecidableProposition.
Proof. intros ? dec. exists X. now apply decidable_to_isdecprop. Defined.

Definition DecidableProposition_to_isdecprop (X : DecidableProposition) :
  isdecprop (pr1 X).
Proof. apply pr2. Defined.

Definition DecidableProposition_to_hProp : DecidableProposition -> hProp.
Proof.
  intros X.
  exact (pr1 X,, isdecproptoisaprop (pr1 X) (pr2 X)).
Defined.
Coercion DecidableProposition_to_hProp : DecidableProposition >-> hProp.
Definition decidabilityProperty (X : DecidableProposition) :
  isdecprop X := pr2 X.

Definition DecidableSubtype (X : UU) : UU := X -> DecidableProposition.
Definition DecidableRelation (X : UU) : UU := X -> X -> DecidableProposition.

Definition decidableAnd (P Q : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (P × Q). apply isdecpropdirprod; apply decidabilityProperty.
Defined.

Definition decidableOr (P Q : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (P ∨ Q). apply isdecprophdisj; apply decidabilityProperty.
Defined.

Lemma neg_isdecprop {X : UU} : isdecprop X -> isdecprop (¬ X).
Proof.
  intros ? i.
  set (j := isdecproptoisaprop X i).
  apply isdecpropif.
  - apply isapropneg.
  - unfold isdecprop in i.
    set (k := pr1 i).
    induction k as [k|k].
    + apply ii2. now apply todneg.
    + now apply ii1.
Defined.

Definition decidableNot (P : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (¬ P). apply neg_isdecprop; apply decidabilityProperty.
Defined.

Notation "X ∨ Y" := (decidableOr X Y) (at level 85, right associativity) :
                      decidable_logic.
Notation "A ∧ B" := (decidableAnd A B) (at level 80, right associativity) :
                      decidable_logic.
Notation "'¬' X" := (decidableNot X) (at level 35, right associativity) :
                      decidable_logic.
Delimit Scope decidable_logic with declog.

Ltac choose P yes no := induction (pr1 (decidabilityProperty P)) as [yes|no].

Definition choice {W : UU} : DecidableProposition -> W -> W -> W.
Proof.
  intros ? P yes no.
  choose P p q.
  - exact yes.
  - exact no.
Defined.

Definition dependent_choice {W : UU} (P : DecidableProposition) :
  (P -> W) -> (¬ P -> W) -> W.
Proof.
  intros ? P yes no.
  choose P p q.
  - exact (yes p).
  - exact (no q).
Defined.

Definition choice_compute_yes {W : UU} (P : DecidableProposition) (p : P)
           (yes no : W) :
  choice P yes no = yes.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. reflexivity.
  - simpl. contradicts p b.
Defined.

Definition choice_compute_no {W : UU} (P : DecidableProposition) (p : ¬ P)
           (yes no : W) :
  choice P yes no = no.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. contradicts p a.
  - simpl. reflexivity.
Defined.

Definition decidableSubtypeCarrier {X : UU} : DecidableSubtype X -> UU.
Proof. intros ? S. exact (∑ x, S x). Defined.

Definition decidableSubtypeCarrier' {X : UU} : DecidableSubtype X -> UU.
Proof. intros ? P.
       (* for use with isfinitedecsubset *)
       exact (hfiber (λ x, choice (P x) true false) true).
Defined.

Definition decidableSubtypeCarrier_weq {X : UU} (P : DecidableSubtype X) :
  decidableSubtypeCarrier' P ≃ decidableSubtypeCarrier P.
Proof.
  intros.
  apply weqfibtototal.
  intros x.
  unfold choice.
  simpl.
  change (pr1 (decidabilityProperty (P x)))
  with (pr1 (decidabilityProperty (P x))).
  choose (P x) p q.
  - simpl. apply weqiff.
    + apply logeq_both_true.
      * reflexivity.
      * assumption.
    + apply isasetbool.
    + apply (propproperty (DecidableProposition_to_hProp _)).
  - simpl. apply weqiff.
    + apply logeq_both_false.
      * exact nopathsfalsetotrue.
      * assumption.
    + apply isasetbool.
    + apply (propproperty (DecidableProposition_to_hProp _)).
Defined.

(** ** Univalence for hProp *)

Theorem hPropUnivalence@{i j} : ∏ (P Q : hProp@{i j}), (P -> Q) -> (Q -> P) -> paths@{j} P Q.
  (* this theorem replaced a former axiom, with the same statement, called
     "uahp" *)
Proof.
  Set Printing Universes.
  Unset Printing Notations.
  intros ? ? f g.
  apply subtypeEquality.
  - intro X. change (isofhlevel@{j} 1 (isofhlevel@{i} 1 X)).
    apply isapropisofhlevel@{i}.
  - apply propositionalUnivalenceAxiom.
    + apply propproperty.
    + apply propproperty.
    + exact f.
    + exact g.
  Unset Printing Universes.
  Set Printing Notations.
Defined.

Definition eqweqmaphProp {P P' : hProp} (e : @paths hProp P P') : weq P P'.
Proof. intros. destruct e. apply idweq. Defined.

Definition weqtopathshProp {P P' : hProp} (w : weq P P') : P = P'
  := hPropUnivalence P P' w (invweq w).

Definition weqpathsweqhProp {P P' : hProp} (w : weq P P') :
  eqweqmaphProp (weqtopathshProp w) = w.
Proof.
  intros. apply proofirrelevance.
  apply (isapropweqtoprop P P' (pr2 P')).
Defined.

Theorem univfromtwoaxiomshProp (P P' : hProp) : isweq (@eqweqmaphProp P P').
Proof.
  intros.

  set (P1 := fun XY : hProp × hProp => (pr1 XY) = (pr2 XY)).
  set (P2 := fun XY : hProp × hProp => weq (pr1 XY) (pr2 XY)).
  set (Z1 :=  total2 P1).
  set (Z2 :=  total2 P2).
  set (f := (totalfun _ _ (fun XY : hProp × hProp =>
                             @eqweqmaphProp (pr1 XY) (pr2 XY)): Z1 -> Z2)).
  set (g := (totalfun _ _ (fun XY : hProp × hProp =>
                             @weqtopathshProp (pr1 XY) (pr2 XY)): Z2 -> Z1)).
  assert (efg : ∏ z2 : Z2 , @paths Z2 (f (g z2)) z2).
  {
    intros. induction z2 as [ XY w].
    exact (maponpaths (fun w : weq (pr1 XY) (pr2 XY) => tpair P2 XY w)
                      (@weqpathsweqhProp (pr1 XY) (pr2 XY) w)).
  }

  set (h := fun a1 : Z1 => (pr1 (pr1 a1))).
  assert (egf0 : ∏ a1 : Z1, (pr1 (g (f a1))) = (pr1 a1))
         by (intro; apply idpath).
  assert (egf1 : ∏ a1 a1' : Z1, (pr1 a1') = (pr1 a1) -> a1' = a1).
  {
    intros ? ? X.
    set (X' := maponpaths (@pr1 _ _) X).
    assert (is : isweq h) by apply (isweqpr1pr1 hProp).
    apply (invmaponpathsweq (weqpair h is) _ _ X').
  }
  set (egf := fun a1:_ => (egf1 _ _ (egf0 a1))).
  set (is2 := gradth _ _ egf efg).
  apply (isweqtotaltofib P1 P2 (fun XY : hProp × hProp =>
                                  @eqweqmaphProp (pr1 XY) (pr2 XY)) is2
                         (dirprodpair P P')).
Defined.

Definition weqeqweqhProp (P P' : hProp) : P = P' ≃ (P ≃ P')
  := weqpair _ (univfromtwoaxiomshProp P P').

Corollary isasethProp : isaset hProp.
Proof.
  unfold isaset. simpl. intros x x'.
  apply (isofhlevelweqb (S O) (weqeqweqhProp x x')
                        (isapropweqtoprop x x' (pr2 x'))).
Defined.

Definition weqpathsweqhProp' {P P' : hProp} (e : P = P') :
  weqtopathshProp (eqweqmaphProp e) = e.
Proof. intros. apply isasethProp. Defined.

Lemma iscontrtildehProp@{i j} : iscontr@{j} tildehProp@{i j}.
Proof.
  Set Printing Universes.
  split with (tpair _ htrue tt). intro tP. destruct tP as [ P p ].
  apply subtypeEquality.
  - intros Q. induction Q as [Q ipQ]. change (isaprop@{j} Q).
    exact ipQ.
  - change (P = htrue@{i j}). apply hPropUnivalence.
    + intros _. exact tt.
    + intros _. exact p.
  Unset Printing Universes.
Defined.

Lemma isaproptildehProp : isaprop tildehProp.
Proof. apply (isapropifcontr iscontrtildehProp). Defined.

Lemma isasettildehProp : isaset tildehProp.
Proof. apply (isasetifcontr iscontrtildehProp). Defined.


(* ** Logical equivalence yields weak equivalence *)

Definition logeqweq (P Q : hProp) : (P -> Q) -> (Q -> P) -> weq P Q :=
  fun f g => weqimplimpl f g (pr2 P) (pr2 Q).

(* ** A variant of a lemma proved in uu0b.v *)
Theorem total2_paths_hProp_equiv {A : UU} (B : A -> hProp)
   (x y : total2 (fun x => B x)) : weq (x = y) (pr1 x = pr1 y).
Proof.
  intros.
  apply subtypeInjectivity.
  intro a. apply (pr2 (B a)).
Defined.
