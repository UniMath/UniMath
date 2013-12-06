(** * utilities concerning paths, hlevel, and logic *)

Unset Automatic Introduction.

Require Import RezkCompletion.pathnotations.
Require Import Foundations.hlevel2.hSet.
        Import RezkCompletion.pathnotations.PathNotations.

Definition type_equality_to_function {X Y:UU} : (X==Y) -> X -> Y.
  intros ? ? e x. destruct e. exact x.
Defined.

Definition transport {X:UU} (P:X->UU) {x x':X} (e:x==x'): P x -> P x'.
  (* this is a replacement for transportf in uu0.v that pushes the path
     forward to the universe before destroying it, to make it more likely
     we can prove it's trivial *)
  intros ? ? ? ? e p.
  exact (type_equality_to_function (maponpaths P e) p).
Defined.

Module Import Notations.
    Notation ap := maponpaths.
    Notation "f ~ g" := (Foundations.Generalities.uu0.homot f g) (at level 51).
    Notation "g ∘ f" := (Foundations.Generalities.uu0.funcomp f g) (at level 50).
    Notation "f ;; g" := (Foundations.Generalities.uu0.funcomp f g) (at level 50).
    Notation "x ,, y" := (tpair _ x y) (at level 41, right associativity).
    (* funcomp' is like funcomp, but with the arguments in the other order *)
    Definition funcomp' { X Y Z : UU } ( g : Y -> Z ) ( f : X -> Y ) := fun x : X => g ( f x ) . 
    Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
End Notations.

Definition sections {T:UU} (P:T->UU) := forall t:T, P t.

Definition evalat {T:UU} {U:UU} (t:T) (f:T->U) := f t.

Definition evalsecat {T:UU} {P:T->UU} (t:T) (f:sections P) := f t.

(** * h-levels and paths *)

Lemma isaprop_wma_inhab (X:UU) : (X -> isaprop X) -> isaprop X.
Proof.
  intros ? f.
  apply invproofirrelevance.
  intros x y.
  apply (f x).
Defined.

Lemma isaprop_wma_inhab' (X:UU) : (X -> iscontr X) -> isaprop X.
Proof.
  intros ? f.
  apply isaprop_wma_inhab.
  intro x.
  apply isapropifcontr.
  apply (f x).
Defined.

Ltac prop_logic := 
  intros;
  simpl;
  repeat (try (apply isapropdirprod); try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr);
  try assumption.

Global Opaque isapropiscontr isapropishinh.

Ltac intermediate  x   := apply (@pathscomp0  _  _ x).
Ltac intermediate2 x y := apply (@pathscomp0  _  _ x _  _ (@pathscomp0 _  _ y _  _ _)).
Ltac path_from f := apply (@ap _ _ f).

Definition isaset_if_isofhlevel2 {X:UU} : isofhlevel 2 X -> isaset X.
(* The use of this lemma ahead of something like 'impred' can be avoided by
   providing 2 as first argument. *)
Proof. trivial. Defined.

Definition isofhlevel2_if_isaset {X:UU} : isaset X -> isofhlevel 2 X.
Proof. trivial. Defined.

Definition isaprop_hProp (X:hProp) : isaprop X.
Proof. intro. exact (pr2 X). Defined.

Definition isaset_hSet (X:hSet) : isaset X.
Proof. intro. exact (pr2 X). Defined.

Definition the {T:UU} : iscontr T -> T.
Proof. intros ? is. exact (pr1 is). Defined.

Definition uniqueness {T:UU} (i:iscontr T) (t:T) : t == the i.
Proof. intros. exact (pr2 i t). Defined.

Definition uniqueness' {T:UU} (i:iscontr T) (t:T) : the i == t.
Proof. intros. exact (! (pr2 i t)). Defined.

(** * Squashing. *)

Notation squash := ishinh_UU.
(* Definition squash (X:UU) := forall P:UU, isaprop P -> (X -> P) -> P. (* compare with ishinh_UU *) *)

Definition squash_element {X:UU} : X -> squash X.
Proof. intros ? x P f. exact (f x). Defined.

Lemma isaprop_squash (X:UU) : isaprop (squash X).
Proof. prop_logic. Qed.
 
Lemma squash_uniqueness {X:UU} (x:X) (h:squash X) : squash_element x == h.
Proof. intros. apply isaprop_squash. Qed.

Lemma factor_through_squash {X Q:UU} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros ? ? i f h. apply (h (hProppair _ i)). intro x. exact (f x). Defined.

Lemma factor_through_squash_factors {X Q:UU} (i:isaprop Q) (f:X -> Q) (x:X)
   : factor_through_squash i f (squash_element x) == f x.
Proof. trivial. Defined.

Lemma factor_dep_through_squash {X:UU} {Q:squash X->UU} : 
  (forall h, isaprop (Q h)) -> 
  (forall x, Q(squash_element x)) -> 
  (forall h, Q h).
Proof.
  intros ? ? i f ?.  apply (h (hProppair (Q h) (i h))). 
  intro x. simpl. destruct (squash_uniqueness x h). exact (f x).
Defined.

Lemma factor_through_squash_hProp {X:UU} : forall hQ:hProp, (X -> hQ) -> (squash X -> hQ).
Proof. intros ? [Q i] f h. apply h. assumption. Defined.

Lemma funspace_isaset {X Y:UU} : isaset Y -> isaset (X -> Y).
Proof. intros ? ? is. apply (impredfun 2). assumption. Defined.    

Lemma pair_path {X:UU} {P:X->UU} {x x':X} {p: P x} {p' : P x'} (e : x == x') (e' : transport _ e p == p') : x ,, p == x' ,, p'.
  (* an alternative to this lemma is total2_paths *)
Proof. intros. destruct e. destruct e'. apply idpath. Defined.

Lemma iscontr_if_inhab_prop {P:UU} : isaprop P -> P -> iscontr P.
Proof. intros ? i p. exists p. intros p'. apply i. Defined.

(** ** show that squashing is a set-quotient *)

Lemma squash_to_set {X Y:UU} (f : X -> Y) :
  isaset Y -> (forall x x', f x == f x') -> squash X -> Y.

(** from Voevodsky, for future work:

    I think one can get another proof using "isapropimeqclass" (hSet.v) with "R :=
    fun x1 x1 => unit". This Lemma will show that under your assumptions "Im f" is
    a proposition. Therefore "X -> Im f" factors through "squash X". *)

Proof.
  intros ? ? ? is e.
  set (L := fun y:Y => forall x:X, f x == y).
  set (P := total2 L).
  assert(ip : isaset P).
   apply (isofhleveltotal2 2). exact is.
   intros y. apply impred.
   intros t. apply isasetaprop. apply is.
  assert(m : X -> forall y:Y, isaprop (L y)).
   intros a z. apply impred.
   intros t. apply is.
  assert(h : X -> isaprop P).
   intros a.
   apply invproofirrelevance.
   intros [r i] [s j].
   assert(k : r == s). 
     intermediate (f a). 
     apply pathsinv0; apply i.
     apply j.
   apply (pair_path k). apply m. exact a.
  assert(h' : squash X -> isaprop P).
   apply factor_through_squash. apply isapropisaprop.
   exact h.
  assert(k : squash X -> P).
   intros z.
   apply (@factor_through_squash X _ (h' z)).
    intros x. exists (f x). intros x'. apply e.
   exact z.
  intro z. apply (pr1 (k z)).
Defined.

Lemma squash_to_set_equal (X Y:UU) (f : X -> Y) (is : isaset Y) (eq: forall x x', f x == f x') :
  forall x, squash_to_set f is eq (squash_element x) == f x.
Proof. trivial. Defined.

Lemma squash_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element ~ g' ∘ squash_element -> g ~ g'.
Proof.
  intros ? ? ? ? ? h.
  set ( Q := fun y => g y == g' y ).
  unfold homot.
  apply (@factor_dep_through_squash X). intros y. apply ip.
  intro x. apply h.
Qed.

Lemma squash_map_epi {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element == g'∘ squash_element -> g == g'.
Proof.
  intros ? ? ? ? ? e.
  apply funextfunax.
  apply squash_map_uniqueness. exact ip.
  intro x. destruct e. apply idpath.
Qed.

Lemma isaxiomfuncontr { X : UU } (P:X -> UU) : isaprop ((forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x)).
Proof.
  intros.
  apply impred; intro.
  apply isapropiscontr.
Defined.

(* compare this to functtransportf in uu0 *)
Lemma functtransportf_universal {X:UU} {P:X->UU} {x x':X } (e:x==x') (p:P x) :
  type_equality_to_function (ap P e) p == e # p.
Proof.  intros. destruct e. apply idpath. Defined.   

(* from Vladimir, possible useful for eta-correction: *)

Definition fpmaphomotfun {X: UU} {P Q: X -> UU} (h: homot P Q) (xp: total2 P): total2 Q.
Proof. intros ? ? ? ? [x p]. split with x.  destruct (h x). exact p. Defined.

Definition fpmaphomothomot {X: UU} {P Q: X -> UU} (h1 h2: P ~ Q) (H: forall x: X, h1 x == h2 x) :
  fpmaphomotfun h1 ~ fpmaphomotfun h2.
Proof. intros. intros [x p].
       apply (maponpaths (tpair _ x)).  
       destruct (H x). apply idpath.  
Defined.
