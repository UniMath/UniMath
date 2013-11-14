(** * utilities concerning paths, hlevel, and logic *)

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import Foundations.hlevel2.hSet.

Local Notation "f ~ g" := (Foundations.Generalities.uu0.homot f g) (at level 51).
Local Notation "g ∘ f" := (Foundations.Generalities.uu0.funcomp f g) (at level 50).

Unset Automatic Introduction.

Notation pathReversal := pathsinv0.

(** * h-levels and paths *)

Ltac prop_logic := 
  intros;
  simpl;
  repeat (try (apply isapropdirprod); try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr);
  try assumption.

Global Opaque isapropiscontr isapropishinh.

Definition pathscomp0' {T:UU} {a b c:T} : a == b -> b == c -> a == c.
Proof. intros ? ? ? ? e1 e2. 
  destruct e2. (* compare to Foundations.uu0.pathscomp0, which destructs e1, instead *)
  assumption. 
Defined.

Ltac intermediate  x   := apply (@pathscomp0  _  _ x).
Ltac intermediate' x   := apply (@pathscomp0' _  _ x).
Ltac intermediate2 x y := apply (@pathscomp0  _  _ x _  _ (@pathscomp0 _  _ y _  _ _)).
Ltac path_from f := apply (@maponpaths _ _ f).

(*

The use of this lemma ahead of something like 'impred' can be avoided by
providing 2 as first argument.

    Definition isaset_hlevel2 {X:UU} : isofhlevel 2 X -> isaset X.
    Proof. trivial. Defined.

*)

Definition isaprop_hProp (X:hProp) : isaprop X.
Proof. intro. exact (pr2 X). Defined.

Definition isaset_hSet (X:hSet) : isaset X.
Proof. intro. exact (pr2 X). Defined.

Definition the {T:UU} : iscontr T -> T.
Proof. intro. exact pr1. Defined.

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

Lemma pair_path {X:UU} {P:X->UU} {x x':X} {p: P x} {p' : P x'} (e : x == x') (e' : transportf P e p == p') : tpair P x p == tpair P x' p'.
Proof. intros. destruct e. destruct e'. apply idpath. Defined.

Lemma iscontr_if_inhab_prop {P:UU} : isaprop P -> P -> iscontr P.
Proof. intros ? i p. exists p. intros p'. apply i. Defined.

(** ** show that squashing is a set-quotient *)

Lemma squash_to_set (X Y:UU) : forall f : X -> Y, 
  isaset Y -> (forall x x' : X, f x == f x') -> squash X -> Y.

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
  assert(h : X -> isaprop P). Focus.
   intros a [r i] [s j].
   assert(k : r == s). intermediate (f a). apply pathReversal. apply i. apply j.
   assert(l : tpair L r i == tpair L s j).
    apply (pair_path k). apply m. exact a.
   exists l. intro t. apply (ip _ _ t l).
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

Lemma squash_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element ~ g' ∘ squash_element -> g ~ g'.
Proof.
  intros ? ? ? ? ? h.
  set ( Q := fun y => g y == g' y ).
  unfold homot.
  apply (@factor_dep_through_squash X). intros y. apply ip.
  intro x. apply h.
Defined.

Lemma squash_map_epi {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element == g'∘ squash_element -> g == g'.
Proof.
  intros ? ? ? ? ? e.
  apply funextfunax.
  apply squash_map_uniqueness. exact ip.
  intro x. destruct e. apply idpath.
Qed.
