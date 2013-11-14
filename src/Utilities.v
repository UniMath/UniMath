(** * utilities concerning paths, hlevel, and logic *)

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import Foundations.hlevel2.hSet.

Local Notation "f ~ g" := (Foundations.Generalities.uu0.homot f g) (at level 51).

Unset Automatic Introduction.

Definition pathReversal := @pathsinv0.

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

Lemma factor_dep_through_squash {X:UU} {Q:squash X->UU} : 
  (forall y, isaprop (Q y)) -> 
  (forall x, Q(squash_element x)) -> 
  (forall h, Q h).
Proof.
  intros ? ? i f ?.  apply (h (hProppair _ (i h))). 
  intro x. destruct (squash_uniqueness x h).  exact (f x).
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
   apply (isofhleveltotal2 2). assumption.
   intros y. apply impred.
   intros t. apply isasetaprop. apply is.
  assert(g : X -> P). intros x. exists (f x). intros x'. apply e.
  assert(m : X -> forall y:Y, isaprop (L y)).
   intros a z. apply impred.
   intros t. apply is.
  assert(h : X -> isaprop P).
   intros a [r i] [s j].
   assert(k : r == s). intermediate (f a). apply pathsinv0. apply i. apply j.
   assert(l : tpair L r i == tpair L s j).
    apply (pair_path k). apply m. assumption.
   exists l. intro t. apply (ip _ _ t l).
  assert(h' : squash X -> isaprop P).
   apply factor_through_squash. intro z. apply isapropisaprop.
   assumption.
  assert(k : squash X -> P).
   intros z.
   apply (@factor_through_squash X _ (h' z)). assumption.    
   assumption.
  intro z.
  exact (pr1 (k z)).
Defined.

(** * Dependent squashing *)

Definition squash_dep (X:UU) := forall P:X -> UU, (forall x:X, isaprop (P x)) -> (forall x:X, P x) -> squash (total2 P).

Definition squash_dep_element (X:UU) : X -> squash_dep X.
Proof.
  intros ? x P h s.
  apply squash_element.
  exists x.
  apply s.
Defined.

Lemma isaprop_squash_dep (X:UU) : isaprop (squash_dep X).
Proof. 
  intro.
  apply (impred 1).
  intro S.
  apply impred.
  intro is.
  apply impred.  
  intro s.  
  apply isaprop_squash.
Defined.

Lemma lift_through_squash_dep {X:UU} {Q : squash_dep X -> UU} : 
  (forall y : squash_dep X, isaprop (Q y)) 
  -> (forall x:X, Q (squash_dep_element X x))
  -> (forall y : squash_dep X, Q y).
Proof.
  intros ? ? is q y.
  assert (t : hProppair (Q y) (is y)).
    apply (y (funcomp (squash_dep_element X) Q)).
        intro x. apply is.
      apply q.
    intros [x p].
    set (y' := squash_dep_element _ x).
    assert(e : y' == y).
      apply isaprop_squash_dep.
    assert(t : Q y').
      exact p.
    apply (transportf _ e t).  
  exact t.
Defined.

Lemma foo {Q:UU} (is:isaprop Q) (q:Q) : hProppair Q is.
Proof. intros. assumption. Defined.

Lemma factor_through_squash_dep {X Q:UU} : isaprop Q -> (X -> Q) -> (squash_dep X -> Q).
Proof.
  intros ? ? is q y.
  assert (t : hProppair Q is).
    apply (y (fun _ => Q)).
        intros x.
        assumption.
      assumption.
    intros [_ q'].
    assumption.
  exact t.
Defined.

Lemma squashes_agree {X:UU} : weq (squash X) (squash_dep X).
Proof.
  intros.
  unfold weq.
  exists (factor_through_squash (isaprop_squash_dep X) (squash_dep_element X)).
  apply (gradth _ (factor_through_squash_dep (isaprop_squash X) (@squash_element X))).
  intro x.
  apply (isaprop_squash X).
  intro y.
  apply (isaprop_squash_dep X).
Defined.

(* now that we know the two squashes agree, we should figure out how to eliminate
   squash_dep in favor of squash *)

Lemma squash_dep_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash_dep X -> S) : 
  funcomp (squash_dep_element X) g ~ funcomp (squash_dep_element X) g' 
  -> g ~ g'.
Proof.
  intros ? ? ? ? ? h.
  set ( Q := fun y => g y == g' y ).
  assert ( iq : forall y, isaprop (Q y) ).
    intros y. apply ip.
  intros y.
  apply (lift_through_squash_dep iq h).
Defined.

Lemma squash_dep_map_epi {X S:UU} (ip : isaset S) (g g' : squash_dep X -> S) : 
  funcomp (squash_dep_element X) g == funcomp (squash_dep_element X) g' 
  -> g == g'.
Proof.
  intros ? ? ? ? ? e.
  apply funextfunax.
  apply squash_dep_map_uniqueness.
  assumption.
  intro x.
  path_from (fun q : X -> S => q x).
  assumption.
Defined.

Definition squash_dep_factoring {X Y:UU} (f : X -> Y) := total2 (fun g : squash_dep X -> Y => f == funcomp (squash_dep_element X) g).
