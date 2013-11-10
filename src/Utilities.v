(** * utilities concerning paths, hlevel, and logic *)

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import Foundations.hlevel2.hSet.

Local Notation "f ~ g" := (Foundations.Generalities.uu0.homot f g) (at level 51).

(** * h-levels and paths *)

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropdirprod); try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr);
  try assumption.

Global Opaque isapropiscontr isapropishinh.

Definition pathscomp0' {T:UU} {a b c:T} : a == b -> b == c -> a == c.
Proof. intros e1 e2. 
  destruct e2. (* compare to Foundations.uu0.pathscomp0, which destructs e1, instead *)
  assumption. 
Defined.

Ltac path_via  x   := apply (@pathscomp0  _  _ x).
Ltac path_via' x   := apply (@pathscomp0' _  _ x).
Ltac path_via2 x y := apply (@pathscomp0  _  _ x _  _ (@pathscomp0 _  _ y _  _ _)).
Ltac path_from f := apply (@maponpaths _ _ f).

Lemma hlevel1_isaprop {X:UU} : isaprop X -> isofhlevel 1 X.
Proof. trivial. Defined.

Lemma isaprop_hlevel1 {X:UU} : isofhlevel 1 X -> isaprop X.
Proof. trivial. Defined.

Lemma hlevel2_isaset {X:UU} : isaset X -> isofhlevel 2 X.
Proof. trivial. Defined.

Lemma isaset_hlevel2 {X:UU} : isofhlevel 2 X -> isaset X.
Proof. trivial. Defined.

Lemma isaset_hSet (X:hSet) : isaset X.
Proof. exact (pr2 X). Defined.

(** * Squashing. *)

Definition squash (X:UU) := forall P:UU, isaprop P -> (X -> P) -> P. (* compare with ishinh_UU *)

Definition squash_element (X:UU) : X -> squash X.
Proof. intros x P. auto. Defined.

Lemma isaprop_squash (X:UU) : isaprop (squash X).
Proof. prop_logic. Qed.

Lemma factor_through_squash {X Q:UU} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros i f h.  apply h.  assumption.  assumption. Defined.

Lemma funspace_isaset {X Y:UU} : isaset Y -> isaset (X -> Y).
Proof. intro is. apply isaset_hlevel2. apply impredfun. assumption. Defined.    

Lemma pair_path {X:UU} {P:X->UU} {x x':X} {p: P x} {p' : P x'} (e : x == x') (e' : transportf P e p == p') : tpair P x p == tpair P x' p'.
Proof. destruct e. destruct e'. apply idpath. Defined.

Lemma iscontr_if_inhab_prop {P:UU} : isaprop P -> P -> iscontr P.
Proof. intros i p. exists p. intros p'. apply i. Defined.

(** ** show that squashing is a set-quotient *)

Lemma squash_to_set (X Y:UU) : forall f : X -> Y, 
  isaset Y -> (forall x x' : X, f x == f x') -> squash X -> Y.
Proof.
  intros f is e.
  set (L := fun y:Y => forall x:X, f x == y).
  set (P := total2 L).
  assert(ip : isaset P).
   apply isaset_hlevel2.
   apply isofhleveltotal2. apply hlevel2_isaset. assumption.
   intros y. apply impred.
   intros t. apply hlevel2_isaset. apply isasetaprop. apply is.
  assert(g : X -> P). intros x. exists (f x). intros x'. apply e.
  assert(m : X -> forall y:Y, isaprop (L y)).
   intros a z. apply isaprop_hlevel1. apply impred.
   intros t. apply is.
  assert(h : X -> isaprop P).
   intros a [r i] [s j].
   assert(k : r == s). path_via (f a). apply pathsinv0. apply i. apply j.
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
  intros x P h s.
  apply squash_element.
  exists x.
  apply s.
Defined.

Lemma isaprop_squash_dep (X:UU) : isaprop (squash_dep X).
Proof. 
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
  intros is q y.
  set (S := funcomp (squash_dep_element X) Q).
  apply (y S).
    intro x.
    apply is.
  apply q.
  apply is.
  intros [x p].
  set (y' := squash_dep_element _ x).
  assert(e : y' == y).
  apply isaprop_squash_dep.
  assert(t : Q y').
  exact p.
  apply (transportf _ e).  
  assumption.
Defined.

Lemma factor_through_squash_dep {X Q:UU} : isaprop Q -> (X -> Q) -> (squash_dep X -> Q).
Proof.
  intros is q y.
  unfold squash_dep in y.
  apply (y (fun _ => Q)).
  intros x.
  assumption.
  assumption.
  assumption.
  intros [_ q'].
  assumption.
Defined.

Lemma squashes_agree {X:UU} : weq (squash X) (squash_dep X).
Proof.
  unfold weq.
  exists (factor_through_squash (isaprop_squash_dep X) (squash_dep_element X)).
  apply (gradth _ (factor_through_squash_dep (isaprop_squash X) (squash_element X))).
  intro x.
  apply (isaprop_squash X).
  intro y.
  apply (isaprop_squash_dep X).
Defined.

Lemma squash_dep_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash_dep X -> S) : 
  funcomp (squash_dep_element X) g ~ funcomp (squash_dep_element X) g' 
  -> g ~ g'.
Proof.
  intros h.
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
  intro e.
  apply funextfunax.
  apply squash_dep_map_uniqueness.
  assumption.
  intro x.
  path_from (fun q : X -> S => q x).
  assumption.
Defined.

Definition squash_dep_factoring {X Y:UU} (f : X -> Y) := total2 (fun g : squash_dep X -> Y => f == funcomp (squash_dep_element X) g).
