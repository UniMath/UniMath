(** * Ordered sets *)

(** see Bourbaki, Set Theory, III.1, where they are called totally ordered sets *)

Require Import UniMath.Foundations.hlevel2.finitesets.

Definition Object := total2 (fun X : Poset => dirprod (istotal (pr1 (pr2 X))) (isantisymm (pr1 (pr2 X)))).

Definition underlyingSet (X:Object) : hSet := pr1 X.
Coercion underlyingSet : Object >-> hSet.

Definition underlyingRelation (X:Object) := pr1 (pr2 (pr1 X)).

Notation "m <= n" := (underlyingRelation _ m n).
Notation "m >= n" := (n <= m).
Notation "m < n" := (dirprod (m <= n) (not (m = n))).
Notation "m > n" := (n < m).

Definition std (n:nat) : Object.
Proof.
  intros.
  exists (stnposet n).
  split.
  { intros x y. apply istotalnatleh. }
  { intros ? ? ? ?.
    apply (invmaponpathsincl (stntonat _)).
    { apply isinclstntonat. }
    { apply isantisymmnatleh. assumption. assumption. }}
Defined.

Definition isordered {X Y:Object} (f:X->Y) := forall (x x':X), x <= x' -> f x <= f x'.

Definition Map (X Y:Object) := total2 (fun f:X->Y => isordered f).

Definition finstruct (X:Object) := total2 (fun n => total2 (fun f : weq (std n) X => isordered (pr1 f))).
