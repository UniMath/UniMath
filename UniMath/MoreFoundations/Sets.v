Require Export UniMath.MoreFoundations.Propositions.

Local Open Scope set.

Definition isconst {X:UU} {Y:hSet} (f : X -> Y) : hProp := ∀ x x', f x = f x'.

Definition squash_to_hSet {X : UU} {Y : hSet} (f : X -> Y) : isconst f -> ∥ X ∥ -> Y.
Proof.
  apply squash_to_set, setproperty.
Defined.

Definition isconst_2 {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
  (∀ x x' y y', f x y = f x' y')%set.

Definition squash_to_hSet_2 {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2 f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros c. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (c x x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y y). }
Defined.

Definition isconst_2' {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
  (
    (∀ x x' y, f x y = f x' y)
    ∧
    (∀ x y y', f x y = f x y')
  )%set.

Definition squash_to_hSet_2' {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2' f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros [c d]. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (d x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y). }
Defined.

Definition eqset_to_path {X:hSet} (x y:X) : eqset x y -> x = y := λ e, e.
