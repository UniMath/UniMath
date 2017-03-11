Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.Resizing2.

(* this file is not compiled with type-in-type *)

Section A.

  Universe i j.
  Constraint i < j.
  Set Printing Universes.
  Unset Printing Notations.
  Arguments paths : clear implicits.

  Definition lower_path {X : Type@{j}} (x y : ResizeType X) :
    @paths@{j} X x y -> @paths@{i} (ResizeType X) x y.
  Proof.
    intros p.
    now induction p.
  Defined.

  Goal ∏ (X : Type@{j}), raise_type@{i j} (ResizeType X) = X.
  Proof.
    reflexivity.
  Defined.

  Definition resize_lower {X:Type@{j}} : X -> ResizeType@{i j} X.
  Proof.
    intros x.
    exact x.
  Defined.

  Definition resize_raise {X:Type@{j}} : ResizeType@{i j} X -> X.
  Proof.
    intros x.
    exact x.
  Defined.

  Lemma resize_weq {X:Type@{j}} : X ≃ ResizeType@{i j} X.
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - intros x. exact x.
    - intros x. exact x.
    - reflexivity.
    - reflexivity.
  Defined.

End A.

Lemma isaprop_resize@{i j} (P:Type@{j}) : isaprop@{j} P -> isaprop@{i} (ResizeType@{i j} P).
Proof.
  intros ip.
  apply invproofirrelevance@{i i}; intros p q.
  assert (e := proofirrelevance@{j} _ ip p q); clear ip.
  now induction e.
Defined.
