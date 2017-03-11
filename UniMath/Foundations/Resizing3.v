Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.Resizing2.

(* this file is not compiled with type-in-type *)

Section A.

  Universe i j.
  Constraint i < j.

  Definition raise_type : Type@{i} -> Type@{j}.
  Proof.
    intros T.
    exact T.
  Defined.

  Lemma weq_raise {X : Type@{i}} (x y : X) : @paths@{i} X x y ≃ @paths@{j} (raise_type X) x y.
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)); intros p; now induction p.
  Defined.

  Definition lower_path {X : Type@{j}} (x y : ResizeType X) :
    @paths@{j} X x y -> @paths@{i} (ResizeType X) x y.
  Proof.
    intros p.
    now induction p.
  Defined.

  Goal ∏ (X : Type@{j}), raise_type (ResizeType X) = X.
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

Lemma isofhlevel_resize@{i j} n (X:Type@{j}) : isofhlevel@{j j} n X -> isofhlevel@{i i} n (ResizeType@{i j} X).
Proof.
  apply isofhlevelweqf, resize_weq.
Defined.
