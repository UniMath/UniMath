Require Export UniMath.Foundations.PartB.

Section SafeResizing.

  (** this file is not compiled with type-in-type *)

  (** In this section we put any type-safe definitions needed by Resizing.v, which
     is compiled with type-in-type. *)

  Universe i j.
  Constraint i < j.
  Set Printing Universes.
  Unset Printing Notations.

  Definition raise_type : Type@{i} -> Type@{j}.
  Proof.
    intros T.
    exact T.
  Defined.

  Lemma weq_raise {X : Type@{i}} (x y : X) : @paths@{i} X x y ≃ @paths@{j} (raise_type X) x y.
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)); intros p; now induction p.
  Defined.

End SafeResizing.
