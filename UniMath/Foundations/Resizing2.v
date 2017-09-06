Require Export UniMath.Foundations.PartB.

(* this file is compiled with type-in-type *)

Section A.

  Universe i j.

  Constraint i < j.             (* we impose this constraint so we don't resize a type needlessly *)

  Definition ResizeProp@{} (T : Type@{j}) : isaprop@{j} T -> Type@{i}.
  Proof.
    intros _.
    exact T.
  Defined.

  Definition ResizeType@{} {S : Type@{i}} (T : Type@{j}) : weq@{j} S T -> Type@{i}.
  Proof.
    intros _.
    exact T.
  Defined.

End A.

