Require Export UniMath.Foundations.PartB.

(* this file is compiled with type-in-type *)

Section A.

  Universe i j.

  (* If we don't impose this constraint, Coq generates the constraint j <= i for us, which
     excludes exactly the cases we want. *)
  Constraint i < j.

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

