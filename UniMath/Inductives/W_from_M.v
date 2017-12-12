(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Inductives.algebras.


Section Wtypes.

  (* Assuming M-types construct W-types *)

  Variable (A : UU) (B : A -> UU).

  CoInductive M : Type :=
    supM : total2 (fun a : A => B a -> M) -> M.

  Definition labelM (m : M) : A.
  Proof.
    intros.
    destruct m.
    exact (pr1 t).
  Defined.

  Definition argM (m : M) : B (labelM m) -> M.
  Proof.
    intros m.
    destruct m.
    exact (pr2 t).
  Defined.

  Definition isWf (m : M) : UU :=
    ∏ P : M -> hProp,
      (∏ a : A, ∏ f : B a -> M, (∏ b : B a, P (f b)) -> P (supM (a ,, f)))
        -> P m.

  Definition isprop_isWf (m : M) : isaprop (isWf m).
  Proof.
    intros. apply impred.
    intro. apply impred.
    intro. exact (pr2 (t m)).
  Defined.

  Definition W : UU := total2 isWf.

  Definition sup (a : A) (f : B a -> W) : W.
  Proof.
    intros.
    exists (supM (a ,, pr1 ∘ f)).
    intros P step.
    apply step.
    intro b.
    apply (pr2 (f b)).
    exact step.
  Defined.

  Definition label : W -> A.
  Proof.
    intro w. destruct w as [m p].
    destruct m.
    exact (pr1 t).
  Defined.

  Definition subtr_wf_then_wf (m : M) (stwf : ∏ b : B (labelM m), isWf (argM m b) ) : isWf m.
  Proof.
    intros.
    intros P step.
    destruct m.
    destruct t as [a f].
    simpl in *.
    apply step.
    intro b.
    apply (stwf b).
    exact step.
  Defined.

  Definition P (m : M) : UU := ∏ b : B (labelM m), isWf (argM m b).


  Definition ispropP (m : M) : isaprop (P m).
  Proof.
    intros.
    apply impred.
    intro.
    apply isprop_isWf.
  Defined.

  Definition Pp (m : M) : hProp.
  Proof.
    intros.
    exists (P m).
    apply ispropP.
  Defined.

  Definition wf_then_subtr_wf (m : M) (p : isWf m) : Pp m.
  Proof.
    intros.
    apply p.
    intros. clear p m.
    simpl in *.
    unfold P in *.
    simpl.
    intro b.
    apply subtr_wf_then_wf.
    apply (X b).
  Defined.

  (*
  Definition arg (w : W) (b : B (label w)) : W.
  Proof.
    intros w. destruct w as [m p].
    destruct m. destruct t as [a f].
    intro b.
    exists (f b).
    simpl in b.
    revert b.
    apply wf_then_subtr_wf.

    intros P step.
    simpl in b.
  *)

End Wtypes.
