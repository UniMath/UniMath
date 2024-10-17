Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Section SubPreorder.

  Context {X : UU}.
  Context (P : po X).
  Context (A : hsubtype X).

  Definition subpreorder
    : po A.
  Proof.
    use make_po.
    - exact (resrel P A).
    - abstract (
        split;
        [ apply istransresrel;
          apply istrans_po
        | apply isreflresrel;
          apply isrefl_po ]
      ).
  Defined.

End SubPreorder.

Section DownType.

  Definition down_type
    {X : UU}
    (P : hrel X)
    (y : X)
    : hsubtype X
    := λ x, P x y.

  Definition up_type
    {X : UU}
    (P : hrel X)
    (x : X)
    : hsubtype X
    := λ y, P x y.

End DownType.

Section DownwardClosed.

  Context {X : UU}.
  Context (P : hrel X).

  Definition is_downward_closed
    (f : hsubtype X)
    : UU
    := ∏ (x : f)
      (y : down_type P (pr1carrier _ x)),
      f (pr1carrier _ y).

  Definition downward_closed_subtype
    : UU
    := ∑ f, is_downward_closed f.

  Coercion downward_closed_subtype_to_subtype
    (f : downward_closed_subtype)
    : hsubtype X
    := pr1 f.

  Definition downward_closed_is_downward_closed
    (f : downward_closed_subtype)
    : is_downward_closed f
    := pr2 f.

  Definition make_downward_closed_subtype
    (f : hsubtype X)
    (H : is_downward_closed f)
    : downward_closed_subtype
    := f ,, H.

End DownwardClosed.

Section DownwardClosure.

  Context {X : UU}.
  Context (P : po X).
  Context (f : hsubtype X).

  Definition downward_closure_hsubtype
    : hsubtype X.
  Proof.
    intro y.
    refine (∃ (z : f), P y (pr1carrier _ z)).
  Defined.

  Lemma downward_closure_is_downward_closed
    : is_downward_closed P downward_closure_hsubtype.
  Proof.
    intros y z.
    use (hinhfun _ (pr2 y)).
    intro Hy.
    exists (pr1 Hy).
    refine (istrans_po P _ _ _ (pr2 z) (pr2 Hy)).
  Qed.

  Definition downward_closure
    : downward_closed_subtype P
    := make_downward_closed_subtype P _ downward_closure_is_downward_closed.

End DownwardClosure.
