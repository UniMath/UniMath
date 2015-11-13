
Parameter X:Type.
Goal forall x:Empty_set, X.
      intro x.
      induction x.
Defined.

(*
Empty_set_rect : forall (P : Empty_set -> Type) (e : Empty_set), P e
*)

Goal forall x:Empty_set, X.
       apply Empty_set_rect.
Defined.

Goal forall (a b:X), bool -> X.
Proof.
  intros a b.
  now apply bool_rect.
Defined.

\