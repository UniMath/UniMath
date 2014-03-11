Set Primitive Projections.
Set Printing All.
Parameter T : Type.
Parameter P : T -> Type.

Module A.
  Record total2 { T: Type } ( P: T -> Type ) :=
    tpair : forall t : T , forall tp : P t , total2 P .
  Definition pr1 { T: Type } { P : T -> Type } ( tp : total2 P ) : T :=
    match tp with tpair _ t p => t end .
  Definition pr2 { T: Type } { P : T -> Type } ( tp : total2 P ) : P ( pr1 tp ) :=
    match tp as a return P ( pr1 a ) with tpair _ t p => p end .
  Definition X := total2 P.
  Parameter x : X.
  Definition x' : X := tpair _ (pr1 x) (pr2 x).
  Print x'.
  Goal x = x'.                  (* @tpair T P (@pr1 T P x) (@pr2 T P x) -- can be bulky *)
    (* reflexivity. (* fails *) *)
    admit.
  Defined.
End A.

Module B.
  Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.
  Arguments tpair {T} _ _ _.
  Definition X := total2 P.
  Parameter x : X.
  Definition x' : X := tpair _ (pr1 x) (pr2 x).
  Print x'.                     (* @tpair T P (pr1 x) (pr2 x)   ! *)
  Goal x = x'.
    reflexivity.                (* ! *)
  Defined.
End B.

(*
  Local Variables:
  coq-prog-name: "~/local/encap/coq-polyproj/bin/coqtop"
  End:
*)