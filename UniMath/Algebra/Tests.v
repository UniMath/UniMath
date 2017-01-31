Unset Automatic Introduction.

Module Test_assoc.

  Require Import UniMath.Algebra.IteratedBinaryOperations.
  Require Import UniMath.Foundations.NaturalNumbers.

  (* verify that our associativity matches that of the parser, with an extra "1" *)

  Open Scope stn.

  Open Scope multmonoid.

  Goal Π (M:monoid) (f:stn 3 -> M),
         product_seq_mon(3,,f) = 1 * f(●O) * f(●1%nat) * f(●2).
  Proof. reflexivity. Defined.

  Goal Π (M:monoid) (f:stn 3 -> Sequence M),
         prodprod_seq_mon(3,,f) =
            1 * product_seq_mon (f(●0))
              * product_seq_mon (f(●1%nat))
              * product_seq_mon (f(●2)).
  Proof. reflexivity. Defined.

  (* demonstrate that the Coq parser is left-associative with "*" *)
  Goal Π (M:monoid) (x y z:M), x*y*z = (x*y)*z. Proof. reflexivity. Defined.
  Goal Π (M:monoid) (x y z:M), x*y*z = x*(y*z). Proof. apply assocax. Defined.

  (* demonstrate that the Coq parser is left-associative with "+" *)
  Open Scope addmonoid.
  Goal Π (M:monoid) (x y z:M), x+y+z = (x+y)+z. Proof. reflexivity. Defined.
  Goal Π (M:monoid) (x y z:M), x+y+z = x+(y+z). Proof. apply assocax. Defined.

End Test_assoc.

(*
Local Variables:
compile-command: "make -C ../../.. TAGS UniMath/Foundations/Algebra/Tests.vo"
End:
*)
