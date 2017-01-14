Unset Automatic Introduction.

Module Test_assoc.

  Require Import UniMath.Algebra.IteratedBinaryOperations.
  Require Import UniMath.Foundations.NaturalNumbers.

  (* verify that our associativity matches that of the parser, with an extra "1" *)

  Open Scope stn.

  Open Scope multmonoid.

  Goal Π (M:monoid) (f:stn 3 -> M),
         sequenceProduct(3,,f) = 1 * f(●O) * f(●1%nat) * f(●2).
  Proof. reflexivity. Defined.

  Goal Π (M:monoid) (f:stn 3 -> Sequence M),
         doubleProduct(3,,f) =
            1 * sequenceProduct (f(●0))
              * sequenceProduct (f(●1%nat))
              * sequenceProduct (f(●2)).
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
