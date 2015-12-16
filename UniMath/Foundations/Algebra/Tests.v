Unset Automatic Introduction.

Module Test_assoc.

  Require Import UniMath.Foundations.Algebra.IteratedBinaryOperations.
  Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

  (* verify that our associativity matches that of the parser, with an extra "1" *)

  Open Scope stn.

  Open Scope multmonoid.

  Goal ∀ (M:monoid) (f:stn 3 -> M),
         sequenceProduct(3,,f) = 1 * f(●O) * f(●1%nat) * f(●2).
  Proof. reflexivity. Defined.

  Goal ∀ (M:monoid) (f:stn 3 -> Sequence M),
         doubleProduct(3,,f) =
            1 * sequenceProduct (f(●0))
              * sequenceProduct (f(●1%nat))
              * sequenceProduct (f(●2)).
  Proof. reflexivity. Defined.

End Test_assoc.

(*
Local Variables:
compile-command: "make -C ../../.. TAGS UniMath/Foundations/Algebra/Tests.vo"
End:
*)
