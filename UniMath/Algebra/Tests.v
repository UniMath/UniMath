Require UniMath.Algebra.IteratedBinaryOperations.
Require UniMath.Foundations.NaturalNumbers.
Require UniMath.Algebra.IteratedBinaryOperations.
Require UniMath.Combinatorics.FiniteSets.

Module Test_assoc.

  Import UniMath.Algebra.IteratedBinaryOperations.
  Import UniMath.Foundations.NaturalNumbers.

  (* verify that our associativity matches that of the parser, without an extra "1" *)

  Local Notation "[]" := Lists.nil (at level 0, format "[]").
  Local Infix "::" := cons.

  Section Test.
    Context (X:UU) (e:X) (op:binop X) (w x y z:X).
    Goal iterop_list e op [] = e. reflexivity. Qed.
    Goal iterop_list e op (x::[]) = x. reflexivity. Qed.
    Goal iterop_list e op (x::y::[]) = op x y. reflexivity. Qed.
    Goal iterop_list e op (w::x::y::z::[]) = op w (op x (op y z)). reflexivity. Qed.
  End Test.

  Local Open Scope stn.

  Open Scope multmonoid.

  Goal ∏ (M:monoid) (f:stn 3 -> M),
         iterop_seq_mon(3,,f) = f(●O) * f(●1%nat) * f(●2).
  Proof. reflexivity. Defined.

  Goal ∏ (M:monoid) (f:stn 3 -> Sequence M),
         iterop_seq_seq_mon(3,,f) =
                iterop_seq_mon (f(●0))
              * iterop_seq_mon (f(●1%nat))
              * iterop_seq_mon (f(●2)).
  Proof. reflexivity. Defined.

  (* demonstrate that the Coq parser is left-associative with "*" *)
  Goal ∏ (M:monoid) (x y z:M), x*y*z = (x*y)*z. Proof. reflexivity. Defined.
  Goal ∏ (M:monoid) (x y z:M), x*y*z = x*(y*z). Proof. apply assocax. Defined.

  (* demonstrate that the Coq parser is left-associative with "+" *)
  Local Open Scope addmonoid.
  Import UniMath.Algebra.Monoids_and_Groups.AddNotation.
  Goal ∏ (M:monoid) (x y z:M), x+y+z = (x+y)+z. Proof. reflexivity. Defined.
  Goal ∏ (M:monoid) (x y z:M), x+y+z = x+(y+z). Proof. apply assocax. Defined.

End Test_assoc.
(*
Local Variables:
compile-command: "make -C ../../.. TAGS UniMath/Foundations/Algebra/Tests.vo"
End:
*)
