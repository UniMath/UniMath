Unset Automatic Introduction.

Module Test_assoc.

  Require Import UniMath.Algebra.IteratedBinaryOperations.
  Require Import UniMath.Foundations.NaturalNumbers.

  (* verify that our associativity matches that of the parser, without an extra "1" *)

  Local Notation "[]" := Lists.nil (at level 0, format "[]").
  Local Infix "::" := cons.

  Section Test.
    Context (X:UU) (e:X) (op:binop X) (w x y z:X).
    Goal product_list e op [] = e. reflexivity. Qed.
    Goal product_list e op (x::[]) = x. reflexivity. Qed.
    Goal product_list e op (x::y::[]) = op x y. reflexivity. Qed.
    Goal product_list e op (w::x::y::z::[]) = op w (op x (op y z)). reflexivity. Qed.
  End Test.

  Open Scope stn.

  Open Scope multmonoid.

  Goal ∏ (M:monoid) (f:stn 3 -> M),
         product_seq_mon(3,,f) = f(●O) * f(●1%nat) * f(●2).
  Proof. reflexivity. Defined.

  Goal ∏ (M:monoid) (f:stn 3 -> Sequence M),
         prodprod_seq_mon(3,,f) =
                product_seq_mon (f(●0))
              * product_seq_mon (f(●1%nat))
              * product_seq_mon (f(●2)).
  Proof. reflexivity. Defined.

  (* demonstrate that the Coq parser is left-associative with "*" *)
  Goal ∏ (M:monoid) (x y z:M), x*y*z = (x*y)*z. Proof. reflexivity. Defined.
  Goal ∏ (M:monoid) (x y z:M), x*y*z = x*(y*z). Proof. apply assocax. Defined.

  (* demonstrate that the Coq parser is left-associative with "+" *)
  Open Scope addmonoid.
  Goal ∏ (M:monoid) (x y z:M), x+y+z = (x+y)+z. Proof. reflexivity. Defined.
  Goal ∏ (M:monoid) (x y z:M), x+y+z = x+(y+z). Proof. apply assocax. Defined.

End Test_assoc.

(*
Local Variables:
compile-command: "make -C ../../.. TAGS UniMath/Foundations/Algebra/Tests.vo"
End:
*)
