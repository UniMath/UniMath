Unset Automatic Introduction.

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
  Goal ∏ (M:monoid) (x y z:M), x+y+z = (x+y)+z. Proof. reflexivity. Defined.
  Goal ∏ (M:monoid) (x y z:M), x+y+z = x+(y+z). Proof. apply assocax. Defined.

End Test_assoc.

Module Test_finsum.

  Import UniMath.Algebra.IteratedBinaryOperations.
  Import UniMath.Combinatorics.FiniteSets.

  Goal ∏ X (fin : finstruct X) (f : X -> nat),
    finsum (hinhpr fin) f = stnsum (f ∘ pr1weq (pr2 fin)).
  Proof.
    intros.
    intermediate_path (iterop_fun_mon (M := nat_add_abmonoid) (f ∘ pr1weq (pr2 fin))).
    - reflexivity.
    - apply iterop_fun_nat.
  Qed.

  Goal 15 = finsum (isfinitestn _) (λ i:stn 6, i). reflexivity. Qed.
  Goal 20 = finsum isfinitebool (λ i:bool, 10). reflexivity. Qed.
  Goal 21 = finsum (isfinitecoprod isfinitebool isfinitebool)
                   (coprod_rect (λ _, nat) (bool_rect _ 10 4) (bool_rect _  6 1)).
    reflexivity.            (* fixed *)
  Qed.

  Goal 10 = finsum' (isfinitestn _) (λ i:stn 5, i). reflexivity. Defined. (* fixed! *)
  Goal 20 = finsum' isfinitebool (λ i:bool, 10). reflexivity. Qed.
  Goal 21 = finsum' (isfinitecoprod isfinitebool isfinitebool)
                   (coprod_rect (λ _, nat) (bool_rect _ 10 4) (bool_rect _  6 1)).
    try reflexivity.            (* fails, for some reason *)
  Abort.

  Section Iteration.
    Local Notation "s □ x" := (append s x) (at level 64, left associativity).
    Context (G:abgr) (R:rng) (S:commrng) (g g' g'':G) (r r' r'':R) (s s' s'':S).
    Local Open Scope multmonoid.
    Goal iterop_unoseq_abgr (nil : Sequence G) = 1. reflexivity. Qed.
    Goal iterop_unoseq_abgr (nil □ g □ g') = g*g'. reflexivity. Qed.
    Goal iterop_unoseq_abgr (nil □ g □ g' □ g'') = g*g'*g''. reflexivity. Qed.
    Goal iterop_unoseq_unoseq_mon (M:=G) (sequenceToUnorderedSequence(nil □ sequenceToUnorderedSequence(nil □ g □ g') □ sequenceToUnorderedSequence(nil □ g □ g' □ g''))) = (g*g') * (g*g'*g''). reflexivity. Qed.
    Goal iterop_unoseq_unoseq_mon (M:=G) (sequenceToUnorderedSequence(nil □ sequenceToUnorderedSequence(nil □ g) □ sequenceToUnorderedSequence(nil))) = g * 1. reflexivity. Qed.
    Goal iterop_unoseq_unoseq_mon (M:=G) (sequenceToUnorderedSequence(nil □ sequenceToUnorderedSequence(nil) □ sequenceToUnorderedSequence(nil □ g))) = 1 * g. reflexivity. Qed.
    Close Scope multmonoid.

    Local Open Scope rng.
    Goal sum_unoseq_rng (nil : Sequence R) = 0. reflexivity. Qed.
    Goal sum_unoseq_rng (nil □ r □ r') = r+r'. reflexivity. Qed.
    Goal sum_unoseq_rng (nil □ r □ r' □ r'') = r+r'+r''. reflexivity. Qed.
    Goal product_unoseq_rng (nil : Sequence S) = 1. reflexivity. Qed.
    Goal product_unoseq_rng (nil □ s □ s') = s*s'. reflexivity. Qed.
    Goal product_unoseq_rng (nil □ s □ s' □ s'') = s*s'*s''. reflexivity. Qed.
  End Iteration.

End Test_finsum.

(*
Local Variables:
compile-command: "make -C ../../.. TAGS UniMath/Foundations/Algebra/Tests.vo"
End:
*)
