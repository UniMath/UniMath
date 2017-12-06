Unset Automatic Introduction.
Require Export UniMath.Foundations.PartD.

Goal ∑ (_:nat) (_:nat) (_:nat) (_:nat), nat. exact (2,,3,,4,,5,,6). Defined.
Goal ∏ i j k, i+j+k = (i+j)+k. intros. apply idpath. Defined.
Goal ∏ n, 1+n = S n. intros. apply idpath. Defined.
Goal ∏ i j k, i*j*k = (i*j)*k. intros. apply idpath. Defined.
Goal ∏ n, 0*n = 0. intros. apply idpath. Defined.
Goal ∏ n, 0+n = n. intros. apply idpath. Defined.
Goal ∏ n, 0*n = 0. intros. apply idpath. Defined.
Goal ∏ n m, S n * m = n*m + m. intros. apply idpath. Defined.
Goal ∏ n, 1*n = n. intros. apply idpath. Defined.
Goal ∏ n, 4*n = n+n+n+n. intros. apply idpath. Defined.
Goal ∏ X x, idweq X x = x. intros. apply idpath. Defined.

Module Test_gradth.
  Let f := idfun nat.
  Definition w : nat ≃ nat := weqgradth f f (λ _, idpath _) (λ _, idpath _).
  Goal homotinvweqweq w 3 = idpath _. apply idpath. Defined.
  Goal homotweqinvweq w 3 = idpath _. apply idpath. Defined.
  Goal homotweqinvweqweq w 3 = idpath _. apply idpath. Defined.

  Definition v : bool ≃ bool.
    simple refine (weqgradth negb negb _ _); intro x; induction x; apply idpath. Defined.
  Goal homotinvweqweq v true = idpath _. apply idpath. Defined.
  Goal homotweqinvweq v true = idpath _. apply idpath. Defined.
  Goal homotweqinvweqweq v true = idpath _. apply idpath. Defined.
End Test_gradth.

Goal ∏ X x, invweq (idweq X) x = x. intros. apply idpath. Defined.

Module Test_weqtotal2overcoprod.
  Let P (t : bool ⨿ bool) := nat.
  Goal weqtotal2overcoprod P (ii1 true,,3) = ii1 (true,,3). apply idpath. Defined.
  Goal weqtotal2overcoprod P (ii2 false,,3) = ii2 (false,,3). apply idpath. Defined.
  Goal invmap (weqtotal2overcoprod P) (ii1 (true,,3)) = ii1 true,,3. apply idpath. Defined.
  Goal invmap (weqtotal2overcoprod P) (ii2 (false,,3)) = ii2 false,,3. apply idpath. Defined.
End Test_weqtotal2overcoprod.

Goal weqcoprodf (idweq nat) (idweq nat) (ii1 3) = ii1 3. apply idpath. Defined.
Goal weqcoprodf (idweq nat) (idweq nat) (ii2 3) = ii2 3. apply idpath. Defined.
Goal invmap (weqcoprodf (idweq nat) (idweq nat)) (ii1 3) = ii1 3. apply idpath. Defined.
Goal invmap (weqcoprodf (idweq nat) (idweq nat)) (ii2 3) = ii2 3. apply idpath. Defined.

Goal bool_to_type true  = unit . apply idpath. Defined.
Goal bool_to_type false = empty. apply idpath. Defined.

Goal @weqfibtototal bool _ _ (λ _, idweq bool) (true,,true) = (true,,true).
  apply idpath. Defined.
Goal invmap (@weqfibtototal bool _ _ (λ _, idweq bool)) (true,,true) = (true,,true).
  apply idpath. Defined.

Goal @weqfp_map nat nat (idweq _) (λ _,nat) (3,,4) = (3,,4). apply idpath. Defined.
Goal @weqfp_map _ _ boolascoprod (λ _,nat) (ii1 tt,,4) = (true,,4). apply idpath. Defined.

Goal @weqfp_invmap nat nat (idweq _) (λ _,nat) (3,,4) = (3,,4). apply idpath. Defined.
Goal @weqfp_invmap _ _ boolascoprod (λ _,nat) (true,,4) = (ii1 tt,,4). apply idpath. Defined.

Goal weqfp (idweq nat) (λ _,nat) (3,,4) = (3,,4). apply idpath. Defined.
Goal invmap (weqfp (idweq nat) (λ _,nat)) (3,,4) = (3,,4). apply idpath. Defined.

Goal weqtotal2overunit (λ _,nat) (tt,,3) = 3. apply idpath. Defined.
Goal invmap (weqtotal2overunit (λ _,nat)) 3 = (tt,,3). apply idpath. Defined.

Goal iscontr = isofhlevel 0. apply idpath. Defined.
Goal isaset = isofhlevel 2.  apply idpath. Defined.

Require UniMath.Foundations.Sets.

Module Test_sets.

  Import UniMath.Foundations.Sets.

  Goal ∏ Y (is:isaset Y) (F:Y->UU) (e :∏ y y', F y -> F y' -> y=y')
         y (f:F y), squash_pairs_to_set F is e (hinhpr (y,,f)) = y.
  Proof.
    intros. apply idpath.
  Qed.

  Goal ∏ X Y (is:isaset Y) (f:X->Y) (e:∏ x x', f x = f x'),
         f = funcomp hinhpr (squash_to_set is f e).
  Proof.
    intros. apply idpath.
  Qed.

End Test_sets.
