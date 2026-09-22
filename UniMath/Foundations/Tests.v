Require Export UniMath.Foundations.PartD.

Goal ∑ (_:nat) (_:nat) (_:nat) (_:nat), nat. Proof. exact (2,,3,,4,,5,,6). Defined.
Goal ∏ i j k, i+j+k = (i+j)+k. Proof. intros. apply idpath. Defined.
Goal ∏ n, 1+n = S n. Proof. intros. apply idpath. Defined.
Goal ∏ i j k, i*j*k = (i*j)*k. Proof. intros. apply idpath. Defined.
Goal ∏ n, 0*n = 0. Proof. intros. apply idpath. Defined.
Goal ∏ n, 0+n = n. Proof. intros. apply idpath. Defined.
Goal ∏ n, 0*n = 0. Proof. intros. apply idpath. Defined.
Goal ∏ n m, S n * m = n*m + m. Proof. intros. apply idpath. Defined.
Goal ∏ n, 1*n = n. Proof. intros. apply idpath. Defined.
Goal ∏ n, 4*n = n+n+n+n. Proof. intros. apply idpath. Defined.
Goal ∏ X x, idweq X x = x. Proof. intros. apply idpath. Defined.

Section Test_isweq_iso.
  Let f := idfun nat.
  Let w : nat ≃ nat := weq_iso f f (λ _, idpath _) (λ _, idpath _).
  Goal homotinvweqweq w 3 = idpath _. Proof. apply idpath. Defined.
  Goal homotweqinvweq w 3 = idpath _. Proof. apply idpath. Defined.
  Goal homotweqinvweqweq w 3 = idpath _. Proof. apply idpath. Defined.

  Definition v : bool ≃ bool.
  Proof. simple refine (weq_iso negb negb _ _); intro x; induction x; apply idpath. Defined.
  Goal homotinvweqweq v true = idpath _. Proof. apply idpath. Defined.
  Goal homotweqinvweq v true = idpath _. Proof. apply idpath. Defined.
  Goal homotweqinvweqweq v true = idpath _. Proof. apply idpath. Defined.
End Test_isweq_iso.

Goal ∏ X x, invweq (idweq X) x = x. Proof. intros. apply idpath. Defined.

Section Test_weqtotal2overcoprod.
  Let P (t : bool ⨿ bool) := nat.
  Goal weqtotal2overcoprod P (ii1 true,,3) = ii1 (true,,3). Proof. apply idpath. Defined.
  Goal weqtotal2overcoprod P (ii2 false,,3) = ii2 (false,,3). Proof. apply idpath. Defined.
  Goal invmap (weqtotal2overcoprod P) (ii1 (true,,3)) = ii1 true,,3. Proof. apply idpath. Defined.
  Goal invmap (weqtotal2overcoprod P) (ii2 (false,,3)) = ii2 false,,3. Proof. apply idpath. Defined.
End Test_weqtotal2overcoprod.

Goal weqcoprodf (idweq nat) (idweq nat) (ii1 3) = ii1 3. Proof. apply idpath. Defined.
Goal weqcoprodf (idweq nat) (idweq nat) (ii2 3) = ii2 3. Proof. apply idpath. Defined.
Goal invmap (weqcoprodf (idweq nat) (idweq nat)) (ii1 3) = ii1 3. Proof. apply idpath. Defined.
Goal invmap (weqcoprodf (idweq nat) (idweq nat)) (ii2 3) = ii2 3. Proof. apply idpath. Defined.

Goal bool_to_type true  = unit . Proof. apply idpath. Defined.
Goal bool_to_type false = empty. Proof. apply idpath. Defined.

Goal @weqfibtototal bool _ _ (λ _, idweq bool) (true,,true) = (true,,true).
  Proof. apply idpath. Defined.
Goal invmap (@weqfibtototal bool _ _ (λ _, idweq bool)) (true,,true) = (true,,true).
  Proof. apply idpath. Defined.

Goal @weqfp_map nat nat (idweq _) (λ _,nat) (3,,4) = (3,,4). Proof. apply idpath. Defined.
Goal @weqfp_map _ _ boolascoprod (λ _,nat) (ii1 tt,,4) = (true,,4). Proof. apply idpath. Defined.

Goal @weqfp_invmap nat nat (idweq _) (λ _,nat) (3,,4) = (3,,4). Proof. apply idpath. Defined.
Goal @weqfp_invmap _ _ boolascoprod (λ _,nat) (true,,4) = (ii1 tt,,4). Proof. apply idpath. Defined.

Goal weqfp (idweq nat) (λ _,nat) (3,,4) = (3,,4). Proof. apply idpath. Defined.
Goal invmap (weqfp (idweq nat) (λ _,nat)) (3,,4) = (3,,4). Proof. apply idpath. Defined.

Goal weqtotal2overunit (λ _,nat) (tt,,3) = 3. Proof. apply idpath. Defined.
Goal invmap (weqtotal2overunit (λ _,nat)) 3 = (tt,,3). Proof. apply idpath. Defined.

Goal iscontr = isofhlevel 0. Proof. apply idpath. Defined.
Goal isaset = isofhlevel 2.  Proof. apply idpath. Defined.

Require UniMath.Foundations.Sets.

Module Test_sets.

  Import UniMath.Foundations.Sets.

  Goal ∏ Y (iss:isaset Y) (F:Y->UU) (e :∏ y y', F y -> F y' -> y=y')
         y (f:F y), squash_pairs_to_set F iss e (hinhpr (y,,f)) = y.
  Proof.
    intros. apply idpath.
  Qed.

  Goal ∏ X Y (iss:isaset Y) (f:X->Y) (e:∏ x x', f x = f x'),
         f = funcomp hinhpr (squash_to_set iss f e).
  Proof.
    intros. apply idpath.
  Qed.

End Test_sets.
