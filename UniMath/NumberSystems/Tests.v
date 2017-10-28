Unset Automatic Introduction.

Require UniMath.Foundations.NaturalNumbers.
Require UniMath.MoreFoundations.DecidablePropositions.

Module Test_nat.

  Import UniMath.Foundations.NaturalNumbers.
  Import UniMath.MoreFoundations.DecidablePropositions.

  Local Open Scope nat_scope.

  Goal 3 ≠ 5. easy. Defined.
  Goal ¬ (3 ≠ 3). easy. Defined.

  Module Test_A.
    Let C  := compl nat 0.
    Let C' := compl_ne nat 0 (λ m, 0 ≠ m).
    Let w := compl_ne_weq_compl nat 0 (λ m, 0 ≠ m) : C ≃ C'.
    Let cn : C := (3,,negpaths0sx _).
    Let cn' : C' := (3,,tt).
    Goal w cn = cn'. reflexivity. Defined.
    Goal invmap w cn' = cn. reflexivity. Defined.
    Goal homotinvweqweq w cn = idpath _. try reflexivity. Abort. (* prevented by funextfun *)
    Goal homotweqinvweq w cn' = idpath _. reflexivity. Defined. (* 2 seconds *)
    Let f := weqrecompl nat 0 (isdeceqnat 0).
    Let f' := weqrecompl_ne nat 0 (isdeceqnat 0) (λ m, 0 ≠ m).
    Goal f (ii1 cn) = 3. reflexivity. Defined.
    Goal f' (ii1 cn') = 3. reflexivity. Defined.
    Goal invmap f 3 = (ii1 cn). reflexivity. Defined.
    Goal invmap f' 3 = (ii1 cn'). reflexivity. Defined.
    Goal homotweqinvweq f 3 = idpath _. reflexivity. Defined.
    Goal homotweqinvweq f' 3 = idpath _. reflexivity. Defined.
    Goal homotinvweqweq f (ii1 cn) = idpath _. try reflexivity. Abort. (* prevented by funextfun *)
    Goal homotinvweqweq f' (ii1 cn') = idpath _. reflexivity. Defined. (* succeeds by avoiding funextfun *)
  End Test_A.

  Goal choice (3 < 4)%dnat true false = true. reflexivity. Defined.
  Goal choice (3 < 4 ∧ 4 < 5)%dnat%declog true false = true. reflexivity. Defined.
  Goal choice (¬ (3 < 4))%dnat%declog true false = false. reflexivity. Defined.
  Goal choice (3 < 4 ∨ 4 < 3)%dnat%declog true false = true. reflexivity. Defined.
  Goal choice (4 < 3 ∨ 2 < 1)%dnat%declog true false = false. reflexivity. Defined.

  Goal si 3 (di 3 2) = 2. reflexivity. Defined.
  Goal si 3 (di 3 3) = 3. reflexivity. Defined.
  Goal si 3 (di 3 4) = 4. reflexivity. Defined.

  Goal si 3 2 = 2. reflexivity. Defined.
  Goal si 3 3 = 3. reflexivity. Defined.
  Goal si 3 4 = 3. reflexivity. Defined.
  Goal si 3 5 = 4. reflexivity. Defined.

  Module Test_weqdicompl.

    Let w := weqdicompl 3 : nat ≃ nat_compl 3.
    Goal w 2 = (2,,tt). reflexivity. Defined.
    Goal w 3 = (4,,tt). reflexivity. Defined.
    Goal invmap w (2,,tt) = 2. reflexivity. Defined.
    Goal invmap w (4,,tt) = 3. reflexivity. Defined.
    Goal homotweqinvweq w (2,,tt) = idpath _. reflexivity. Defined.
    Goal homotweqinvweq w (4,,tt) = idpath _. reflexivity. Defined.
    Goal homotinvweqweq w 2 = idpath _. reflexivity. Defined.
    Goal homotinvweqweq w 4 = idpath _. reflexivity. Defined.
    Goal homotweqinvweqweq w 2 = idpath _. reflexivity. Defined.
    Goal homotweqinvweqweq w 4 = idpath _. reflexivity. Defined.

  End Test_weqdicompl.

End Test_nat.

Require UniMath.NumberSystems.Integers.

Module Test_int.

  Import UniMath.NumberSystems.Integers.

  Goal true = (hzbooleq (natnattohz 3 4) (natnattohz 17 18)) . reflexivity. Qed.
  Goal false = (hzbooleq (natnattohz 3 4) (natnattohz 17 19)) . reflexivity. Qed.
  Goal 274 = (hzabsval (natnattohz 58 332)) . reflexivity. Qed.
  Goal O = (hzabsval (hzplus (natnattohz 2 3) (natnattohz 3 2))) . reflexivity. Qed.
  Goal 2 = (hzabsval (hzminus (natnattohz 2 3) (natnattohz 3 2))) . reflexivity. Qed.
  Goal 300 =  (hzabsval (hzmult (natnattohz 20 50) (natnattohz 30 20))) . reflexivity. Qed.

End Test_int.

Require UniMath.NumberSystems.RationalNumbers.

Module Test_rat.

  Import UniMath.NumberSystems.RationalNumbers.

  Open Scope hz_scope .

  Open Scope hq_scope .

  Transparent hz .

  Goal true = ( hqbooleq ( hzhztohq ( natnattohz 4 0 ) ( tpair _ ( natnattohz 3 0 ) ( ct ( hzneq , isdecrelhzneq, ( natnattohz 3 0 ) , 0 %hz ) ) ) )  ( hzhztohq ( natnattohz 13 1 ) ( tpair _ ( natnattohz 11 2 ) ( ct ( hzneq , isdecrelhzneq , ( natnattohz 11 2 ) , 0 %hz ) ) ) ) ) . reflexivity. Qed.

  Goal true = ( decreltobrel hqgthdec ( hzhztohq ( natnattohz 5 0 ) ( tpair _ ( natnattohz 3 0 ) ( ct ( hzneq , isdecrelhzneq , ( natnattohz 3 0 ) , hzzero ) ) ) )  ( hzhztohq ( natnattohz 13 1 ) ( tpair _ ( natnattohz 11 2 ) ( ct ( hzneq , isdecrelhzneq , ( natnattohz 11 2 ) , hzzero ) ) ) ) ) . reflexivity. Qed.

  Goal 4 = ( hzabsval ( intpart ( hqdiv ( hztohq ( nattohz ( 10 ) ) )  ( - ( 1 + 1 + 1 ) ) ) ) ) . reflexivity. Qed.



End Test_rat.
