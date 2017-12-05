Unset Automatic Introduction.

Require UniMath.Combinatorics.Lists.
Require UniMath.Combinatorics.StandardFiniteSets.
Require UniMath.Combinatorics.FiniteSets.
Require UniMath.Combinatorics.FiniteSequences.
Require UniMath.Combinatorics.FiniteSets.
Require UniMath.Combinatorics.OrderedSets.
Require UniMath.Combinatorics.StandardFiniteSets.
Require UniMath.Combinatorics.BoundedSearch.
Require UniMath.MoreFoundations.DecidablePropositions.

Module Test_list.

  Import UniMath.Combinatorics.Lists.

  Local Notation "[]" := nil (at level 0, format "[]").
  Local Infix "::" := cons.

  Goal concatenate (1::2::[]) (3::4::5::[]) = (1::2::3::4::5::[]).
    reflexivity.
  Defined.

  Goal flatten ((1::2::[])::(3::4::5::[])::(6::[])::[]) = (1::2::3::4::5::6::[]).
    reflexivity.
  Defined.

End Test_list.

Module Test_stn.

  Import UniMath.Combinatorics.StandardFiniteSets.

  Local Open Scope stn.

  Goal stn 6. exact (stnel(6,3)). Qed.
  Goal stn 6. exact (stnpr 3). Qed.


  Goal (stnel(6,3) ≠ stnel(6,4)). easy. Defined.
  Goal ¬(stnel(6,3) ≠ stnel(6,3)). easy. Defined.

  Goal ∏ m n (i:m≤n) (j:stn m), pr1 (stnmtostnn m n i j) = pr1 j.
    intros. induction j as [j J]. reflexivity.
  Defined.

  Goal @sni 6 (●3) (@dni 6 (●3) (●2)) = ●2. reflexivity. Defined.
  Goal @sni 6 (●3) (@dni 6 (●3) (●3)) = ●3. reflexivity. Defined.
  Goal @sni 6 (●3) (@dni 6 (●3) (●4)) = ●4. reflexivity. Defined.


  Goal @sni 6 (●3) (●2) = ●2. reflexivity. Defined.
  Goal @sni 6 (●3) (●3) = ●3. reflexivity. Defined.
  Goal @sni 6 (●3) (●4) = ●3. reflexivity. Defined.
  Goal @sni 6 (●3) (●5) = ●4. reflexivity. Defined.

  Module Test_weqdnicompl.

    Let n := 5.
    Let X := stn n.
    Let i := ●3 : stn (S n).
    Let Y := @stn_compl (S n) i.
    Let v := weqdnicompl i : X ≃ Y.
    Let j := ●4 : X.
    Let jni := ●5,,tt : Y.

    Goal v j = jni. reflexivity. Defined.
    Goal invmap v jni = j. reflexivity. Defined.
    Goal homotweqinvweq v jni = idpath _. reflexivity. Defined.
    Goal homotinvweqweq v j = idpath _.
      reflexivity.                (* fixed; 2 seconds *)
    Defined.                      (* fixed, 2 seconds *)
    Goal homotweqinvweqweq v j = idpath _. (* 2 seconds *)
      reflexivity.                         (* 2 seconds *)
    Defined.                               (* 3 seconds *)

  End Test_weqdnicompl.

  Module Test2.
    Goal weqdnicoprod 4 firstelement (ii1 (●0)) = ●1. reflexivity. Defined.
    Goal weqdnicoprod 4 firstelement (ii1 (●3)) = ●4. reflexivity. Defined.
    Goal invmap (weqdnicoprod 4 firstelement) (●1) = (ii1 (●0)). reflexivity. Defined.
    Goal invmap (weqdnicoprod 4 firstelement) (●4) = (ii1 (●3)). reflexivity. Defined.
    Goal weqdnicoprod 4 lastelement (ii1 (●3)) = ●3. reflexivity. Defined.
    Goal weqdnicoprod 4 lastelement (ii2 tt) = ●4. reflexivity. Defined.
    Goal invmap (weqdnicoprod 4 lastelement) (●1) = (ii1 (●1)). reflexivity. Defined.
    Goal invmap (weqdnicoprod 4 lastelement) (●4) = (ii2 tt). reflexivity. Defined.
    Goal homotweqinvweq (weqdnicoprod 4 lastelement) (● 0) = idpath _. reflexivity. Defined. (* fixed! *)
    Goal homotinvweqweq (weqdnicoprod 4 (●4)) (ii2 tt) = idpath _. reflexivity. Defined.
    Goal homotinvweqweq (weqdnicoprod 4 (●4)) (ii1 (●1)) = idpath _.
      reflexivity.                (* fixed; 5 seconds *)
    Defined.                      (* 5 seconds *)

    (* here's an example that shows complications need not impede that sort of computability: *)
    Local Definition w : unit ≃ stn 1.
      simple refine (weqgradth _ _ _ _).
      { intro. exact firstelement. }
      { intro. exact tt. }
      { intro u. simpl. induction u. reflexivity. }
      { intro i. simpl. apply subtypeEquality_prop.
        simpl. induction i as [i I]. simpl. apply pathsinv0. apply natlth1tois0. exact I. }
    Defined.
    Goal w tt = firstelement. reflexivity. Defined.
    Goal invmap w firstelement = tt. reflexivity. Defined.
    Goal homotweqinvweq w firstelement = idpath _. reflexivity. Defined.
    Goal homotinvweqweq w tt = idpath _. reflexivity. Defined.

    Local Definition w' := invweq w.
    Goal w' firstelement = tt. reflexivity. Defined.
    Goal invmap w' tt= firstelement. reflexivity. Defined.
    Goal homotweqinvweq w' tt = idpath _. reflexivity. Defined.
    Goal homotinvweqweq w' firstelement = idpath _. reflexivity. Defined.

    Definition ww' := weqcomp w w'.
    Goal ww' tt = tt. reflexivity. Defined.
    Goal invmap ww' tt = tt. reflexivity. Defined.
    Goal homotweqinvweq ww' tt = idpath _. reflexivity. Defined.
    Goal homotinvweqweq ww' tt = idpath _. reflexivity. Defined.

    Definition w_w := weqcoprodf w w.
    Goal w_w (ii1 tt) = ii1 firstelement. reflexivity. Defined.
    Goal invmap w_w (ii2 firstelement) = ii2 tt. reflexivity. Defined.
    Goal homotweqinvweq w_w (ii2 firstelement) = idpath _. reflexivity. Defined.
    Goal homotinvweqweq w_w (ii1 tt) = idpath _. reflexivity. Defined.

    Definition i := ●1 : stn 4.
    Definition j := ●0 : stn 4.
    Lemma ne : ¬ (i = j).
    Proof. apply stnneq_to_nopath. easy. Defined.
    Definition re := weqrecompl (stn 4) i (isisolatedinstn _).
    Definition re' := weqrecompl_ne (stn 4) i (isisolatedinstn i) (stnneq i).
    Definition c := complpair (stn 4) i j ne : compl _ i.
    Definition c' := compl_ne_pair (stn 4) i (stnneq i) j tt : stn_compl i.
    Goal re (ii2 tt) = i. reflexivity. Defined.
    Goal re (ii1 c) = j. reflexivity. Defined.
    Goal invmap re i = (ii2 tt). reflexivity. Defined.
    Goal invmap re j = (ii1 c). reflexivity. Defined.
    Goal homotweqinvweq re i = idpath _. reflexivity. Defined.
    Goal homotweqinvweq re j = idpath _. reflexivity. Defined.
    Goal homotinvweqweq re (ii2 tt) = idpath _. reflexivity. Defined.
    Goal homotinvweqweq re (ii1 c) = idpath _.
      try reflexivity.
      (* quickly returns due to the use of funextemptyAxiom in the proof of isweqrecompl. *)
    Abort.

    Goal re' (ii2 tt) = i. reflexivity. Defined.
    Goal re' (ii1 c') = j. reflexivity. Defined.
    Goal invmap re' i = (ii2 tt). reflexivity. Defined.
    Goal invmap re' j = (ii1 c'). reflexivity. Defined.
    Goal homotweqinvweq re' i = idpath _. reflexivity. Defined.
    Goal homotweqinvweq re' j = idpath _. reflexivity. Defined.
    Goal homotinvweqweq re' (ii2 tt) = idpath _. reflexivity. Defined.
    Goal homotinvweqweq re' (ii1 c') = idpath _. reflexivity. Defined. (* fixed! *)


    Goal @weqdnicoprod_map 4 (●2) (ii2 tt) = (●2). reflexivity. Defined.
    Goal @weqdnicoprod_map 4 (●2) (ii1 (●2)) = (●3). reflexivity. Defined.
    Goal @weqdnicoprod_map 4 (●2) (ii1 (●1)) = (●1). reflexivity. Defined.
    Goal @weqdnicoprod_invmap 4 (●2) (●2) = (ii2 tt). reflexivity. Defined.
    Goal @weqdnicoprod_invmap 4 (●2) (●3) = (ii1 (●2)). reflexivity. Defined.
    Goal @weqdnicoprod_invmap 4 (●2) (●1) = (ii1 (●1)). reflexivity. Defined.



  End Test2.

  (* confirm that [stnsum] is associative in the same way as the parser, which is left associative *)
  Goal ∏ (f : stn 3 -> nat), stnsum f =  f(●0) + f(●1)  +  f(●2). reflexivity. Defined.
  Goal ∏ (f : stn 3 -> nat), stnsum f = (f(●0) + f(●1)) +  f(●2). reflexivity. Defined.

  Module Test_weqstnsum.
    (* this module exports nothing *)
    Let X := stnset 7.
    Let Y (x:X) := stnset (pr1 x).
    Let W := ∑ x, Y x.
    Let f : W ≃ stn _ := weqstnsum1 _.
    Let f' : stn _ ≃ W := invweq f.
    Goal f(●1,,●0) = ●0. reflexivity. Defined. (* fixed! (formerly, it failed quickly) *)
    Goal f(●2,,●0) = ●1. reflexivity. Defined.
    Goal f(●2,,●1) = ●2. reflexivity. Defined.
    Goal f(●3,,●0) = ●3. reflexivity. Defined.
    Goal f(●3,,●1) = ●4. reflexivity. Defined.
    Goal f(●3,,●2) = ●5. reflexivity. Defined.
    Goal f(●4,,●0) = ●6. reflexivity. Defined.
    Goal f(●5,,●0) = ●10. reflexivity. Defined.
    Goal f(●6,,●0) = ●15. reflexivity. Defined.

    Goal (pr2 (pr2 (f'(●0)))) = idpath true. reflexivity. Defined. (* fixed, Coq bug? *)
    Goal f'(●0) = (●1,,●0). reflexivity. Defined. (* fixed, Coq bug? *)
    Goal f'(●0) = (●1,,●0). reflexivity. Defined.
    Goal f'(●1) = (●2,,●0). reflexivity. Defined.
    Goal f'(●2) = (●2,,●1). reflexivity. Defined.
    Goal f'(●3) = (●3,,●0). reflexivity. Defined.
    Goal f'(●4) = (●3,,●1). reflexivity. Defined.
    Goal f'(●5) = (●3,,●2). reflexivity. Defined.
    Goal f'(●6) = (●4,,●0). reflexivity. Defined.
    Goal f'(●10) = (●5,,●0). reflexivity. Defined.
    Goal f'(●15) = (●6,,●0). reflexivity. Defined.

  End Test_weqstnsum.

  Module Test_weqfromprodofstn.
    (* verify computability in both directions *)
    (* this module exports nothing *)
    Let f : stn 5 × stn 4 ≃ stn 20 := weqfromprodofstn 5 4.
    Goal f(●0,,●0) = ●0. reflexivity. Defined.
    Goal f(●0,,●1) = ●1. reflexivity. Defined.
    Goal f(●2,,●0) = ●8. reflexivity. Defined.
    Goal f(●4,,●3) = ●19. reflexivity. Defined.
    Let f' := invweq f.
    Goal f'(●19) = (●4,,●3). reflexivity. Defined.
    Goal f'(●18) = (●4,,●2). reflexivity. Defined.
    Goal f'(●14) = (●3,,●2). reflexivity. Defined.
  End Test_weqfromprodofstn.

  (* confirm that [stnprod] is associative in the same way as the parser *)
  Goal ∏ (f : stn 3 -> nat), stnprod f = f(●0) * f(●1) * f(●2).
  Proof. reflexivity. Defined.


  Local Definition testfun : stn 3 -> stn 10.
    Proof.
      intros n.
      induction n as [n b].
      induction n as [|n].
      - exact (2,,idpath _).
      - induction n as [|n].
        + exact (3,,idpath _).
        + induction n as [|n].
          * exact (4,,idpath _).
          * contradicts (negnatlthn0 n) b.
    Defined.

  Goal ∏ n, testfun n < 5.
    Proof.
      intros.
      induction n as [i c].
      inductive_reflexivity i c.
    Defined.


End Test_stn.

Module Test_fin.

  Import UniMath.Combinatorics.FiniteSets.

  (** ** Test computations. *)
  Goal fincard (isfiniteempty) = 0. reflexivity. Qed.
  Goal fincard (isfiniteunit) = 1. reflexivity. Qed.
  Goal fincard (isfinitebool) = 2. reflexivity. Qed.
  Goal fincard (isfinitecompl true isfinitebool) = 1. reflexivity. Qed.
  Goal fincard (isfinitedirprod  isfinitebool isfinitebool) = 4. reflexivity. Qed.
  Goal fincard (isfinitedirprod  isfinitebool (isfinitedirprod  isfinitebool isfinitebool)) = 8. reflexivity. Qed.
  Goal cardinalityFiniteSet (isfinite_to_FiniteSet (isfinitedirprod  isfinitebool (isfinitedirprod  isfinitebool isfinitebool))) = 8. reflexivity. Qed.
  Goal fincard (isfinitecompl (ii1 tt) (isfinitecoprod  (isfiniteunit) (isfinitebool))) = 2. reflexivity. Qed.
  Goal fincard (isfinitecompl (ii1 tt) (isfinitecoprod (isfiniteunit) (isfinitebool))) = 2. reflexivity. Qed.
  Goal fincard (isfinitecompl (dirprodpair tt tt) (isfinitedirprod  isfiniteunit isfiniteunit)) = 0. reflexivity. Qed.
  Goal fincard (isfinitecompl (dirprodpair  true (dirprodpair  true false)) (isfinitedirprod  (isfinitebool) (isfinitedirprod  (isfinitebool) (isfinitebool)))) = 7. reflexivity. Qed.

  Goal fincard (
         isfiniteweq (isfinitedirprod isfinitebool isfinitebool)
       ) = 24. reflexivity. Qed.

  (*

  stack overflow:

  Goal fincard (isfiniteweq ( isfinitedirprod ( isfinitedirprod isfinitebool isfinitebool ) isfinitebool )) = 40320. reflexivity. Qed.

  *)

  (* Eval compute in (carddneg _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O)))))). *)
  (* Eval lazy in   (pr1 (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))). *)

  Module Test_isfinite_isdeceq.

    (* This module exports nothing. *)

    Import UniMath.MoreFoundations.DecidablePropositions.

    (* The proofs of isfinite_isdeceq and isfinite_isaset depend on funextfun
       and funextemptyAxiom, so here we do an experiment to see if that impedes
       computability of equality using it. *)

    Local Open Scope stn.

    Let X := stnset 5.
    Let finX : isfinite X := isfinitestn _.
    Let eqX := isfinite_to_DecidableEquality finX.
    Let x := ●3 : X.
    Let x' := ●4 : X.
    Let decide P := choice P true false.
    Goal decide (eqX x x') = false. reflexivity. Defined.
    Goal decide (eqX x x) = true. reflexivity. Defined.

    (* test isfinitebool *)

    Let eqbool := isfinite_to_DecidableEquality isfinitebool : DecidableRelation bool.
    Goal decide (eqbool true true) = true. reflexivity. Defined.
    Goal decide (eqbool false true) = false. reflexivity. Defined.

    (* test isfinitecoprod *)

    Let C := X ⨿ X.
    Let eqQ : DecidableRelation C :=
      isfinite_to_DecidableEquality (isfinitecoprod finX finX).
    Let c := ii1 x : C.
    Let c' := ii1 x' : C.
    Let c'' := ii2 x : C.
    Goal decide (eqQ c c') = false. reflexivity. Defined.
    Goal decide (eqQ c c) = true. reflexivity. Defined.
    Goal decide (eqQ c c'') = false. reflexivity. Defined.

    (* test isfinitedirprod *)
    Let Y := stnset 4.
    Let y := ●1 : Y.
    Let y' := ●2 : Y.
    Let finY : isfinite Y := isfinitestn _.
    Let V := X × Y.
    Let eqV := isfinite_to_DecidableEquality (isfinitedirprod finX finY).
    Goal decide (eqV (x,,y) (x',,y')) = false. reflexivity. Defined.

    (* test isfinitetotal2 *)

    Let Y' (x:X) : hSet := Y.
    Let W := ∑ x, Y' x.
    Let eqW : DecidableRelation W :=
      isfinite_to_DecidableEquality (isfinitetotal2 Y' finX (λ _, finY)).
    Goal decide (eqW (x,,y) (x',,y')) = false.
      reflexivity. (* fixed *)
    Defined.

    (* test isfiniteforall *)
    Let T := ∏ x, Y' x.
    Let eqT : DecidableRelation T :=
      isfinite_to_DecidableEquality (isfiniteforall Y' finX (λ _, finY)).
    Goal decide (eqT (λ _, y) (λ _, y)) = true.
      reflexivity. (* fixed *)
    Defined.

  End Test_isfinite_isdeceq.

End Test_fin.

Module Test_seq.

  Import UniMath.Combinatorics.FiniteSequences.

  Local Open Scope stn.

End Test_seq.

Module Test_finite_sets.
  Import UniMath.Combinatorics.FiniteSets.
  Import UniMath.MoreFoundations.DecidablePropositions.

  Local Open Scope stn.

  Goal 3 = fincard_standardSubset (λ i:stn 10, 2*i < 6)%dnat. Proof. reflexivity. Defined.

  Goal 6 = tallyStandardSubset (λ i:stn 10, 3 ≤ i ∧ i ≤ 8)%dnat%declog. Proof. reflexivity. Defined.

  Goal 6 = tallyStandardSubsetSegment (λ i:stn 14, 2*i ≠ 4)%dnat (●7). Proof. reflexivity. Defined.

End Test_finite_sets.

Module Test_ord.

  Import UniMath.Combinatorics.OrderedSets.
  Import UniMath.Combinatorics.StandardFiniteSets.
  Import UniMath.MoreFoundations.DecidablePropositions.

  Local Open Scope stn.

  Goal 3 = height ( ●3 : ⟦ 8 ⟧ %foset ). reflexivity. Defined.

  Module TestLex.
    (* we want lex order to be computable if R and S both are *)
    Let X := stnset 5.
    Let R := λ (x x':X), (pr1 x ≤ pr1 x')%dnat.
    Let Y := λ x:X, stnset (pr1 x).
    Let S := λ (x:X) (y y':Y x), (pr1 y ≤ pr1 y')%dnat.
    Let Z := ∑ x, Y x.
    Let T := lexicographicOrder X Y R S.

    Let x2 := ●2 : X.
    Let x3 := ●3 : X.

    Goal (choice (R x2 x3) true false = true). reflexivity. Defined.
    Goal (choice (R x2 x2) true false = true). reflexivity. Defined.
    Goal (choice (R x3 x2) true false = false). reflexivity. Defined.

    Let y1 := ●1 : Y x2.
    Let y2 := ●2 : Y x3.
    Let t  := (x2,,y1) : Z.
    Let t' := (x3,,y2) : Z.

  End TestLex.

  Module TestLex2.

    Import UniMath.MoreFoundations.DecidablePropositions.

    Open Scope foset.

    Let i := ●2 : ⟦ 4 ⟧.
    Let j := ●3 : ⟦ 4 ⟧.

    Goal choice (i < j)%foset true false = true. reflexivity. Defined.
    Goal choice (i ≤ j)%foset true false = true. reflexivity. Defined.
    Goal choice (i ≐ j)%foset true false = false. reflexivity. Defined.

    Let X := (∑ i:⟦ 4 ⟧, ⟦ pr1 i ⟧)%foset.
    Let x := ( ●2 ,, ●1 ):X.
    Let y := ( ●3 ,, ●1 ):X.

    Lemma d : isdeceq X.
    Proof.
      apply isdeceq_total2.
      - apply isdeceqstn.
      - intro i. apply isdeceqstn.
    Defined.

    Definition which {X} : X ⨿ ¬X -> bool.
    Proof.
      intros X c.
      induction c.
      - exact true.
      - exact false.
    Defined.

    (* we want these to work: *)

    Goal choice (x < y) true false = true.
      reflexivity.                (* fixed *)
    Defined.

    Goal choice (x ≤ y)%foset true false = true.
      reflexivity.
    Defined.

    Goal choice (y < x)%foset true false = false.
      reflexivity.
    Defined.

    Goal choice (y ≤ x)%foset true false = false.
      reflexivity.
    Defined.

    Goal choice (x ≐ y)%foset true false = false.
      reflexivity.
    Defined.

    Goal choice (x ≐ x)%foset true false = true.
      reflexivity.
    Defined.

    Goal which (d x y) = false.
      reflexivity.
    Defined.

    Goal which (d x x) = true.
      reflexivity.
    Defined.

    Goal choice (x ≠ y)%foset true false = true.
      reflexivity.
    Defined.

    Goal which (isdeceqnat 2 (height x)) = true.
      try reflexivity.          (* fix *)
    Abort.

    Goal 2 = height x.
      try reflexivity.                (* fix *)
    Abort.

  End TestLex2.

  Goal ∏ X (lt:hrel X), iscotrans lt <-> iswklin lt.
  Proof.
    intros. unfold iscotrans, iswklin. split.
    { intros i x1 x3 x2. apply i. }
    { intros i x z y. apply i. }
  Defined.

  Goal (idweq nat ∘ idweq _ ∘ idweq _)%weq 3 = 3. reflexivity. Defined.
  Goal (idweq nat ∘ invweq (idweq _) ∘ idweq _)%weq 3 = 3. reflexivity. Defined.
  Goal invmap (idweq nat ∘ idweq _ ∘ idweq _)%weq 3 = 3. reflexivity. Defined.
  Goal invmap (idweq nat ∘ invweq (idweq _) ∘ idweq _)%weq 3 = 3. reflexivity. Defined.

End Test_ord.

Module Test_search.

  Import UniMath.Combinatorics.BoundedSearch.
  Import UniMath.Foundations.Propositions.

  Local Definition someseq (n : nat) : bool.
  Proof.
    intros n. destruct n.
    - exact false.
    - destruct n.
      + exact true.
      + destruct n.
        * exact true.
        * exact false.
  Defined.

  Definition P : nat → hProp.
  Proof.
    intros n.
    refine (hProppair (someseq n = true) _).
    refine (isasetbool _ _).
  Defined.

  Local Definition P_dec (n : nat) : P n ⨿ ¬ P n.
  Proof.
    unfold P, someseq.
    destruct n.
    - apply ii2. exact nopathsfalsetotrue.
    - destruct n.
      + apply ii1. apply idpath.
      + destruct n.
        * apply ii1, idpath.
        * apply ii2. exact nopathsfalsetotrue.
  Defined.

  Local Definition P_inhab : ∃ n, P n.
  Proof.
    apply hinhpr. refine (2%nat,,_). apply idpath.
  Defined.

  Goal 1 = pr1 (minimal_n P P_dec P_inhab). reflexivity. Defined.

  Axiom P_inhab' : ∃ n, P n.

  Definition new_n' :  ∑ n : nat, P n := minimal_n P P_dec P_inhab'.

End Test_search.
