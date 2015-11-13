Require Export UniMath.Foundations.Algebra.Associativity.
Require Export UniMath.Foundations.FunctionalExtensionality.
Unset Automatic Introduction.
Local Notation "● x" := (x,,idpath _) (at level 35).
Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  sequenceProduct (n,,x) = sequenceProduct (n,,x∘f).
Proof.
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros.
  induction n as [|n IH].
  - reflexivity.
  - assert (specialcase : ∀ (y:stn _->M) (g : stn _ ≃ stn _), g (lastelement n) = lastelement n ->
        sequenceProduct (S n,, y) = sequenceProduct (S n,, y ∘ g)).
    { intros ? ? a. rewrite 2? sequenceProductStep. change ((_ ∘ _) _) with (y (g (lastelement n))).
      rewrite a. apply (maponpaths (λ m, m * _)). change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_lastelement)).
      set (h := eqweqmap (maponpaths (compl (stn (S n))) a)).
      assert (pr1_h : ∀ i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. }
      set (wc := weqdnicompl n (lastelement n)).
      set (g' := (invweq wc ∘ (h ∘ (weqoncompl g (lastelement n) ∘ wc))) %weq).
      intermediate_path (sequenceProduct (n,, y ∘ dni_lastelement ∘ g')).
      { apply IH. }
      { change ((_ ∘ _) ∘ _) with (y ∘ (dni_lastelement ∘ g')).
        apply maponpaths; apply maponpaths; apply (maponpaths (λ g, _ ∘ g)).
        apply funextfun; intros i.
        change ((g ∘ _) _) with (g (dni_lastelement i)). change ((_ ∘ g') _) with (dni_lastelement (g' i)).
        apply isinjstntonat. rewrite pr1_dni_lastelement. unfold g'.
        rewrite 3? weqcomp_to_funcomp_app. rewrite inv_weqdnicompl_compute_last. rewrite pr1_h.
        rewrite weqoncompl_compute. apply maponpaths. apply maponpaths. apply isinjstntonat.
        unfold wc. rewrite weqdnicompl_compute_last. rewrite pr1_dni_lastelement. reflexivity. }}
    set (j := f (lastelement n)).
    induction j as [j jlt].
    assert (jle := natlthsntoleh _ _ jlt).
    Local Open Scope nat.
    set (m := nil □ j □ 1 □ n-j).
    set (m' := nil □ j □ n-j □ 1).
    set (sw := nil □ ●0 □ ●2 □ ●1 : Sequence (stn 3)).
    assert (B : stnsum m = S n). 
    { unfold stnsum; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc. rewrite (natpluscomm 1). rewrite <- natplusassoc.
      rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }                                 
    assert (B' : stnsum m' = S n).
    { unfold stnsum; simpl. rewrite natplusassoc. rewrite (natpluscomm _ 1). rewrite <- natplusassoc. apply B. }
    assert (C : m' ∘ sw ~ m).
    { intro i. change (pr1 sw) with 3 in i.
      induction i as [i b]. inductive_reflexivity i b. }
    assert (isweqsw : isweq sw).
    { apply (gradth sw sw); ( intros [i b]; inductive_reflexivity i b). }
    set (w := weqstnsum_idweq m). rewrite B in w. change (pr1 m) with 3 in w.
    set (w' := weqstnsum_idweq m'). rewrite B' in w'. change (pr1 m') with 3 in w'.

(*
    induction (isdeceqstn (S n) (f (lastelement n)) (lastelement n)) as [p|p].
    + now apply specialcase.
    + 
*)

Abort.



    
    
    
    
