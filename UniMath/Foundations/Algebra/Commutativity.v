Require Export UniMath.Foundations.Algebra.Associativity.
Require Export UniMath.Foundations.FunctionalExtensionality.
Unset Automatic Introduction.

Definition weqcomp_to_funcomp {X Y Z} {x:X} {f:X≃Y} {g:Y≃Z} :
  (weqcomp f g) x = pr1weq g (pr1weq f x).
Proof. reflexivity. Defined.

Definition weqcomp_to_funcomp' {X Y Z} {f:X≃Y} {g:Y≃Z} :
  pr1weq (weqcomp f g) = pr1weq g ∘ pr1weq f.
Proof. reflexivity. Defined.

Definition pr1_dni_allButLast {n i} : pr1 (dni_allButLast n i) = pr1 i.
Proof. intros. induction i as [i b]. reflexivity. Defined.

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  sequenceProduct (n,,x) = sequenceProduct (n,,x∘f).
Proof.
  intros.
  induction n as [|n IH].
  - reflexivity.
  - assert (specialcase : ∀ (y:stn _->M) (g : stn _ ≃ stn _), g (lastelement n) = lastelement n ->
        sequenceProduct (S n,, y) = sequenceProduct (S n,, y ∘ g)).
    { intros ? ? a.
      rewrite 2? sequenceProductStep.
      change ((_ ∘ _) _) with (y (g (lastelement n))).
      rewrite a.
      apply (maponpaths (λ m, m * _)).
      change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_allButLast n)).
      set (h := eqweqmap (maponpaths (compl (stn (S n))) a)).
      assert (pr1_h : ∀ i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. }
      set (wc := weqdnicompl n (lastelement n)).
      set (g' := weqcomp (weqcomp wc (weqcomp (weqoncompl g (lastelement n)) h)) (invweq wc)).
      intermediate_path (sequenceProduct (n,, y ∘ dni_allButLast n ∘ g')).
      { apply IH. }
      { change ((_ ∘ _) ∘ _) with (y ∘ (dni_allButLast n ∘ g')).
        apply maponpaths; apply maponpaths; apply (maponpaths (λ g, _ ∘ g)).
        apply funextfun; intros i.
        change ((g ∘ _) _) with (g (dni_allButLast n i)).
        change ((_ ∘ g') _) with (dni_allButLast n (g' i)).
        apply isinjstntonat.
        rewrite pr1_dni_allButLast.
        unfold g'.
        rewrite 3? weqcomp_to_funcomp.
        rewrite inv_weqdnicompl_compute_last.
        rewrite pr1_h.
        rewrite weqoncompl_compute.
	apply maponpaths.                                           
	apply maponpaths.                                           
        apply isinjstntonat.
        unfold wc.
        rewrite weqdnicompl_compute_last.
        rewrite pr1_dni_allButLast.
        reflexivity.
        }}
    induction (isdeceqstn (S n) (f (lastelement n)) (lastelement n)) as [p|p].
    + now apply specialcase.
    + 


Abort.



    
    
    
    
