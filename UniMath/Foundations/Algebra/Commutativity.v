Require Export UniMath.Foundations.Algebra.Associativity.
Require Export UniMath.Foundations.FunctionalExtensionality.
Unset Automatic Introduction.

Definition weqcomp_to_funcomp {X Y Z} {x:X} {f:X≃Y} {g:Y≃Z} :
  (weqcomp f g) x = pr1weq g (pr1weq f x).
Proof. reflexivity. Defined.

Definition pr1_dni_allButLast {n i} : pr1 (dni_allButLast n i) = pr1 i.
Proof. intros. induction i as [i b]. reflexivity. Defined.

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  sequenceProduct (n,,x) = sequenceProduct (n,,x∘f).
Proof.
  intros.
  induction n as [|n IH].
  - reflexivity.
  - induction (isdeceqstn (S n) (f (lastelement n)) (lastelement n)).
    + rewrite 2? sequenceProductStep.
      change ((x ∘ f) (lastelement n)) with (x (f (lastelement n))).
      rewrite a.
      change ((x ∘ f) ∘ dni_allButLast n) with (x ∘ (f ∘ dni_allButLast n)).
      apply (maponpaths (λ m, m * x(lastelement n))).
      set (f' := weqoncompl f (lastelement n)).
      set (g := eqweqmap (maponpaths (compl (stn (S n))) a)).
      set (f'' := weqcomp f' g).
      set (wc := weqdnicompl n (lastelement n)).
      set (f''' := weqcomp (weqcomp wc f'') (invweq wc)).
      intermediate_path (sequenceProduct (n,, x ∘ dni_allButLast n ∘ f''')).
      * apply IH.
      * change ((x ∘ dni_allButLast n) ∘ f''') with (x ∘ (dni_allButLast n ∘ f''')).
        apply maponpaths.
        apply maponpaths.
        apply (maponpaths (λ g, x ∘ g)).
        apply funextfun; intros i.
        change ((f ∘ dni_allButLast n) i) with (f  (dni_allButLast n i)).
        induction i as [i b].
        unfold dni_allButLast at 2.
        set (b' := natlthtolths i n b).
        unfold f''', f'', f', funcomp.
        rewrite 3? weqcomp_to_funcomp.
        apply total2_paths_second_isaprop.
        { apply isasetbool. }
        rewrite pr1_dni_allButLast.
        unfold wc at 2.
        Set Printing Coercions.
        unfold weqdnicompl.
        change (pr1weq
                 (weqpair (dnitocompl n (lastelement n))
                          (isweqdnitocompl n (lastelement n))))
        with (dnitocompl n (lastelement n)).
        unfold weqoncompl.
        change (pr1weq
                  (weqpair (maponcomplweq f (lastelement n))
                           (isweqmaponcompl f (lastelement n))))
        with (maponcomplweq f (lastelement n)).


Abort.



