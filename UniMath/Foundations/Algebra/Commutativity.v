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
      assert (pr1_g : ∀ i, pr1 (pr1 (g i)) = pr1 (pr1 i)).
      { intros. induction a. reflexivity. }
      set (f'' := weqcomp f' g).
      set (wc := weqdnicompl n (lastelement n)).
      assert (pr1_wc : ∀ i, pr1 (pr1 (wc i)) = pr1 i).
      { induction i as [i b].
        unfold wc; simpl.
        unfold dni; simpl.
        induction (natlthorgeh i n) as [p|p]. { reflexivity. } { contradicts b p. } }
      assert (pr1_inv_wc : ∀ i, pr1 (invweq wc i) = pr1 (pr1 i)).
      { intros.
        set (k := homotweqinvweq wc i).
        set (l := maponpaths pr1 (maponpaths pr1 k)).
        rewrite pr1_wc in l.
        exact l. }
      set (f''' := weqcomp (weqcomp wc f'') (invweq wc)).
      intermediate_path (sequenceProduct (n,, x ∘ dni_allButLast n ∘ f''')).
      { apply IH. }
      { change ((x ∘ dni_allButLast n) ∘ f''') with (x ∘ (dni_allButLast n ∘ f''')).
        apply maponpaths.
        apply maponpaths.
        apply (maponpaths (λ g, x ∘ g)).
        apply funextfun; intros i.
        change ((f ∘ dni_allButLast n) i) with (f  (dni_allButLast n i)).
        induction i as [i b].
        unfold dni_allButLast at 2.
        unfold f''', f'', f', funcomp.
        rewrite 3? weqcomp_to_funcomp.
        apply total2_paths_second_isaprop.
        { apply isasetbool. }
        rewrite pr1_dni_allButLast.
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
        rewrite pr1_inv_wc.
        rewrite pr1_g.
        assert (pp: ∀ j, pr1 (pr1 (maponcomplweq f (lastelement n) j)) = pr1 (f (pr1 j))).
        { intros. unfold maponcomplweq. unfold maponcomplincl.
          induction j as [j c]; simpl. reflexivity. }
        rewrite pp.
        apply maponpaths.
        apply maponpaths.
        apply total2_paths_second_isaprop.
        { exact (pr2 (natlth _ _)). }
        rewrite pr1_wc.
        simpl.
        reflexivity.
        }
    + 



Abort.



