(****************************************************************

 Set indexed coproducts of DCPOs

 We construct set-indexed coproducts of DCPOs. For the idea
 behind the construction see the header of the file about binary
 sums.

 Contents
 1. Directed sets in set-indexed coproducts
 2. Set-indexed coproducts of DCPOs
 3. Scott continuity of inclusion of set-indexed coproducts
 4. The set-indexed sum of Scott continuous maps

 ****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

Section CoproductOfDCPO.
  Context {X : hSet}
          (Y : X → dcpo).

  (**
   1. Directed sets in set-indexed coproducts
   *)
  Section DirectedSet.
    Context (D : directed_set (coproduct_set_PartialOrder _ (λ x, Y x))).

    Definition directed_set_all_incl
      : ∃ (x : X), ∀ (i : D), ∃ (y : Y x), D i = (x ,, y).
    Proof.
      assert (h := directed_set_el D).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros i.
      refine (hinhpr (pr1 (D i) ,, λ j, _)).
      assert (t := directed_set_top D i j).
      revert t.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros k.
      induction k as [ t [ [ p₁ q₁ ] [ p₂ q₂ ] ]].
      destruct (D i) as [ di di' ].
      destruct (D j) as [ dj dj' ].
      destruct (D t) as [ dt dt' ].
      cbn in p₁, q₁, p₂, q₂.
      induction p₁, p₂.
      refine (hinhpr (dj' ,, _)).
      apply idpath.
    Qed.

    Section DirectedSetPoint.
      Context (x : X)
              (H : ∀ (i : D), ∃ (y : Y x), D i = (x ,, y)).

      Definition directed_set_point_map
                 (i : D)
        : Y x.
      Proof.
        refine (transportf Y _ (pr2 (D i))).
        abstract
          (assert (h := H i) ;
           revert h ;
           use factor_through_squash ; [ apply setproperty | ] ;
           intro p ;
           exact (base_paths _ _ (pr2 p))).
      Defined.

      Proposition directed_set_point_map_eq
                  (i : D)
                  (y : Y x)
                  (p : D i = x ,, y)
        : directed_set_point_map i = y.
      Proof.
        refine (_ @ fiber_paths p).
        unfold directed_set_point_map.
        apply maponpaths_2.
        apply setproperty.
      Qed.

      Proposition is_directed_directed_set_point
        : is_directed (Y x) directed_set_point_map.
      Proof.
        split.
        - exact (directed_set_el D).
        - intros i j.
          assert (w := directed_set_top D i j).
          revert w.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intros t.
          induction t as [ t [ [ p₁ q₁ ] [ p₂ q₂ ] ]] ; cbn in p₁, p₂.
          assert (q := H t).
          revert q.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intros [ y r ].
          refine (hinhpr (t ,, _)).
          rewrite (directed_set_point_map_eq t _ r).
          induction (D t) as [ dt dt' ].
          assert (s := total2_paths_equiv _ _ _ (!r)).
          clear r.
          induction s as [ s₁ s₂ ].
          cbn in p₁, p₂, s₁, s₂.
          induction s₁ ; cbn in s₂.
          induction s₂.
          assert (D i = x ,, transportf (λ z, Y z) p₁ (pr2 (D i))) as ri.
          {
            use total2_paths_b.
            - exact p₁.
            - cbn.
              rewrite transportbfinv.
              apply idpath.
          }
          rewrite (directed_set_point_map_eq i _ ri).
          assert (D j = x ,, transportf (λ z, Y z) p₂ (pr2 (D j))) as rj.
          {
            use total2_paths_b.
            - exact p₂.
            - cbn.
              rewrite transportbfinv.
              apply idpath.
          }
          rewrite (directed_set_point_map_eq j _ rj).
          induction (D i) as [ di di' ].
          induction (D j) as [ dj dj' ].
          cbn in *.
          induction p₁, p₂ ; cbn in *.
          exact (q₁ ,, q₂).
      Qed.

      Definition directed_set_point
        : directed_set (Y x).
      Proof.
        use make_directed_set.
        - exact D.
        - exact directed_set_point_map.
        - exact is_directed_directed_set_point.
      Defined.

      Proposition is_lub_directed_set_point
        : is_least_upperbound
            (coproduct_set_PartialOrder _ (λ x, Y x))
            D
            (x ,, ⨆ directed_set_point).
      Proof.
        split.
        - intros i.
          assert (p := H i).
          revert p.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intro p.
          induction p as [ y p ].
          rewrite p.
          refine (idpath _ ,, _) ; cbn.
          use (less_than_dcpo_lub directed_set_point _ i) ; cbn.
          rewrite (directed_set_point_map_eq _ _ p).
          apply refl_dcpo.
        - intros y Hy ; cbn.
          induction y as [ x' y' ].
          cbn in *.
          assert (p : x = x').
          {
            assert (el := directed_set_el D).
            revert el.
            use factor_through_squash.
            {
              apply setproperty.
            }
            intro i.
            assert (H' := H i).
            revert H'.
            use factor_through_squash.
            {
              apply setproperty.
            }
            intros H'.
            induction H' as [ z H' ].
            pose (Hy i) as p.
            cbn in p.
            rewrite H' in p.
            exact (pr1 p).
          }
          induction p.
          refine (idpath _ ,, _) ; cbn.
          use dcpo_lub_is_least.
          intro i.
          pose (Hy i) as p.
          cbn in p.
          assert (H' := H i).
          revert H'.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intros H'.
          induction H' as [ x' H' ].
          rewrite H' in p.
          cbn in p ; cbn.
          rewrite (directed_set_point_map_eq i _ H').
          induction p as [ p q ].
          assert (r : idpath _ = p) by apply setproperty.
          induction r.
          exact q.
      Qed.
    End DirectedSetPoint.

    Definition directed_set_coproduct_set_with_eq
      : ∃ (x : X),
        ∑ (D' : D → Y x)
          (HD : is_directed (Y x) D'),
        let DX := make_directed_set _ D D' HD in
        is_least_upperbound
          (coproduct_set_PartialOrder _ (λ x, Y x))
          D
          (x ,, ⨆ DX)
        ×
        (∏ (i : D), D i = (x ,, D' i)).
    Proof.
      assert (h := directed_set_all_incl).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros xH.
      induction xH as [ x H ].
      refine (hinhpr (x ,, _)).
      refine (directed_set_point_map x H ,, _).
      refine (is_directed_directed_set_point x H ,, _).
      split.
      - apply is_lub_directed_set_point.
      - intro i.
        assert (p := H i).
        revert p.
        use factor_through_squash.
        {
          apply setproperty.
        }
        intros yH.
        induction yH as [ y p ].
        rewrite (directed_set_point_map_eq x H i y p).
        exact p.
    Defined.

    Definition directed_set_set_coproduct
      : ∃ (x : X),
        ∑ (D' : D → Y x)
          (HD : is_directed (Y x) D'),
        let DX := make_directed_set _ D D' HD in
        is_least_upperbound
          (coproduct_set_PartialOrder _ (λ x, Y x))
          D
          (x ,, ⨆ DX).
    Proof.
      assert (h := directed_set_all_incl).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros xH.
      induction xH as [ x H ].
      refine (hinhpr (x ,, _)).
      refine (directed_set_point_map x H ,, _).
      refine (is_directed_directed_set_point x H ,, _).
      apply is_lub_directed_set_point.
    Defined.
  End DirectedSet.

  (**
   2. Set-indexed coproducts of DCPOs
   *)
  Definition coproduct_dcpo_incl_lub
             (x : X)
             (D : directed_set (Y x))
    : lub
        (coproduct_set_PartialOrder _ (λ x, Y x))
        (directed_set_comp
           (set_in_monotone_function Y Y x)
           D).
  Proof.
    use make_lub.
    - exact (x ,, ⨆ D).
    - split.
      + abstract
          (intro i ;
           refine (idpath _ ,, _) ; cbn in * ;
           apply (less_than_dcpo_lub _ _ i (refl_dcpo _))).
      + abstract
          (intros y Hy ;
           cbn in y, Hy ;
           induction y as [ x' y' ] ;
           cbn in * ;
           assert (p : x = x') ;
             [ assert (w := directed_set_el D) ;
               revert w ;
               use factor_through_squash ; [ apply setproperty | ] ;
               intro i ;
               exact (pr1 (Hy i))
             | ] ;
           induction p ;
           refine (idpath _ ,, _) ; cbn ;
           use (dcpo_lub_is_least D y') ;
           intro i ;
           specialize (Hy i) ;
           induction Hy as [ p q ] ;
           assert (idpath _ = p) as r by apply setproperty ;
           induction r ;
           cbn in * ;
           exact q).
  Defined.

  Definition coproduct_set_dcpo_lub
             (D : directed_set (coproduct_set_PartialOrder _ (λ x, Y x)))
    : lub (coproduct_set_PartialOrder _ (λ x, Y x)) D.
  Proof.
    assert (D' := directed_set_set_coproduct D).
    revert D'.
    use factor_through_squash.
    {
      apply isaprop_lub.
    }
    intros D'.
    induction D' as [ x D' ].
    induction D' as [ D' HD ].
    induction HD as [ HD H ].
    use make_lub.
    - exact (x ,, ⨆ (make_directed_set _ _ D' HD)).
    - exact H.
  Defined.

  Definition coproduct_set_dcpo_struct
    : dcpo_struct (∑ (x : X), Y x)%set.
  Proof.
    use make_dcpo_struct.
    - exact (coproduct_set_PartialOrder _ (λ x, Y x)).
    - intros I Df HDf.
      pose (D := make_directed_set _ I Df HDf).
      exact (coproduct_set_dcpo_lub D).
  Defined.

  Definition coproduct_set_dcpo
    : dcpo
    := _ ,, coproduct_set_dcpo_struct.

  (**
   3. Scott continuity of inclusion of set-indexed coproducts
   *)
  Proposition is_scott_continuous_incl
              (x : X)
    : is_scott_continuous (Y x) coproduct_set_dcpo (λ y, x ,, y).
  Proof.
    use make_is_scott_continuous.
    - exact (λ y₁ y₂ p, is_monotone_set_in Y Y x y₁ y₂ p).
    - intro D ; cbn.
      use (eq_lub
             coproduct_set_dcpo
             (directed_set_comp (set_in_monotone_function Y Y x) D)).
      + exact (pr2 (coproduct_dcpo_incl_lub x D)).
      + exact (is_least_upperbound_dcpo_comp_lub
                 _
                 D).
  Qed.

  Definition incl_scott_continuous_map
             (x : X)
    : scott_continuous_map (Y x) coproduct_set_dcpo
    := (λ y, x ,, y) ,, is_scott_continuous_incl x.

  (**
   4. The set-indexed sum of Scott continuous maps
   *)
  Proposition is_scott_continuous_set_coproduct_map
              {Z : dcpo}
              {f : ∏ (x : X), Y x → Z}
              (Pf : ∏ (x : X), is_scott_continuous (Y x) Z (f x))
    : is_scott_continuous coproduct_set_dcpo Z (λ xy, f (pr1 xy) (pr2 xy)).
  Proof.
    use make_is_scott_continuous.
    - exact (λ xy₁ xy₂ p, is_monotone_set_coproduct_map Y Y (λ x, pr1 (Pf x)) xy₁ xy₂ p).
    - intros D.
      assert (D' := directed_set_coproduct_set_with_eq D).
      revert D'.
      use factor_through_squash.
      {
        apply (pr1 Z).
      }
      intros D'.
      induction D' as [ x [ D' [ HD' H ]]].
      pose (DX := make_directed_set _ _ D' HD').
      assert (⨆ D = x ,, ⨆ DX) as q.
      {
        use (eq_lub coproduct_set_dcpo D _ (pr1 H)).
        apply is_least_upperbound_dcpo_lub.
      }
      rewrite q.
      cbn.
      refine (scott_continuous_map_on_lub (f x ,, Pf x) DX @ _).
      use antisymm_dcpo.
      + use dcpo_lub_is_least.
        intro i ; cbn.
        use less_than_dcpo_lub.
        * exact i.
        * cbn.
          rewrite (pr2 H i) ; cbn.
          apply refl_dcpo.
      + use dcpo_lub_is_least.
        intro i ; cbn.
        use less_than_dcpo_lub.
        * exact i.
        * cbn.
          rewrite (pr2 H i) ; cbn.
          apply refl_dcpo.
  Qed.

  Definition set_coproduct_scott_continuous_map
             {Z : dcpo}
             (f : ∏ (x : X), scott_continuous_map (Y x) Z)
    : scott_continuous_map coproduct_set_dcpo Z
    := (λ xy, f (pr1 xy) (pr2 xy))
       ,,
       is_scott_continuous_set_coproduct_map (λ x, pr2 (f x)).
End CoproductOfDCPO.
