(****************************************************************

 Coproducts of DCPOs

 We construct coproducts of DCPOs, and we show that the
 inclusion functions are Scott continuous. In addition, we show
 that the map coming from the universal property is Scott
 continuous.

 To construct the coproduct, we take the coproduct of the
 underlying posets, and then it remains to prove completeness.
 The idea of this proof as follows: a directed set in the
 coproduct of `X` and `Y` is either a directed set in `X` or a
 directed set in `Y`. The main statement for this is proven in
 [directed_set_all_inl_or_all_inr].
 It says that either every value of the directed set is in `X`
 or that every value is in `Y`. We can determine in which of
 these cases we are by looking at the element of the directed
 set and since every two elements have an upper bound, all other
 elements must be in the same one. Note that it is essential here
 to use propositional truncations, because they are necessary to
 make use of directedness.

 The statement [directed_set_all_inl_or_all_inr] gives us two
 cases to consider, and these are treated similarly. In the first
 case, we construct a directed set in `X`:
 [all_inl_directed_set_to_left]
 while in the second case, we construct a directed set in `Y`:
 [all_inr_directed_set_to_right].
 We also prove that the least upperbound of these directed sets
 correspond to the least upperbound of the original directed set.

 Afterwards, we prove two statements:
 1. [directed_set_coproduct_with_eq]
 2. [directed_set_coproduct]
 These collect all the facts about directed sets in the
 coproduct. The first is a bit stronger, because it also gives
 equality between members of the two directed sets.

 Contents
 1. Directed sets in the coproduct
 2. Coproduct of DCPOs
 3. Scott continuity of inclusion
 4. The sum of Scott continuous maps is Scott continuous

 ****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

Section CoproductOfDCPO.
  Context (X Y : dcpo).

  (**
   1. Directed sets in the coproduct
   *)
  Section DirectedSetInCoproduct.
    Context (D : directed_set (coproduct_PartialOrder X Y)).

    Definition directed_set_all_inl_or_all_inr
      : (∀ (i : D), ∃ (x : X), D i = inl x)
        ∨
        (∀ (i : D), ∃ (y : Y), D i = inr y).
    Proof.
      assert (h := directed_set_el D).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros i.
      pose (d := D i).
      assert (p : d = D i) by apply idpath.
      induction d as [ x | y ].
      - refine (hinhpr (inl (λ j, _))).
        assert (t := directed_set_top D i j).
        revert t.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros k.
        induction k as [ t [ H₁ H₂ ]].
        pose (Dt := D t).
        assert (q : Dt = D t) by apply idpath.
        induction Dt as [ x' | y' ].
        + use hinhpr.
          pose (w := D j).
          assert (r : w = D j) by apply idpath.
          induction w as [ x'' | y'' ].
          * exact (x'' ,, !r).
          * rewrite <- q, <- r in H₂.
            cbn in H₂.
            apply fromempty.
            exact H₂.
        + rewrite <- p, <- q in H₁.
          cbn in H₁.
          apply fromempty.
          exact H₁.
      - refine (hinhpr (inr (λ j, _))).
        assert (t := directed_set_top D i j).
        revert t.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros k.
        induction k as [ t [ H₁ H₂ ]].
        pose (Dt := D t).
        assert (q : Dt = D t) by apply idpath.
        induction Dt as [ x' | y' ].
        + use hinhpr.
          pose (w := D j).
          rewrite <- p, <- q in H₁.
          cbn in H₁.
          apply fromempty.
          exact H₁.
        + use hinhpr.
          pose (w := D j).
          assert (r : w = D j) by apply idpath.
          induction w as [ x'' | y'' ].
          * rewrite <- q, <- r in H₂.
            cbn in H₂.
            apply fromempty.
            exact H₂.
          * exact (y'' ,, !r).
    Qed.

    Section LeftDirectedSet.
      Context (H : ∀ (i : D), ∃ (x : X), D i = inl x).

      Definition all_inl_directed_set_map_help
                 (i : D)
                 (w : X ⨿ Y)
                 (r : w = D i)
        : X.
      Proof.
        induction w as [ x | y ].
        - exact x.
        - abstract
            (apply fromempty ;
             assert (bot := H i) ;
             revert bot ;
             use factor_through_squash ; [ apply isapropempty | ] ;
             intros dx ;
             destruct dx as [ x p ] ;
             exact (negpathsii1ii2 x y (!p @ !r))).
      Defined.

      Proposition all_inl_directed_set_map_eq_help
                  (i : D)
                  (x : X)
                  (r : inl x = D i)
        : all_inl_directed_set_map_help i (inl x) r = x.
      Proof.
        apply idpath.
      Qed.

      Definition all_inl_directed_set_map
                 (i : D)
        : X
        := all_inl_directed_set_map_help i (D i) (idpath _).

      Proposition all_inl_directed_set_map_eq
                  (i : D)
                  (x : X)
                  (p : D i = inl x)
        : all_inl_directed_set_map i = x.
      Proof.
        unfold all_inl_directed_set_map.
        refine (_ @ all_inl_directed_set_map_eq_help i x (!p)).
        induction p.
        apply idpath.
      Qed.

      Proposition is_directed_all_inl_directed_set_to_left
        : is_directed X all_inl_directed_set_map.
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
          induction t as [ t [ H₁ H₂ ]].
          assert (q := H t).
          revert q.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intros [ x Hx ].
          rewrite Hx in H₁, H₂.
          pose (wi := D i).
          assert (pi : wi = D i) by apply idpath.
          pose (wj := D j).
          assert (pj : wj = D j) by apply idpath.
          induction wi as [ xi | yi ].
          + induction wj as [ xj | yj ].
            * rewrite <- pi in H₁.
              rewrite <- pj in H₂.
              cbn in H₁, H₂.
              refine (hinhpr (t ,, _)).
              rewrite (all_inl_directed_set_map_eq t x Hx).
              rewrite (all_inl_directed_set_map_eq i xi (!pi)).
              rewrite (all_inl_directed_set_map_eq j xj (!pj)).
              split.
              ** exact H₁.
              ** exact H₂.
            * rewrite <- pj in H₂.
              cbn in H₂.
              exact (fromempty H₂).
          + rewrite <- pi in H₁.
            cbn in H₁.
            exact (fromempty H₁).
      Qed.

      Definition all_inl_directed_set_to_left
        : directed_set X.
      Proof.
        use make_directed_set.
        - exact D.
        - exact all_inl_directed_set_map.
        - exact is_directed_all_inl_directed_set_to_left.
      Defined.

      Proposition is_lub_all_inl_directed_set_to_left
        : is_least_upperbound
            (coproduct_PartialOrder X Y)
            D
            (inl (⨆ all_inl_directed_set_to_left)).
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
          induction p as [ x p ].
          rewrite p.
          use (less_than_dcpo_lub all_inl_directed_set_to_left _ i).
          cbn.
          rewrite (all_inl_directed_set_map_eq i x p).
          apply refl_dcpo.
        - intros y Hy.
          induction y as [ x | y ].
          + use dcpo_lub_is_least ; cbn.
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
            cbn in p.
            rewrite (all_inl_directed_set_map_eq i x' H').
            exact p.
          + cbn.
            assert (el := directed_set_el D).
            revert el.
            use factor_through_squash.
            {
              apply isapropempty.
            }
            intro i.
            assert (H' := H i).
            revert H'.
            use factor_through_squash.
            {
              apply isapropempty.
            }
            intros H'.
            induction H' as [ x H' ].
            pose (Hy i) as p.
            cbn in p.
            rewrite H' in p.
            exact p.
      Qed.
    End LeftDirectedSet.

    Section RightDirectedSet.
      Context (H : ∀ (i : D), ∃ (y : Y), D i = inr y).

      Definition all_inr_directed_set_map_help
                 (i : D)
                 (w : X ⨿ Y)
                 (r : w = D i)
        : Y.
      Proof.
        induction w as [ x | y ].
        - abstract
            (apply fromempty ;
             assert (bot := H i) ;
             revert bot ;
             use factor_through_squash ; [ apply isapropempty | ] ;
             intros dy ;
             destruct dy as [ y p ] ;
             exact (negpathsii1ii2 _ _ (r @ p))).
        - exact y.
      Defined.

      Proposition all_inr_directed_set_map_eq_help
                  (i : D)
                  (y : Y)
                  (r : inr y = D i)
        : all_inr_directed_set_map_help i (inr y) r = y.
      Proof.
        apply idpath.
      Qed.

      Definition all_inr_directed_set_map
                 (i : D)
        : Y
        := all_inr_directed_set_map_help i (D i) (idpath _).

      Proposition all_inr_directed_set_map_eq
                  (i : D)
                  (y : Y)
                  (p : D i = inr y)
        : all_inr_directed_set_map i = y.
      Proof.
        unfold all_inr_directed_set_map.
        refine (_ @ all_inr_directed_set_map_eq_help i y (!p)).
        induction p.
        apply idpath.
      Qed.

      Proposition is_directed_all_inr_directed_set_to_right
        : is_directed Y all_inr_directed_set_map.
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
          induction t as [ t [ H₁ H₂ ]].
          assert (q := H t).
          revert q.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intros [ y Hy ].
          rewrite Hy in H₁, H₂.
          pose (wi := D i).
          assert (pi : wi = D i) by apply idpath.
          pose (wj := D j).
          assert (pj : wj = D j) by apply idpath.
          induction wi as [ xi | yi ].
          + rewrite <- pi in H₁.
            cbn in H₁.
            exact (fromempty H₁).
          + induction wj as [ xj | yj ].
            * rewrite <- pj in H₂.
              cbn in H₂.
              exact (fromempty H₂).
            * rewrite <- pi in H₁.
              rewrite <- pj in H₂.
              cbn in H₁, H₂.
              refine (hinhpr (t ,, _)).
              rewrite (all_inr_directed_set_map_eq t y Hy).
              rewrite (all_inr_directed_set_map_eq i yi (!pi)).
              rewrite (all_inr_directed_set_map_eq j yj (!pj)).
              split.
              ** exact H₁.
              ** exact H₂.
      Qed.

      Definition all_inr_directed_set_to_right
        : directed_set Y.
      Proof.
        use make_directed_set.
        - exact D.
        - exact all_inr_directed_set_map.
        - exact is_directed_all_inr_directed_set_to_right.
      Defined.

      Proposition is_lub_all_inr_directed_set_to_right
        : is_least_upperbound
            (coproduct_PartialOrder X Y)
            D
            (inr (⨆ all_inr_directed_set_to_right)).
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
          use (less_than_dcpo_lub all_inr_directed_set_to_right _ i).
          cbn.
          rewrite (all_inr_directed_set_map_eq i y p).
          apply refl_dcpo.
        - intros y Hy.
          induction y as [ x | y ].
          + cbn.
            assert (el := directed_set_el D).
            revert el.
            use factor_through_squash.
            {
              apply isapropempty.
            }
            intro i.
            assert (H' := H i).
            revert H'.
            use factor_through_squash.
            {
              apply isapropempty.
            }
            intros H'.
            induction H' as [ y' H' ].
            pose (Hy i) as p.
            cbn in p.
            rewrite H' in p.
            exact p.
          + use dcpo_lub_is_least ; cbn.
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
            induction H' as [ y' H' ].
            rewrite H' in p.
            cbn in p.
            rewrite (all_inr_directed_set_map_eq i y' H').
            exact p.
      Qed.
    End RightDirectedSet.

    Definition directed_set_coproduct_with_eq
      : ((∑ (D' : D → X) (HD : is_directed X D'),
          let DX := make_directed_set _ D D' HD in
          (is_least_upperbound (coproduct_PartialOrder X Y) D (inl (⨆ DX)))
          ×
          (∏ (i : D), D i = inl (D' i)))
        ∨
        (∑ (D' : D → Y) (HD : is_directed Y D'),
         let DY := make_directed_set _ D D' HD in
         is_least_upperbound (coproduct_PartialOrder X Y) D (inr (⨆ DY))
         ×
         (∏ (i : D), D i = inr (D' i))))%type.
    Proof.
      assert (h := directed_set_all_inl_or_all_inr).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros H.
      destruct H as [ H | H ].
      - use hinhpr.
        use inl.
        refine (all_inl_directed_set_map H ,, _).
        refine (is_directed_all_inl_directed_set_to_left H ,, _).
        split.
        + apply is_lub_all_inl_directed_set_to_left.
        + intro i.
          assert (p := H i).
          revert p.
          use factor_through_squash.
          {
            apply setproperty.
          }
          intros xH.
          induction xH as [ x p ].
          rewrite (all_inl_directed_set_map_eq H i x p).
          exact p.
      - use hinhpr.
        use inr.
        refine (all_inr_directed_set_map H ,, _).
        refine (is_directed_all_inr_directed_set_to_right H ,, _).
        split.
        + apply is_lub_all_inr_directed_set_to_right.
        + intro i.
          assert (p := H i).
          revert p.
          use factor_through_squash.
          {
            apply setproperty.
          }
          intros xH.
          induction xH as [ x p ].
          rewrite (all_inr_directed_set_map_eq H i x p).
          exact p.
    Defined.

    Definition directed_set_coproduct
      : (∑ (D' : directed_set X),
         is_least_upperbound (coproduct_PartialOrder X Y) D (inl (⨆ D')))
        ∨
        (∑ (D' : directed_set Y),
         is_least_upperbound (coproduct_PartialOrder X Y) D (inr (⨆ D'))).
    Proof.
      assert (h := directed_set_all_inl_or_all_inr).
      revert h.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros H.
      destruct H as [ H | H ].
      - refine (hinhpr (inl (all_inl_directed_set_to_left H ,, _))).
        apply is_lub_all_inl_directed_set_to_left.
      - refine (hinhpr (inr (all_inr_directed_set_to_right H ,, _))).
        apply is_lub_all_inr_directed_set_to_right.
    Defined.
  End DirectedSetInCoproduct.

  (**
   2. Coproduct of DCPOs
   *)
  Definition coproduct_dcpo_inl_lub
             (D : directed_set X)
    : lub
        (coproduct_PartialOrder X Y)
        (directed_set_comp (inl_monotone_function X Y) D).
  Proof.
    use make_lub.
    - exact (inl (⨆ D)).
    - split.
      + abstract
          (intro i ;
           apply (less_than_dcpo_lub _ _ i (refl_dcpo _))).
      + abstract
          (intros y Hy ;
           cbn in y, Hy ;
           induction y as [ x' | y' ] ; [ exact (dcpo_lub_is_least D x' Hy) | ] ;
           cbn in * ;
           assert (w := directed_set_el D) ;
           revert w ;
           use factor_through_squash ; [ apply isapropempty | ] ;
           exact Hy).
  Defined.

  Definition coproduct_dcpo_inr_lub
             (D : directed_set Y)
    : lub
        (coproduct_PartialOrder X Y)
        (directed_set_comp (inr_monotone_function X Y) D).
  Proof.
    use make_lub.
    - exact (inr (⨆ D)).
    - split.
      + abstract
          (intro i ;
           apply (less_than_dcpo_lub _ _ i (refl_dcpo _))).
      + abstract
          (intros y Hy ;
           cbn in y, Hy ;
           induction y as [ x' | y' ] ; [ | exact (dcpo_lub_is_least D y' Hy) ] ;
           cbn in * ;
           assert (w := directed_set_el D) ;
           revert w ;
           use factor_through_squash ; [ apply isapropempty | ] ;
           exact Hy).
  Defined.

  Definition coproduct_dcpo_lub
             (D : directed_set (coproduct_PartialOrder X Y))
    : lub (coproduct_PartialOrder X Y) D.
  Proof.
    assert (D' := directed_set_coproduct D).
    revert D'.
    use factor_through_squash.
    {
      apply isaprop_lub.
    }
    intros D'.
    induction D' as [ D' | D' ].
    - induction D' as [ D' H ].
      use make_lub.
      + exact (inl (⨆ D')).
      + exact H.
    - induction D' as [ D' H ].
      use make_lub.
      + exact (inr (⨆ D')).
      + exact H.
  Defined.

  Definition coproduct_dcpo_struct
    : dcpo_struct (setcoprod X Y).
  Proof.
    use make_dcpo_struct.
    - exact (coproduct_PartialOrder X Y).
    - intros I Df HDf.
      pose (D := make_directed_set _ I Df HDf).
      exact (coproduct_dcpo_lub D).
  Defined.

  Definition coproduct_dcpo
    : dcpo
    := _ ,, coproduct_dcpo_struct.

  (**
   3. Scott continuity of inclusion
   *)
  Proposition is_scott_continuous_inl
    : is_scott_continuous X coproduct_dcpo inl.
  Proof.
    use make_is_scott_continuous.
    - apply inl_monotone_function.
    - intro D ; cbn.
      use (eq_lub
             coproduct_dcpo
             (directed_set_comp (inl_monotone_function X Y) D)).
      + exact (pr2 (coproduct_dcpo_inl_lub D)).
      + exact (is_least_upperbound_dcpo_comp_lub
                 _
                 D).
  Qed.

  Definition inl_scott_continuous_map
    : scott_continuous_map X coproduct_dcpo
    := inl ,, is_scott_continuous_inl.

  Proposition is_scott_continuous_inr
    : is_scott_continuous Y coproduct_dcpo inr.
  Proof.
    use make_is_scott_continuous.
    - apply inr_monotone_function.
    - intro D ; cbn.
      use (eq_lub
             coproduct_dcpo
             (directed_set_comp (inr_monotone_function X Y) D)).
      + exact (pr2 (coproduct_dcpo_inr_lub D)).
      + exact (is_least_upperbound_dcpo_comp_lub
                 _
                 D).
  Qed.

  Definition inr_scott_continuous_map
    : scott_continuous_map Y coproduct_dcpo
    := inr ,, is_scott_continuous_inr.

  (**
   4. The sum of Scott continuous maps is Scott continuous
   *)
  Proposition is_scott_continuous_sumofmaps
              {Z : dcpo}
              {f : X → Z}
              (Pf : is_scott_continuous X Z f)
              {g : Y → Z}
              (Pg : is_scott_continuous Y Z g)
    : is_scott_continuous coproduct_dcpo Z (sumofmaps f g).
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_sumofmaps _ _ (pr1 Pf) (pr1 Pg)).
    - intros D.
      assert (D' := directed_set_coproduct_with_eq D).
      revert D'.
      use factor_through_squash.
      {
        apply (pr1 Z).
      }
      intros D'.
      induction D' as [ D' | D' ].
      + induction D' as [ D' [ HD' [ H p ]]].
        pose (DX := make_directed_set _ _ D' HD').
        assert (⨆ D = inl (⨆ DX)) as q.
        {
          use (eq_lub
                 coproduct_dcpo
                 D
                 _
                 H).
          apply is_least_upperbound_dcpo_lub.
        }
        rewrite q.
        cbn.
        refine (scott_continuous_map_on_lub (f ,, Pf) DX @ _).
        use antisymm_dcpo.
        * use dcpo_lub_is_least.
          intro i ; cbn.
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             rewrite p ; cbn.
             apply refl_dcpo.
        * use dcpo_lub_is_least.
          intro i ; cbn.
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             rewrite p ; cbn.
             apply refl_dcpo.
      + induction D' as [ D' [ HD' [ H p ]]].
        pose (DY := make_directed_set _ _ D' HD').
        assert (⨆ D = inr (⨆ DY)) as q.
        {
          use (eq_lub
                 coproduct_dcpo
                 D
                 _
                 H).
          apply is_least_upperbound_dcpo_lub.
        }
        rewrite q.
        cbn.
        refine (scott_continuous_map_on_lub (g ,, Pg) DY @ _).
        use antisymm_dcpo.
        * use dcpo_lub_is_least.
          intro i ; cbn.
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             rewrite p ; cbn.
             apply refl_dcpo.
        * use dcpo_lub_is_least.
          intro i ; cbn.
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             rewrite p ; cbn.
             apply refl_dcpo.
  Qed.

  Definition sumof_scott_continuous_maps
             {Z : dcpo}
             (f : scott_continuous_map X Z)
             (g : scott_continuous_map Y Z)
    : scott_continuous_map coproduct_dcpo Z
    := sumofmaps f g ,, is_scott_continuous_sumofmaps (pr2 f) (pr2 g).
End CoproductOfDCPO.
