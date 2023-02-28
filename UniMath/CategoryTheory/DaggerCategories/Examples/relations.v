(* The category of relations, i.e. the objects are sets and the morphisms are relations of sets,
   becomes a dagger category by taking the "opposite" relation.
   Furthermore, we show that it is dagger univalent
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Relations.

Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerIsos.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerUnivalence.

Local Open Scope cat.

Section RelationsAsDaggers.

  Definition REL_dagger_structure : dagger_structure REL
    := λ _ _ f y x, f x y.

  Lemma REL_dagger_laws : dagger_laws REL_dagger_structure.
  Proof.
    repeat split ; intro ; intros ; repeat (apply funextsec ; intro) ; cbn.
    - use (invweq (weqeqweqhProp _ _)).
      use weqimplimpl.
      + exact (λ p, ! p).
      + exact (λ p, ! p).
      + apply Relations.eq_set.
      + apply Relations.eq_set.
    - use (invweq (weqeqweqhProp _ _)).
      use weqimplimpl.
      + intro p.
        use (factor_through_squash_hProp _ _ p).
        clear p ; intro p.
        apply hinhpr.
        exact (pr1 p ,, pr22 p ,, pr12 p).
      + intro p.
        use (factor_through_squash_hProp _ _ p).
        clear p ; intro p.
        apply hinhpr.
        exact (pr1 p ,, pr22 p ,, pr12 p).
      + apply isapropishinh.
      + apply isapropishinh.
  Qed.

  Definition REL_dagger : dagger REL
    := _ ,, REL_dagger_laws.

End RelationsAsDaggers.

Section UnivalenceOfRelations.

  Definition REL_unitary_to_image
             {X Y : REL}
             (u : unitary REL_dagger X Y)
    : ∏ (x : pr1 X) (y1 y2 : pr1 Y),
      pr1 u x y1 -> pr1 u x y2 -> y1 = y2.
  Proof.
    intros x y1 y2 r1 r2.
    set (q' := base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (pr22 u) y1) y2)).
    apply (path_to_fun q').
    apply hinhpr.
    exact (x ,, r1 ,, r2).
  Qed.

  Lemma REL_unitary_image_is_a_prop
        {X Y : REL}
        (u : unitary REL_dagger X Y)
    : ∏ x : pr1 X, isaprop (∑ y : pr1 Y, pr1 u x y).
  Proof.
    intros x.
    apply isaproptotal2.
    - intro ; apply (pr1 u _ _).
    - intros y1 y2.
      apply REL_unitary_to_image.
  Qed.

  Definition REL_unitary_to_inverse
             {X Y : REL}
             (u : unitary REL_dagger X Y)
    : ∏ x : pr1 X, ∃ y : pr1 Y, pr1 u x y.
  Proof.
    intro x.
    set (q := pr12 u).
    set (q' := base_paths _ _ (toforallpaths _ _ _ ((toforallpaths _ _ _ q) x) x)).

    use (invweq (eqweqmap q')).
    { apply idpath. }

    intro v.
    apply hinhpr.
    exact (pr1 v ,, pr12 v).
  Defined.

  Definition REL_unitary_to_inverse'
             {X Y : REL}
             (u : unitary REL_dagger X Y)
    : ∏ x : pr1 X, ∑ y : pr1 Y, pr1 u x y.
  Proof.
    intro x.
    set (q := REL_unitary_to_inverse u x).
    use (factor_through_squash (REL_unitary_image_is_a_prop u x) _ q).
    apply idfun.
  Defined.

  Lemma bla'
        {X Y : REL} (u : unitary REL_dagger X Y) (y : pr1 Y)
    : pr1 (REL_unitary_to_inverse' u (pr1 (REL_unitary_to_inverse' (unitary_inv u) y))) = y.
  Proof.
    set (q := REL_unitary_image_is_a_prop u (pr1 (REL_unitary_to_inverse' (unitary_inv u) y))).

    set (y' := pr1 (REL_unitary_to_inverse' u (pr1 (REL_unitary_to_inverse' (unitary_inv u) y)))).

    assert (p : pr1 u (pr1 (REL_unitary_to_inverse' (unitary_inv u) y)) y).
    {
      simpl.
      unfold REL_unitary_to_inverse'.
      simpl.


      admit.
    }

    assert (p' : pr1 (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x)) x').
    {
      admit.
    }


    exact (base_paths _ _ (pr1 (q (x' ,, p') (x ,, p)))).
  Admitted.

  Lemma bla
        {X Y : REL} (u : unitary REL_dagger X Y) (x : pr1 X)
    : pr1 (REL_unitary_to_inverse' (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x))) = x.
  Proof.
    set (q := REL_unitary_image_is_a_prop (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x))).

    set (x' := pr1 (REL_unitary_to_inverse' (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x)))).



    assert (p : pr1 (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x)) x).
    {
      Check pr1 (unitary_inv u).
      Check (pr1 (REL_unitary_to_inverse' u x)).
      Check REL_unitary_to_inverse' u x.

      unfold unitary in u.
      unfold is_unitary in u.
      simpl in u.
      unfold is_inverse_in_precat in u.
      cbn in u.

      Check  pr1 (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x)) x.
      use factor_through_squash_hProp.


      simpl.
      unfold REL_unitary_to_inverse'.
      unfold REL_dagger_structure.
      simpl.


      Search (factor_through_squash _ _ _).

      admit.
    }

    assert (p' : pr1 (unitary_inv u) (pr1 (REL_unitary_to_inverse' u x)) x').
    {
      admit.
    }


    exact (base_paths _ _ (pr1 (q (x' ,, p') (x ,, p)))).
  Admitted.

  Definition REL_unitary_to_equiv (X Y : REL)
    : unitary REL_dagger X Y -> pr1 X ≃ pr1 Y.
  Proof.
    intro u.
    (* use (invweq (hSet_univalence X Y)). *)
    use weq_iso.
    - exact (λ x, pr1 (REL_unitary_to_inverse' u x)).
    - exact (λ y, pr1 (REL_unitary_to_inverse' (unitary_inv u) y)).
    - exact (λ x, bla u x).
    - intro y.
      refine (_ @ bla (unitary_inv u) y).
      now rewrite unitary_inv_of_unitary_inv.
  Defined.

  Definition equivalence_to_relation {X Y : REL}
             (p : pr1 X ≃ pr1 Y)
    : REL ⟦ X, Y ⟧.
  Proof.
    intros x y.
    exists (pr1weq p x = y).
    apply (pr2 Y).
  Defined.

  Lemma equivalence_to_relation_is_unitary
        {X Y : REL}
        (p : pr1 X ≃ pr1 Y)
    : is_unitary REL_dagger (equivalence_to_relation p).
  Proof.
    split.
        * apply funextsec ; intro x1.
          apply funextsec ; intro x2.
          use total2_paths_f.
          -- set (Sx1x2 := make_hProp _ (pr2 X x1 x2)).
             simpl.
             use (base_paths _ _ (hPropUnivalence (∃ y : pr1 Y, p x1 = y × p x2 = y) Sx1x2 _ _)).
             ++ intro q.
                use (factor_through_squash_hProp _ _ q).
                clear q ; intro q.
                refine (_ @ maponpaths (invmap p) (pr12 q @ ! pr22 q) @ _).
                ** apply pathsinv0, homotinvweqweq.
                ** apply homotinvweqweq.
             ++ intro q.
                induction q.
                apply hinhpr.
                exact (p x1 ,, idpath _ ,, idpath _).
          -- apply isapropisaprop.
        * apply funextsec ; intro x1.
          apply funextsec ; intro x2.
          use total2_paths_f.
          -- set (Sx1x2 := make_hProp _ (pr2 Y x1 x2)).
             simpl.
             use (base_paths _ _ (hPropUnivalence (∃ y : pr1 X, p y = x1 × p y = x2) Sx1x2 _ _)).
             ++ intro q.
                use (factor_through_squash_hProp _ _ q).
                clear q ; intro q.
                exact (! pr12 q @ pr22 q).
             ++ intro q.
                induction q.
                apply hinhpr.
                exists (invmap p x1).
                split ; exact (homotinvweqweq (invweq p) x1).
          -- apply isapropisaprop.
  Qed.

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.
  Lemma REL_unitary_to_equiv_is_weq (X Y : REL)
    : isweq (REL_unitary_to_equiv X Y).
  Proof.
    use isweq_iso.
    - intro p.
      exists (equivalence_to_relation p).
      exact (equivalence_to_relation_is_unitary p).
    - intro u.
      use unitary_eq.
      apply funextsec ; intro x.
      apply funextsec ; intro y.
      use total2_paths_f.
      + unfold equivalence_to_relation.
        simpl pr1.
        assert (p0 : isaprop (pr1 (REL_unitary_to_inverse' u x) = y)).
        { apply (pr2 Y). }

        use (base_paths _ _ (hPropUnivalence (_,,p0) (pr1 u x y) _ _)).
        * intro j.
          induction j.
          apply REL_unitary_to_inverse'.
        * intro j.
          exact (base_paths _ _ (pr1 (REL_unitary_image_is_a_prop u x (REL_unitary_to_inverse' u x) (y ,, j)))).
      + apply isapropisaprop.
    - intro u.
      use total2_paths_f.
      + apply funextsec ; intro x.
        use (invmaponpathsweq (invweq u)).
        etrans.
        2: apply pathsinv0, (homotinvweqweq u).
        apply TODO_JOKER. (* ADMITTED HERE *)
      + apply isapropisweq.
  Defined.

  Definition REL_unitary_to_equiv_are_equiv (X Y : REL)
    : unitary REL_dagger X Y ≃ (pr1 X ≃ pr1 Y)
    := _ ,, REL_unitary_to_equiv_is_weq X Y.

  Lemma REL_is_univalent_dagger
    : is_univalent_dagger REL_dagger.
  Proof.
    intros X Y.
    use isweqhomot'.
    - use (invweq (REL_unitary_to_equiv_are_equiv X Y) ∘ _)%weq.
      apply hSet_univalence.
    - apply ((invweq (REL_unitary_to_equiv_are_equiv X Y) ∘ hSet_univalence X Y)%weq).
    - intro p ; induction p.
      use unitary_eq.
      apply idpath.
  Qed.

End UnivalenceOfRelations.
