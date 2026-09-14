(**

 Weak equivalences of hyperdoctrines

 In the notion of hyperdoctrine, we assume that the collection of formulas forms a
 partial order. Since our notion of hyperdoctrine is based on displayed categories,
 this means 'concretely' that the displayed category of formulas over contexts is
 univalent. However, not every hyperdoctrine that one meets, satisfies this
 requirement. For instance, if we want to construct the syntactic hyperdoctrine,
 then we need to take a quotient to guarantee that this requirement is satisfied.
 Hyperdoctrines arising in the context of realizability also do not necessarily
 satisfy this requirement: again, one needs to take the appropriate quotient. In
 addition, if we have a topos `E` that is not necessarily univalent, then the
 hyperdoctrine arising from the monomorphisms also is not necessarily univalent.

 Hence, there is a need to give a completion operation for hyperdoctrines and their
 variants (like first-order hyperdoctrines and triposes). Such a completion is
 essentially an extension of the Rezk completion. The Rezk completion generalizes
 the poset completion of preorders, and that is exactly what we want to do to
 complete hyperdoctrines.

 In this file, we set up some of the necessary infrastructure to work with the Rezk
 completion of hyperdoctrines. Specifically, we show that displayed weak equivalence
 over the identity preserves various kinds of properties and structures of displayed
 categories. Our precise starting point is that we have two displayed categories `D₁`
 and `D₂` over the same category `C`, and we have displayed functor `FF` from `D₁` to
 `D₂` over the identity. We assume that `FF` is fully faithful and essentially surjective
 and that `D₂` is univalent. Note that these assumptions make `D₂` a univalent completion
 of `D₁`.

 Content
 1. The morphisms in the completion form a preorder
 2. The completion is a fibration
 3. Some useful lemmas for the remainder
 4. Fiberwise terminal object in the completion
 5. Fiberwise initial object in the completion
 6. Fiberwise binary products in the completion
 7. Fiberwise binary coproducts in the completion
 8. Fiberwise exponentials in the completion
 9. Dependent sums in the completion
 10. Dependent products in the completion

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Initial.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Bincoproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinCoproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Exponentials.

Local Open Scope mor_disp.
Local Open Scope cat.

Section HyperdoctrineWeakEquiv.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          (FF : disp_functor (functor_identity _) D₁ D₂)
          (HFF₁ : disp_functor_ff FF)
          (HFF₂ : disp_functor_disp_ess_surj FF)
          (HD₁ : locally_propositional D₁)
          (HD₂ : is_univalent_disp D₂).

  (** * 1. The morphisms in the completion form a preorder *)
  Definition disp_functor_weak_equivalence_locally_propositional
    : locally_propositional D₂.
  Proof.
    intros x y f yy₁ yy₂.
    use invproofirrelevance.
    intros ff gg.
    pose proof (HFF₂ x yy₁) as p.
    revert p.
    use factor_through_squash.
    {
      apply homsets_disp.
    }
    intros (xx₁ & hh₁).
    pose proof (HFF₂ y yy₂) as p.
    revert p.
    use factor_through_squash.
    {
      apply homsets_disp.
    }
    intros (xx₂ & hh₂).
    refine (id_left_disp_var _ @ _ @ !(id_left_disp_var _)).
    apply maponpaths.
    refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)).
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (_ @ maponpaths (transportf _ _) (!(z_iso_disp_after_inv_mor hh₁))).
      refine (!_).
      apply transportfbinv.
    }
    rewrite !mor_disp_transportf_postwhisker.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (_ @ maponpaths (transportf _ _) (!(z_iso_disp_after_inv_mor hh₁))).
      refine (!_).
      apply transportfbinv.
    }
    rewrite !mor_disp_transportf_postwhisker.
    apply maponpaths.
    rewrite !assoc_disp_var.
    do 3 apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      refine (_ @ maponpaths (transportf _ _) (!(z_iso_disp_after_inv_mor hh₂))).
      refine (!_).
      apply transportfbinv.
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (_ @ maponpaths (transportf _ _) (!(z_iso_disp_after_inv_mor hh₂))).
      refine (!_).
      apply transportfbinv.
    }
    rewrite !mor_disp_transportf_prewhisker.
    apply maponpaths.
    rewrite !assoc_disp.
    do 2 apply maponpaths.
    apply maponpaths_2.
    refine (_ @ transportfbinv (λ z, _ -->[ z ] _) (!(id_right _ @ id_left _)) _).
    refine (!(transportfbinv (λ z, _ -->[ z ] _) (!(id_right _ @ id_left _)) _) @ _).
    apply maponpaths.
    use (invmaponpathsweq (invweq (disp_functor_ff_weq FF HFF₁ xx₁ xx₂ f))).
    apply HD₁.
  Qed.

  (** * 2. The completion is a fibration *)
  Definition disp_functor_weak_equivalence_cleaving
             (H : cleaving D₁)
    : cleaving D₂.
  Proof.
    intros x y f xx'.
    pose proof (HFF₂ x xx') as xx.
    revert xx.
    use factor_through_squash.
    {
      use isaprop_cartesian_lifts.
      exact HD₂.
    }
    intros (xx & gg).
    simple refine (_ ,, _ ,, _).
    - exact (FF y (H x y f xx)).
    - exact (transportf
               (λ z, _ -->[ z ] _)
               (id_right _)
               (♯FF (H x y f xx) ;; gg)).
    - intros w h ww' hh.
      pose proof (HFF₂ w ww') as ww.
      revert ww.
      use factor_through_squash.
      {
        apply isapropiscontr.
      }
      intros (ww & ff).
      use make_iscontr.
      + simple refine (_ ,, _).
        * refine (transportf
                    (λ z, _ -->[ z ] _)
                    (id_left _)
                    (inv_mor_disp_from_z_iso ff
                     ;; ♯FF (cartesian_factorisation (H x y f xx) h _))).
          use (disp_functor_ff_inv FF HFF₁) ; cbn.
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (ff
                     ;; hh
                     ;; inv_mor_disp_from_z_iso gg)).
          abstract
            (cbn ;
             rewrite id_left, id_right ;
             apply idpath).
        * apply disp_functor_weak_equivalence_locally_propositional.
      + abstract
          (intros ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           apply disp_functor_weak_equivalence_locally_propositional).
  Defined.

  (** * 3. Some useful lemmas for the remainder *)
  Proposition is_cartesian_disp_functor_weak_equivalence_cleaving
              (H : cleaving D₁)
    : is_cartesian_disp_functor FF.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact H.
    }
    intros x y f yy w h ww' hh.
    pose proof (HFF₂ w ww') as ww.
    revert ww.
    use factor_through_squash.
    {
      apply isapropiscontr.
    }
    intros (ww & ff).
    use make_iscontr.
    - simple refine (_ ,, _).
      + refine (transportf
                  (λ z, _ -->[ z ] _)
                  (id_left _)
                  (inv_mor_disp_from_z_iso ff
                   ;; ♯FF _)).
        use (cartesian_factorisation (H y x f yy)).
        use (disp_functor_ff_inv FF HFF₁) ; cbn.
        exact (transportf
                 (λ z, _ -->[ z ] _)
                 (id_left _)
                 (ff ;; hh)).
      + apply disp_functor_weak_equivalence_locally_propositional.
    - intros.
      use subtypePath.
      {
        intro.
        apply homsets_disp.
      }
      apply disp_functor_weak_equivalence_locally_propositional.
  Qed.

  Definition weak_equivalence_cartesian_disp_functor
             (H : cleaving D₁)
    : cartesian_disp_functor (functor_identity _) D₁ D₂
    := make_cartesian_disp_functor
         _
         (is_cartesian_disp_functor_weak_equivalence_cleaving H).

  Proposition disp_functor_weak_equivalence_preserves_lift
              (H : cleaving D₁)
              {x y : C}
              (f : x --> y)
              (yy : D₁ y)
    : FF x (H y x f yy)
      =
      disp_functor_weak_equivalence_cleaving H y x f (FF y yy).
  Proof.
    use (isotoid_disp HD₂ (idpath _)).
    simple refine (_ ,, _ ,, _ ,, _).
    - cbn.
      use (cartesian_factorisation
             (disp_functor_weak_equivalence_cleaving H y x f (FF y yy))).
      refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (♯FF (H y x f yy))).
      cbn.
      rewrite id_left.
      apply idpath.
    - cbn.
      use (cartesian_factorisation
             (is_cartesian_disp_functor_weak_equivalence_cleaving
                H
                _ _ _ _ _ _
                (H y x f yy))).
      refine (transportf
                (λ z, _ -->[ z ] _)
                (!(id_left _))
                _).
      exact (mor_disp_of_cartesian_lift
               _ _
               (disp_functor_weak_equivalence_cleaving H y x f (FF y yy))).
    - apply disp_functor_weak_equivalence_locally_propositional.
    - apply disp_functor_weak_equivalence_locally_propositional.
  Qed.

  Definition disp_functor_weak_cleaving_nat_z_iso
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (H' := disp_functor_weak_equivalence_cleaving H)
    : nat_z_iso
        (fiber_functor FF y
         ∙ fiber_functor_from_cleaving _ H' f)
        (fiber_functor_from_cleaving _ H f
         ∙ fiber_functor FF x).
  Proof.
    exact (fiber_functor_natural_nat_z_iso
             _ _
             (weak_equivalence_cartesian_disp_functor H)
             f).
  Defined.

  Proposition disp_functor_weak_equivalence_fiber
              (x : C)
    : is_weak_equiv (fiber_functor FF x).
  Proof.
    split.
    - use fiber_functor_essentially_surjective.
      apply HFF₂.
    - use fiber_functor_ff.
      apply HFF₁.
  Qed.

  (** * 4. Fiberwise terminal object in the completion *)
  Definition disp_functor_weak_equivalence_terminal_fib
             {x : C}
             (T : Terminal (D₁[{x}]))
    : Terminal (D₂[{x}]).
  Proof.
    exact (weak_equiv_creates_terminal
             (disp_functor_weak_equivalence_fiber x)
             T).
  Defined.

  Definition disp_functor_weak_equivalence_fiberwise_terminal
             (H : cleaving D₁)
             (T : fiberwise_terminal H)
    : fiberwise_terminal (disp_functor_weak_equivalence_cleaving H).
  Proof.
    split.
    - intro x.
      use disp_functor_weak_equivalence_terminal_fib.
      apply T.
    - intros x y f.
      use (weak_equiv_lifts_preserves_terminal
             (disp_functor_weak_cleaving_nat_z_iso H f)).
      + apply disp_functor_weak_equivalence_fiber.
      + use composition_preserves_terminal.
        * apply T.
        * use weak_equiv_preserves_terminal.
          apply disp_functor_weak_equivalence_fiber.
  Defined.

  Proposition preserves_terminal_fiber_functor_weak_equiv
              (x : C)
    : preserves_terminal (fiber_functor FF x).
  Proof.
    use weak_equiv_preserves_terminal.
    apply disp_functor_weak_equivalence_fiber.
  Qed.

  (** * 5. Fiberwise initial object in the completion *)
  Definition disp_functor_weak_equivalence_initial_fib
             {x : C}
             (I : Initial (D₁[{x}]))
    : Initial (D₂[{x}]).
  Proof.
    exact (weak_equiv_creates_initial
             (disp_functor_weak_equivalence_fiber x)
             I).
  Defined.

  Definition disp_functor_weak_equivalence_fiberwise_initial
             (H : cleaving D₁)
             (I : fiberwise_initial H)
    : fiberwise_initial (disp_functor_weak_equivalence_cleaving H).
  Proof.
    split.
    - intro x.
      use disp_functor_weak_equivalence_initial_fib.
      apply I.
    - intros x y f.
      use (weak_equiv_lifts_preserves_initial
             (disp_functor_weak_cleaving_nat_z_iso H f)).
      + apply disp_functor_weak_equivalence_fiber.
      + use composition_preserves_initial.
        * apply I.
        * use weak_equiv_preserves_initial.
          apply disp_functor_weak_equivalence_fiber.
  Defined.

  Proposition preserves_initial_fiber_functor_weak_equiv
              (x : C)
    : preserves_initial (fiber_functor FF x).
  Proof.
    use weak_equiv_preserves_initial.
    apply disp_functor_weak_equivalence_fiber.
  Qed.

  (** * 6. Fiberwise binary products in the completion *)
  Definition disp_functor_weak_equivalence_binproducts_fib
             {x : C}
             (BP : BinProducts (D₁[{x}]))
    : BinProducts (D₂[{x}]).
  Proof.
    refine (weak_equiv_into_univ_creates_binproducts
              _
              (disp_functor_weak_equivalence_fiber x)
              BP).
    use is_univalent_fiber.
    exact HD₂.
  Defined.

  Definition disp_functor_weak_equivalence_fiberwise_binproducts
             (H : cleaving D₁)
             (BP : fiberwise_binproducts H)
    : fiberwise_binproducts (disp_functor_weak_equivalence_cleaving H).
  Proof.
    split.
    - intro x.
      use disp_functor_weak_equivalence_binproducts_fib.
      apply BP.
    - intros x y f.
      use (weak_equiv_lifts_preserves_binproducts
             (disp_functor_weak_cleaving_nat_z_iso H f)).
      + apply disp_functor_weak_equivalence_fiber.
      + use composition_preserves_binproduct.
        * apply BP.
        * use weak_equiv_preserves_binproducts.
          apply disp_functor_weak_equivalence_fiber.
  Defined.

  Proposition preserves_binproduct_fiber_functor_weak_equiv
              (x : C)
    : preserves_binproduct (fiber_functor FF x).
  Proof.
    use weak_equiv_preserves_binproducts.
    apply disp_functor_weak_equivalence_fiber.
  Defined.

  (** * 7. Fiberwise binary coproducts in the completion *)
  Definition disp_functor_weak_equivalence_bincoproducts_fib
             {x : C}
             (BC : BinCoproducts (D₁[{x}]))
    : BinCoproducts (D₂[{x}]).
  Proof.
    refine (weak_equiv_creates_bincoproducts
              (disp_functor_weak_equivalence_fiber x)
              BC
              _).
    use is_univalent_fiber.
    exact HD₂.
  Defined.

  Definition disp_functor_weak_equivalence_fiberwise_bincoproducts
             (H : cleaving D₁)
             (BC : fiberwise_bincoproducts H)
    : fiberwise_bincoproducts (disp_functor_weak_equivalence_cleaving H).
  Proof.
    split.
    - intro x.
      use disp_functor_weak_equivalence_bincoproducts_fib.
      apply BC.
    - intros x y f.
      use (weak_equiv_lifts_preserves_bincoproducts
             (make_univalent_category _ _)
             (make_univalent_category _ _)
             (disp_functor_weak_cleaving_nat_z_iso H f)).
      + use is_univalent_fiber.
        exact HD₂.
      + use is_univalent_fiber.
        exact HD₂.
      + apply disp_functor_weak_equivalence_fiber.
      + use composition_preserves_bincoproduct.
        * apply BC.
        * use weak_equiv_preserves_bincoproducts.
          apply disp_functor_weak_equivalence_fiber.
  Defined.

  Proposition preserves_bincoproduct_fiber_functor_weak_equiv
              (x : C)
    : preserves_bincoproduct (fiber_functor FF x).
  Proof.
    use weak_equiv_preserves_bincoproducts.
    apply disp_functor_weak_equivalence_fiber.
  Qed.

  (** * 8. Fiberwise exponentials in the completion *)
  Definition disp_functor_weak_equivalence_exponentials_fib
             {x : C}
             (BP : BinProducts (D₁[{x}]))
             (E : Exponentials BP)
    : Exponentials (disp_functor_weak_equivalence_binproducts_fib BP).
  Proof.
    use (weak_equiv_into_univ_creates_exponentials
           (disp_functor_weak_equivalence_fiber x)
           _
           E).
    use is_univalent_fiber.
    exact HD₂.
  Defined.

  Definition disp_functor_weak_equivalence_fiberwise_exponentials
             (H : cleaving D₁)
             (BP : fiberwise_binproducts H)
             (E : fiberwise_exponentials BP)
    : fiberwise_exponentials
        (disp_functor_weak_equivalence_fiberwise_binproducts H BP).
  Proof.
    simple refine (_ ,, _).
    - intro x.
      apply disp_functor_weak_equivalence_exponentials_fib.
      apply E.
    - intros x y f.
      simpl.
      use (weak_equiv_lifts_preserves_exponentials
             (make_univalent_category _ _)
             (make_univalent_category _ _)
             (disp_functor_weak_cleaving_nat_z_iso H f)).
      + use is_univalent_fiber.
        exact HD₂.
      + use is_univalent_fiber.
        exact HD₂.
      + apply BP.
      + use preserves_exponential_objects'_to_preserves_exponential_objects.
        {
          apply E.
        }
        use preserves_exponentials_to_preserves_exponential_objects.
        {
          apply disp_functor_weak_equivalence_exponentials_fib.
          apply E.
        }
        use comp_preserves_exponentials.
        * apply BP.
        * apply E.
        * cbn.
          exact (pr2 E x y f).
        * apply weak_equiv_preserves_exponentials.
  Defined.

  Proposition preserves_exponential_fiber_functor_weak_equiv
              {x : C}
              (BP₁ : BinProducts (D₁[{x}]))
              (E₁ : Exponentials BP₁)
              (BP₂ : BinProducts (D₂[{x}]))
              (E₂ : Exponentials BP₂)
    : preserves_exponentials
        E₁
        E₂
        (preserves_binproduct_fiber_functor_weak_equiv x).
  Proof.
    assert (E₂
            =
            exponentials_independent
              _ _
              (disp_functor_weak_equivalence_exponentials_fib BP₁ E₁))
      as ->.
    {
      apply isaprop_Exponentials.
      use is_univalent_fiber.
      exact HD₂.
    }
    use preserves_exponentials_independent_cod.
    apply weak_equiv_preserves_exponentials.
  Qed.

  (** * 9. Dependent sums in the completion *)
  Definition disp_functor_weak_equivalence_dependent_sum_reflection
             (H₁ : cleaving D₁)
             (H₂ : cleaving D₂)
             {x y : C}
             (f : x --> y)
             (S : dependent_sum H₁ f)
             (xx : D₁ x)
    : reflection (D := D₂ [{x}]) (FF x xx) (fiber_functor_from_cleaving D₂ H₂ f).
  Proof.
    use make_reflection.
    - simple refine (_ ,, _).
      + exact (FF _ (left_adjoint S xx)).
      + refine (#(fiber_functor FF _) (unit_from_right_adjoint S xx) · _).
        refine (nat_z_iso_inv
                  (disp_functor_weak_cleaving_nat_z_iso H₁ f)
                  (left_adjoint S xx)
                · _).
        apply cartesian_lifts_iso.
    - intros f'.
      induction f' as [ yy' gg ].
      pose proof (HFF₂ y yy') as yy.
      revert yy.
      use factor_through_squash.
      {
        intro.
        apply isapropiscontr.
      }
      intros (yy & hh).
      use make_iscontr.
      + simple refine (_ ,, _).
        * refine (_  · z_iso_fiber_from_z_iso_disp _ _ _ _ hh).
          refine (#(fiber_functor FF _) _).
          refine (_ · counit_from_right_adjoint S yy).
          refine (#(left_adjoint S) _).
          use (cartesian_factorisation (H₁ y x f yy)).
          use (disp_functor_ff_inv FF HFF₁).
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (gg
                     ;; H₂ y x f yy'
                     ;; inv_mor_disp_from_z_iso hh)).
          abstract
            (cbn ;
             rewrite !id_left, id_right ;
             apply idpath).
        * apply disp_functor_weak_equivalence_locally_propositional.
      + abstract
          (intro ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           apply disp_functor_weak_equivalence_locally_propositional).
  Defined.

  Definition disp_functor_weak_equivalence_dependent_sum
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (S : dependent_sum H f)
    : dependent_sum (disp_functor_weak_equivalence_cleaving H) f.
  Proof.
    use reflections_to_is_right_adjoint.
    intros xx'.
    pose proof (HFF₂ x xx') as xx.
    revert xx.
    use factor_through_squash.
    {
      use isaprop_reflection.
      use is_univalent_fiber.
      exact HD₂.
    }
    intros (xx & ff).
    refine (reflection_transport_along_iso_ob
              (z_iso_fiber_from_z_iso_disp _ _ _ _ ff)
              _).
    clear ff xx'.
    exact (disp_functor_weak_equivalence_dependent_sum_reflection H _ _ S xx).
  Defined.

  Proposition disp_functor_weak_equivalence_preserves_dependent_sum
              {H₁ : cleaving D₁}
              {H₂ : cleaving D₂}
              {x y : C}
              (f : x --> y)
              (S₁ : dependent_sum H₁ f)
              (S₂ : dependent_sum H₂ f)
              (xx : D₁ x)
    : z_iso
        (left_adjoint S₂ (FF x xx))
        (FF y (left_adjoint S₁ xx)).
  Proof.
    exact (reflection_uniqueness_iso
             (left_adjoint_to_reflection S₂ (FF x xx))
             (disp_functor_weak_equivalence_dependent_sum_reflection H₁ H₂ f S₁ xx)).
  Defined.

  (**
     We also verify the Beck-Chevalley condition for dependent sums
   *)
  Definition disp_functor_weak_equivalence_fiber_dep_sum
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (S : dependent_sum H f)
             (xx : D₁ x)
    : left_adjoint (disp_functor_weak_equivalence_dependent_sum H f S) (FF x xx)
      -->
      fiber_functor FF _ (left_adjoint S xx).
  Proof.
    pose (counit_from_right_adjoint
            (disp_functor_weak_equivalence_dependent_sum H f S)
            (fiber_functor FF _ (left_adjoint S xx)))
      as ε.
    refine (_ · ε).
    refine (#(left_adjoint _) _).
    refine (_ · nat_z_iso_inv (disp_functor_weak_cleaving_nat_z_iso H f) _).
    refine (#(fiber_functor FF _) _).
    exact (unit_from_right_adjoint S xx).
  Qed.

  Definition disp_functor_weak_equivalence_fiber_dep_sum_inv
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (S : dependent_sum H f)
             (xx : D₁ x)
    : fiber_functor FF y (left_adjoint S xx)
      -->
      left_adjoint (disp_functor_weak_equivalence_dependent_sum H f S) (FF x xx).
  Proof.
    pose proof (HFF₂
                  _
                  (left_adjoint
                     (disp_functor_weak_equivalence_dependent_sum H f S)
                     (FF x xx)))
      as yy.
    revert yy.
    use factor_through_squash.
    {
      apply disp_functor_weak_equivalence_locally_propositional.
    }
    intros (yy & i).
    refine (_ · z_iso_fiber_from_z_iso_disp _ _ _ _ i).
    refine (#(fiber_functor FF y) _).
    refine (_ · counit_from_right_adjoint S yy).
    refine (#(left_adjoint S) _).
    use (disp_functor_ff_inv FF HFF₁).
    refine (_ · disp_functor_weak_cleaving_nat_z_iso H f yy).
    refine (unit_from_right_adjoint (disp_functor_weak_equivalence_dependent_sum H f S) _ · _).
    refine (#(fiber_functor_from_cleaving _ _ f) _).
    exact (inv_from_z_iso (z_iso_fiber_from_z_iso_disp _ _ _ _ i)).
  Qed.

  Definition disp_functor_weak_equivalence_dependent_sum_stable
             (H : cleaving D₁)
             {w x y z : C}
             {f : x --> w}
             {g : y --> w}
             {h : z --> y}
             {k : z --> x}
             (Sf : dependent_sum H f)
             (Sh : dependent_sum H h)
             (yy : D₂ x)
             (s : ∏ (xx : D₁ x),
                  fiber_functor_from_cleaving _ H g (left_adjoint Sf xx)
                  -->
                  left_adjoint Sh (fiber_functor_from_cleaving _ H k xx))
    : fiber_functor_from_cleaving
        _
        (disp_functor_weak_equivalence_cleaving H)
        g
        (left_adjoint
           (disp_functor_weak_equivalence_dependent_sum H f Sf)
           yy)
      -->
      left_adjoint
        (disp_functor_weak_equivalence_dependent_sum H h Sh)
        (fiber_functor_from_cleaving _ (disp_functor_weak_equivalence_cleaving H) k yy).
  Proof.
    pose proof (HFF₂ x yy) as xx.
    revert xx.
    use factor_through_squash.
    {
      apply disp_functor_weak_equivalence_locally_propositional.
    }
    intros (xx & i).
    specialize (s xx).
    refine (_ · #(fiber_functor FF y) s · _).
    - refine (_ · disp_functor_weak_cleaving_nat_z_iso H g _).
      refine (#(fiber_functor_from_cleaving _ _ g) _).
      refine (_ · disp_functor_weak_equivalence_fiber_dep_sum _ _ _ _).
      exact (#(left_adjoint _) (inv_from_z_iso (z_iso_fiber_from_z_iso_disp _ _ _ _ i))).
    - refine (disp_functor_weak_equivalence_fiber_dep_sum_inv _ _ _ _ · _).
      refine (#(left_adjoint _) _).
      refine (nat_z_iso_inv (disp_functor_weak_cleaving_nat_z_iso H k) xx · _).
      refine (#(fiber_functor_from_cleaving _ _ k) _).
      exact (z_iso_fiber_from_z_iso_disp _ _ _ _ i).
  Qed.

  (** * 10. Dependent products in the completion *)
  Definition disp_functor_weak_equivalence_dependent_product_coreflection
             (H₁ : cleaving D₁)
             (H₂ : cleaving D₂)
             {x y : C}
             (f : x --> y)
             (P : dependent_product H₁ f)
             (xx : D₁ x)
    : coreflection (D := D₂ [{x}]) (FF x xx) (fiber_functor_from_cleaving D₂ H₂ f).
  Proof.
    use make_coreflection.
    - simple refine (_ ,, _).
      + exact (FF _ (right_adjoint P xx)).
      + refine (_ · disp_functor_weak_cleaving_nat_z_iso H₁ f (right_adjoint P xx)
                  · #(fiber_functor FF _) (counit_from_left_adjoint P xx)).
        apply cartesian_lifts_iso.
    - intros f'.
      induction f' as [ yy' gg ].
      pose proof (HFF₂ y yy') as yy.
      revert yy.
      use factor_through_squash.
      {
        intro.
        apply isapropiscontr.
      }
      intros (yy & hh).
      use make_iscontr.
      + simple refine (_ ,, _).
        * refine (inv_from_z_iso (z_iso_fiber_from_z_iso_disp _ _ _ _ hh) · _).
          refine (#(fiber_functor FF _) _).
          refine (unit_from_left_adjoint P yy · _).
          refine (#(right_adjoint P) _).
          use (disp_functor_ff_inv FF HFF₁).
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    (id_right _)
                    (cartesian_factorisation (H₂ y x f yy') _ _
                     ;; gg)).
          cbn.
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (♯FF (H₁ y x f yy) ;; hh)).
          cbn.
          abstract
            (rewrite id_left, id_right ;
             apply idpath).
        * apply disp_functor_weak_equivalence_locally_propositional.
      + abstract
          (intro ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           apply disp_functor_weak_equivalence_locally_propositional).
  Defined.

  Definition disp_functor_weak_equivalence_dependent_product
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (P : dependent_product H f)
    : dependent_product (disp_functor_weak_equivalence_cleaving H) f.
  Proof.
    use coreflections_to_is_left_adjoint.
    intros xx'.
    pose proof (HFF₂ x xx') as xx.
    revert xx.
    use factor_through_squash.
    {
      use isaprop_coreflection.
      use is_univalent_fiber.
      exact HD₂.
    }
    intros (xx & ff).
    refine (coreflection_transport_along_iso_ob
              (z_iso_fiber_from_z_iso_disp _ _ _ _ ff)
              _).
    apply (disp_functor_weak_equivalence_dependent_product_coreflection H).
    exact P.
  Defined.

  Proposition disp_functor_weak_equivalence_preserves_dependent_product
              {H₁ : cleaving D₁}
              {H₂ : cleaving D₂}
              {x y : C}
              (f : x --> y)
              (P₁ : dependent_product H₁ f)
              (P₂ : dependent_product H₂ f)
              (xx : D₁ x)
    : z_iso
        (right_adjoint P₂ (FF x xx))
        (FF y (right_adjoint P₁ xx)).
  Proof.
    exact (coreflection_uniqueness_iso
             (right_adjoint_to_coreflection P₂ (FF x xx))
             (disp_functor_weak_equivalence_dependent_product_coreflection H₁ H₂ f P₁ xx)).
  Defined.

  (**
     We also verify the Beck-Chevalley condition for dependent products.
   *)
  Definition disp_functor_weak_equivalence_fiber_dep_prod
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (P : dependent_product H f)
             (xx : D₁ x)
    : fiber_functor FF y (right_adjoint P xx)
      -->
      right_adjoint (disp_functor_weak_equivalence_dependent_product H f P) (FF x xx).
  Proof.
    pose (unit_from_left_adjoint
            (disp_functor_weak_equivalence_dependent_product H f P)
            (fiber_functor FF y (right_adjoint P xx)))
      as η.
    refine (η · _).
    refine (#(right_adjoint _) _).
    refine (disp_functor_weak_cleaving_nat_z_iso H f _ · _).
    refine (#(fiber_functor FF _) _).
    exact (counit_from_left_adjoint P xx).
  Qed.

  Definition disp_functor_weak_equivalence_fiber_dep_prod_inv
             (H : cleaving D₁)
             {x y : C}
             (f : x --> y)
             (P : dependent_product H f)
             (xx : D₁ x)
    : right_adjoint (disp_functor_weak_equivalence_dependent_product H f P) (FF x xx)
      -->
      fiber_functor FF _ (right_adjoint P xx).
  Proof.
    pose proof (HFF₂
                  _
                  (right_adjoint
                     (disp_functor_weak_equivalence_dependent_product H f P)
                     (FF x xx)))
      as yy.
    revert yy.
    use factor_through_squash.
    {
      apply disp_functor_weak_equivalence_locally_propositional.
    }
    intros (yy & i).
    refine (inv_from_z_iso (z_iso_fiber_from_z_iso_disp _ _ _ _ i) · _).
    refine (#(fiber_functor FF y) _).
    refine (unit_from_left_adjoint P yy · _).
    refine (#(right_adjoint P) _).
    use (disp_functor_ff_inv FF HFF₁).
    refine (nat_z_iso_inv (disp_functor_weak_cleaving_nat_z_iso H f) yy · _).
    refine (#(fiber_functor_from_cleaving _ _ f) (pr1 i) · _).
    apply (counit_from_left_adjoint (disp_functor_weak_equivalence_dependent_product H f P)).
  Qed.

  Definition disp_functor_weak_equivalence_dependent_product_stable
             (H : cleaving D₁)
             {w x y z : C}
             {f : x --> w}
             {g : y --> w}
             {h : z --> y}
             {k : z --> x}
             (Pf : dependent_product H f)
             (Ph : dependent_product H h)
             (yy : D₂ x)
             (s : ∏ (xx : D₁ x),
                  right_adjoint Ph (fiber_functor_from_cleaving _ H k xx)
                  -->
                  fiber_functor_from_cleaving _ H g (right_adjoint Pf xx))
    : right_adjoint
        (disp_functor_weak_equivalence_dependent_product H h Ph)
        (fiber_functor_from_cleaving _ (disp_functor_weak_equivalence_cleaving H) k yy)
      -->
      fiber_functor_from_cleaving
        _
        (disp_functor_weak_equivalence_cleaving H)
        g
        (right_adjoint
           (disp_functor_weak_equivalence_dependent_product H f Pf)
           yy).
  Proof.
    pose proof (HFF₂ x yy) as xx.
    revert xx.
    use factor_through_squash.
    {
      apply disp_functor_weak_equivalence_locally_propositional.
    }
    intros (xx & i).
    specialize (s xx).
    refine (_ · #(fiber_functor FF y) s · _).
    - refine (_ · disp_functor_weak_equivalence_fiber_dep_prod_inv _ _ _ _).
      refine (#(right_adjoint _) _).
      refine (_ · disp_functor_weak_cleaving_nat_z_iso H k xx).
      refine (#(fiber_functor_from_cleaving _ _ k) _).
      exact (inv_from_z_iso (z_iso_fiber_from_z_iso_disp _ _ _ _ i)).
    - refine (nat_z_iso_inv (disp_functor_weak_cleaving_nat_z_iso H g) _ · _).
      refine (#(fiber_functor_from_cleaving _ _ g) _).
      refine (disp_functor_weak_equivalence_fiber_dep_prod _ _ _ _ · _).
      exact (#(right_adjoint _) (z_iso_fiber_from_z_iso_disp _ _ _ _ i)).
  Qed.
End HyperdoctrineWeakEquiv.
