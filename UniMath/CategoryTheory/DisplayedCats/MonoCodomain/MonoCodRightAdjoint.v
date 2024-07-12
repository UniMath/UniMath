(**************************************************************************************

 Universal quantification of monomorphisms

 In a locally Cartesian closed regular category, we can interpret the universal quantifier
 in the displayed category of monomorphisms. The construction is quite direct: the only
 thing that we need to show, is that the right adjoint of pullbacks lifts to the level
 of monomorphisms. This follows from the fact that right adjoint preserves monomorphisms.
 Stability under substitution follows from the fact that the left adjoint of pullback
 (i.e., existential quantification) is stable under substitution. From the universal
 quanfitier, we can also construct implications.

 Content
 1. Preservation of monomorphisms by dependent products
 2. Rules for universal quantification
 3. Stability under substitution for the universal quantifier
 4. The universal quantifier
 5. Introduction/elimination rules for the implication
 6. Stability under substitution for the implication
 7. The implication

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.AdjunctionMonics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.MonoCodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.Inclusion.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.

Local Open Scope cat.

Section DependentProductsMonoCodomain.
  Context {C : category}
          {PB : Pullbacks C}
          (HC : is_locally_cartesian_closed PB)
          (HC' : is_regular_category C).

  Let HD : cleaving (disp_mono_codomain C)
    := mono_cod_disp_cleaving PB.

  Section UniversalQuantification.
    Context {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂).

    Let R := right_adjoint (HC _ _ s).
    Let η := unit_from_left_adjoint (HC _ _ s).
    Let ε := counit_from_left_adjoint (HC _ _ s).

    (** * 1. Preservation of monomorphisms by dependent products *)
    Proposition is_monic_dependent_product
                (φ : C /m Γ₁)
      : isMonic (cod_mor (R (mono_cod_to_cod_fib Γ₁ φ))).
    Proof.
      pose (right_adjoint_preserves_monics
              R
              (is_right_adjoint_right_adjoint _)
              (from_monic_slice_to_terminal
                 (mono_cod_to_cod_fib _ φ)
                 (codomain_fib_terminal _)
                 (pr22 φ)))
        as H.
      pose (make_Terminal
              _
              (right_adjoint_preserves_terminal
                 _
                 (HC _ _ s)
                 _
                 (pr2 (codomain_fib_terminal _))))
        as terminal_Γ₂.
      refine (to_monic_slice_from_terminal _ terminal_Γ₂ _).
      refine (transportf (λ z, isMonic z) _ H).
      apply (TerminalArrowEq (T := terminal_Γ₂)).
    Qed.

    (** * 2. Rules for universal quantification *)
    Definition mono_cod_forall
               (φ : C /m Γ₁)
      : C /m Γ₂.
    Proof.
      use make_mono_cod_fib_ob.
      - exact (cod_dom (R (mono_cod_to_cod_fib _ φ))).
      - use make_Monic.
        + exact (cod_mor (R (mono_cod_to_cod_fib _ φ))).
        + apply is_monic_dependent_product.
    Defined.

    Definition mono_cod_forall_intro
               (φ : C /m Γ₁)
      : mono_cod_pb PB s (mono_cod_forall φ) --> φ.
    Proof.
      exact (ε (mono_cod_to_cod_fib _ φ)).
    Defined.

    Definition mono_cod_forall_elim
               (ψ : C /m Γ₁)
               (χ : C /m Γ₂)
               (p : mono_cod_pb PB s χ --> ψ)
      : χ --> mono_cod_forall ψ.
    Proof.
      refine (η (mono_cod_to_cod_fib _ χ) · #R _).
      exact p.
    Defined.
  End UniversalQuantification.

  Definition mono_cod_dep_prod
             {Γ₁ Γ₂ : C}
             (s : Γ₁ --> Γ₂)
    : dependent_product HD s.
  Proof.
    use make_dependent_product_of_mor_poset.
    - apply locally_propositional_mono_cod_disp_cat.
    - exact @mono_cod_forall.
    - exact @mono_cod_forall_intro.
    - exact @mono_cod_forall_elim.
  Defined.

  (** * 3. Stability under substitution for the universal quantifier *)
  Proposition mono_cod_right_beck_chevalley
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (H : isPullback p)
    : right_beck_chevalley
        HD
        f g h k
        p
        (mono_cod_dep_prod f)
        (mono_cod_dep_prod h).
  Proof.
    use right_from_left_beck_chevalley.
    - exact (pr1 (mono_codomain_has_dependent_sums HC' PB) _ _ g).
    - exact (pr1 (mono_codomain_has_dependent_sums HC' PB) _ _ k).
    - use (pr2 (mono_codomain_has_dependent_sums HC' PB)).
      apply is_symmetric_isPullback.
      exact H.
  Defined.

  (** * 4. The universal quantifier *)
  Definition has_dependent_products_mono_cod
    : has_dependent_products HD.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ s, mono_cod_dep_prod s).
    - exact @mono_cod_right_beck_chevalley.
  Defined.

  (** * 5. Introduction/elimination rules for the implication *)
  Local Definition mono_cod_impl_pb_map
                   {Γ : C}
                   (xφ yψ : C /m Γ)
    : mono_cod_dom (mono_cod_pb PB (mono_cod_mor xφ) yψ)
      -->
      mono_cod_dom (binprod_in_fib (mono_codomain_fiberwise_binproducts PB) xφ yψ).
  Proof.
    use PullbackArrow.
    - exact (PullbackPr2 _).
    - exact (PullbackPr1 _).
    - abstract
        (refine (!_) ;
         apply PullbackSqrCommutes).
  Defined.

  Section Implication.
    Context {Γ : C}
            (xφ yψ : C /m Γ).

    Let x : C := mono_cod_dom xφ.
    Let φ : x --> Γ := mono_cod_mor xφ.

    Let y : C := mono_cod_dom yψ.
    Let ψ : y --> Γ := mono_cod_mor yψ.

    Let P : Pullback φ ψ := PB _ _ _ φ ψ.

    Local Definition mono_cod_implication_pb : C /m x.
    Proof.
      use make_mono_cod_fib_ob.
      - exact P.
      - use make_Monic.
        + exact (PullbackPr1 P).
        + use MonicPullbackisMonic'.
    Defined.

    Definition mono_cod_implication
      : C /m Γ
      := mono_cod_forall φ mono_cod_implication_pb.

    Definition mono_cod_implication_intro
      : binprod_in_fib (mono_codomain_fiberwise_binproducts PB) xφ mono_cod_implication
        -->
        yψ.
    Proof.
      use make_mono_cod_fib_mor.
      - refine (_
                · mono_dom_mor (mono_cod_forall_intro φ mono_cod_implication_pb)
                · PullbackPr2 P).
        apply mono_cod_impl_pb_map.
      - abstract
          (cbn ;
           rewrite !assoc' ;
           etrans ;
           [ do 2 apply maponpaths ;
             refine (!(PullbackSqrCommutes P))
           | ] ;
           etrans ;
           [ apply maponpaths ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply (mono_mor_eq (mono_cod_forall_intro φ mono_cod_implication_pb))
           | ] ;
           cbn ;
           rewrite !assoc ;
           unfold mono_cod_impl_pb_map ;
           rewrite PullbackArrow_PullbackPr2 ;
           apply idpath).
    Defined.

    Context {zχ : C /m Γ}
            (l : binprod_in_fib (mono_codomain_fiberwise_binproducts PB) xφ zχ --> yψ).

    Let z : C := mono_cod_dom zχ.
    Let χ : z --> Γ := mono_cod_mor zχ.

    Let ζ : _ --> y := mono_dom_mor l.

    Definition mono_cod_implication_elim
      : zχ --> mono_cod_implication.
    Proof.
      use make_mono_cod_fib_mor.
      - refine (mono_dom_mor (mono_cod_forall_elim φ _ zχ _)).
        use make_mono_cod_fib_mor.
        + use PullbackArrow.
          * exact (PullbackPr2 _).
          * exact (mono_cod_impl_pb_map _ _ · ζ).
          * abstract
              (cbn ;
               refine (!_) ;
               etrans ;
               [ rewrite !assoc' ;
                 apply maponpaths ;
                 exact (mono_mor_eq l)
               | ] ;
               cbn ;
               unfold mono_cod_impl_pb_map ;
               rewrite !assoc ;
               rewrite PullbackArrow_PullbackPr1 ;
               apply idpath).
        + abstract
            (apply PullbackArrow_PullbackPr1).
      - abstract
          (exact (mono_mor_eq (mono_cod_forall_elim _ _ _ _))).
    Defined.
  End Implication.

  (** * 6. Stability under substitution for the implication *)
  Definition mono_cod_implication_stable
             {Γ₁ Γ₂ : C}
             (s : Γ₁ --> Γ₂)
             (xφ yψ : C /m Γ₂)
    : mono_cod_implication (mono_cod_pb PB s xφ) (mono_cod_pb PB s yψ)
      -->
      mono_cod_pb PB s (mono_cod_implication xφ yψ).
  Proof.
    pose (P := PB _ _ _ (mono_cod_mor xφ) s).
    refine (_ · pr1 (mono_cod_right_beck_chevalley _ _ _ _ _ (isPullback_Pullback P) _)).
    refine (#(right_adjoint (mono_cod_dep_prod (PullbackPr2 P))) _).
    use make_mono_cod_fib_mor.
    - use PullbackArrow.
      + use PullbackArrow.
        * exact (PullbackPr1 _ · PullbackPr1 _).
        * exact (PullbackPr2 _ · PullbackPr1 _).
        * abstract
            (rewrite !assoc' ;
             etrans ;
             [ apply maponpaths ;
               apply PullbackSqrCommutes
             | ] ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               apply PullbackSqrCommutes
             | ] ;
             rewrite !assoc' ;
             apply maponpaths ;
             cbn ;
             refine (!_) ;
             apply PullbackSqrCommutes).
      + use PullbackArrow.
        * exact (PullbackPr1 _ · PullbackPr1 _).
        * exact (PullbackPr2 _ · PullbackPr2 _).
        * abstract
            (rewrite !assoc' ;
             etrans ;
             [ apply maponpaths ;
               apply PullbackSqrCommutes
             | ] ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply PullbackSqrCommutes).
      + abstract
          (cbn ;
           rewrite !PullbackArrow_PullbackPr1 ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         use (MorphismsIntoPullbackEqual (isPullback_Pullback P)) ;
         [ rewrite PullbackArrow_PullbackPr1 ;
           apply idpath
         | rewrite PullbackArrow_PullbackPr2 ;
           refine (!_) ;
           apply PullbackSqrCommutes ]).
  Defined.

  (** * 7. The implication *)
  Definition fiberwise_exponentials_mono_cod
    : fiberwise_exponentials (mono_codomain_fiberwise_binproducts PB).
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - apply locally_propositional_mono_cod_disp_cat.
    - exact @mono_cod_implication.
    - exact @mono_cod_implication_intro.
    - exact @mono_cod_implication_elim.
    - exact @mono_cod_implication_stable.
  Defined.
End DependentProductsMonoCodomain.
