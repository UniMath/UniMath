(***************************************************************************************

 The existential quantifier in regular categories

 Suppose that we have a regular category. Then the displayed category of monomorphisms
 has dependent sums. The construction is similar to how dependent sums of morphisms are
 constructed. However, instead of taking the composition, we factorize the composition
 as an epimorphism followed by a monomorphism.

 The main work lies in proving the stability of the existential quantifier under
 pullback. The main steps are described throughout the proof.

 Content
 1. Interpretation of the existential quantifier
 2. Stability
 3. Dependent sums in the displayed category of monomorphisms

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.

Local Open Scope cat.

#[local] Opaque regular_category_epi_mono_factorization.

Section MonoCodomainLeftAdj.
  Context {C : category}
          (HC : is_regular_category C).

  Let PB : Pullbacks C := is_regular_category_pullbacks HC.
  Let HD : cleaving (disp_mono_codomain C) := mono_cod_disp_cleaving PB.

  (** * 1. Interpretation of the existential quantifier *)
  Section ExistentialQuantifier.
    Context {y₁ y₂ : C}
            (f : y₁ --> y₂)
            (xg : C /m y₁).

    Let x : C := mono_cod_dom xg.
    Let g : Monic _ x y₁ := mono_cod_mor xg.

    (**
       The factorization
     *)
    Let im : C
      := pr1 (regular_category_epi_mono_factorization HC (g · f)).

    Let e : x --> im
      := pr12 (regular_category_epi_mono_factorization HC (g · f)).

    Let He : is_strong_epi e
      := is_strong_epi_regular_epi
           (pr1 (pr222 (regular_category_epi_mono_factorization HC (g · f)))).
    Let m : Monic _ im y₂
      := make_Monic _ _ (pr12 (pr222 (regular_category_epi_mono_factorization HC (g · f)))).
    Let p : g · f = e · m
      := pr22 (pr222 (regular_category_epi_mono_factorization HC (g · f))).

    (**
       The existential quantifier
     *)
    Definition mono_codomain_exists
      : C /m y₂
      := make_mono_cod_fib_ob m.

    Definition mono_codomain_exists_intro
      : xg --> mono_cod_pb PB f mono_codomain_exists.
    Proof.
      use make_mono_cod_fib_mor.
      - use (PullbackArrow _ _ e (mono_cod_mor xg)).
        abstract
          (exact (!p)).
      - abstract
          (apply PullbackArrow_PullbackPr2).
    Defined.

    Context {zh : C /m y₂}
            (φ : xg --> mono_cod_pb PB f zh).

    Let z : C := mono_cod_dom zh.
    Let h : Monic _ z y₂ := mono_cod_mor zh.
    Let φf : x --> mono_cod_dom (mono_cod_pb PB f zh) := mono_dom_mor φ.
    Let q : φf · PullbackPr2 _ = g := mono_mor_eq φ.

    Definition mono_codomain_exists_elim
      : mono_codomain_exists --> zh.
    Proof.
      use make_mono_cod_fib_mor.
      - simple refine (pr11 (He _ _ h _ _ _ (MonicisMonic _ h))).
        + exact (φf · PullbackPr1 _).
        + exact m.
        + abstract
            (refine (!p @ !_) ;
             rewrite <- q ;
             rewrite !assoc' ;
             apply maponpaths ;
             apply PullbackSqrCommutes).
      - abstract
          (exact (pr121 (He _ _ h _ _ _ (MonicisMonic _ h)))).
    Defined.
  End ExistentialQuantifier.

  (** * 2. Stability *)
  Section Stability.
    Context {x₁ x₂ x₃ x₄ : C}
            {s₁ : x₂ --> x₁}
            {s₂ : x₃ --> x₁}
            {s₃ : x₄ --> x₃}
            {s₄ : x₄ --> x₂}
            {p : s₄ · s₁ = s₃ · s₂}
            (Hp : isPullback p)
            (yg : C /m x₂).

    (**
       We use the following abbreviations.
     *)
    Let P : Pullback _ _ := make_Pullback _ Hp.
    Let y : C := mono_cod_dom yg.
    Let g : Monic _ y x₂ := mono_cod_mor yg.

    Let Q₁ : Pullback g s₄ := PB x₂ y x₄ g s₄.
    Let f₁ : Q₁ --> x₃ := PullbackPr2 Q₁ · s₃.

    Let im₁ : C := pr1 (regular_category_epi_mono_factorization HC f₁).
    Let e₁ : Q₁ --> im₁
      := pr12 (regular_category_epi_mono_factorization HC f₁).
    Let m₁ : Monic _ im₁ x₃
      := make_Monic _ _ (pr12 (pr222 (regular_category_epi_mono_factorization HC f₁))).
    Let He₁ : is_strong_epi e₁
      := is_strong_epi_regular_epi
           (pr1 (pr222 (regular_category_epi_mono_factorization HC f₁))).
    Let p₁ : f₁ = e₁ · m₁
      := pr22 (pr222 (regular_category_epi_mono_factorization HC f₁)).

    Let f₂ : y --> x₁ := g · s₁.

    Let im₂ : C := pr1 (regular_category_epi_mono_factorization HC f₂).
    Let e₂ : y --> im₂
      := pr12 (regular_category_epi_mono_factorization HC f₂).
    Let m₂ : Monic _ im₂ x₁
      := make_Monic _ _ (pr12 (pr222 (regular_category_epi_mono_factorization HC f₂))).
    Let He₂ : is_regular_epi e₂
      := pr1 (pr222 (regular_category_epi_mono_factorization HC f₂)).
    Let p₂ : f₂ = e₂ · m₂
      := pr22 (pr222 (regular_category_epi_mono_factorization HC f₂)).

    Let Q₂ : Pullback m₂ s₂ := PB x₁ im₂ x₃ m₂ s₂.
    Let Q₃ := PB x₁ y x₃ (g · s₁) s₂.

    (**
       To show that dependent sums are stable under pullback in the displayed category
       of all arrows, we use the following morphism. We also use it here.
     *)
    Local Definition mono_cod_left_beck_chevalley_mor_inv
      : Q₃ --> Q₁.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - use (PullbackArrow P).
        + exact (PullbackPr1 _ · g).
        + exact (PullbackPr2 _).
        + abstract
            (cbn ;
             rewrite !assoc' ;
             apply PullbackSqrCommutes).
      - abstract
          (exact (!(PullbackArrow_PullbackPr1 P _ _ _ _))).
    Defined.

    (**
       The key idea in the proof is showing that we have a regular epimorphism from
       the pullback `Q₃` to `Q₁`. This permits us to use the lifting property of
       regular epimorphisms.
     *)
    Local Definition map_between_pbs
      : Q₃ --> Q₂.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _ · e₂).
      - exact (PullbackPr2 _).
      - abstract
          (rewrite !assoc' ;
           rewrite <- p₂ ;
           apply PullbackSqrCommutes).
    Defined.

    (**
       To show that this map is a regular epimorphism, we construct a pullback square
       such that the side opposite to `map_between_pbs` is a regular epimorphism. Then
       by stability of regular epimorphisms (`C` is a regular category), we obtain that
       this morphism is a regular epimorphism.
     *)
    Local Lemma map_between_pbs_eq
      : PullbackPr1 Q₃ · e₂ = map_between_pbs · PullbackPr1 _.
    Proof.
      unfold map_between_pbs.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    Qed.

    Section UMP.
      Context {w : C}
              {h : w --> y}
              {k : w --> Q₂}
              (r : h · e₂ = k · PullbackPr1 Q₂).

      Local Lemma is_pb_square_mor_unique
        : isaprop (∑ hk, hk · PullbackPr1 Q₃ = h × hk · map_between_pbs = k).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback Q₃)).
        - exact (pr12 ζ₁ @ !(pr12 ζ₂)).
        - pose (maponpaths (λ z, z · PullbackPr2 _) (pr22 ζ₁ @ !(pr22 ζ₂))) as q.
          cbn in q.
          unfold map_between_pbs in q.
          rewrite !assoc' in q.
          rewrite !PullbackArrow_PullbackPr2 in q.
          exact q.
      Qed.

      Local Definition is_pb_square_mor
        : w --> Q₃.
      Proof.
        use PullbackArrow.
        - exact h.
        - exact (k · PullbackPr2 _).
        - abstract
            (rewrite !assoc' ;
             rewrite <- PullbackSqrCommutes ;
             rewrite !assoc ;
             rewrite <- r ;
             rewrite !assoc' ;
             rewrite <- p₂ ;
             apply idpath).
      Defined.

      Local Lemma is_pb_square_mor_pr2
        : is_pb_square_mor · map_between_pbs = k.
      Proof.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback Q₂)).
        - refine (assoc' _ _ _ @ _).
          unfold map_between_pbs, is_pb_square_mor.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          exact r.
        - refine (assoc' _ _ _ @ _).
          unfold map_between_pbs, is_pb_square_mor.
          rewrite !PullbackArrow_PullbackPr2.
          apply idpath.
      Qed.
    End UMP.

    Local Definition is_pb_square
      : isPullback map_between_pbs_eq.
    Proof.
      intros w h k r.
      use iscontraprop1.
      - apply is_pb_square_mor_unique.
      - simple refine (_ ,, _ ,, _).
        + exact (is_pb_square_mor r).
        + abstract
            (apply PullbackArrow_PullbackPr1).
        + apply is_pb_square_mor_pr2.
    Defined.

    Local Lemma is_strong_epi_map_between_pbs
      : is_strong_epi map_between_pbs.
    Proof.
      use is_strong_epi_regular_epi.
      exact (is_regular_category_regular_epi_pb_stable
               HC
               _ _ _ _ _ _ _ _ _
               is_pb_square
               He₂).
    Qed.

    (**
       Now we consider the following square

<<
                                 e₁
        Q₃ -------------> Q₁ --------> im₁
        |                              |
        |                              | m₁
        |                              |
        V                              V
        Q₂ --------------------------> x₃
>>

       The map `Q₁ --> Q₂` is `map_between_pbs`, which is a regular
       epimorphism. The map `Q₂ --> x₃` is a pullback projection, and
       `mono_cod_left_beck_chevalley_mor_inv` is the moprhism from `Q₃`
       to `Q₁`. By showing that this diagram commutes, we can use the
       lifting property of regular epimorphisms with respect to
       monomorphism to obtain a map `Q₂ --> im₁` making the triangles
       commute. From this we can directly conclude the stability under
       pullback of existential quantification.
     *)
    Local Lemma mono_codomain_exists_stable_mor_eq
      : map_between_pbs · PullbackPr2 _
        =
        mono_cod_left_beck_chevalley_mor_inv · e₁ · m₁.
    Proof.
      rewrite !assoc'.
      rewrite <- p₁.
      unfold f₁.
      rewrite !assoc.
      unfold map_between_pbs, mono_cod_left_beck_chevalley_mor_inv.
      rewrite !PullbackArrow_PullbackPr2.
      refine (!_).
      apply (PullbackArrow_PullbackPr2 P).
    Qed.

    Definition mono_codomain_exists_stable_mor
      : Q₂ --> im₁
      := pr11 (is_strong_epi_map_between_pbs
                 _ _ _ _ _
                 mono_codomain_exists_stable_mor_eq
                 (MonicisMonic _ m₁)).

    Definition mono_codomain_exists_stable
      : mono_cod_pb PB s₂ (mono_codomain_exists s₁ yg)
        -->
        mono_codomain_exists s₃ (mono_cod_pb PB s₄ yg).
    Proof.
      use make_mono_cod_fib_mor.
      - exact mono_codomain_exists_stable_mor.
      - abstract
          (apply (pr121 (is_strong_epi_map_between_pbs _ _ _ _ _ _ (MonicisMonic _ _)))).
    Defined.
  End Stability.

  (** 3. Dependent sums in the displayed category of monomorphisms *)
  Definition mono_codomain_has_dependent_sums
    : has_dependent_sums HD.
  Proof.
    use make_has_dependent_sums_poset.
    - apply locally_propositional_mono_cod_disp_cat.
    - exact (λ y₁ y₂ f xg, mono_codomain_exists f xg).
    - exact (λ y₁ y₂ f xg, mono_codomain_exists_intro f xg).
    - intros.
      apply mono_codomain_exists_elim.
      exact p.
    - intros x₁ x₂ x₃ x₄ s₁ s₂ s₃ s₄ p Hp yg.
      exact (mono_codomain_exists_stable Hp yg).
  Defined.
End MonoCodomainLeftAdj.
