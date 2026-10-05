Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.OrderTheory.Lattice.DerivedLawsCompleteHeyting.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ExamplesSites.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HValuedSets.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.

Local Open Scope heyting.
Local Open Scope cat.

Section HValuedSetsVersusSheaves.
  Context (H : complete_heyting_algebra).

  Let C : site := cha_to_site H.

  Proposition cha_sheaf_le_eq
              {F : sheaf C}
              {ω₁ ω₂ : H}
              (p q : ω₁ ≤ ω₂)
              (x : (F ω₂ : hSet))
    : #F p x = #F q x.
  Proof.
    apply maponpaths_2.
    apply propproperty.
  Qed.

  Proposition cha_sheaf_le_trans
              {F : sheaf C}
              {ω₁ ω₂ ω₃ ω₄ : H}
              (x : (F ω₁ : hSet))
              (y : (F ω₂ : hSet))
              {px : ω₃ ≤ ω₁}
              {py : ω₃ ≤ ω₂}
              (q : ω₄ ≤ ω₃)
              (rx : ω₄ ≤ ω₁)
              (ry : ω₄ ≤ ω₂)
              (eq : #F px x = #F py y)
    : #F rx x = #F ry y.
  Proof.
    refine (_ @ maponpaths (#F q) eq @ _).
    - refine (_ @ eqtohomot (functor_comp F _ _) _).
      apply cha_sheaf_le_eq.
    - refine (!(eqtohomot (functor_comp F _ _) _) @ _).
      apply cha_sheaf_le_eq.
  Qed.

  Definition cha_sheaf_rel
             {F : sheaf C}
             {ω₁ ω₂ : H}
             (x : (F ω₁ : hSet))
             (y : (F ω₂ : hSet))
    : H
    := \/_{ z : ∑ (ωm : H) (p : ωm ≤ ω₁) (q : ωm ≤ ω₂), #F p x = #F q y} pr1 z.

  Proposition cha_sheaf_rel_partial_refl
              {F : sheaf C}
              {ω : H}
              (x : (F ω : hSet))
    : ω = cha_sheaf_rel x x.
  Proof.
    unfold cha_sheaf_rel.
    use cha_le_antisymm.
    - use cha_le_lub.
      + simple refine (ω ,, _ ,, _ ,, _).
        * apply cha_le_refl.
        * apply cha_le_refl.
        * cbn.
          apply idpath.
      + cbn.
        apply cha_le_refl.
    - use cha_lub_le.
      intros ( ωm & p & q & r ).
      cbn.
      exact p.
  Qed.

  Proposition cha_sheaf_rel_sym
              {F : sheaf C}
              {ω₁ ω₂ : H}
              (x : (F ω₁ : hSet))
              (y : (F ω₂ : hSet))
    : cha_sheaf_rel x y = cha_sheaf_rel y x.
  Proof.
    unfold cha_sheaf_rel.
    use cha_le_antisymm.
    - use cha_lub_le.
      cbn.
      intros ( ωm & p & q & r).
      cbn.
      use cha_le_lub.
      + refine (ωm ,, q ,, p ,, _).
        exact (!r).
      + cbn.
        apply cha_le_refl.
    - use cha_lub_le.
      cbn.
      intros ( ωm & p & q & r).
      cbn.
      use cha_le_lub.
      + refine (ωm ,, q ,, p ,, _).
        exact (!r).
      + cbn.
        apply cha_le_refl.
  Qed.

  Proposition cha_sheaf_rel_trans
              {F : sheaf C}
              {ω₁ ω₂ ω₃ : H}
              (x : (F ω₁ : hSet))
              (y : (F ω₂ : hSet))
              (z : (F ω₃ : hSet))
    : (cha_sheaf_rel x y ∧ cha_sheaf_rel y z) ≤ cha_sheaf_rel x z.
  Proof.
    unfold cha_sheaf_rel.
    rewrite cha_frobenius.
    use cha_lub_le.
    intros ( ωm₁ & p₁ & p₂ & p₃ ).
    cbn.
    rewrite cha_min_comm.
    rewrite cha_frobenius.
    use cha_lub_le.
    intros ( ωm₂ & q₁ & q₂ & q₃ ).
    cbn.
    use cha_le_lub.
    - simple refine ((ωm₁ ∧ ωm₂) ,, _ ,, _ ,, _).
      + refine (cha_le_trans _ q₁).
        exact (cha_min_le_r _ _).
      + refine (cha_le_trans _ p₂).
        exact (cha_min_le_l _ _).
      + cbn.
        etrans.
        {
          exact (eqtohomot (functor_comp F _ _) _).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          exact q₃.
        }
        refine (!(eqtohomot (functor_comp F _ _) _) @ _).
        refine (!_).
        etrans.
        {
          exact (eqtohomot (functor_comp F _ _) _).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (!p₃).
        }
        refine (!(eqtohomot (functor_comp F _ _) _) @ _).
        cbn.
        apply cha_sheaf_le_eq.
    - cbn.
      apply cha_le_refl.
  Qed.

  Definition sheaf_to_h_valued_set
             (F : sheaf C)
    : h_valued_set H.
  Proof.
    use make_h_valued_set.
    - exact (∑ (ω : H), F ω)%set.
    - exact (λ ωx ωy, cha_sheaf_rel (pr2 ωx) (pr2 ωy)).
    - exact (λ x y, cha_sheaf_rel_sym (pr2 x) (pr2 y)).
    - exact (λ x y z, cha_sheaf_rel_trans (pr2 x) (pr2 y) (pr2 z)).
  Defined.

  Definition cha_nat_trans_to_rel
             {F G : sheaf C}
             (τ : sheaf_nat_trans F G)
             {ω₁ ω₂ : H}
             (x : (F ω₁ : hSet))
             (y : (G ω₂ : hSet))
    : H
    := \/_{ z : ∑ (ωm : H) (p : ωm ≤ ω₁) (q : ωm ≤ ω₂), #G p (τ _ x) = #G q y } pr1 z.

  Proposition cha_nat_trans_to_rel_dom
              {F G : sheaf C}
              (τ : sheaf_nat_trans F G)
              {ω₁ ω₂ : H}
              (x : (F ω₁ : hSet))
              (y : (G ω₂ : hSet))
    : cha_nat_trans_to_rel τ x y ≤ cha_sheaf_rel x x.
  Proof.
    unfold cha_nat_trans_to_rel, cha_sheaf_rel.
    use cha_lub_le.
    intros ( ωm & p & q & r ).
    cbn.
    use cha_le_lub.
    - simple refine (ωm ,, _ ,, _ ,, _).
      + exact p.
      + exact p.
      + cbn.
        apply idpath.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition cha_nat_trans_to_rel_cod
              {F G : sheaf C}
              (τ : sheaf_nat_trans F G)
              {ω₁ ω₂ : H}
              (x : (F ω₁ : hSet))
              (y : (G ω₂ : hSet))
    : cha_nat_trans_to_rel τ x y ≤ cha_sheaf_rel y y.
  Proof.
    unfold cha_nat_trans_to_rel, cha_sheaf_rel.
    use cha_lub_le.
    intros ( ωm & p & q & r ).
    cbn.
    use cha_le_lub.
    - simple refine (ωm ,, _ ,, _ ,, _).
      + exact q.
      + exact q.
      + cbn.
        apply idpath.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition cha_nat_trans_to_rel_eq
              {F G : sheaf C}
              (τ : sheaf_nat_trans F G)
              {ω₁ ω₁' ω₂ ω₂' : H}
              (x : (F ω₁ : hSet))
              (x' : (F ω₁' : hSet))
              (y : (G ω₂ : hSet))
              (y' : (G ω₂' : hSet))
    : (cha_sheaf_rel x x' ∧ cha_sheaf_rel y y' ∧ cha_nat_trans_to_rel τ x y)
      ≤
      cha_nat_trans_to_rel τ x' y'.
  Proof.
    unfold cha_nat_trans_to_rel, cha_sheaf_rel.
    rewrite !cha_frobenius.
    use cha_lub_le.
    intros ( ζ₁ & p₁ & q₁ & r₁ ).
    cbn.
    rewrite cha_min_comm.
    rewrite cha_frobenius.
    use cha_lub_le.
    intros ( ζ₂ & p₂ & q₂ & r₂ ).
    cbn.
    rewrite cha_min_assoc.
    rewrite cha_min_comm.
    rewrite cha_frobenius.
    use cha_lub_le.
    intros ( ζ₃ & p₃ & q₃ & r₃ ).
    cbn.
    use cha_le_lub.
    - simple refine (((ζ₁ ∧ ζ₂) ∧ ζ₃) ,, _ ,, _ ,, _).
      + refine (cha_le_trans _ q₂).
        refine (cha_le_trans (cha_min_le_l _ _) _).
        exact (cha_min_le_r _ _).
      + refine (cha_le_trans _ q₃).
        exact (cha_min_le_r _ _).
      + cbn.
        refine (_ @ eqtohomot (!(functor_comp G _ _)) _).
        cbn.
        rewrite <- r₃.
        clear r₃.
        refine (eqtohomot (functor_comp G _ _) _ @ _).
        cbn.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (eqtohomot (nat_trans_ax τ _ _ q₂) x').
        }
        cbn.
        rewrite <- r₂.
        refine (_ @ eqtohomot (functor_comp G _ _) _).
        cbn.
        refine (!_).
        etrans.
        {
          refine (cha_sheaf_le_trans _ _ _ _ _ (!r₁)).
          {
            refine (cha_le_trans (cha_min_le_l _ _) _).
            exact (cha_min_le_l _ _).
          }
          refine (cha_le_trans _ p₁).
          refine (cha_le_trans (cha_min_le_l _ _) _).
          exact (cha_min_le_l _ _).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (eqtohomot (nat_trans_ax τ _ _ p₂) x).
        }
        cbn.
        refine (!(eqtohomot (functor_comp G _ _) _) @ _).
        cbn.
        apply cha_sheaf_le_eq.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition cha_nat_trans_to_rel_unique
              {F G : sheaf C}
              (τ : sheaf_nat_trans F G)
              {ω₁ ω₂ ω₂' : H}
              (x : (F ω₁ : hSet))
              (y : (G ω₂ : hSet))
              (y' : (G ω₂' : hSet))
    : (cha_nat_trans_to_rel τ x y ∧ cha_nat_trans_to_rel τ x y')
       ≤
       cha_sheaf_rel y y'.
  Proof.
    unfold cha_nat_trans_to_rel, cha_sheaf_rel.
    rewrite !cha_frobenius.
    use cha_lub_le.
    intros ( ζ₁ & p₁ & q₁ & r₁ ).
    cbn.
    rewrite cha_min_comm.
    rewrite cha_frobenius.
    use cha_lub_le.
    intros ( ζ₂ & p₂ & q₂ & r₂ ).
    cbn.
    use cha_le_lub.
    - simple refine ((ζ₁ ∧ ζ₂) ,, _ ,, _ ,, _).
      + refine (cha_le_trans _ q₂).
        exact (cha_min_le_r _ _).
      + refine (cha_le_trans _ q₁).
        exact (cha_min_le_l _ _).
      + refine (eqtohomot (functor_comp G _ _) _ @ _).
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (!r₂).
        }
        cbn.
        refine (_ @ eqtohomot (!(functor_comp G _ _)) _).
        cbn.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!r₁).
        }
        cbn.
        refine (eqtohomot (!(functor_comp G _ _)) _ @ _).
        refine (_ @ eqtohomot (functor_comp G _ _) _).
        cbn.
        apply cha_sheaf_le_eq.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition cha_nat_trans_to_rel_im
              {F G : sheaf C}
              (τ : sheaf_nat_trans F G)
              {ω : H}
              (x : (F ω : hSet))
    : cha_sheaf_rel x x
      ≤
      \/_{ y : ∑ (x : H), (G x : hSet) } (cha_nat_trans_to_rel τ x (pr2 y)).
  Proof.
    unfold cha_nat_trans_to_rel, cha_sheaf_rel.
    use cha_lub_le.
    intros ( ωm & p & q & r ).
    cbn.
    use cha_le_lub.
    - exact (ω ,, τ ω x).
    - cbn.
      use cha_le_lub.
      + refine (ωm ,, p ,, p ,, _).
        apply idpath.
      + cbn.
        apply cha_le_refl.
  Qed.

  Definition nat_trans_to_h_valued_morphism
             {F G : sheaf C}
             (τ : sheaf_nat_trans F G)
    : h_valued_morphism
        H
        (sheaf_to_h_valued_set F)
        (sheaf_to_h_valued_set G).
  Proof.
    use make_h_valued_morphism.
    - exact (λ ωx ωy, cha_nat_trans_to_rel τ (pr2 ωx) (pr2 ωy)).
    - exact (λ ωx ωy, cha_nat_trans_to_rel_dom τ (pr2 ωx) (pr2 ωy)).
    - exact (λ ωx ωy, cha_nat_trans_to_rel_cod τ (pr2 ωx) (pr2 ωy)).
    - exact (λ ωx₁ ωx₂ ωy₁ ωy₂,
             cha_nat_trans_to_rel_eq τ (pr2 ωx₁) (pr2 ωx₂) (pr2 ωy₁) (pr2 ωy₂)).
    - exact (λ ωx ωy₁ ωy₂, cha_nat_trans_to_rel_unique τ (pr2 ωx) (pr2 ωy₁) (pr2 ωy₂)).
    - exact (λ ωx, cha_nat_trans_to_rel_im τ (pr2 ωx)).
  Defined.


  Definition sheaf_to_h_valued_set_functor_data
    : functor_data (cat_of_sheaves C) (topos_of_h_valued_sets H).
  Proof.
    use make_functor_data.
    - exact sheaf_to_h_valued_set.
    - exact (λ _ _ τ, nat_trans_to_h_valued_morphism τ).
  Defined.

  Proposition sheaf_to_h_valued_set_functor_laws
    : is_functor sheaf_to_h_valued_set_functor_data.
  Proof.
    split.
    - intros F.
      use h_valued_morphism_eq.
      + intros ( ω₁ & x ) ( ω₂ & y ) ; cbn.
        unfold cha_nat_trans_to_rel, cha_sheaf_rel.
        cbn.
        use cha_lub_le.
        intros ( ωm & p & q & r ).
        cbn.
        use cha_le_lub.
        * simple refine (_ ,, _ ,, _ ,, _).
          ** exact ωm.
          ** exact p.
          ** exact q.
          ** cbn.
             exact r.
        * cbn.
          apply cha_le_refl.
      + intros ( ω₁ & x ) ( ω₂ & y ) ; cbn.
        unfold cha_nat_trans_to_rel, cha_sheaf_rel.
        cbn.
        use cha_lub_le.
        intros ( ωm & p & q & r ).
        cbn.
        use cha_le_lub.
        * simple refine (_ ,, _ ,, _ ,, _).
          ** exact ωm.
          ** exact p.
          ** exact q.
          ** cbn.
             exact r.
        * cbn.
          apply cha_le_refl.
    - refine (λ (F₁ F₂ F₃ : sheaf C)
                (τ₁ : sheaf_nat_trans F₁ F₂)
                (τ₂ : sheaf_nat_trans F₂ F₃), _).
      use h_valued_morphism_eq.
      + intros ( ω₁ & x ) ( ω₂ & y ) ; cbn.
        unfold cha_nat_trans_to_rel, cha_sheaf_rel.
        cbn.
        use cha_lub_le.
        intros ( ωm & p & q & r ).
        cbn.
        use cha_le_lub.
        * simple refine (((_ ,, _) ,, _) ,, _).
          ** exact (ω₁ ,, x).
          ** exact (ω₂ ,, y).
          ** exact (ω₁ ,, τ₁ ω₁ x).
          ** cbn.
             apply idpath.
        * cbn.
          rewrite cha_frobenius.
          use cha_le_lub.
          ** refine (ωm ,, p ,, q ,, _).
             exact r.
          ** cbn.
             use cha_min_le_case ; [ | apply cha_le_refl ].
             use cha_le_lub.
             *** refine (ωm ,, p ,, p ,, _).
                 apply idpath.
             *** cbn.
                 apply cha_le_refl.
      + intros ( ω₁ & x ) ( ω₂ & y ) ; cbn.
        unfold cha_nat_trans_to_rel, cha_sheaf_rel.
        cbn.
        use cha_lub_le.
        intros i.
        induction i as [ i p ].
        cbn.
        induction i as [ [ z₁ z₂ ] z₃ ].
        cbn.
        induction z₁ as [ ωm₁ z₁ ].
        cbn.
        induction z₂ as [ ωm₂ z₂ ].
        induction z₃ as [ ωm₃ z₃ ].
        cbn in p.
        pose proof (p₁ := base_paths _ _ (maponpaths dirprod_pr1 p)).
        pose proof (p₂ := fiber_paths (maponpaths dirprod_pr1 p)).
        pose proof (p₃ := base_paths _ _ (maponpaths dirprod_pr2 p)).
        pose proof (p₄ := fiber_paths (maponpaths dirprod_pr2 p)).
        cbn in p₁, p₂, p₃, p₄.
        induction p₁, p₃.
        assert (z₁ = x) as q.
        {
          refine (_ @ p₂).
          refine (!_).
          use (transportf_set (λ z, (F₁ z : hSet))).
          cbn.
          apply setproperty.
        }
        induction q.
        assert (z₂ = y) as q.
        {
          refine (_ @ p₄).
          refine (!_).
          use (transportf_set (λ z, (F₃ z : hSet))).
          cbn.
          apply setproperty.
        }
        induction q.
        clear p p₂ p₄.
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ζ₁ & p₁ & q₁ & r₁ ).
        cbn.
        rewrite cha_min_comm.
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ζ₂ & p₂ & q₂ & r₂ ).
        cbn in p₁, q₁, r₁.
        cbn.
        use cha_le_lub.
        * simple refine ((ζ₁ ∧ ζ₂) ,, _ ,, _ ,, _).
          ** refine (cha_le_trans _ p₂).
             apply cha_min_le_r.
          ** refine (cha_le_trans _ q₁).
             apply cha_min_le_l.
          ** cbn.
             refine (eqtohomot (functor_comp F₃ _ _) _ @ _).
             cbn.
             etrans.
             {
               apply maponpaths.
               exact (eqtohomot (!(nat_trans_ax τ₂ _ _ p₂)) _).
             }
             cbn.
             etrans.
             {
               do 2 apply maponpaths.
               exact r₂.
             }
             cbn.
             etrans.
             {
               apply maponpaths.
               exact (eqtohomot (nat_trans_ax τ₂ _ _ q₂) z₃).
             }
             cbn.
             refine (eqtohomot (!(functor_comp F₃ _ _)) _ @ _).
             refine (!_).
             refine (eqtohomot (functor_comp F₃ _ _) _ @ _).
             cbn.
             etrans.
             {
               apply maponpaths.
               exact (!r₁).
             }
             cbn.
             refine (eqtohomot (!(functor_comp F₃ _ _)) _ @ _).
             cbn.
             apply cha_sheaf_le_eq.
        * cbn.
          apply cha_le_refl.
  Qed.

  Definition sheaf_to_h_valued_set_functor
    : cat_of_sheaves C ⟶ topos_of_h_valued_sets H.
  Proof.
    use make_functor.
    - exact sheaf_to_h_valued_set_functor_data.
    - exact sheaf_to_h_valued_set_functor_laws.
  Defined.


  Section EqFromSheaf.
    Context {F : sheaf C}
            {ω : H}
            (x y : (F ω : hSet))
            (p : ω ≤ cha_sheaf_rel x y).

    Definition cha_sheaf_rel_to_eq_sieve
      : sieve (ω : C).
    Proof.
      use make_sieve.
      - exact (λ ω' q, #F q x = #F q y)%logic.
      - abstract
          (cbn ;
           intros ω₁ ω₂ q₁ q₂ q₃ r₁ r₂ ;
           induction r₁ ;
           refine (_ @ eqtohomot (!(functor_comp F _ _)) _) ;
           refine (eqtohomot (functor_comp F _ _) _ @ _) ;
           cbn ;
           apply maponpaths ;
           exact r₂).
    Defined.

    Proposition cha_sheaf_rel_to_eq_covers
      : cha_sieve_covers H cha_sheaf_rel_to_eq_sieve.
    Proof.
      unfold cha_sieve_covers.
      refine (cha_le_trans p _).
      use cha_lub_le.
      intros ( ωm & q₁ & q₂ & q₃ ).
      cbn.
      use cha_le_lub.
      - refine (ωm ,, q₁ ,, _).
        cbn.
        refine (q₃ @ _).
        apply cha_sheaf_le_eq.
      - cbn.
        apply cha_le_refl.
    Qed.

    Definition cha_sheaf_rel_to_eq_matching_family
      : matching_family F cha_sheaf_rel_to_eq_sieve.
    Proof.
      use make_matching_family.
      - exact (λ ω' q r, #F q x).
      - abstract
          (cbn ;
           intros ω' ω'' q₁ q₂ q₃ eq r₁ r₂ ;
           induction eq ;
           induction r₂ ;
           exact (eqtohomot (!(functor_comp F _ _)) _)).
    Defined.

    Proposition cha_sheaf_rel_to_eq
      : x = y.
    Proof.
      use (sheaf_amalgamation_unique (is_sheaf_sheaf F) cha_sheaf_rel_to_eq_covers).
      - exact cha_sheaf_rel_to_eq_matching_family.
      - cbn.
        intros.
        apply idpath.
      - cbn.
        intros ω' q r.
        exact (!r).
    Qed.
  End EqFromSheaf.

  Section Fullness.
    Context {F₁ F₂ : sheaf C}
            (τ : h_valued_morphism
                   H
                   (sheaf_to_h_valued_set F₁)
                   (sheaf_to_h_valued_set F₂)).

    Definition sheaf_h_valued_morphism_el
               {ω₁ ω₂ : H}
               (x : (F₁ ω₁ : hSet))
               (y : (F₂ ω₂ : hSet))
      : H
      := τ (ω₁ ,, x) (ω₂ ,, y).

    Section Amalgamation.
      Context {ω : H}
              (x : (F₁ ω : hSet)).

      Proposition h_valued_morphism_to_nat_trans_unique
                  {ω' : H}
                  {p : ω' ≤ ω}
                  {y₁ y₂ : (F₂ ω' : hSet)}
                  (q₁ : ω' ≤ sheaf_h_valued_morphism_el (#F₁ p x) y₁)
                  (q₂ : ω' ≤ sheaf_h_valued_morphism_el (#F₁ p x) y₂)
        : y₁ = y₂.
      Proof.
        use cha_sheaf_rel_to_eq.
        - refine (cha_le_trans
                    _
                    (h_valued_morphism_unique_im H τ (ω ,, x) (ω' ,, y₁) (ω' ,, y₂))).
          use cha_min_le_case.
          + refine (cha_le_trans q₁ _).
            unfold sheaf_h_valued_morphism_el.
            pose (h_valued_morphism_eq_defined
                    H τ
                    (ω' ,, #F₁ p x) (ω ,, x)
                    (ω' ,, y₁) (ω' ,, y₁))
              as r.
            refine (cha_le_trans _ r).
            clear r.
            cbn.
            repeat use cha_min_le_case.
            * refine (cha_le_trans
                        (h_valued_morphism_dom_defined H τ _ _)
                        _).
              cbn.
              use cha_lub_le.
              intros ( ωm & r₁ & r₂ & r₃).
              cbn.
              use cha_le_lub.
              ** refine (ωm ,, r₁ ,, cha_le_trans r₁ p ,, _).
                 exact (!(eqtohomot (functor_comp F₁ _ _) _)).
              ** cbn.
                 apply cha_le_refl.
            * exact (h_valued_morphism_cod_defined H τ _ _).
            * apply cha_le_refl.
          + refine (cha_le_trans q₂ _).
            unfold sheaf_h_valued_morphism_el.
            pose (h_valued_morphism_eq_defined
                    H τ
                    (ω' ,, #F₁ p x) (ω ,, x)
                    (ω' ,, y₂) (ω' ,, y₂))
              as r.
            refine (cha_le_trans _ r).
            clear r.
            cbn.
            repeat use cha_min_le_case.
            * refine (cha_le_trans
                        (h_valued_morphism_dom_defined H τ _ _)
                        _).
              cbn.
              use cha_lub_le.
              intros ( ωm & r₁ & r₂ & r₃).
              cbn.
              use cha_le_lub.
              ** refine (ωm ,, r₁ ,, cha_le_trans r₁ p ,, _).
                 exact (!(eqtohomot (functor_comp F₁ _ _) _)).
              ** cbn.
                 apply cha_le_refl.
            * exact (h_valued_morphism_cod_defined H τ _ _).
            * apply cha_le_refl.
      Qed.

      Definition h_valued_morphism_to_nat_trans_rel
                 (ω' : H)
                 (p : ω' ≤ ω)
        : hProp.
      Proof.
        use make_hProp.
        - exact (∑ (y : (F₂ ω' : hSet)), ω' ≤ sheaf_h_valued_morphism_el (#F₁ p x) y).
        - abstract
            (use invproofirrelevance ;
             intros yq₁ yq₂ ;
             use subtypePath_prop ;
             exact (h_valued_morphism_to_nat_trans_unique (pr2 yq₁) (pr2 yq₂))).
      Defined.

      Proposition h_valued_morphism_to_nat_trans_closed
                  {ω' ω'' : H}
                  (p : ω' ≤ ω)
                  (q : ω'' ≤ ω')
                  (r : h_valued_morphism_to_nat_trans_rel ω' p)
        : h_valued_morphism_to_nat_trans_rel ω'' (cha_le_trans q p).
      Proof.
        induction r as [ y r ].
        refine (#F₂ q y ,, _).
        unfold sheaf_h_valued_morphism_el in *.
        pose (h_valued_morphism_eq_defined
                H τ
                (ω' ,, #F₁ p x)
                (ω'' ,, #F₁ (cha_le_trans q p) x)  (ω' ,, y) (ω'' ,, # F₂ q y))
          as le.
        refine (cha_le_trans _ le).
        cbn.
        repeat use cha_min_le_case.
        - unfold cha_sheaf_rel.
          use cha_le_lub.
          + refine (ω'' ,, q ,, cha_le_refl _ ,, _).
            refine (eqtohomot (!(functor_comp F₁ _ _)) _ @ _).
            refine (_ @ eqtohomot (functor_comp F₁ _ _) _).
            apply cha_sheaf_le_eq.
          + cbn.
            apply cha_le_refl.
        - unfold cha_sheaf_rel.
          use cha_le_lub.
          + refine (ω'' ,, q ,, cha_le_refl _ ,, _).
            refine (_ @ eqtohomot (functor_comp F₂ _ _) _).
            apply cha_sheaf_le_eq.
          + cbn.
            apply cha_le_refl.
        - refine (cha_le_trans _ r).
          exact q.
      Qed.

      Definition h_valued_morphism_to_nat_trans_sieve
        : sieve (ω : C).
      Proof.
        use make_cha_sieve.
        - exact h_valued_morphism_to_nat_trans_rel.
        - intros ω' ω'' p q.
          exact (h_valued_morphism_to_nat_trans_closed p q).
      Defined.

      Definition h_valued_morphism_to_nat_trans_sieve_covers
        : cha_sieve_covers H h_valued_morphism_to_nat_trans_sieve.
      Proof.
        unfold cha_sieve_covers.
        refine (cha_le_trans _ _).
        {
          use cha_eq_to_refl.
          refine (!_).
          refine (cha_min_le_eq_l (h_valued_morphism_hom_exists _ τ (ω ,, x)) @ _).
          cbn.
          exact (!(cha_sheaf_rel_partial_refl x)).
        }
        cbn.
        refine (cha_le_trans _ _).
        {
          use cha_eq_to_refl.
          apply maponpaths_2.
          exact (!(cha_sheaf_rel_partial_refl x)).
        }
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ω' & y ).
        use cha_le_lub.
        - unfold cha_sieve_fam.
          cbn.
          simple refine (_ ,, _ ,, _ ,, _).
          + exact (ω ∧ sheaf_h_valued_morphism_el x y).
          + apply cha_min_le_l.
          + refine (#F₂ _ y).
            abstract
              (refine (cha_le_trans (cha_min_le_r _ _) _) ;
               refine (cha_le_trans (h_valued_morphism_cod_defined H τ _ _) _) ;
               cbn ;
               use cha_eq_to_refl ;
               exact (!(cha_sheaf_rel_partial_refl y))).
          + cbn.
            refine (cha_le_trans
                      _
                      (h_valued_morphism_eq_defined
                         H τ
                         (ω ,, x) _
                         (ω' ,, y) _)).
            cbn.
            repeat use cha_min_le_case.
            * refine (cha_le_trans _ _).
              {
                use cha_eq_to_refl.
                apply maponpaths.
                refine (!_).
                exact (cha_min_le_eq_l (h_valued_morphism_dom_defined H τ _ _)).
              }
              cbn.
              unfold cha_sheaf_rel.
              rewrite !cha_frobenius.
              use cha_lub_le.
              intros ( ωm & p & q & r ).
              cbn.
              use cha_le_lub.
              ** simple refine (_ ,, _ ,, _ ,, _).
                 *** exact (ω ∧ τ (ω ,, x) (ω' ,, y) ∧ ωm).
                 *** apply cha_min_le_l.
                 *** use cha_min_le_case.
                     {
                       apply cha_min_le_l.
                     }
                     refine (cha_le_trans (cha_min_le_r _ _) _).
                     apply cha_min_le_l.
                 *** cbn.
                     refine (_ @ eqtohomot (functor_comp F₁ _ _) _).
                     apply cha_sheaf_le_eq.
              ** cbn.
                 apply cha_le_refl.
            * refine (cha_le_trans _ _).
              {
                use cha_eq_to_refl.
                apply maponpaths.
                refine (!_).
                exact (cha_min_le_eq_l (h_valued_morphism_cod_defined H τ _ _)).
              }
              cbn.
              unfold cha_sheaf_rel.
              rewrite !cha_frobenius.
              use cha_lub_le.
              intros ( ωm & p & q & r ).
              cbn.
              use cha_le_lub.
              ** simple refine (_ ,, _ ,, _ ,, _).
                 *** exact (ω ∧ τ (ω ,, x) (ω' ,, y) ∧ ωm).
                 *** refine (cha_le_trans _ p).
                     refine (cha_le_trans (cha_min_le_r _ _) _).
                     apply cha_min_le_r.
                 *** use cha_min_le_case.
                     {
                       apply cha_min_le_l.
                     }
                     refine (cha_le_trans (cha_min_le_r _ _) _).
                     apply cha_min_le_l.
                 *** cbn.
                     refine (_ @ eqtohomot (functor_comp F₂ _ _) _).
                     apply cha_sheaf_le_eq.
              ** cbn.
                 apply cha_le_refl.
            * apply cha_min_le_r.
        - cbn.
          apply cha_le_refl.
      Qed.

      Proposition h_valued_morphism_to_nat_trans_matching_family_laws
                  {ω'' ω' : H}
                  {p₂ : ω' ≤ ω}
                  {p₃ : ω'' ≤ ω'}
                  {y₁ : (F₂ ω'' : hSet)}
                  (q₁ : ω'' ≤ sheaf_h_valued_morphism_el (#F₁ (cha_le_trans p₃ p₂) x) y₁)
                  {y₂ : (F₂ ω' : hSet)}
                  (q₂ : ω' ≤ sheaf_h_valued_morphism_el (#F₁ p₂ x) y₂)
        : # F₂ p₃ y₂ = y₁.
      Proof.
        use cha_sheaf_rel_to_eq.
        pose (h_valued_morphism_unique_im H τ (ω ,, x) (ω'' ,, # F₂ p₃ y₂) (ω'' ,, y₁))
          as h.
        refine (cha_le_trans _ h).
        clear h.
        use cha_min_le_case.
        - refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            exact (!(cha_min_le_eq_l (cha_le_trans p₃ q₂))).
          }
          unfold sheaf_h_valued_morphism_el.
          refine (cha_le_trans
                    _
                    (h_valued_morphism_eq_defined
                       H τ
                       (ω' ,, # F₁ p₂ x) _
                       (ω',, y₂) _)).
          cbn.
          repeat use cha_min_le_case.
          + refine (cha_le_trans _ _).
            {
              refine (cha_and_monotone_r _).
              exact (h_valued_morphism_dom_defined _ _ _ _).
            }
            cbn.
            unfold cha_sheaf_rel.
            rewrite cha_frobenius.
            use cha_lub_le.
            intros ( ωm & r₁ & r₂ & r₃ ).
            cbn.
            use cha_le_lub.
            * refine (ωm ,, r₁ ,, cha_le_trans r₁ p₂ ,, _).
              refine (r₃ @ _).
              refine (eqtohomot (!(functor_comp F₁ _ _)) _ @ _).
              apply cha_sheaf_le_eq.
            * cbn.
              apply cha_min_le_r.
          + refine (cha_le_trans _ _).
            {
              refine (cha_and_monotone_r _).
              exact (h_valued_morphism_cod_defined _ _ _ _).
            }
            cbn.
            unfold cha_sheaf_rel.
            rewrite cha_frobenius.
            use cha_lub_le.
            intros ( ωm & r₁ & r₂ & r₃ ).
            cbn.
            use cha_le_lub.
            * simple refine ((ω'' ∧ ωm) ,, _ ,, _ ,, _).
              ** refine (cha_le_trans _ r₁).
                 apply cha_min_le_r.
              ** apply cha_min_le_l.
              ** cbn.
                 refine (_ @ eqtohomot (functor_comp F₂ _ _) _).
                 apply cha_sheaf_le_eq.
            * cbn.
              apply cha_le_refl.
          + cbn.
            apply cha_min_le_r.
        - refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            exact (!(cha_min_le_eq_l q₁)).
          }
          refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            refine (!(cha_min_le_eq_l _)).
            refine (cha_le_trans (cha_min_le_l _ _) _).
            refine (cha_le_trans p₃ _).
            exact q₂.
          }
          unfold sheaf_h_valued_morphism_el.
          refine (cha_le_trans
                    _
                    (h_valued_morphism_eq_defined
                       H τ
                       (ω' ,, # F₁ p₂ x) _
                       (ω',, y₂) _)).
          cbn.
          repeat use cha_min_le_case.
          + refine (cha_le_trans (cha_min_le_l _ _) _).
            refine (cha_le_trans _ _).
            {
              refine (cha_and_monotone_r _).
              exact (h_valued_morphism_cod_defined _ _ _ _).
            }
            cbn.
            unfold cha_sheaf_rel.
            rewrite cha_frobenius.
            use cha_lub_le.
            intros ( ωm & r₁ & r₂ & r₃ ).
            cbn.
            use cha_le_lub.
            * simple refine (ωm ,, _ ,, _ ,, _).
              ** exact (cha_le_trans r₁ p₃).
              ** refine (cha_le_trans r₁ _).
                 exact (cha_le_trans p₃ p₂).
              ** refine (eqtohomot (!(functor_comp F₁ _ _)) _ @ _).
                 apply cha_sheaf_le_eq.
            * cbn.
              apply cha_min_le_r.
          + pose (h_valued_morphism_unique_im
                    H τ
                    (ω' ,, #F₁ p₂ x)
                    (ω'' ,, y₁) (ω' ,, y₂))
              as r.
            cbn in r.
            rewrite (cha_sheaf_rel_sym y₂ y₁).
            refine (cha_le_trans _ r).
            clear r.
            use cha_min_le_case.
            * refine (cha_le_trans (cha_min_le_l _ _) _).
              refine (cha_le_trans (cha_min_le_r _ _) _).
              refine (cha_le_trans
                        _
                        (h_valued_morphism_eq_defined
                           H τ
                           (ω'' ,, #F₁ (cha_le_trans p₃ p₂) x) _
                           (ω'' ,, y₁) _)).
              repeat use cha_min_le_case.
              ** cbn.
                 refine (cha_le_trans _ _).
                 {
                   exact (h_valued_morphism_dom_defined _ _ _ _).
                 }
                 cbn.
                 use cha_lub_le.
                 intros ( ωm & r₁ & r₂ & r₃ ).
                 cbn.
                 use cha_le_lub.
                 *** refine (ωm ,, r₁ ,, cha_le_trans r₁ p₃ ,, _).
                     refine (_ @ eqtohomot (functor_comp F₁ _ _) _).
                     refine (eqtohomot (!(functor_comp F₁ _ _)) _ @ _).
                     apply cha_sheaf_le_eq.
                 *** cbn.
                     apply cha_le_refl.
              ** cbn.
                 exact (h_valued_morphism_cod_defined _ _ _ _).
              ** apply cha_le_refl.
            * apply cha_min_le_r.
          + cbn.
            apply cha_min_le_r.
      Qed.

      Definition h_valued_morphism_to_nat_trans_matching_family
        : matching_family F₂ h_valued_morphism_to_nat_trans_sieve.
      Proof.
        use make_matching_family.
        - exact (λ ω' p y, pr1 y).
        - abstract
            (cbn ;
             intros ω'' ω' p₁ p₂ p₃ eq ( y₁ & q₁ ) ( y₂ & q₂ ) ;
             induction eq ;
             exact (h_valued_morphism_to_nat_trans_matching_family_laws q₁ q₂)).
      Defined.

      Definition h_valued_morphism_to_nat_trans_amalgamation
        : amalgamation h_valued_morphism_to_nat_trans_matching_family
        := sheaf_amalgamation
             (is_sheaf_sheaf F₂)
             h_valued_morphism_to_nat_trans_sieve_covers
             h_valued_morphism_to_nat_trans_matching_family.

      Proposition h_valued_morphism_to_nat_trans_amalgamation_restr
                  {ω' : H}
                  (p : ω' ≤ ω)
                  (y : (F₂ ω' : hSet))
                  (q : ω' ≤ sheaf_h_valued_morphism_el (# F₁ p x) y)
        : #F₂ p h_valued_morphism_to_nat_trans_amalgamation = y.
      Proof.
        exact (amalgamation_restr h_valued_morphism_to_nat_trans_amalgamation p (y ,, q)).
      Qed.

      Proposition h_valued_morphism_to_nat_trans_amalgamation_map
        : ω ≤ sheaf_h_valued_morphism_el x h_valued_morphism_to_nat_trans_amalgamation.
      Proof.
        refine (cha_le_trans _ _).
        {
          use cha_eq_to_refl.
          refine (!_).
          refine (cha_min_le_eq_l (h_valued_morphism_hom_exists _ τ (ω ,, x)) @ _).
          cbn.
          exact (!(cha_sheaf_rel_partial_refl x)).
        }
        cbn.
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ω' & y ).
        refine (cha_le_trans
                  _
                  (h_valued_morphism_eq_defined
                     H τ
                     (ω ,, x) _
                     (ω' ,, y) _)).
        cbn.
        repeat use cha_min_le_case.
        - apply cha_min_le_l.
        - refine (cha_le_trans (cha_min_le_r _ _) _).
          use cha_le_lub.
          + simple refine ((τ (ω ,, x) (ω' ,, y)) ,, _ ,, _ ,, _).
            * refine (cha_le_trans _ _).
              {
                apply (h_valued_morphism_cod_defined H τ _ _).
              }
              cbn.
              apply cha_eq_to_refl.
              exact (!(cha_sheaf_rel_partial_refl _)).
            * refine (cha_le_trans _ _).
              {
                apply (h_valued_morphism_dom_defined H τ _ _).
              }
              cbn.
              apply cha_eq_to_refl.
              exact (!(cha_sheaf_rel_partial_refl _)).
            * cbn.
              refine (!_).
              use h_valued_morphism_to_nat_trans_amalgamation_restr.
              refine (cha_le_trans
                        _
                        (h_valued_morphism_eq_defined
                           H τ
                           (ω ,, x) _
                           (ω' ,, y) _)).
              cbn.
              repeat use cha_min_le_case.
              ** refine (cha_le_trans _ _).
                 {
                   use cha_eq_to_refl.
                   refine (!(cha_min_le_eq_l _)).
                   apply (h_valued_morphism_dom_defined H τ _ _).
                 }
                 cbn.
                 unfold cha_sheaf_rel.
                 rewrite cha_frobenius.
                 use cha_lub_le.
                 intros ( ω'' & q₁ & q₂ & q₃ ).
                 cbn.
                 use cha_le_lub.
                 *** simple refine ((τ (ω ,, x) (ω' ,, y) ∧ ω'') ,, _ ,, _ ,, _).
                     **** refine (cha_le_trans (cha_min_le_r _ _) q₁).
                     **** apply cha_min_le_l.
                     **** cbn.
                          refine (_ @ eqtohomot (functor_comp F₁ _ _) _).
                          apply cha_sheaf_le_eq.
                 *** cbn.
                     apply cha_le_refl.
              ** refine (cha_le_trans _ _).
                 {
                   use cha_eq_to_refl.
                   refine (!(cha_min_le_eq_l _)).
                   apply (h_valued_morphism_cod_defined H τ _ _).
                 }
                 cbn.
                 unfold cha_sheaf_rel.
                 rewrite cha_frobenius.
                 use cha_lub_le.
                 intros ( ω'' & q₁ & q₂ & q₃ ).
                 cbn.
                 use cha_le_lub.
                 *** simple refine ((τ (ω ,, x) (ω' ,, y) ∧ ω'') ,, _ ,, _ ,, _).
                     **** refine (cha_le_trans (cha_min_le_r _ _) q₁).
                     **** apply cha_min_le_l.
                     **** cbn.
                          refine (_ @ eqtohomot (functor_comp F₂ _ _) _).
                          apply cha_sheaf_le_eq.
                 *** cbn.
                     apply cha_le_refl.
              ** apply cha_le_refl.
          + cbn.
            apply cha_le_refl.
        - apply cha_min_le_r.
      Qed.
    End Amalgamation.

    Definition h_valued_morphism_to_nat_trans_data
      : nat_trans_data F₁ F₂
      := λ ω x, h_valued_morphism_to_nat_trans_amalgamation x.

    Proposition h_valued_morphism_to_nat_trans_laws
      : is_nat_trans F₁ F₂ h_valued_morphism_to_nat_trans_data.
    Proof.
      intros ω₁ ω₂ p.
      cbn in ω₁, ω₂, p.
      use funextsec.
      intro x.
      cbn.
      use (sheaf_amalgamation_unique (is_sheaf_sheaf F₂)).
      - exact (h_valued_morphism_to_nat_trans_sieve (#F₁ p x)).
      - apply h_valued_morphism_to_nat_trans_sieve_covers.
      - apply h_valued_morphism_to_nat_trans_matching_family.
      - cbn.
        intros ω' q₁ y.
        apply h_valued_morphism_to_nat_trans_amalgamation_restr.
        exact (pr2 y).
      - cbn.
        intros ω' q₁ ( y & q₂ ).
        cbn.
        etrans.
        {
          refine (eqtohomot (!(functor_comp F₂ _ _)) _ @ _).
          use h_valued_morphism_to_nat_trans_amalgamation_restr.
          cbn.
          refine (cha_le_trans q₂ _).
          use cha_eq_to_refl.
          apply maponpaths_2.
          exact (eqtohomot (!(functor_comp F₁ _ _)) _).
        }
        cbn.
        apply idpath.
    Qed.

    Definition h_valued_morphism_to_nat_trans
      : F₁ ⟹ F₂.
    Proof.
      use make_nat_trans.
      - exact h_valued_morphism_to_nat_trans_data.
      - exact h_valued_morphism_to_nat_trans_laws.
    Defined.

    Definition h_valued_morphism_to_sheaf_nat_trans
      : sheaf_nat_trans F₁ F₂.
    Proof.
      use make_sheaf_nat_trans.
      exact h_valued_morphism_to_nat_trans.
    Defined.

    Proposition h_valued_morphism_to_sheaf_nat_trans_eq
      : nat_trans_to_h_valued_morphism h_valued_morphism_to_sheaf_nat_trans = τ.
    Proof.
      use h_valued_morphism_eq.
      - intros ( ω₁ & x ) ( ω₂ & y ).
        cbn.
        use cha_lub_le.
        cbn.
        unfold h_valued_morphism_to_nat_trans_data.
        intros ( ωm & p & q & r ).
        cbn.
        refine (cha_le_trans
                  _
                  (h_valued_morphism_eq_defined
                     H τ
                     (ω₁ ,, x) _
                     (ω₁ ,, pr1 (h_valued_morphism_to_nat_trans_amalgamation x)) _)).
        repeat use cha_min_le_case.
        + cbn.
          refine (cha_le_trans p _).
          apply cha_eq_to_refl.
          exact (cha_sheaf_rel_partial_refl _).
        + cbn.
          use cha_le_lub.
          * exact (ωm ,, p ,, q ,, r).
          * apply cha_le_refl.
        + refine (cha_le_trans p _).
          apply h_valued_morphism_to_nat_trans_amalgamation_map.
      - intros ( ω₁ & x ) ( ω₂ & y ).
        cbn.
        use cha_le_lub.
        + cbn.
          simple refine (τ (ω₁ ,, x) (ω₂ ,, y) ,, _ ,, _ ,, _).
          * refine (cha_le_trans _ _).
            {
              apply (h_valued_morphism_dom_defined H τ _ _).
            }
            cbn.
            apply cha_eq_to_refl.
            exact (!(cha_sheaf_rel_partial_refl _)).
          * refine (cha_le_trans _ _).
            {
              apply (h_valued_morphism_cod_defined H τ _ _).
            }
            cbn.
            apply cha_eq_to_refl.
            exact (!(cha_sheaf_rel_partial_refl _)).
          * cbn.
            use h_valued_morphism_to_nat_trans_amalgamation_restr.
            unfold sheaf_h_valued_morphism_el.
            refine (cha_le_trans
                      _
                      (h_valued_morphism_eq_defined
                         H τ
                         (ω₁ ,, x) _
                         (ω₂ ,, y) _)).
            cbn.
            repeat use cha_min_le_case.
            ** use cha_le_lub.
               *** simple refine (τ (ω₁ ,, x) (ω₂ ,, y) ,, _ ,, _ ,, _).
                   **** refine (cha_le_trans _ _).
                        {
                          apply (h_valued_morphism_dom_defined H τ _ _).
                        }
                        cbn.
                        apply cha_eq_to_refl.
                        exact (!(cha_sheaf_rel_partial_refl _)).
                   **** apply cha_le_refl.
                   **** cbn.
                        refine (_ @ eqtohomot (functor_comp F₁ _ _) _).
                        apply cha_sheaf_le_eq.
               *** cbn.
                   apply cha_le_refl.
            ** use cha_le_lub.
               *** simple refine (τ (ω₁ ,, x) (ω₂ ,, y) ,, _ ,, _ ,, _).
                   **** refine (cha_le_trans _ _).
                        {
                          apply (h_valued_morphism_cod_defined H τ _ _).
                        }
                        cbn.
                        apply cha_eq_to_refl.
                        exact (!(cha_sheaf_rel_partial_refl _)).
                   **** apply cha_le_refl.
                   **** cbn.
                        refine (_ @ eqtohomot (functor_comp F₂ _ _) _).
                        apply cha_sheaf_le_eq.
               *** cbn.
                   apply cha_le_refl.
            ** apply cha_le_refl.
        + cbn.
          apply cha_le_refl.
    Qed.
  End Fullness.

  Proposition fully_faithful_sheaf_to_h_valued_set_functor
    : fully_faithful sheaf_to_h_valued_set_functor.
  Proof.
    refine (λ (F₁ F₂ : sheaf C), _).
    use isweq_iso.
    - intro τ.
      exact (h_valued_morphism_to_sheaf_nat_trans τ).
    - refine (λ (τ : sheaf_nat_trans F₁ F₂), _).
      use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro ω.
      use funextsec.
      intro x.
      cbn in ω, x.
      cbn.
      unfold h_valued_morphism_to_nat_trans_data.
      unfold h_valued_morphism_to_nat_trans_amalgamation.
      use (sheaf_amalgamation_unique (is_sheaf_sheaf F₂)).
      + exact (h_valued_morphism_to_nat_trans_sieve
                 (nat_trans_to_h_valued_morphism τ)
                 x).
      + exact (h_valued_morphism_to_nat_trans_sieve_covers
                 (nat_trans_to_h_valued_morphism τ)
                 x).
      + exact (h_valued_morphism_to_nat_trans_matching_family
                 (nat_trans_to_h_valued_morphism τ)
                 x).
      + intros ω' p q.
        apply h_valued_morphism_to_nat_trans_amalgamation_restr.
        exact (pr2 q).
      + cbn.
        intros ω' p ( y & q ).
        cbn.
        use cha_sheaf_rel_to_eq.
        refine (cha_le_trans q _).
        use cha_lub_le.
        intros ( ωm & r₁ & r₂ & r₃ ).
        cbn.
        use cha_le_lub.
        * refine (ωm ,, r₁ ,, r₂ ,, _).
          refine (_ @ r₃).
          apply maponpaths.
          refine (!_).
          exact (eqtohomot (nat_trans_ax τ _ _ p) x).
        * cbn.
          apply cha_le_refl.
    - intro τ.
      cbn.
      exact (h_valued_morphism_to_sheaf_nat_trans_eq τ).
  Qed.


  Definition is_singleton_h_valued_set
             {X : h_valued_set H}
             (f : X → H)
             (ω : H)
    : hProp
    := hconj
         (∀ (x y : X), (f x ∧ (x ~_{X} y)) ≤ f y)
         (hconj
            (∀ (x y : X), (f x ∧ f y) ≤ (x ~_{X} y))
            (ω ≤ \/_{ x : X } (f x))).

  Definition singleton_h_valued_set
             (X : h_valued_set H)
             (ω : H)
    : UU
    := ∑ (f : X → H), is_singleton_h_valued_set f ω.

  Definition make_singleton_h_valued_set
             {X : h_valued_set H}
             {ω : H}
             (f : X → H)
             (Hf : is_singleton_h_valued_set f ω)
    : singleton_h_valued_set X ω
    := f ,, Hf.

  Definition singleton_h_valued_set_fun
             {X : h_valued_set H}
             {ω : H}
             (f : singleton_h_valued_set X ω)
    : X → H
    := pr1 f.

  Coercion singleton_h_valued_set_fun : singleton_h_valued_set >-> Funclass.

  Proposition singleton_h_valued_set_on_eq
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
              (x y : X)
    : (f x ∧ (x ~_{X} y)) ≤ f y.
  Proof.
    exact (pr12 f x y).
  Qed.

  Proposition singleton_h_valued_set_unique
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
              (x y : X)
    : (f x ∧ f y) ≤ (x ~_{X} y).
  Proof.
    exact (pr122 f x y).
  Qed.

  Proposition singleton_h_valued_set_extent
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
    : ω ≤ \/_{ x : X } (f x).
  Proof.
    exact (pr222 f).
  Qed.

  Proposition eq_singleton_h_valued_set
              {X : h_valued_set H}
              {ω : H}
              {f g : singleton_h_valued_set X ω}
              (p : ∏ (x : X), f x = g x)
    : f = g.
  Proof.
    use subtypePath_prop.
    use funextsec.
    exact p.
  Qed.

  Proposition isaset_singleton_h_valued_set
              (X : h_valued_set H)
              (ω : H)
    : isaset (singleton_h_valued_set X ω).
  Proof.
    use isaset_total2.
    - apply impred_isaset.
      intro.
      apply setproperty.
    - intros.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition singleton_h_valued_set_hSet
             (X : h_valued_set H)
             (ω : H)
    : hSet
    := make_hSet
         (singleton_h_valued_set X ω)
         (isaset_singleton_h_valued_set X ω).

  Proposition el_to_singleton_h_valued_laws
              {X : h_valued_set H}
              (x : X)
    : is_singleton_h_valued_set (λ y, y ~_{X} x) (x ~_{X} x).
  Proof.
    repeat split.
    - intros y₁ y₂.
      refine (cha_le_trans _ (trans_per_of_h_valued_set H y₂ y₁ x)).
      rewrite cha_min_comm.
      use cha_and_monotone_l.
      use cha_eq_to_refl.
      exact (sym_per_of_h_valued_set H y₁ y₂).
    - intros y₁ y₂.
      refine (cha_le_trans _ (trans_per_of_h_valued_set H y₁ x y₂)).
      use cha_and_monotone_r.
      use cha_eq_to_refl.
      exact (sym_per_of_h_valued_set H y₂ x).
    - use cha_le_lub.
      {
        exact x.
      }
      cbn.
      apply cha_le_refl.
  Qed.

  Definition el_to_singleton_h_valued
             {X : h_valued_set H}
             (x : X)
    : singleton_h_valued_set X (x ~_{X} x).
  Proof.
    use make_singleton_h_valued_set.
    - exact (λ y, y ~_{X} x).
    - exact (el_to_singleton_h_valued_laws x).
  Defined.

  Section HValuedSetToSheaf.
    Context (X : h_valued_set H).

    Proposition is_singleton_h_valued_set_le
                {ω₁ ω₂ : H}
                (p : ω₂ ≤ ω₁)
                (f : singleton_h_valued_set X ω₁)
      : is_singleton_h_valued_set f ω₂.
    Proof.
      repeat split.
      - exact (singleton_h_valued_set_on_eq f).
      - exact (singleton_h_valued_set_unique f).
      - refine (cha_le_trans p _).
        exact (singleton_h_valued_set_extent f).
    Qed.

    (* RESTRICTION DEFINED INCORRECTLY *)
    Definition h_valued_set_to_psh_data
      : functor_data C^op SET.
    Proof.
      use make_functor_data.
      - exact (λ (ω : H), singleton_h_valued_set_hSet X ω).
      - refine (λ (ω₁ ω₂ : H)
                  (p : ω₂ ≤ ω₁)
                  (f : singleton_h_valued_set X ω₁), _).
        use make_singleton_h_valued_set.
        + exact f.
        + exact (is_singleton_h_valued_set_le p f).
    Defined.

    Proposition h_valued_set_to_psh_laws
      : is_functor h_valued_set_to_psh_data.
    Proof.
      split.
      - intros ω.
        use funextsec.
        intro f.
        cbn in ω, f.
        use eq_singleton_h_valued_set.
        cbn.
        intro x.
        apply idpath.
      - intros ω₁ ω₂ ω₃ p q.
        use funextsec.
        intro f.
        use eq_singleton_h_valued_set.
        cbn.
        intro x.
        apply idpath.
    Qed.

    Definition h_valued_set_to_psh
      : C^op ⟶ SET.
    Proof.
      use make_functor.
      - exact h_valued_set_to_psh_data.
      - exact h_valued_set_to_psh_laws.
    Defined.

    Definition is_sheaf_h_valued_set_to_psh
      : is_sheaf h_valued_set_to_psh.
    Proof.
      intros ω₁ P HP z.
    Admitted.

    Definition h_valued_set_to_sheaf
      : sheaf C.
    Proof.
      use make_sheaf.
      - exact h_valued_set_to_psh.
      - exact is_sheaf_h_valued_set_to_psh.
    Defined.

    Definition h_valued_set_to_sheaf_mor_rel
               {ω : H}
               (f : singleton_h_valued_set X ω)
               (x : X)
      : H
      := ω ∧ f x.

    Proposition h_valued_set_to_sheaf_mor_rel_dom
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x : X)
      : h_valued_set_to_sheaf_mor_rel f x
        ≤
        cha_sheaf_rel (F := h_valued_set_to_sheaf) f f.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      use cha_le_lub.
      - refine (ω ,, cha_le_refl _ ,, cha_le_refl _ ,, _).
        use eq_singleton_h_valued_set.
        cbn.
        intro y.
        apply idpath.
      - cbn.
        apply cha_min_le_l.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_rel_cod
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x : X)
      : h_valued_set_to_sheaf_mor_rel f x
        ≤
        (x ~_{X} x).
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      refine (cha_le_trans _ (singleton_h_valued_set_unique f x x)).
      rewrite cha_min_id.
      apply cha_min_le_r.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_eq
                {ω₁ ω₂ : H}
                (f₁ : singleton_h_valued_set X ω₁)
                (f₂ : singleton_h_valued_set X ω₂)
                (x₁ x₂ : X)
      : (cha_sheaf_rel (F := h_valued_set_to_sheaf) f₁ f₂
         ∧ x₁ ~_{X} x₂
         ∧ h_valued_set_to_sheaf_mor_rel f₁ x₁)
        ≤
        h_valued_set_to_sheaf_mor_rel f₂ x₂.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      unfold cha_sheaf_rel.
      rewrite cha_min_comm.
      rewrite cha_frobenius.
      use cha_lub_le.
      intros ( ωm & p & q & r ).
      cbn.
      use cha_min_le_case.
      - refine (cha_le_trans _ q).
        exact (cha_min_le_r _ _).
      - cbn.
        refine (cha_le_trans _ _).
        + refine (cha_le_trans _ (singleton_h_valued_set_on_eq f₁ x₁ x₂)).
          use cha_min_le_case.
          * refine (cha_le_trans (cha_min_le_l _ _) _).
            refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_r.
          * refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_l.
        + apply cha_eq_to_refl.
          exact (maponpaths (λ h, pr1 h x₂) r).
    Qed.

    Proposition h_valued_set_to_sheaf_mor_unique
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x₁ x₂ : X)
      : (h_valued_set_to_sheaf_mor_rel f x₁ ∧ h_valued_set_to_sheaf_mor_rel f x₂)
        ≤
        (x₁ ~_{X} x₂).
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      refine (cha_le_trans _ (singleton_h_valued_set_unique f _ _)).
      use cha_min_le_case.
      - refine (cha_le_trans (cha_min_le_l _ _) _).
        apply cha_min_le_r.
      - refine (cha_le_trans (cha_min_le_r _ _) _).
        apply cha_min_le_r.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_im
                {ω : H}
                (f : singleton_h_valued_set X ω)
      : cha_sheaf_rel (F := h_valued_set_to_sheaf) f f
        ≤
        \/_{ x : X } h_valued_set_to_sheaf_mor_rel f x.
    Proof.
      refine (cha_le_trans _ _).
      {
        use cha_eq_to_refl.
        exact (!(cha_sheaf_rel_partial_refl (F := h_valued_set_to_sheaf) f)).
      }
      refine (cha_le_trans _ _).
      {
        use cha_eq_to_refl.
        exact (!(cha_min_le_eq_l (singleton_h_valued_set_extent f))).
      }
      rewrite cha_frobenius.
      unfold h_valued_set_to_sheaf_mor_rel.
      apply cha_le_refl.
    Qed.

    Definition h_valued_set_to_sheaf_mor
      : h_valued_morphism
          H
          (sheaf_to_h_valued_set_functor h_valued_set_to_sheaf)
          X.
    Proof.
      use make_h_valued_morphism.
      - exact (λ ωf x, h_valued_set_to_sheaf_mor_rel (pr2 ωf) x).
      - intros ωf x.
        apply h_valued_set_to_sheaf_mor_rel_dom.
      - intros ωf x.
        apply h_valued_set_to_sheaf_mor_rel_cod.
      - intros ωf₁ ωf₂ x₁ x₂.
        apply h_valued_set_to_sheaf_mor_eq.
      - intros ωf x₁ x₂.
        apply h_valued_set_to_sheaf_mor_unique.
      - intro ωf.
        apply h_valued_set_to_sheaf_mor_im.
    Defined.

    Proposition h_valued_set_to_sheaf_mor_surjective
                (x : X)
      : (x ~_{X} x) ≤ \/_{ f } h_valued_set_to_sheaf_mor f x.
    Proof.
      use cha_le_lub.
      - refine ((x ~_{X} x) ,, _).
        exact (el_to_singleton_h_valued x).
      - cbn.
        unfold h_valued_set_to_sheaf_mor_rel.
        cbn.
        rewrite cha_min_id.
        apply cha_le_refl.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_injective
                {ω₁ ω₂ : H}
                (f₁ : singleton_h_valued_set X ω₁)
                (f₂ : singleton_h_valued_set X ω₂)
                (x : X)
      : (h_valued_set_to_sheaf_mor_rel f₁ x ∧ h_valued_set_to_sheaf_mor_rel f₂ x)
        ≤
        cha_sheaf_rel (F := h_valued_set_to_sheaf) f₁ f₂.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.

      use cha_le_lub.
      all:cbn.
      - cbn.
    Admitted.
  End HValuedSetToSheaf.

  Definition split_eso_sheaf_to_h_valued_set_functor
    : split_essentially_surjective sheaf_to_h_valued_set_functor.
  Proof.
    refine (λ (X : h_valued_set H), _).
    refine (h_valued_set_to_sheaf X ,, _).
    use make_h_valued_isomorphism.
    - exact (h_valued_set_to_sheaf_mor X).
    - exact (h_valued_set_to_sheaf_mor_surjective X).
    - intros.
      apply h_valued_set_to_sheaf_mor_injective.
  Defined.

  Definition adj_equivalence_of_cats_sheaf_to_h_valued_set_functor
    : adj_equivalence_of_cats sheaf_to_h_valued_set_functor.
  Proof.
    use rad_equivalence_of_cats'.
    - exact fully_faithful_sheaf_to_h_valued_set_functor.
    - exact split_eso_sheaf_to_h_valued_set_functor.
  Defined.
