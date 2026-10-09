(**

 Sheaves versus H-valued sets

 Let H be a complete Heyting algebra. From `H`, we can obtain two toposes
 - We can look at sheaves over `H`. Specifically, for each `ω : H` we have
   a set `F ω`. We also have restriction maps: if `p : ω₁ ≤ ω₂`, then we
   have a map `F p : F ω₂ → F ω₁`, and these restriction maps turn `F` into
   a functor. This functor must be a sheaf in the following sense: if we
   have `ω ≤ \/_{ i } ω_i` (with `ω_i ≤ ω`) and an element `x_i : F ω_i`, then
   there is a unique `x : F ω` whose restrictions are the `x_i`. Note that the
   category of sheaves always is univalent.
 - We can look at sets together with a partial equivalence relation valued
   in `H`. This construction is an instance of the tripos-to-topos construction
   where we use the tripos of H-valued predicates. Note that the category of
   H-valued sets is not necessarily univalent.
 These constructions provide us toposes that are adjoint equivalent, which is
 a theorem proven by Higgs. Our goal is to prove this theorem.

 The reason why this theorem is interesting, is because it provides two
 different perspectives. The notion of H-valued set is very much grounded in
 partial elements: an element in `(X, ~)` is given by `x : X` and its extent
 is defined to be `x ~ x`. The extent of `x` indicates the definedness of `x`.
 For instance, if `H` is the collection of open sets in a topological space,
 then an example of an `H`-valued set is given by a pair of `U : H` together
 with a continuous function from `U` to `R`. If `f : U → R` is a continuous
 function, then `f ~ f` is `U`. Concretely, `f` is a partial element who is
 only defined on `U`. Sheaves provide a different perspective. Sheaves connect
 very naturally to geometry, as sheaves are commonly used in, for instance,
 algebraic geometry and differential geometry. In addition, H-valued sets
 and sheaves connect to different constructions in forcing. H-valued sets
 are closer to Heyting-valued models (and Boolean-valued models), whereas
 sheaves are more similar to forcing over a partial order.

 In this file, we construct a functor from he category of sheaves to the
 category of H-valued sets.

 References
 - "Injectivity in the topos of complete Heyting algebra valued sets" by Higgs

 Content
 1. Some preliminaries
 2. The partial equivalence relation induced by a sheaf
 3. Natural transformations to H-valued morphisms
 4. The functor from sheaves to H-valued sets

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.OrderTheory.Lattice.DerivedLawsCompleteHeyting.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ExamplesSites.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HValuedSets.

Local Open Scope heyting.
Local Open Scope cat.

Section SheafToHValuedSet.
  Context {H : complete_heyting_algebra}.

  Let C : site := cha_to_site H.

  (** * 1. Some preliminaries *)
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

  (** * 2. The partial equivalence relation induced by a sheaf *)
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

  (** * 3. Natural transformations to H-valued morphisms *)
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

  (** * 4. The functor from sheaves to H-valued sets *)
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
        * exact (ω₁ ,, τ₁ ω₁ x).
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
        induction i as [ ωm₁ z₁ ].
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ζ₁ & p₁ & q₁ & r₁ ).
        rewrite cha_min_comm.
        rewrite cha_frobenius.
        use cha_lub_le.
        intros ( ζ₂ & p₂ & q₂ & r₂ ).
        cbn in p₁, q₂, r₁, r₂.
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
               exact (eqtohomot (nat_trans_ax τ₂ _ _ q₂) z₁).
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
End SheafToHValuedSet.

Arguments sheaf_to_h_valued_set_functor_data : clear implicits.
Arguments sheaf_to_h_valued_set_functor_laws : clear implicits.
Arguments sheaf_to_h_valued_set_functor : clear implicits.
