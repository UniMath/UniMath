(**

 The functor from sheaves to H-valued sets is fully faithful

 In another file, we defined the functor from sheaves to H-valued sets, and
 we explained why relating sheaves and H-valued sets is interesting. Our goal
 is to show that this functor from sheaves to H-valued sets is an adjoint
 equivalence of categpories, and to do so, we show that it is fully faithful
 and split essentially surjective. We prove in this file that this functor is
 fully faithful. Concretely, this means that natural transformations of sheaves
 are the same H-valued morphisms (i.e., functional relations valued in the
 complete Heyting algebra `H`).

 To prove fully faithfulness, we first prove another principle that allows us
 to conclude the equality of two elements in `F ω` for some `ω` given a sheaf
 `F`. This principle uses the induced partial equivalence relation by the sheaf.
 Most work in this file lies in showing that the aforementioned functor is full,
 because we are required to construct a natural transformation. In addition, we
 construct this transformation using that `F` is a sheaf condition, and the family
 of morphisms is defined using the unique amalgamations.

 Content
 1. Equality from the partial equivalence relation
 2. Fullness
 3. Fully faithfulness

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
Require Import UniMath.CategoryTheory.Presheaves.SheafToHValuedSet.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HValuedSets.

Local Open Scope heyting.
Local Open Scope cat.

Section SheafToHValuedSetFullyFaithful.
  Context {H : complete_heyting_algebra}.

  Let C : site := cha_to_site H.

  (** * 1. Equality from the partial equivalence relation *)
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

  (** * 2. Fullness *)
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

  (** * 3. Fully faithfulness *)
  Proposition fully_faithful_sheaf_to_h_valued_set_functor
    : fully_faithful (sheaf_to_h_valued_set_functor H).
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
End SheafToHValuedSetFullyFaithful.
