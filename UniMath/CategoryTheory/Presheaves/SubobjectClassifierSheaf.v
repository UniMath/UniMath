(**

 The subobject classifier of sheaves

 We show that the sheaf model of type theory comes with subobject classifier types. To do
 so, we equip each category of dependent sheaves (which are the categories of types in
 the sheaf model) with a subobject classifier, and we show that this choice is stable
 under reindexing. In essence, this corresponds to equipping the category of sheaves
 with a subobject classifier.

 Recall that the subobject classifier of sheaves is defined to be the presheaf of all
 closed sieves. Note the difference with presheaf where all sieves are considered rather
 than only the closed ones. The importance of only considering the closed sieves, comes
 from the following. If we have a natural transformation from some dependent sheaf to the
 collection of all sieves, then the subobject represented by this predicate is only
 guaranteed to be a presheaf, and not necessarily a sheaf. In a sheaf, we must be able
 to find amalgamations for matching families, and we can only do so if we look at closed
 sieves rather than arbitrary sieves.

 Content
 1. The presheaf of closed sieves
 2. The sheaf of closed sieves
 2.1. The closed sieve that is the amalgamation
 2.2. The law for the amalgamation
 2.3. The proof that the presheaf of closed sieves is a sheaf
 3. The truth morphism for closed sieves
 4. The universal property of the subobject classifier
 4.1. The characteristic morphism
 4.2. The pullback square
 4.3. Uniqueness of the characteristic morphism
 5. Stability of the subobject classifier

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.FullSubDispCat.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.

Local Open Scope cat.

Section SubobjectClassifier.
  Context {C : site}.

  (** * 1. The presheaf of closed sieves *)
  Definition dep_psh_closed_sieves
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, set_of_closed_sieves x).
    - exact (λ x y xx yy s p ω, precomp_closed_sieve ω s).
    - abstract
        (intros x xx p ω ; cbn ;
         use closed_sieve_eq ;
         apply id_precomp_sieve).
    - abstract
        (intros x y z xx yy zz s₁ s₂ p₁ p₂ p₃ ω ; cbn ;
         use closed_sieve_eq ;
         apply comp_precomp_sieve).
  Defined.

  (** * 2. The sheaf of closed sieves *)
  Section SubobjectClassifierSheaf.
    Context {Γ : C^op ⟶ HSET}
            {x : C}
            {ω : sieve x}
            (p : C x ω)
            {z : matching_family Γ ω}
            (zz : matching_family_dep (dep_psh_closed_sieves Γ) z).

    (** * 2.1. The closed sieve that is the amalgamation *)
    Definition dep_psh_closed_sieves_amalgamation_ob
               {y : C}
               (f : y --> x)
      : hProp
      := ∃ (z : C)
           (g₁ : y --> z)
           (g₂ : z --> x)
           (p : ω _ g₂),
         (f = g₁ · g₂)
         ×
         ((zz _ g₂ p : closed_sieve _) _ g₁).

    Proposition is_sieve_dep_psh_closed_sieves_amalgamation_ob
                {y₁ y₂ : C}
                {g₁ : y₁ --> x}
                {g₂ : y₂ --> x}
                {h : y₂ --> y₁}
                (q : h · g₁ = g₂)
      : dep_psh_closed_sieves_amalgamation_ob g₁
        →
        dep_psh_closed_sieves_amalgamation_ob g₂.
    Proof.
      use factor_through_squash_hProp.
      intros ( w & k₁ & k₂ & r₁ & r₂ & r₃ ).
      use hinhpr.
      refine (w ,, _).
      refine (h · k₁ ,, _).
      refine (k₂ ,, _).
      refine (r₁ ,, _).
      split.
      - rewrite <- q.
        rewrite r₂.
        rewrite assoc.
        apply idpath.
      - exact (#ω (zz w k₂ r₁ : closed_sieve _) h (idpath _) r₃).
    Qed.

    Definition dep_psh_closed_sieves_amalgamation_sieve
      : sieve x.
    Proof.
      use make_sieve.
      - exact (λ y f, dep_psh_closed_sieves_amalgamation_ob f).
      - intros y₁ y₂ g₁ g₂ h q.
        exact (is_sieve_dep_psh_closed_sieves_amalgamation_ob q).
    Defined.

    Definition dep_psh_closed_sieves_amalgamation_closed_sieve
      : closed_sieve x.
    Proof.
      use closure_closed_sieve.
      exact dep_psh_closed_sieves_amalgamation_sieve.
    Defined.

    (** * 2.2. The law for the amalgamation *)
    Proposition dep_psh_closed_sieves_amalgamation_law
                (a : amalgamation z)
      : amalgamation_dep_law
          (a := a)
          zz
          dep_psh_closed_sieves_amalgamation_closed_sieve.
    Proof.
      intros y f q ; cbn.
      use closed_sieve_eq.
      use sieve_eq.
      - intros w g.
        cbn -[precomp_sieve].
        rewrite precomp_closure_sieve.
        use contains_closure_sieve.
        intros w' h.
        use factor_through_squash_hProp ; cbn.
        intros (w'' & k₁ & k₂ & r₁ & r₂ & r₃).
        pose proof (maponpaths
                      (λ (φ : closed_sieve _), φ _ (identity _))
                      (matching_family_dep_restr zz r₂ (#ω ω _ r₂ q) q))
          as eq.
        cbn in eq.
        rewrite id_left in eq.
        rewrite eq.
        clear eq.
        pose proof (maponpaths
                      (λ (φ : closed_sieve _), φ _ (identity _))
                      (matching_family_dep_restr zz (!r₂) (#ω ω _ (!r₂) r₁) r₁))
          as eq.
        cbn in eq.
        rewrite id_left in eq.
        rewrite eq in r₃.
        rewrite r₂ in r₃.
        assert (#ω ω k₁ (! idpath (k₁ · k₂)) r₁ = #ω ω h r₂ q) as <-.
        {
          apply propproperty.
        }
        exact r₃.
      - intros w g r.
        cbn -[precomp_sieve].
        rewrite precomp_closure_sieve.
        use closure_sieve_contains.
        use hinhpr ; cbn.
        refine (y ,, _).
        refine (g ,, _).
        refine (f ,, _).
        refine (q ,, _).
        split.
        + apply idpath.
        + exact r.
    Qed.

    Definition dep_psh_closed_sieves_amalgamation
               (a : amalgamation z)
      : amalgamation_dep a zz.
    Proof.
      use make_amalgamation_dep.
      - exact dep_psh_closed_sieves_amalgamation_closed_sieve.
      - exact (dep_psh_closed_sieves_amalgamation_law a).
    Defined.

    Proposition dep_psh_closed_sieves_amalgamation_unique
                {a : amalgamation z}
                (aa : amalgamation_dep a zz)
      : aa = dep_psh_closed_sieves_amalgamation a.
    Proof.
      use amalgamation_dep_eq.
      use (closed_sieve_eq_cover p) ; cbn -[closure_sieve].
      + intros y g q r.
        use closure_sieve_contains.
        use hinhpr ; cbn.
        refine (y ,, _).
        refine (identity _ ,, _).
        refine (g ,, _).
        refine (q ,, _).
        split.
        * rewrite id_left.
          apply idpath.
        * rewrite <- (amalgamation_dep_restr aa g q).
          cbn.
          rewrite id_left.
          exact r.
      + intros y f q.
        clear q.
        revert y f.
        use contains_closure_sieve.
        intros y f.
        use factor_through_squash_hProp ; cbn.
        intros (w & g₁ & g₂ & q₁ & q₂ & q₃).
        rewrite q₂.
        pose proof (maponpaths
                      (λ (φ : closed_sieve _), φ y g₁)
                      (amalgamation_dep_restr aa g₂ q₁))
          as eq.
        cbn in eq.
        rewrite <- eq in q₃.
        exact q₃.
    Qed.
  End SubobjectClassifierSheaf.

  (** * 2.3. The proof that the presheaf of closed sieves is a sheaf *)
  Definition is_sheaf_dep_psh_closed_sieves
             (Γ : C^op ⟶ HSET)
    : is_dep_sheaf (dep_psh_closed_sieves Γ).
  Proof.
    intros x ω p z a zz.
    use make_iscontr.
    - exact (dep_psh_closed_sieves_amalgamation zz a).
    - exact (dep_psh_closed_sieves_amalgamation_unique p zz).
  Defined.

  Definition subobject_classifier_dep_sheaf
             (Γ : sheaf C)
    : dep_sheaf Γ.
  Proof.
    use make_dep_sheaf.
    - exact (dep_psh_closed_sieves Γ).
    - exact (is_sheaf_dep_psh_closed_sieves Γ).
  Defined.

  (** * 3. The truth morphism for closed sieves *)
  Definition dep_sheaf_truth
             (Γ : C^op ⟶ HSET)
    : dep_psh_nat_trans
        (unit_dep_psh Γ)
        (dep_psh_closed_sieves Γ)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x _ _, truth_closed_sieve x).
    - abstract
        (intros x y xx yy f p q t ;
         use closed_sieve_eq ;
         cbn ;
         exact (truth_sieve_comp f)).
  Defined.

  Definition dep_sheaf_truth_mor
             (Γ : sheaf C)
    : terminal_in_fib (fiberwise_terminal_disp_cat_of_dep_sheaves C) Γ
      -->
      subobject_classifier_dep_sheaf Γ
    := dep_sheaf_truth Γ.

  (** * 4. The universal property of the subobject classifier *)
  Section SubobjectClassifierUMP.
    Context {Γ : sheaf C}
            {A B : dep_sheaf Γ}
            (τM : Monic ((disp_cat_of_dep_sheaves C)[{Γ}]) A B).

    Let τ : dep_psh_nat_trans A B (nat_trans_id _) := pr1 τM.
    Let τP : Monic (disp_cat_dep_psh C)[{pr1 Γ}] (pr1 A) (pr1 B).
    Proof.
      use make_Monic.
      - exact τ.
      - apply preserves_monic_dep_sheaf_incl.
        exact (pr2 τM).
    Defined.

    (** * 4.1. The characteristic morphism *)
    Section Predicate.
      Context {x : C}
              {xx : (Γ x : hSet)}
              (b : B x xx).

      Definition is_closed_fiber_sieve_matching_fam
                 {y : C}
                 (f : y --> x)
        : matching_family Γ (f ^* fiber_sieve τP b).
      Proof.
        use make_matching_family.
        - exact (λ z g _, #Γ (g · f) xx).
        - abstract
            (cbn ;
             intros z₁ z₂ g₁ g₂ h p a₁ a₂ ;
             refine (!(eqtohomot (functor_comp Γ _ _) _) @ _) ; cbn ;
             apply maponpaths_2 ;
             rewrite !assoc ;
             rewrite p ;
             apply idpath).
      Defined.

      Definition is_closed_fiber_sieve_amalgamation
                 {y : C}
                 (f : y --> x)
        : amalgamation (is_closed_fiber_sieve_matching_fam f).
      Proof.
        use make_amalgamation.
        - exact (#Γ f xx).
        - abstract
            (intros z g p ; cbn ;
             exact (!(eqtohomot (functor_comp Γ _ _) _))).
      Defined.

      Definition is_closed_fiber_sieve_matching_fam_dep
                 {y : C}
                 (f : y --> x)
        : matching_family_dep A (is_closed_fiber_sieve_matching_fam f).
      Proof.
        use make_matching_family_dep.
        - exact (λ z g aa, pr1 aa).
        - abstract
            (intros z₁ z₂ g₁ g₂ h p q₁ q₂ ; cbn in q₁, q₂ ; cbn ;
             use (monic_dep_psh_nat_trans_monic τP) ;
             unfold in_fiber in q₁, q₂ ;
             cbn in q₁, q₂ ;
             refine (_ @ !(pr2 q₁)) ;
             simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _) ;
             [ refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _) ;
               cbn ;
               apply maponpaths_2 ;
               rewrite <- p ;
               rewrite assoc ;
               apply idpath
             | etrans ;
               [ apply maponpaths ;
                 exact (pr2 q₂)
               | ] ;
               rewrite dep_psh_mor_comp' ;
               use dep_psh_mor_path_eq ;
               rewrite assoc ;
               rewrite p ;
               apply idpath ]).
      Defined.

      Proposition is_closed_fiber_sieve
        : is_closed_sieve (fiber_sieve τP b).
      Proof.
        intros y f p.
        cbn.
        unfold in_fiber.
        pose (dep_sheaf_amalgamation
                (is_dep_sheaf_dep_sheaf A)
                p
                (is_closed_fiber_sieve_matching_fam f)
                (is_closed_fiber_sieve_amalgamation f)
                (is_closed_fiber_sieve_matching_fam_dep f))
          as aa.
        cbn in aa.
        refine (aa ,, _).
        use (dep_sheaf_amalgamation_unique
               (is_dep_sheaf_dep_sheaf B)
               p
               (a := is_closed_fiber_sieve_amalgamation f)).
        - exact (dep_psh_nat_trans_on_matching_family
                   τ
                   (is_closed_fiber_sieve_matching_fam_dep f)).
        - cbn.
          intros z g q.
          refine (!(dep_psh_nat_trans_ax τ _ _ _ _) @ _).
          apply maponpaths.
          apply (dep_sheaf_amalgamation_restr
                   (is_dep_sheaf_dep_sheaf A)
                   p
                   (is_closed_fiber_sieve_matching_fam f)
                   (is_closed_fiber_sieve_amalgamation f)
                   (is_closed_fiber_sieve_matching_fam_dep f)).
        - cbn.
          intros z g q.
          rewrite dep_psh_mor_comp'.
          refine (_ @ !(pr2 q)).
          use dep_psh_mor_path_eq.
          apply idpath.
      Qed.

      Definition monic_to_closed_sieve
        : closed_sieve x.
      Proof.
        use make_closed_sieve.
        - exact (fiber_sieve τP b).
        - exact is_closed_fiber_sieve.
      Defined.
    End Predicate.

    Proposition dep_sheaf_characteristic_mor_naturality
                {x₁ x₂ : C}
                {xx₁ : (Γ x₁ : hSet)}
                {xx₂ : (Γ x₂ : hSet)}
                {f : x₂ --> x₁}
                (p : # Γ f xx₁ = xx₂)
                (b : B x₁ xx₁)
      : monic_to_closed_sieve (#d B f p b)
        =
        precomp_closed_sieve (monic_to_closed_sieve b) f.
    Proof.
      use closed_sieve_eq.
      use sieve_eq.
      + intros y g [ a q ].
        cbn in a, q ; cbn.
        simple refine (_ ,, _).
        * refine (#d A (identity _) _ a).
          abstract
            (refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _) ;
             cbn ;
             rewrite id_left ;
             rewrite <- p ;
             exact (eqtohomot (!(functor_comp Γ _ _)) _)).
        * cbn.
          unfold in_fiber in *.
          simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _).
          {
            abstract
              (refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _) ;
               cbn ;
               rewrite id_left ;
               rewrite <- p ;
               exact (eqtohomot (!(functor_comp Γ _ _)) _)).
          }
          etrans.
          {
            apply maponpaths.
            exact q.
          }
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
      + intros y g [ a q ].
        cbn in a, q ; cbn.
        simple refine (_ ,, _).
        * refine (#d A (identity _) _ a).
          abstract
            (refine (eqtohomot (functor_id Γ _) _ @ _) ;
             refine (eqtohomot (functor_comp Γ _ _) _ @ _) ;
             cbn ;
             apply maponpaths ;
             exact p).
        * cbn.
          unfold in_fiber in *.
          simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _).
          {
            abstract
              (refine (eqtohomot (functor_id Γ _) _ @ _) ;
               refine (eqtohomot (functor_comp Γ _ _) _ @ _) ;
               cbn ;
               apply maponpaths ;
               exact p).
          }
          etrans.
          {
            apply maponpaths.
            exact q.
          }
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
    Qed.

    Definition dep_sheaf_characteristic_mor
      : dep_psh_nat_trans B (dep_psh_closed_sieves Γ) (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - intros x xx b.
        exact (monic_to_closed_sieve b).
      - intros x₁ x₂ xx₁ xx₂ f p₁ p₂ b.
        exact (dep_sheaf_characteristic_mor_naturality p₁ b).
    Defined.

    Let θ : (disp_cat_of_dep_sheaves C)[{Γ}] ⟦ B , subobject_classifier_dep_sheaf Γ ⟧
      := dep_sheaf_characteristic_mor.

    (** * 4.2. The pullback square *)
    Proposition dep_sheaf_characteristic_mor_eq
      : τM · θ
        =
        TerminalArrow (dep_sheaves_terminal Γ) A
        · dep_sheaf_truth_mor Γ.
    Proof.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      refine (dep_sheaf_fiber_comp τM θ a @ _).
      refine (_ @ !(dep_sheaf_fiber_comp _ _ a)).
      cbn.
      use closed_sieve_eq.
      use sieve_eq.
      - intros.
        exact tt.
      - intros y f _ ; cbn.
        simple refine (_ ,, _).
        + exact (#d A f (idpath _) a).
        + unfold in_fiber ; cbn.
          exact (dep_psh_nat_trans_ax τ _ _ (idpath _) _).
    Qed.

    Section PullbackUMP.
      Context {Z : (disp_cat_of_dep_sheaves C)[{Γ}]}
              {ζ₁ : Z --> B}
              {ζ₂ : Z --> dep_sheaves_terminal Γ}
              (p : ζ₁ · θ = ζ₂ · dep_sheaf_truth_mor Γ).

      Definition unique_im_dep_sheaf_characteristic_mor
                 {x : C}
                 {xx : (Γ x : hSet)}
                 (z : (Z : dep_sheaf Γ) x xx)
        : ∃! (a : A x xx), τ x xx a = (ζ₁ : dep_psh_nat_trans _ _ _) x xx z.
      Proof.
        use iscontraprop1.
        - abstract
            (use invproofirrelevance ;
             intros [ a₁ p₁ ] [ a₂ p₂ ] ;
             use subtypePath ; [ intro ; apply setproperty | ] ;
             cbn ;
             use (monic_dep_psh_nat_trans_monic τP) ;
             exact (p₁ @ !p₂)).
        - pose proof (maponpaths (λ (ξ : dep_psh_nat_trans _ _ _), ξ x xx z) p)
            as q₁.
          simpl in q₁.
          pose (!(dep_sheaf_fiber_comp ζ₁ θ z) @ q₁)
            as q₂.
          simpl in q₂.
          pose (q₂ @ dep_sheaf_fiber_comp ζ₂ (dep_sheaf_truth_mor Γ) z)
            as q₃.
          simpl in q₃.
          pose (from_sieve_eq_r (maponpaths pr1 q₃) (identity x) tt) as a.
          simple refine (_ ,, _).
          + refine (#d A (identity _) _ (pr1 a)).
            exact (eqtohomot (functor_id Γ _) _ @ eqtohomot (functor_id Γ _) _).
          + cbn.
            pose (pr2 a) as r.
            unfold in_fiber in r.
            cbn in r.
            simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _) ;
              [ exact (eqtohomot (functor_id Γ _) _ @ eqtohomot (functor_id Γ _) _)
              | ].
            refine (maponpaths (#d B _ _) (pr2 a) @ _).
            cbn.
            rewrite !dep_psh_mor_comp'.
            apply dep_psh_mor_id'.
            rewrite id_left.
            apply idpath.
      Qed.

      Definition dep_sheaf_characteristic_mor_pb_mor_data
                 (x : C)
                 (xx : (Γ x : hSet))
                 (z : (Z : dep_sheaf Γ) x xx)
        : A x (nat_trans_id Γ x xx)
        := pr11 (unique_im_dep_sheaf_characteristic_mor z).

      Proposition dep_sheaf_characteristic_mor_pb_mor_laws
        : dep_psh_nat_trans_naturality dep_sheaf_characteristic_mor_pb_mor_data.
      Proof.
        intros x y xx yy f q₁ q₂ z.
        use (monic_dep_psh_nat_trans_monic τP).
        cbn.
        refine (pr21 (unique_im_dep_sheaf_characteristic_mor _) @ _).
        refine (!_).
        simple refine (dep_psh_nat_trans_ax τ _ _ q₁ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact (pr21 (unique_im_dep_sheaf_characteristic_mor _)).
        }
        refine (!_).
        apply dep_psh_nat_trans_ax.
      Qed.

      Definition dep_sheaf_characteristic_mor_pb_mor
        : Z --> A.
      Proof.
        use make_dep_psh_nat_trans.
        - exact dep_sheaf_characteristic_mor_pb_mor_data.
        - exact dep_sheaf_characteristic_mor_pb_mor_laws.
      Defined.

      Proposition dep_sheaf_characteristic_mor_pb_comm
        : dep_sheaf_characteristic_mor_pb_mor · τM = ζ₁.
      Proof.
        use dep_psh_nat_trans_eq.
        intros x xx z.
        refine (dep_sheaf_fiber_comp _ _ _ @ _).
        cbn.
        exact (pr21 (unique_im_dep_sheaf_characteristic_mor z)).
      Qed.

      Proposition dep_sheaf_characteristic_mor_pb_unique
                  (ξ : Z --> A)
                  (q : ξ · τM = ζ₁)
        : ξ = dep_sheaf_characteristic_mor_pb_mor.
      Proof.
        cbn in ξ.
        use dep_psh_nat_trans_eq.
        intros x xx z.
        use (monic_dep_psh_nat_trans_monic τP).
        cbn.
        pose proof (maponpaths (λ (ξ : dep_psh_nat_trans _ _ _), ξ x xx z) q)
          as r.
        simpl in r.
        refine (!(dep_sheaf_fiber_comp ξ τ z) @ r @ _).
        refine (!_).
        exact (pr21 (unique_im_dep_sheaf_characteristic_mor z)).
      Qed.
    End PullbackUMP.

    Definition dep_sheaf_characteristic_mor_isPullback
      : isPullback dep_sheaf_characteristic_mor_eq.
    Proof.
      intros Z ζ₁ ζ₂ p.
      use make_iscontr.
      - simple refine (_ ,, _ ,, _).
        + exact (dep_sheaf_characteristic_mor_pb_mor p).
        + exact (dep_sheaf_characteristic_mor_pb_comm p).
        + abstract
            (use dep_psh_nat_trans_eq ;
             intros ;
             apply isapropunit).
      - abstract
          (intros ξ ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           cbn ;
           apply dep_sheaf_characteristic_mor_pb_unique ;
           exact (pr12 ξ)).
    Defined.

    (** * 4.3. Uniqueness of the characteristic morphism *)
    Proposition dep_sheaf_characteristic_mor_unique
                (χ : dep_psh_nat_trans
                       B
                       (subobject_classifier_dep_sheaf Γ)
                       (nat_trans_id _))
                (p : τM · χ
                     =
                     TerminalArrow (dep_sheaves_terminal Γ) A
                     · dep_sheaf_truth_mor Γ)
                (H : isPullback p)
      : χ = dep_sheaf_characteristic_mor.
    Proof.
      assert (# (fiber_functor _ Γ) τM
              · # (fiber_functor (dep_sheaf_incl C) Γ) χ
              =
              # (fiber_functor _ Γ) (TerminalArrow (dep_sheaves_terminal Γ) A)
              · # (fiber_functor _ Γ) (dep_sheaf_truth_mor Γ))
        as r.
      {
        refine (!(functor_comp _ _ _) @ _ @ functor_comp _ _ _).
        apply maponpaths.
        exact p.
      }
      pose (PB := make_Pullback
                    _
                    (preserves_pullback_dep_sheaf_incl Γ _ _ _ _ _ _ _ _ _ r H)).
      use dep_psh_nat_trans_eq.
      intros x xx b.
      use closed_sieve_eq.
      use sieve_eq.
      - cbn ; intros y g γ.
        assert (compose
                  (C := (disp_cat_dep_psh C)[{pr1 Γ}])
                  (dep_psh_nat_trans_from_mor_dep_psh (#d B g (idpath _) b))
                  (#(fiber_functor (dep_sheaf_incl C) Γ) χ)
                =
                compose
                  (C := (disp_cat_dep_psh C)[{pr1 Γ}])
                  (dep_psh_nat_trans_to_unit _)
                  (#(fiber_functor (dep_sheaf_incl C) Γ) (dep_sheaf_truth_mor Γ)))
          as q.
        {
          rewrite !fiber_functor_dep_sheaf_incl.
          use dep_psh_nat_trans_eq.
          intros z zz a.
          refine (dep_psh_fiber_comp _ _ _ _ @ _).
          refine (_ @ !(dep_psh_fiber_comp _ _ _ _)).
          cbn.
          rewrite dep_psh_mor_comp'.
          assert (#Γ (pr1 a · g) xx = zz) as q.
          {
            refine (_ @ pr2 a).
            exact (eqtohomot (functor_comp Γ _ _) _).
          }
          refine (dep_psh_nat_trans_ax χ (pr1 a · g) _ q _ @ _).
          use closed_sieve_eq.
          use sieve_eq.
          {
            exact (λ _ _ _, tt).
          }
          intros w h _.
          simple refine (#ω (χ _ _ _ : closed_sieve _) _ _ γ).
          + exact (h · pr1 a).
          + cbn.
            rewrite assoc'.
            apply idpath.
        }
        pose (PullbackArrow
                PB
                (mor_dep_psh (#Γ g xx))
                (dep_psh_nat_trans_from_mor_dep_psh (#d B g (idpath _) b))
                (dep_psh_nat_trans_to_unit _)
                q : dep_psh_nat_trans _ _ _)
          as f.
        simple refine (_ ,, _).
        + exact (f _ _ (id_mor_dep_psh _)).
        + unfold in_fiber ; cbn.
          pose (PullbackArrow_PullbackPr1
                  PB
                  _ _ _
                  q)
            as r'.
          etrans.
          {
            pose (maponpaths
                    (λ (h : dep_psh_nat_trans _ _ _), h _ _ (id_mor_dep_psh _))
                    r')
              as eq.
            refine (_ @ eq).
            refine (_ @ !(dep_psh_fiber_comp _ _ _ _)).
            cbn -[fiber_category fiber_functor].
            refine (!_).
            apply (fiber_functor_dep_sheaf_incl_pt τ).
          }
          cbn.
          rewrite dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          apply id_left.
      - cbn ; intros y g [ a q ].
        unfold in_fiber in q ; cbn in a, q.
        simple refine (#ω (χ x xx b : closed_sieve _) (identity _) _ _).
        + exact (identity _ · g).
        + cbn.
          rewrite !id_left.
          apply idpath.
        + pose proof (dep_psh_nat_trans_ax χ g (idpath _) (idpath _) b)
            as r₁.
          cbn in r₁.
          pose proof (maponpaths (λ z : closed_sieve _, z _ (identity _)) r₁
              : _ = (χ x xx b : closed_sieve _) y (identity y · g))
            as r₂.
          cbn in r₂.
          cbn.
          rewrite <- r₂.
          clear r₁ r₂.
          pose proof (maponpaths (λ (h : dep_psh_nat_trans _ _ _), h _ _ a) p)
            as r₁.
          cbn -[fiber_category] in r₁.
          pose proof (!(dep_sheaf_fiber_comp τM χ a)
                      @ r₁
                      @ dep_sheaf_fiber_comp _ (dep_sheaf_truth_mor Γ) a)
            as r₂.
          clear r₁.
          cbn in r₂, a.
          pose (from_sieve_eq_r (maponpaths pr1 r₂) (identity _) tt) as r₃.
          use (transportf (λ (P : hProp), P) _ r₃).
          refine (maponpaths (λ (z : closed_sieve _), z y (identity _)) _).
          apply maponpaths.
          exact q.
    Qed.
  End SubobjectClassifierUMP.

  Definition dep_sheaf_subobject_classifier
             (Γ : sheaf C)
    : subobject_classifier (dep_sheaves_terminal Γ).
  Proof.
    use make_subobject_classifier.
    - exact (subobject_classifier_dep_sheaf Γ).
    - exact (dep_sheaf_truth Γ).
    - intros A B τ.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (dep_sheaf_characteristic_mor τ).
        * exact (dep_sheaf_characteristic_mor_eq τ).
        * exact (dep_sheaf_characteristic_mor_isPullback τ).
      + abstract
          (intro χ ;
           use subtypePath ;
           [ intro ;
             use isaproptotal2 ; [ intro ; apply isaprop_isPullback | ] ;
             intros ;
             apply homset_property
           | ] ;
           exact (dep_sheaf_characteristic_mor_unique τ (pr1 χ) (pr12 χ) (pr22 χ))).
  Defined.

  (** * 5. Stability of the subobject classifier *)
  Definition dep_sheaf_subobject_classifier_subst
             {Γ₁ Γ₂ : sheaf C}
             (s : sheaf_nat_trans Γ₁ Γ₂)
    : (disp_cat_of_dep_sheaves C)[{Γ₁}]
        ⟦ subobject_classifier_dep_sheaf Γ₁
        , dep_sheaf_subst s (subobject_classifier_dep_sheaf Γ₂) ⟧.
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ _ _ ω, ω).
    - abstract
        (intros x y xx yy f p q ω ; cbn ;
         apply idpath).
  Defined.

  Definition dep_sheaf_subobject_classifier_subst_inv
             {Γ₁ Γ₂ : sheaf C}
             (s : sheaf_nat_trans Γ₁ Γ₂)
    : (disp_cat_of_dep_sheaves C)[{Γ₁}]
        ⟦ dep_sheaf_subst s (subobject_classifier_dep_sheaf Γ₂)
        , subobject_classifier_dep_sheaf Γ₁ ⟧.
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ _ _ ω, ω).
    - abstract
        (intros x y xx yy f p q ω ; cbn ;
         apply idpath).
  Defined.

  Definition dep_sheaf_subobject_classifier_preservation
             {Γ₁ Γ₂ : sheaf C}
             (s : sheaf_nat_trans Γ₁ Γ₂)
    : preserves_subobject_classifier
        (fiber_functor_from_cleaving
           (disp_cat_of_dep_sheaves C)
           (cleaving_disp_cat_of_dep_sheaves C)
           s)
        (dep_sheaves_terminal Γ₂)
        (dep_sheaves_terminal Γ₁)
        (dep_sheaves_preserves_terminal s).
  Proof.
    use preserves_chosen_to_preserves_subobject_classifier'.
    - use is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    - use is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    - exact (dep_sheaf_subobject_classifier Γ₂).
    - use (z_iso_to_is_subobject_classifier
             (C := univalent_fiber_category (disp_cat_of_dep_sheaves C) _)).
      + exact (dep_sheaf_subobject_classifier Γ₁).
      + use make_z_iso.
        * exact (dep_sheaf_subobject_classifier_subst s).
        * exact (dep_sheaf_subobject_classifier_subst_inv s).
        * abstract
            (split ;
             use dep_psh_nat_trans_eq ;
             intros x xx ω ;
             [ exact (dep_sheaf_fiber_comp
                        (dep_sheaf_subobject_classifier_subst s)
                        (dep_sheaf_subobject_classifier_subst_inv s)
                        _)
             | exact (dep_sheaf_fiber_comp
                        (dep_sheaf_subobject_classifier_subst_inv s)
                        (dep_sheaf_subobject_classifier_subst s)
                        _) ]).
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx ω ;
           refine (dep_sheaf_fiber_comp
                     (dep_sheaf_truth_mor Γ₁)
                     (dep_sheaf_subobject_classifier_subst s) _ @ _) ;
           refine (_ @ !(dep_sheaf_fiber_comp _ _ _)) ;
           refine (_ @ !(fiber_functor_from_cleaving_dep_sheaf s _ _)) ;
           cbn ;
           apply idpath).
  Defined.
End SubobjectClassifier.
