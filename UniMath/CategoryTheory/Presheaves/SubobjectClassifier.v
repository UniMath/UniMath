(**

 Subobject classifier of presheaves

 We show that the presheaf model supports a subobject classifier type, which corresponds
 to the categorical statement that says that the category of presheaves comes with a
 subobject classifier. In this file, we approach this statement from a type theoretic
 perspective. Specifically, we equip each fiber category of dependent presheaves with
 a subobject classifier and we show that subobject classifiers are preserved under
 substitution (aka reindexing).

 Content
 1. Sieves
 2. The presheaf of sieves
 3. The canonical monomorphism into the presheaf of sieves
 4. The universal property of the subobject classifier
 5. Stability of the subobject classifier

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.

Local Open Scope cat.

Section SubobjectClassifier.
  Context {C : category}.

  (** * 1. Sieves *)
  Definition sieve
             (x : C)
    : UU
    := (C / x)^op ⟶ hProp_category.

  Definition sieve_ob
             {x : C}
             (ω : sieve x)
             {y : C}
             (f : y --> x)
    : hProp
    := pr1 ω (make_cod_fib_ob f).

  Coercion sieve_ob : sieve >-> Funclass.

  Definition sieve_mor
             {x : C}
             (ω : sieve x)
             {y₁ y₂ : C}
             {f₁ : y₁ --> x}
             {f₂ : y₂ --> x}
             (h : y₁ --> y₂)
             (p : h · f₂ = f₁)
             (q : ω y₂ f₂)
    : ω y₁ f₁
    := # (ω : functor _ _)
         (make_cod_fib_mor
            (f₁ := make_cod_fib_ob f₁)
            (f₂ := make_cod_fib_ob f₂)
            h
            p)
         q.

  Notation "#ω" := sieve_mor : cat.

  Definition make_sieve
             (x : C)
             (ωo : ∏ (y : C), y --> x → hProp)
             (ωm : ∏ (y₁ y₂ : C)
                     (g₁ : y₁ --> x)
                     (g₂ : y₂ --> x)
                     (h : y₂ --> y₁)
                     (p : h · g₁ = g₂),
                   ωo y₁ g₁ → ωo y₂ g₂)
    : sieve x.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact (λ g, ωo (pr1 g) (pr2 g)).
      + refine (λ g₁ g₂ h, ωm (pr1 g₁) (pr1 g₂) (pr2 g₁) (pr2 g₂) (pr1 h) _).
        abstract
          (exact (pr2 h @ id_right _)).
    - abstract
        (split ; intro ; intros ; apply propproperty).
  Defined.

  Definition sieve_eq
             {x : C}
             {ω₁ ω₂ : sieve x}
             (p : ∏ (y : C) (g : y --> x), ω₁ y g → ω₂ y g)
             (q : ∏ (y : C) (g : y --> x), ω₂ y g → ω₁ y g)
    : ω₁ = ω₂.
  Proof.
    use functor_eq.
    {
      apply homset_property.
    }
    use subtypePath.
    {
      intro.
      repeat (use impred ; intro).
      apply propproperty.
    }
    use funextsec.
    intro g.
    use hPropUnivalence.
    - exact (p (pr1 g) (pr2 g)).
    - exact (q (pr1 g) (pr2 g)).
  Qed.

  Definition from_sieve_eq_l
             {x y : C}
             {ω₁ ω₂ : sieve x}
             (p : ω₁ = ω₂)
             (g : y --> x)
    : ω₁ y g → ω₂ y g.
  Proof.
    induction p.
    exact (λ z, z).
  Defined.

  Definition from_sieve_eq_r
             {x y : C}
             {ω₁ ω₂ : sieve x}
             (p : ω₁ = ω₂)
             (g : y --> x)
    : ω₂ y g → ω₁ y g.
  Proof.
    induction p.
    exact (λ z, z).
  Defined.

  Proposition isaset_sieve
              (x : C)
    : isaset (sieve x).
  Proof.
    use isaset_total2.
    - use isaset_total2.
      + use impred_isaset.
        intro.
        apply setproperty.
      + intro.
        do 3  (use impred_isaset ; intro).
        apply homset_property.
    - intro.
      use isasetaprop.
      use isaprop_is_functor.
      apply homset_property.
  Qed.

  Definition set_of_sieves
             (x : C)
    : hSet.
  Proof.
    use make_hSet.
    - exact (sieve x).
    - exact (isaset_sieve x).
  Defined.

  Definition precomp_sieve
             {x y : C}
             (f : x --> y)
             (ω : sieve y)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ w h, ω _ (h · f)).
    - intros y₁ y₂ g₁ g₂ h p q.
      simple refine (#ω ω  _ _ q).
      + exact h.
      + abstract
          (cbn in * ;
           rewrite !assoc ;
           rewrite p ;
           apply idpath).
  Defined.

  Notation "f ^* ω" := (precomp_sieve f ω) (at level 50) : cat.

  (** * 2. The presheaf of sieves *)
  Proposition id_precomp_sieve
              {x : C}
              (ω : sieve x)
    : identity x ^* ω = ω.
  Proof.
    use sieve_eq.
    - intros g q ; simpl in q.
      simple refine (#ω ω _ _).
      + apply identity.
      + cbn.
        rewrite id_left, id_right.
        apply idpath.
    - intros g q ; simpl in q.
      simple refine (#ω ω _ _).
      + apply identity.
      + cbn.
        rewrite id_left, id_right.
        apply idpath.
  Qed.

  Proposition comp_precomp_sieve
              {x y z : C}
              (f₁ : y --> x)
              (f₂ : z --> y)
              (ω : sieve x)
    : (f₂ · f₁)^* ω = f₂ ^* (f₁ ^* ω).
  Proof.
    use sieve_eq.
    - intros g q ; simpl in q.
      simple refine (#ω ω _ _).
      + apply identity.
      + cbn.
        rewrite id_left.
        rewrite assoc'.
        apply idpath.
    - intros g q ; simpl in q.
      simple refine (#ω ω _ _).
      + apply identity.
      + cbn.
        rewrite id_left.
        rewrite assoc'.
        apply idpath.
  Qed.

  Definition dep_psh_subobject_classifier_ob
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, set_of_sieves x).
    - exact (λ x y xx yy f p ω, f^* ω).
    - intros x xx p ω.
      exact (id_precomp_sieve ω).
    - intros x y z xx yy zz f₁ f₂ p q r ω.
      exact (comp_precomp_sieve f₁ f₂ ω).
  Defined.

  (** * 3. The canonical monomorphism into the presheaf of sieves *)
  Definition truth_sieve
             (x : C)
    : sieve x
    := constant_functor _ hProp_category htrue.

  Definition truth_sieve_comp
             {x y : C}
             (f : y --> x)
    : truth_sieve y = f^* truth_sieve x.
  Proof.
    use sieve_eq.
    - exact (λ _ _ _, tt).
    - exact (λ _ _ _, tt).
  Qed.

  Definition dep_psh_truth
             (Γ : C^op ⟶ HSET)
    : dep_psh_nat_trans
        (unit_dep_psh Γ)
        (dep_psh_subobject_classifier_ob Γ)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x _ _, truth_sieve x).
    - intros x y xx yy f p q t.
      cbn.
      exact (truth_sieve_comp f).
  Defined.

  (** * 4. The universal property of the subobject classifier *)
  Section SubobjectClassifierUMP.
    Context {Γ : C^op ⟶ HSET}
            {A B : dep_psh Γ}
            (τM : Monic ((disp_cat_dep_psh C) [{Γ}]) A B).

    Let τ : dep_psh_nat_trans A B (nat_trans_id _) := pr1 τM.

    Proposition monic_dep_psh_nat_trans_monic
                {x : C}
                {xx : (Γ x : hSet)}
                {a₁ a₂ : A x xx}
                (p : τ x xx a₁ = τ x xx a₂)
      : a₁ = a₂.
    Proof.
      pose (pr2 τM (mor_dep_psh xx)
                   (dep_psh_nat_trans_from_mor_dep_psh a₁)
                   (dep_psh_nat_trans_from_mor_dep_psh a₂))
        as q.
      simple refine (_
                     @ maponpaths
                         (λ (ξ : dep_psh_nat_trans (mor_dep_psh xx) A _),
                           ξ x xx (id_mor_dep_psh xx))
                         (q _)
                     @ _).
      - cbn.
        rewrite dep_psh_mor_id.
        apply idpath.
      - use dep_psh_nat_trans_eq.
        intros y yy a.
        rewrite !dep_psh_fiber_comp.
        cbn.
        refine (dep_psh_nat_trans_ax τ _ _ (pr2 a) _ @ _).
        refine (_ @ !(dep_psh_nat_trans_ax τ _ _ (pr2 a) _)).
        apply maponpaths.
        exact p.
      - cbn.
        rewrite dep_psh_mor_id.
        apply idpath.
    Qed.

    Section Fiber.
      Context {x : C}
              {xx : (Γ x : hSet)}
              (b : B x xx).

      Definition in_fiber
                 {y : C}
                 (g : y --> x)
                 (a : A y (# Γ g xx))
        : UU
        := τ y (# Γ g xx) a = #d B g (idpath (# Γ g xx)) b.

      Proposition isaprop_mor_in_fiber
                  {y : C}
                  (g : y --> x)
        : isaprop
            (∑ (a : A y (# Γ g xx)), in_fiber g a).
      Proof.
        use invproofirrelevance.
        intros a₁ a₂.
        use subtypePath.
        {
          intro.
          apply setproperty.
        }
        use monic_dep_psh_nat_trans_monic.
        exact (pr2 a₁ @ !(pr2 a₂)).
      Qed.

      Definition mor_in_fiber
                 {y : C}
                 (g : y --> x)
        : hProp.
      Proof.
        use make_hProp.
        - exact (∑ (a : A y (#Γ g xx)), in_fiber g a).
        - exact (isaprop_mor_in_fiber g).
      Defined.

      Proposition fiber_sieve_mor_eq
                  {y₁ y₂ : C}
                  {g₁ : y₁ --> x}
                  {g₂ : y₂ --> x}
                  {h : y₂ --> y₁}
                  (p : h · g₁ = g₂)
        : #Γ h (#Γ g₁ xx) = #Γ g₂ xx.
      Proof.
        refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _).
        rewrite <- p.
        apply idpath.
      Qed.

      Proposition in_fiber_fiber_sieve_mor
                  {y₁ y₂ : C}
                  {g₁ : y₁ --> x}
                  {g₂ : y₂ --> x}
                  {h : y₂ --> y₁}
                  (p : h · g₁ = g₂)
                  (a : mor_in_fiber g₁)
        : in_fiber g₂ (#d A h (fiber_sieve_mor_eq p) (pr1 a)).
      Proof.
        simple refine (dep_psh_nat_trans_ax τ h _ _ _ @ _).
        {
          cbn.
          apply fiber_sieve_mor_eq.
          exact p.
        }
        etrans.
        {
          apply maponpaths.
          exact (pr2 a).
        }
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        exact p.
      Qed.

      Definition fiber_sieve_mor
                 {y₁ y₂ : C}
                 {g₁ : y₁ --> x}
                 {g₂ : y₂ --> x}
                 {h : y₂ --> y₁}
                 (p : h · g₁ = g₂)
                 (a : mor_in_fiber g₁)
        : mor_in_fiber g₂.
      Proof.
        simple refine (_ ,, _).
        - exact (#d A h (fiber_sieve_mor_eq p) (pr1 a)).
        - exact (in_fiber_fiber_sieve_mor p a).
      Defined.

      Definition fiber_sieve
        : sieve x.
      Proof.
        use make_sieve.
        - exact (λ y g, mor_in_fiber g).
        - exact (λ y₁ y₂ g₁ g₂ h p a, fiber_sieve_mor p a).
      Defined.
    End Fiber.

    Proposition dep_psh_characteristic_mor_natural
                {x y : C}
                {xx : (Γ x : hSet)}
                {yy : (Γ y : hSet)}
                {f : y --> x}
                (p q : #Γ f xx = yy)
                (b : B x xx)
      : fiber_sieve (#d B f p b)
        =
        #d (dep_psh_subobject_classifier_ob Γ) f q (fiber_sieve b).
    Proof.
      use sieve_eq.
      - intros z g [ a r ].
        simple refine (_ ,, _).
        + simple refine (#d A (identity _) _ a).
          abstract
            (refine (eqtohomot (functor_id Γ _) _ @ _) ;
             cbn ;
             rewrite <- p ;
             exact (!(eqtohomot (functor_comp Γ _ _) _))).
        + unfold in_fiber ; cbn.
          simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _).
          {
            abstract
              (refine (eqtohomot (functor_id Γ _) _ @ _) ;
               cbn ;
               rewrite <- p ;
               exact (!(eqtohomot (functor_comp Γ _ _) _))).
          }
          etrans.
          {
            apply maponpaths.
            exact r.
          }
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
      - intros z g [ a r ].
        simple refine (_ ,, _).
        + simple refine (#d A (identity _) _ a).
          abstract
            (refine (eqtohomot (functor_id Γ _) _ @ _) ;
             cbn ;
             rewrite <- p ;
             exact (eqtohomot (functor_comp Γ _ _) _)).
        + unfold in_fiber ; cbn.
          simple refine (dep_psh_nat_trans_ax τ _ _ _ _ @ _).
          {
            abstract
              (refine (eqtohomot (functor_id Γ _) _ @ _) ;
               cbn ;
               rewrite <- p ;
               exact (eqtohomot (functor_comp Γ _ _) _)).
          }
          etrans.
          {
            apply maponpaths.
            exact r.
          }
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
    Qed.

    Definition dep_psh_characteristic_mor
      : dep_psh_nat_trans
          B
          (dep_psh_subobject_classifier_ob Γ)
          (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx b, fiber_sieve b).
      - intros x y xx yy f p q a.
        exact (dep_psh_characteristic_mor_natural p q a).
    Defined.

    Proposition dep_psh_characteristic_mor_truth
                {x : C}
                {xx : (Γ x : hSet)}
                (a : A x xx)
      : dep_psh_characteristic_mor x xx (τ x xx a) = truth_sieve x.
    Proof.
      use sieve_eq.
      - intros.
        exact tt.
      - intros y g t ; cbn in *.
        simple refine (_ ,, _).
        + exact (#d A g (idpath _) a).
        + unfold in_fiber ; cbn.
          exact (dep_psh_nat_trans_ax τ _ _ _ _).
    Qed.

    Proposition dep_psh_characteristic_mor_pb_eq
      : τM · dep_psh_characteristic_mor
        =
        TerminalArrow (dep_psh_fiber_terminal Γ) A · dep_psh_truth Γ.
    Proof.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      refine (_ @ !(dep_psh_fiber_comp _ _ _ _)).
      exact (dep_psh_characteristic_mor_truth a).
    Qed.

    Section Pullback.
      Context {Z : dep_psh Γ}
              {θ₁ : dep_psh_nat_trans Z B (nat_trans_id _)}
              {θ₂ : dep_psh_nat_trans Z (unit_dep_psh Γ) (nat_trans_id _)}
              (p : compose
                     (C := (disp_cat_dep_psh C)[{Γ}])
                     θ₁
                     (dep_psh_characteristic_mor)
                   =
                   compose
                     (C := (disp_cat_dep_psh C)[{Γ}])
                     θ₂
                     (dep_psh_truth Γ)).

      Definition unique_im_dep_psh_psh_characteristic_mor
                 {x : C}
                 {xx : (Γ x : hSet)}
                 (z : Z x xx)
        : ∃! (a : A x xx), τ x xx a = θ₁ x xx z.
      Proof.
        use iscontraprop1.
        - abstract
            (use invproofirrelevance ;
             intros [ a₁ p₁ ] [ a₂ p₂ ] ;
             use subtypePath ; [ intro ; apply setproperty | ] ;
             cbn ;
             use monic_dep_psh_nat_trans_monic ;
             exact (p₁ @ !p₂)).
        - pose proof (maponpaths (λ (ξ : dep_psh_nat_trans _ _ _), ξ x xx z) p)
            as q₁.
          simpl in q₁.
          pose (!(dep_psh_fiber_comp _ θ₁ dep_psh_characteristic_mor z) @ q₁)
            as q₂.
          simpl in q₂.
          pose (q₂ @ dep_psh_fiber_comp _ θ₂ (dep_psh_truth Γ) z)
            as q₃.
          simpl in q₃.
          pose (from_sieve_eq_r q₃ (identity x) tt) as a.
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

      Definition dep_psh_characteristic_mor_pb_mor_data
                 (x : C)
                 (xx : (Γ x : hSet))
                 (z : Z x xx)
        : A x (nat_trans_id Γ x xx)
        := pr11 (unique_im_dep_psh_psh_characteristic_mor z).

      Proposition dep_psh_characteristic_mor_pb_mor_laws
        : dep_psh_nat_trans_naturality dep_psh_characteristic_mor_pb_mor_data.
      Proof.
        intros x y xx yy f q₁ q₂ z.
        use monic_dep_psh_nat_trans_monic.
        cbn.
        refine (pr21 (unique_im_dep_psh_psh_characteristic_mor _) @ _).
        refine (!_).
        simple refine (dep_psh_nat_trans_ax τ _ _ q₁ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact (pr21 (unique_im_dep_psh_psh_characteristic_mor _)).
        }
        refine (!_).
        apply dep_psh_nat_trans_ax.
      Qed.

      Definition dep_psh_characteristic_mor_pb_mor
        : dep_psh_nat_trans Z A (nat_trans_id _).
      Proof.
        use make_dep_psh_nat_trans.
        - exact dep_psh_characteristic_mor_pb_mor_data.
        - exact dep_psh_characteristic_mor_pb_mor_laws.
      Defined.

      Proposition dep_psh_characteristic_mor_pb_comm
        : compose
            (C := (disp_cat_dep_psh C)[{Γ}])
            dep_psh_characteristic_mor_pb_mor
            τM = θ₁.
      Proof.
        use dep_psh_nat_trans_eq.
        intros x xx z.
        refine (dep_psh_fiber_comp _ _ _ _ @ _).
        cbn.
        exact (pr21 (unique_im_dep_psh_psh_characteristic_mor z)).
      Defined.

      Proposition dep_psh_characteristic_mor_pb_unique
                  (ξ : (disp_cat_dep_psh C)[{Γ}] ⟦ Z, A ⟧)
                  (q : ξ · τM = θ₁)
        : ξ = dep_psh_characteristic_mor_pb_mor.
      Proof.
        cbn in ξ.
        use dep_psh_nat_trans_eq.
        intros x xx z.
        use monic_dep_psh_nat_trans_monic.
        cbn.
        pose proof (maponpaths (λ (ξ : dep_psh_nat_trans _ _ _), ξ x xx z) q)
          as r.
        simpl in r.
        refine (!(dep_psh_fiber_comp _ ξ τ z) @ r @ _).
        refine (!_).
        exact (pr21 (unique_im_dep_psh_psh_characteristic_mor z)).
      Qed.
    End Pullback.

    Proposition dep_psh_characteristic_mor_isPullback
      : isPullback dep_psh_characteristic_mor_pb_eq.
    Proof.
      intros Z θ₁ θ₂ p.
      use make_iscontr.
      - simple refine (_ ,, _ ,, _).
        + exact (dep_psh_characteristic_mor_pb_mor p).
        + exact (dep_psh_characteristic_mor_pb_comm p).
        + apply dep_psh_nat_trans_to_unit_eq.
      - abstract
          (intros ξ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           cbn ;
           apply dep_psh_characteristic_mor_pb_unique ;
           exact (pr12 ξ)).
    Defined.

    Proposition dep_psh_characteristic_mor_unique
                (χ : dep_psh_nat_trans
                       B
                       (dep_psh_subobject_classifier_ob Γ)
                       (nat_trans_id _))
                (p : τM · χ
                     =
                     TerminalArrow (dep_psh_fiber_terminal Γ) A · dep_psh_truth Γ)
                (H : isPullback p)
      : χ = dep_psh_characteristic_mor.
    Proof.
      pose (PB := make_Pullback _ H).
      use dep_psh_nat_trans_eq.
      intros x xx b.
      use sieve_eq.
      - cbn ; intros y g γ.
        assert (compose
                  (C := (disp_cat_dep_psh C)[{Γ}])
                  (dep_psh_nat_trans_from_mor_dep_psh (#d B g (idpath _) b))
                  χ
                =
                compose
                  (C := (disp_cat_dep_psh C)[{Γ}])
                  (dep_psh_nat_trans_to_unit _)
                  (dep_psh_truth Γ))
          as q.
        {
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
          use sieve_eq.
          {
            exact (λ _ _ _, tt).
          }
          intros w h _.
          simple refine (#ω (χ _ _ _ : sieve _) _ _ γ).
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
            as r.
          etrans.
          {
            refine (!(dep_psh_fiber_comp _ _ _ _) @ _).
            exact (maponpaths (λ (h : dep_psh_nat_trans _ _ _), h _ _ (id_mor_dep_psh _)) r).
          }
          cbn.
          rewrite dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          apply id_left.
      - cbn ; intros y g [ a q ].
        unfold in_fiber in q ; cbn in a, q.
        simple refine (#ω (χ x xx b : sieve _) (identity _) _ _).
        + exact (identity _ · g).
        + cbn.
          rewrite !id_left.
          apply idpath.
        + pose proof (dep_psh_nat_trans_ax χ g (idpath _) (idpath _) b)
            as r₁.
          cbn in r₁.
          pose proof (maponpaths (λ z : sieve _, z _ (identity _)) r₁
              : _ = (χ x xx b : sieve _) y (identity y · g))
            as r₂.
          cbn in r₂.
          cbn.
          rewrite <- r₂.
          clear r₁ r₂.
          rewrite <- q.
          pose proof (maponpaths (λ (h : dep_psh_nat_trans _ _ _), h _ _ a) p)
            as r₁.
          pose proof (!(dep_psh_fiber_comp _ _ _ _) @ r₁ @ dep_psh_fiber_comp _ _ _ _)
            as r₂.
          clear r₁.
          cbn in r₂, a.
          pose (from_sieve_eq_r r₂ (identity _) tt) as r₃.
          cbn in r₃.
          exact r₃.
    Qed.
  End SubobjectClassifierUMP.

  Definition dep_psh_subobject_classifier
             (Γ : C^op ⟶ HSET)
    : subobject_classifier (dep_psh_fiber_terminal Γ).
  Proof.
    use make_subobject_classifier.
    - exact (dep_psh_subobject_classifier_ob Γ).
    - exact (dep_psh_truth Γ).
    - intros A B τ.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (dep_psh_characteristic_mor τ).
        * exact (dep_psh_characteristic_mor_pb_eq τ).
        * exact (dep_psh_characteristic_mor_isPullback τ).
      + abstract
          (intro χ ;
           use subtypePath ;
           [ intro ;
             use isaproptotal2 ; [ intro ; apply isaprop_isPullback | ] ;
             intros ;
             apply homset_property
           | ] ;
           exact (dep_psh_characteristic_mor_unique τ (pr1 χ) (pr12 χ) (pr22 χ))).
  Defined.

  (** * 5. Stability of the subobject classifier *)
  Definition dep_psh_subobject_classifier_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subobject_classifier_ob Γ₁)
        (dep_psh_subst s (dep_psh_subobject_classifier_ob Γ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ _ _ ω, ω).
    - abstract
        (intros x y xx yy f p q ω ; cbn ;
         apply idpath).
  Defined.

  Definition dep_psh_subobject_classifier_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (dep_psh_subobject_classifier_ob Γ₂))
        (dep_psh_subobject_classifier_ob Γ₁)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ _ _ ω, ω).
    - abstract
        (intros x y xx yy f p q ω ; cbn ;
         apply idpath).
  Defined.

  Definition dep_psh_subobject_classifier_preservation
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_subobject_classifier
        (fiber_functor_from_cleaving (disp_cat_dep_psh C) (cleaving_disp_cat_dep_psh C) s)
        (dep_psh_fiber_terminal Γ₂)
        (dep_psh_fiber_terminal Γ₁)
        (dep_psh_preserves_terminal s).
  Proof.
    use preserves_chosen_to_preserves_subobject_classifier'.
    - use is_univalent_fiber.
      apply is_univalent_disp_disp_cat_dep_psh.
    - use is_univalent_fiber.
      apply is_univalent_disp_disp_cat_dep_psh.
    - exact (dep_psh_subobject_classifier Γ₂).
    - use (z_iso_to_is_subobject_classifier
             (C := univalent_fiber_category (univalent_disp_cat_dep_psh C) _)).
      + exact (dep_psh_subobject_classifier Γ₁).
      + use make_z_iso.
        * exact (dep_psh_subobject_classifier_subst s).
        * exact (dep_psh_subobject_classifier_subst_inv s).
        * abstract
            (split ;
             use dep_psh_nat_trans_eq ;
             intros x xx ω ;
             refine (dep_psh_fiber_comp _ _ _ _)).
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx ω ;
           rewrite !dep_psh_fiber_comp ;
           refine (_ @ !(dep_psh_fiber_functor_from_cleaving _ s _ _)) ;
           cbn ;
           apply idpath).
  Defined.
End SubobjectClassifier.

Notation "#ω" := sieve_mor : cat.
Notation "f ^* ω" := (precomp_sieve f ω) (at level 50) : cat.
