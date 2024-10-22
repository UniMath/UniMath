(**********************************************************************************************

 The category of H-valued sets

 In this file, we construct the topos of sets valued in a complete Heyting algebra. Given a
 complete Heyting algebra [H], an [H]-valued set consists of a set [X] together with a partial
 equivalence relation on [X] valued in [H]. This category was originally considered independently
 by Higgs and by Fourman and Scott. They provide a categorical way to understand Heyting valued
 models for IZF and Boolean-valued models for ZFC.

 To define the category of H-valued sets, we follow the paper "Tripos Theory in Retrospect" by
 Andrew Pitts, and we use the tripos to topos construction. From this, we directly obtain that
 this category is a topos.

 References
 - "Injectivity in the topos of complete Heyting Algebra valued sets" by Denis Higgs
 - "Sheaves and logic" by Fourman and Scott
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Contents
 1. The topos of H-valued sets
 2. Accessors and builders for H-valued sets
 3. Accessors and builders for morphisms of H-valued sets

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.HValuedPredicates.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.TriposToTopos.

Local Open Scope cat.
Local Open Scope hd.

Section HValuedSets.
  Context (H : complete_heyting_algebra).

  (** * 1. The topos of H-valued sets *)
  Definition topos_of_h_valued_sets
    : Topos
    := tripos_to_topos (tripos_h_valued_sets H).

  (** * 2. Accessors and builders for H-valued sets *)
  Definition h_valued_set
    : UU
    := ob topos_of_h_valued_sets.

  Definition make_h_valued_set
             (X : hSet)
             (R : X → X → H)
             (sym : ∏ (x y : X), R x y = R y x)
             (trans : ∏ (x y z : X), ((R x y ∧ R y z) ≤ R x z)%heyting)
    : h_valued_set.
  Proof.
    use make_partial_setoid.
    - exact X.
    - use make_per.
      + exact (λ x, R (pr1 x) (pr2 x)).
      + repeat split ; intros [] ; cbn.
        * abstract
            (use cha_le_glb ;
             intros i ;
             induction i as [ [ [] x ] p ] ;
             use cha_le_glb ;
             intros i ;
             induction i as [ [ [ [] y ] z ] q ] ;
             cbn in * ;
             use cha_to_le_exp ;
             rewrite cha_lunit_min_top ;
             rewrite sym ;
             apply cha_le_refl).
        * abstract
            (use cha_le_glb ;
             intros i ;
             induction i as [ [ [] x₁ ] p ] ;
             use cha_le_glb ;
             intros i ;
             induction i as [ [ [ [] x₂ ] x₃ ] q ] ;
             use cha_le_glb ;
             intros i ;
             induction i as [ [ [ [ [] x₄ ] x₅ ] x₆ ] r ] ;
             cbn in * ;
             do 2 use cha_to_le_exp ;
             rewrite cha_lunit_min_top ;
             apply trans).
  Defined.

  Coercion set_of_h_valued_set
           (X : h_valued_set)
    : hSet
    := pr1 X.

  Definition per_of_h_valued_set
             {X : h_valued_set}
             (x y : X)
    : H
    := pr12 X (x ,, y).

  Notation "x ~_{ X } y" := (@per_of_h_valued_set X x y) (at level 10).

  Proposition sym_per_of_h_valued_set
              {X : h_valued_set}
              (x y : X)
    : x ~_{X} y = y ~_{X} x.
  Proof.
    pose (pr122 X tt) as p.
    cbn in p ; unfold prodtofuntoprod in p ; cbn in p.
    use cha_le_antisymm.
    - assert (⊤ ≤ (x ~_{X} y ⇒ y ~_{X} x))%heyting as q.
      {
        refine (cha_le_trans p _).
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          refine ((tt ,, x) ,, _).
          apply idpath.
        }
        cbn.
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          refine (((tt ,, x) ,, y) ,, _).
          apply idpath.
        }
        cbn.
        apply cha_le_refl.
      }
      pose proof (cha_from_le_exp q) as r.
      rewrite cha_lunit_min_top in r.
      exact r.
    - assert (⊤ ≤ (y ~_{X} x ⇒ x ~_{X} y))%heyting as q.
      {
        refine (cha_le_trans p _).
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          refine ((tt ,, y) ,, _).
          apply idpath.
        }
        cbn.
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          refine (((tt ,, y) ,, x) ,, _).
          apply idpath.
        }
        cbn.
        apply cha_le_refl.
      }
      pose proof (cha_from_le_exp q) as r.
      rewrite cha_lunit_min_top in r.
      exact r.
  Qed.

  Proposition trans_per_of_h_valued_set
              {X : h_valued_set}
              (x y z : X)
    : ((x ~_{X} y ∧ y ~_{X} z) ≤ (x ~_{X} z))%heyting.
  Proof.
    pose (pr222 X tt) as p.
    cbn in p ; unfold prodtofuntoprod in p ; cbn in p.
    assert (⊤ ≤ (x ~_{X} y ⇒ y ~_{X} z ⇒ x ~_{X} z))%heyting as q.
    {
      refine (cha_le_trans p _).
      simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
      {
        refine ((tt ,, x) ,, _).
        apply idpath.
      }
      cbn.
      simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
      {
        refine (((tt ,, x) ,, y) ,, _).
        apply idpath.
      }
      cbn.
      simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
      {
        refine ((((tt ,, x) ,, y) ,, z) ,, _).
        cbn.
        apply idpath.
      }
      cbn.
      apply cha_le_refl.
    }
    pose proof (cha_from_le_exp q) as r.
    rewrite cha_lunit_min_top in r.
    exact (cha_from_le_exp r).
  Qed.

  (** * 3. Accessors and builders for morphisms of H-valued sets *)
  Definition h_valued_morphism
             (X Y : h_valued_set)
    : UU
    := X --> Y.

  Definition h_valued_morphism_is_function
             {X Y : h_valued_set}
             (f : h_valued_morphism X Y)
             (x : X)
             (y : Y)
    : H
    := partial_setoid_morphism_to_form f (x ,, y).

  Coercion h_valued_morphism_is_function : h_valued_morphism >-> Funclass.

  Section Accessors.
    Context {X Y : h_valued_set}
            (f : h_valued_morphism X Y).

    Proposition h_valued_morphism_dom_defined
                (x : X)
                (y : Y)
      : (f x y ≤ x ~_{X} x)%heyting.
    Proof.
      refine (@partial_setoid_mor_dom_defined
                 _ _ _ f
                 unitset
                 (λ _, f x y) (λ _, x) (λ _, y)
                 _
                 tt).
      intro ; cbn ; unfold prodtofuntoprod ; cbn.
      apply cha_le_refl.
    Qed.

    Proposition h_valued_morphism_cod_defined
                (x : X)
                (y : Y)
      : (f x y ≤ (y ~_{Y} y))%heyting.
    Proof.
      refine (@partial_setoid_mor_cod_defined
                 _ _ _ f
                 unitset
                 (λ _, f x y) (λ _, x) (λ _, y)
                 _
                 tt).
      intro ; cbn ; unfold prodtofuntoprod ; cbn.
      apply cha_le_refl.
    Qed.

    Proposition h_valued_morphism_eq_defined
                (x₁ x₂ : X)
                (y₁ y₂ : Y)
      :  ((x₁ ~_{X} x₂ ∧ y₁ ~_{Y} y₂ ∧ f x₁ y₁) ≤ f x₂ y₂)%heyting.
    Proof.
      refine (@partial_setoid_mor_eq_defined
                 _ _ _ f
                 unitset
                 (λ _, (x₁ ~_{X} x₂ ∧ y₁ ~_{Y} y₂ ∧ f x₁ y₁)%heyting)
                 (λ _, x₁) (λ _, x₂) (λ _, y₁) (λ _, y₂)
                 _ _ _
                 tt) ;
        cbn ; unfold prodtofuntoprod ; cbn ; intro.
      - apply cha_min_le_l.
      - refine (cha_le_trans _ _).
        {
          apply cha_min_le_r.
        }
        apply cha_min_le_l.
      - refine (cha_le_trans _ _).
        {
          apply cha_min_le_r.
        }
        apply cha_min_le_r.
    Qed.

    Proposition h_valued_morphism_hom_exists
                (x : X)
      : (x ~_{X} x ≤ \/_{ y } f x y)%heyting.
    Proof.
      refine (cha_le_trans _ _).
      {
        refine (@partial_setoid_mor_hom_exists
                   _ _ _ f
                   unitset
                   (λ _, x ~_{X} x)%heyting (λ _, x)
                   _
                   tt).
        cbn ; unfold prodtofuntoprod ; cbn ; intro.
        apply cha_le_refl.
      }
      cbn ; unfold prodtofuntoprod ; cbn.
      use cha_lub_le ; cbn.
      intro i.
      induction i as [ [ [] y ] p ] ; cbn.
      use cha_le_lub.
      {
        exact y.
      }
      apply cha_le_refl.
    Qed.

    Proposition h_valued_morphism_unique_im
                (x : X)
                (y₁ y₂ : Y)
      : ((f x y₁ ∧ f x y₂) ≤ y₁ ~_{Y} y₂)%heyting.
    Proof.
      refine (@partial_setoid_mor_unique_im
                 _ _ _ f
                 unitset
                 (λ _, f x y₁ ∧ f x y₂)%heyting
                 (λ _, x) (λ _, y₁) (λ _, y₂)
                 _ _
                 tt) ;
        cbn ; unfold prodtofuntoprod ; cbn ; intro.
      - apply cha_min_le_l.
      - apply cha_min_le_r.
    Qed.
  End Accessors.

  Section Builder.
    Context {X Y : h_valued_set}
            (f : X → Y → H)
            (p₁ : ∏ (x : X) (y : Y),
                  (f x y ≤ x ~_{X} x)%heyting)
            (p₂ : ∏ (x : X) (y : Y),
                  (f x y ≤ y ~_{Y} y)%heyting)
            (p₃ : ∏ (x₁ x₂ : X) (y₁ y₂ : Y),
                  ((x₁ ~_{X} x₂ ∧ y₁ ~_{Y} y₂ ∧ f x₁ y₁) ≤ f x₂ y₂)%heyting)
            (p₄ : ∏ (x : X) (y₁ y₂ : Y),
                  ((f x y₁ ∧ f x y₂) ≤ y₁ ~_{Y} y₂)%heyting)
            (p₅ : ∏ (x : X),
                  (x ~_{X} x ≤ \/_{ y } f x y)%heyting).

    Let XH : partial_setoid (tripos_h_valued_sets H) := X.
    Let YH : partial_setoid (tripos_h_valued_sets H) := Y.

    Let φ : form (XH ×h YH) := λ x, f (pr1 x) (pr2 x).

    Proposition make_h_valued_morphism_laws
      : partial_setoid_morphism_laws φ.
    Proof.
      repeat split ; cbn ; unfold prodtofuntoprod ; cbn ; intros z ; induction z.
      - use cha_le_glb.
        intros [ [ [] x ] p ].
        use cha_le_glb.
        intros [ [ [ [] x' ] y  ] q ].
        cbn in *.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₁.
      - use cha_le_glb.
        intros [ [ [] x ] p ].
        use cha_le_glb.
        intros [ [ [ [] x' ] y  ] q ].
        cbn in *.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₂.
      - use cha_le_glb.
        intros [ [ [] x₁ ] q₁ ].
        use cha_le_glb.
        intros [ [ [ [] x' ] x₂ ] q₂ ].
        cbn in *.
        use cha_le_glb.
        intros [ [ [ [ [ ] x₁' ] x₂' ] y₁ ] q₃ ].
        cbn in *.
        use cha_le_glb.
        intros [ [ [ [ [ [ ] x₁'' ]  x₂'' ] y₁' ] y₂ ] q₄ ].
        cbn in *.
        do 3 use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        rewrite cha_min_assoc.
        apply p₃.
      - use cha_le_glb.
        intros [ [ [] x ] q₁ ].
        use cha_le_glb.
        intros [ [ [ [] x' ] y₁ ] q₂ ].
        use cha_le_glb.
        intros [ [ [ [ [ ] x'' ] y₁' ] y₂ ] q₃ ].
        cbn in *.
        do 2 use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₄.
      - use cha_le_glb.
        intros [ [ [] x ] q ] ; cbn.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        refine (cha_le_trans _ _).
        {
          apply p₅.
        }
        use cha_lub_le.
        intros y.
        use cha_le_lub.
        + refine (((tt ,, x) ,, y) ,, _).
          apply idpath.
        + apply cha_le_refl.
    Qed.

    Definition make_h_valued_morphism
      : h_valued_morphism X Y.
    Proof.
      use make_partial_setoid_morphism.
      - exact φ.
      - exact make_h_valued_morphism_laws.
    Defined.
  End Builder.
End HValuedSets.
