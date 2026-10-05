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
 4. Isomorphisms of H-valued sets
 5. The natural numbers of H-valued sets

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.HValuedPredicates.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HyperdoctrineNat.
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

  Definition topos_of_h_valued_sets_NNO
    : NNO (Topos_Terminal topos_of_h_valued_sets)
    := tripos_to_topos_NNO
         (tripos_h_valued_sets H)
         (h_valued_sets_first_order_hyperdoctrine_nats H).

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
             intro x ;
             use cha_le_glb ;
             intro y ;
             use cha_to_le_exp ;
             rewrite cha_lunit_min_top ;
             rewrite sym ;
             apply cha_le_refl).
        * abstract
            (use cha_le_glb ;
             intro x ;
             use cha_le_glb ;
             intro y ;
             use cha_le_glb ;
             intro z ;
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

  Notation "x ~_{ X } y" := (@per_of_h_valued_set X x y) (at level 70).

  Proposition sym_per_of_h_valued_set
              {X : h_valued_set}
              (x y : X)
    : (x ~_{X} y) = (y ~_{X} x).
  Proof.
    pose (pr122 X tt) as p.
    cbn in p ; unfold prodtofuntoprod in p ; cbn in p.
    use cha_le_antisymm.
    - assert (⊤ ≤ (x ~_{X} y ⇒ y ~_{X} x))%heyting as q.
      {
        refine (cha_le_trans p _).
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          exact x.
        }
        cbn.
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          exact y.
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
          exact y.
        }
        cbn.
        simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
        {
          exact x.
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
        exact x.
      }
      cbn.
      simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
      {
        exact y.
      }
      cbn.
      simple refine (cha_le_trans (cha_glb_le_pt _ _) _).
      {
        exact z.
      }
      cbn.
      apply cha_le_refl.
    }
    pose proof (cha_from_le_exp q) as r.
    rewrite cha_lunit_min_top in r.
    exact (cha_from_le_exp r).
  Qed.

  Proposition refl_l_per_of_h_valued_set
              {X : h_valued_set}
              (x y : X)
    : ((x ~_{X} y) ≤ (x ~_{X} x))%heyting.
  Proof.
    refine (cha_le_trans _ (trans_per_of_h_valued_set x y x)).
    use cha_min_le_case.
    - apply cha_le_refl.
    - rewrite sym_per_of_h_valued_set.
      apply cha_le_refl.
  Qed.

  Proposition refl_r_per_of_h_valued_set
              {X : h_valued_set}
              (x y : X)
    : ((x ~_{X} y) ≤ (y ~_{X} y))%heyting.
  Proof.
    refine (cha_le_trans _ (trans_per_of_h_valued_set y x y)).
    use cha_min_le_case.
    - rewrite sym_per_of_h_valued_set.
      apply cha_le_refl.
    - apply cha_le_refl.
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
      : (f x y ≤ (x ~_{X} x))%heyting.
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
      : ((x₁ ~_{X} x₂ ∧ y₁ ~_{Y} y₂ ∧ f x₁ y₁) ≤ f x₂ y₂)%heyting.
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
      intro y.
      use cha_le_lub.
      {
        exact y.
      }
      apply cha_le_refl.
    Qed.

    Proposition h_valued_morphism_unique_im
                (x : X)
                (y₁ y₂ : Y)
      : ((f x y₁ ∧ f x y₂) ≤ (y₁ ~_{Y} y₂))%heyting.
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

  Proposition h_valued_morphism_eq
              {X Y : h_valued_set}
              {φ ψ : h_valued_morphism X Y}
              (p : ∏ (x : X) (y : Y), (φ x y ≤ ψ x y)%heyting)
              (q : ∏ (x : X) (y : Y), (ψ x y ≤ φ x y)%heyting)
    : φ = ψ.
  Proof.
    use eq_partial_setoid_morphism.
    - intros xy.
      exact (p (pr1 xy) (pr2 xy)).
    - intros xy.
      exact (q (pr1 xy) (pr2 xy)).
  Qed.

  Section Builder.
    Context {X Y : h_valued_set}
            (f : X → Y → H)
            (p₁ : ∏ (x : X) (y : Y),
                  (f x y ≤ (x ~_{X} x))%heyting)
            (p₂ : ∏ (x : X) (y : Y),
                  (f x y ≤ (y ~_{Y} y))%heyting)
            (p₃ : ∏ (x₁ x₂ : X) (y₁ y₂ : Y),
                  ((x₁ ~_{X} x₂ ∧ y₁ ~_{Y} y₂ ∧ f x₁ y₁) ≤ f x₂ y₂)%heyting)
            (p₄ : ∏ (x : X) (y₁ y₂ : Y),
                  ((f x y₁ ∧ f x y₂) ≤ (y₁ ~_{Y} y₂))%heyting)
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
        intro x.
        use cha_le_glb.
        intro y.
        cbn.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₁.
      - use cha_le_glb.
        intro x.
        use cha_le_glb.
        intro y.
        cbn in *.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₂.
      - use cha_le_glb.
        intro x₁.
        use cha_le_glb.
        intro x₂.
        use cha_le_glb.
        intro y₁.
        use cha_le_glb.
        intro y₂.
        cbn in *.
        do 3 use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        rewrite cha_min_assoc.
        apply p₃.
      - use cha_le_glb.
        intro x.
        use cha_le_glb.
        intro y₁.
        use cha_le_glb.
        intro y₂.
        cbn in *.
        do 2 use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply p₄.
      - use cha_le_glb.
        intro x.
        use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        refine (cha_le_trans _ _).
        {
          apply p₅.
        }
        use cha_lub_le.
        intros y.
        use cha_le_lub.
        + exact y.
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

  (** * 4. Isomorphisms of H-valued sets *)
  Proposition h_valued_morphism_surjective
              {X Y : h_valued_set}
              (φ : h_valued_morphism X Y)
              (p : ∏ (y : Y), (y ~_{Y} y ≤ \/_{ x : X} (φ x y))%heyting)
    : per_morphism_surjective_law (tripos_h_valued_sets H) φ.
  Proof.
    unfold per_morphism_surjective_law.
    cbn ; unfold prodtofuntoprod ; cbn.
    intros [].
    use cha_le_glb.
    intro y.
    cbn.
    use cha_to_le_exp.
    rewrite cha_lunit_min_top.
    refine (cha_le_trans (p y) _).
    use cha_lub_le.
    intros x.
    cbn.
    use cha_le_lub.
    - exact x.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition h_valued_morphism_injective
              {X Y : h_valued_set}
              (φ : h_valued_morphism X Y)
              (p : ∏ (x₁ x₂ : X) (y : Y), ((φ x₁ y ∧ φ x₂ y) ≤ (x₁ ~_{X} x₂))%heyting)
    : per_morphism_injective_law (tripos_h_valued_sets H) φ.
  Proof.
    unfold per_morphism_injective_law.
    cbn ; unfold prodtofuntoprod ; cbn.
    intros [].
    use cha_le_glb.
    intro x₁.
    use cha_le_glb.
    intro x₂.
    use cha_le_glb.
    intro y.
    cbn.
    use cha_to_le_exp.
    rewrite cha_lunit_min_top.
    use cha_to_le_exp.
    apply p.
  Qed.

  Definition make_h_valued_isomorphism
             {X Y : h_valued_set}
             (φ : h_valued_morphism X Y)
             (p : ∏ (y : Y), (y ~_{Y} y ≤ \/_{ x : X} (φ x y))%heyting)
             (q : ∏ (x₁ x₂ : X) (y : Y), ((φ x₁ y ∧ φ x₂ y) ≤ (x₁ ~_{X} x₂))%heyting)
    : z_iso (C := topos_of_h_valued_sets) X Y.
  Proof.
    use make_partial_setoid_z_iso.
    - exact φ.
    - use h_valued_morphism_surjective.
      exact p.
    - use h_valued_morphism_injective.
      exact q.
  Defined.

  (** * 5. The natural numbers of H-valued sets *)

  (**
     Every natural number is inductive. As a consequence, the carrier of the natural numbers
     object is the set of natural numbers and the (partial) equivalence relation is equality
     in the first-order hyperdoctrine of H-valued predicates.
   *)
  Section InductiveNat.
    Context {Γ : ty (tripos_h_valued_sets H)}
            (t : tm Γ (h_valued_sets_first_order_hyperdoctrine_nats H)).

    Let φ : form (h_valued_sets_first_order_hyperdoctrine_nats H)
      := is_inductive_nat
           (H := tripos_to_weak_tripos (tripos_h_valued_sets H))
           (h_valued_sets_first_order_hyperdoctrine_nats H).

    Definition h_valued_pred_nat_inductive
      : ⊤ ⊢ φ [ t ].
    Proof.
      intro x.
      cbn.
      use cha_le_glb.
      intro ψ.
      cbn.
      use cha_to_le_exp.
      rewrite cha_lunit_min_top.
      use cha_to_le_exp.
      pose (k := t x).
      assert (t x = k) as -> by apply idpath.
      induction k as [ | k IHk ].
      - apply cha_min_le_l.
      - refine (cha_le_trans _ _).
        {
          use cha_eq_to_refl.
          refine (!_).
          exact (cha_min_le_eq_l IHk).
        }
        rewrite cha_min_assoc.
        refine (cha_le_trans (cha_min_le_r _ _) _).
        use cha_from_le_exp.
        use cha_glb_le.
        + exact k.
        + cbn.
          apply cha_le_refl.
    Qed.
  End InductiveNat.

  (**
     We can conclude that the NNO is equal to a discrete partial setoid.
   *)
  Definition nat_h_valued_set_eq
    : eq_partial_setoid (H := h_valued_sets_first_order_hyperdoctrine H) natset
      =
      pr1 (topos_of_h_valued_sets_NNO).
  Proof.
    cbn ; unfold eq_partial_setoid, nat_partial_setoid ; cbn.
    apply maponpaths.
    use subtypePath.
    {
      intro.
      apply isaprop_per_axioms.
    }
    use funextsec.
    intros [ n m ].
    cbn.
    refine (!(cha_runit_min_top _) @ _).
    apply maponpaths.
    use cha_le_antisymm.
    - refine (cha_le_trans _ _).
      {
        use h_valued_pred_nat_inductive.
        + exact unitset.
        + exact (λ _, n).
        + exact tt.
      }
      cbn.
      apply cha_le_refl.
    - apply cha_le_top.
  Qed.
End HValuedSets.

Notation "x ~_{ X } y" := (@per_of_h_valued_set _ X x y) (at level 70) : heyting.
