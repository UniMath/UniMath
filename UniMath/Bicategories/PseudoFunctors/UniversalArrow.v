(**************************************************************
 Universal arrows

 One way to construct biadjunctions, is via universal arrows.
 These come in two flavors: one to give left biadjoints and one
 to give right biadjoints.

 Contents
 1. Right universal arrows
 2. Left universal arrows
 **************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

(**
 1. Right universal arrows
 *)
Section RightUniversalArrow.
  Context {B₁ B₂ : bicat}
          (L : psfunctor B₁ B₂).

  Definition right_universal_arrow_functor_data
             (x : B₁)
             (y : B₂)
             {R : B₂ → B₁}
             (ε : ∏ (x : B₂), L(R x) --> x)
    : functor_data
        (hom x (R y))
        (hom (L x) y).
  Proof.
    use make_functor_data.
    - exact (λ f, #L f · ε y).
    - exact (λ f g α, ##L α ▹ ε y).
  Defined.

  Definition right_universal_arrow_functor_is_functor
             (x : B₁)
             (y : B₂)
             {R : B₂ → B₁}
             (ε : ∏ (x : B₂), L(R x) --> x)
    : is_functor (right_universal_arrow_functor_data x y ε).
  Proof.
    split.
    - intro f ; cbn.
      rewrite psfunctor_id2.
      rewrite id2_rwhisker.
      apply idpath.
    - intros f g h α β ; cbn.
      rewrite psfunctor_vcomp.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Definition right_universal_arrow_functor
             (x : B₁)
             (y : B₂)
             {R : B₂ → B₁}
             (ε : ∏ (x : B₂), L(R x) --> x)
    : hom x (R y) ⟶ hom (L x) y.
  Proof.
    use make_functor.
    - exact (right_universal_arrow_functor_data x y ε).
    - exact (right_universal_arrow_functor_is_functor x y ε).
  Defined.

  Definition right_universal_arrow
    : UU
    := ∑ (R : B₂ → B₁)
         (ε : ∏ (x : B₂), L(R x) --> x),
       ∏ (x : B₁)
         (y : B₂),
       adj_equivalence_of_cats
         (right_universal_arrow_functor x y ε).

  Section Constructor.
    Context (R : B₂ → B₁)
            (ε : ∏ (x : B₂), L(R x) --> x)
            (inv : ∏ (x : B₁) (y : B₂), hom (L x) y ⟶ hom x (R y))
            (unit_adj : ∏ (x : B₁) (y : B₂),
                        functor_identity _
                        ⟹
                        right_universal_arrow_functor x y ε ∙ inv x y)
            (counit_adj : ∏ (x : B₁) (y : B₂),
                          inv x y ∙ right_universal_arrow_functor x y ε
                              ⟹
                              functor_identity _)
            (unit_iso : ∏ (x : B₁) (y : B₂)
                          (f : x --> R y),
                        is_z_isomorphism (unit_adj x y f))
            (counit_iso : ∏ (x : B₁) (y : B₂)
                            (f : L x --> y),
                          is_z_isomorphism (counit_adj x y f)).

    Definition make_right_universal_arrow_equivalence
               (x : B₁)
               (y : B₂)
      : equivalence_of_cats
          (hom x (R y))
          (hom (L x) y).
    Proof.
      simple refine ((_ ,, (_ ,, (_ ,, _))) ,, _ ,, _) ; cbn.
      - exact (right_universal_arrow_functor x y ε).
      - exact (inv x y).
      - exact (unit_adj x y).
      - exact (counit_adj x y).
      - exact (unit_iso x y).
      - exact (counit_iso x y).
    Defined.

    Definition make_right_universal_arrow
      : right_universal_arrow.
    Proof.
      simple refine (R ,, ε ,, _) ; cbn.
      intros x y.
      exact (adjointificiation (make_right_universal_arrow_equivalence x y)).
    Defined.
  End Constructor.

  Section Constructor.
    Context (HB₁ : is_univalent_2_1 B₁)
            (R : B₂ → B₁)
            (ε : ∏ (x : B₂), L(R x) --> x)
            (H₁ : ∏ (x : B₁)
                    (y : B₂)
                    (f g : x --> R y)
                    (α : # L f · ε y ==> # L g · ε y),
                  ∑ (β : f ==> g),
                  ##L β ▹ ε y = α)
            (H₂ : ∏ (x : B₁)
                    (y : B₂)
                    (f g : x --> R y)
                    (α : # L f · ε y ==> # L g · ε y)
                    (β₁ β₂ : f ==> g)
                    (p₁ : ##L β₁ ▹ ε y = α)
                    (p₂ : ##L β₂ ▹ ε y = α),
                  β₁ = β₂)
            (H₃ : ∏ (x : B₁)
                    (y : B₂)
                    (f : L x --> y),
                  ∑ (g : x --> R y),
                  invertible_2cell (# L g · ε y) f).

    Definition make_right_universal_arrow'
      : right_universal_arrow.
    Proof.
      simple refine (R ,, ε ,, _) ; cbn.
      intros x y.
      use rad_equivalence_of_cats.
      - apply is_univ_hom.
        exact HB₁.
      - use full_and_faithful_implies_fully_faithful.
        split.
        + intros f g α.
          apply hinhpr.
          apply H₁.
        + intros f g α.
          use invproofirrelevance.
          intros β₁ β₂ ; cbn in *.
          use subtypePath ; [ intro ; apply cellset_property | ].
          exact (H₂ x y f g α (pr1 β₁) (pr1 β₂) (pr2 β₁) (pr2 β₂)).
      - intros f.
        apply hinhpr.
        simple refine (_ ,, _).
        + exact (pr1 (H₃ x y f)).
        + simpl.
          apply inv2cell_to_z_iso.
          exact (pr2 (H₃ x y f)).
    Defined.
  End Constructor.
End RightUniversalArrow.

(**
 2. Left universal arrows
 *)
Section LeftUniversalArrow.
  Context {B₁ B₂ : bicat}
          (R : psfunctor B₂ B₁).

  Definition left_universal_arrow_functor_data
             (x : B₁)
             (y : B₂)
             {L : B₁ → B₂}
             (η : ∏ (x : B₁), x --> R(L x))
    : functor_data
        (hom (L x) y)
        (hom x (R y)).
  Proof.
    use make_functor_data.
    - exact (λ f, η x · #R f).
    - exact (λ f g α, η x ◃ ##R α).
  Defined.

  Definition left_universal_arrow_functor_is_functor
             (x : B₁)
             (y : B₂)
             {L : B₁ → B₂}
             (η : ∏ (x : B₁), x --> R(L x))
    : is_functor (left_universal_arrow_functor_data x y η).
  Proof.
    split.
    - intro f ; cbn.
      rewrite psfunctor_id2.
      rewrite lwhisker_id2.
      apply idpath.
    - intros f g h α β ; cbn.
      rewrite psfunctor_vcomp.
      rewrite lwhisker_vcomp.
      apply idpath.
  Qed.

  Definition left_universal_arrow_functor
             (x : B₁)
             (y : B₂)
             {L : B₁ → B₂}
             (η : ∏ (x : B₁), x --> R(L x))
    : hom (L x) y ⟶ hom x (R y).
  Proof.
    use make_functor.
    - exact (left_universal_arrow_functor_data x y η).
    - exact (left_universal_arrow_functor_is_functor x y η).
  Defined.

  Definition left_universal_arrow
    : UU
    := ∑ (L : B₁ → B₂)
         (η : ∏ (x : B₁), x --> R(L x)),
       ∏ (x : B₁)
         (y : B₂),
       adj_equivalence_of_cats
         (left_universal_arrow_functor x y η).

  Section Constructor.
    Context (L : B₁ → B₂)
            (η : ∏ (x : B₁), x --> R(L x))
            (inv : ∏ (x : B₁) (y : B₂), hom x (R y) ⟶ hom (L x) y)
            (unit_adj : ∏ (x : B₁) (y : B₂),
                        functor_identity _
                        ⟹
                        left_universal_arrow_functor x y η ∙ inv x y)
            (counit_adj : ∏ (x : B₁) (y : B₂),
                          inv x y ∙ left_universal_arrow_functor x y η
                          ⟹
                          functor_identity _)
            (unit_iso : ∏ (x : B₁) (y : B₂)
                          (f : L x --> y),
                        is_z_isomorphism (unit_adj x y f))
            (counit_iso : ∏ (x : B₁) (y : B₂)
                            (f : x --> R y),
                          is_z_isomorphism (counit_adj x y f)).

    Definition make_left_universal_arrow_equivalence
               (x : B₁)
               (y : B₂)
      : equivalence_of_cats
          (hom (L x) y)
          (hom x (R y)).
    Proof.
      simple refine ((_ ,, (_ ,, (_ ,, _))) ,, _ ,, _) ; cbn.
      - exact (left_universal_arrow_functor x y η).
      - exact (inv x y).
      - exact (unit_adj x y).
      - exact (counit_adj x y).
      - exact (unit_iso x y).
      - exact (counit_iso x y).
    Defined.

    Definition make_left_universal_arrow
      : left_universal_arrow.
    Proof.
      simple refine (L ,, η ,, _) ; cbn.
      intros x y.
      exact (adjointificiation (make_left_universal_arrow_equivalence x y)).
    Defined.
  End Constructor.

  Section Constructor.
    Context (HB₂ : is_univalent_2_1 B₂)
            (L : B₁ → B₂)
            (η : ∏ (x : B₁), x --> R(L x))
            (H₁ : ∏ (x : B₁)
                    (y : B₂)
                    (f g : L x --> y)
                    (α : η x · # R f ==> η x · # R g),
                  ∑ (β : f ==> g),
                  η x ◃ ## R β = α)
            (H₂ : ∏ (x : B₁)
                    (y : B₂)
                    (f g : L x --> y)
                    (α : η x · # R f ==> η x · # R g)
                    (β₁ β₂ : f ==> g)
                    (p₁ : η x ◃ ##R β₁ = α)
                    (p₂ : η x ◃ ##R β₂ = α),

                  β₁ = β₂)
            (H₃ : ∏ (x : B₁)
                    (y : B₂)
                    (f : x --> R y),
             ∑ (g : L x --> y),
             invertible_2cell (η x · # R g) f).

    Definition make_left_universal_arrow'
      : left_universal_arrow.
    Proof.
      simple refine (L ,, η ,, _) ; cbn.
      intros x y.
      use rad_equivalence_of_cats.
      - apply is_univ_hom.
        exact HB₂.
      - use full_and_faithful_implies_fully_faithful.
        split.
        + intros f g α.
          apply hinhpr.
          apply H₁.
        + intros f g α.
          use invproofirrelevance.
          intros β₁ β₂ ; cbn in *.
          use subtypePath ; [ intro ; apply cellset_property | ].
          exact (H₂ x y f g α (pr1 β₁) (pr1 β₂) (pr2 β₁) (pr2 β₂)).
      - intros f.
        apply hinhpr.
        simple refine (_ ,, _).
        + exact (pr1 (H₃ x y f)).
        + simpl.
          apply inv2cell_to_z_iso.
          exact (pr2 (H₃ x y f)).
    Defined.
  End Constructor.
End LeftUniversalArrow.
