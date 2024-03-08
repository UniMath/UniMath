(********************************************************************

 Strong monads

 In this file, we define the notion of strong monad on a monoidal
 category.

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section LeftStrength.
  Context {V : monoidal_cat}.

  Definition left_strength_data
             (F : V ⟶ V)
    : UU
    := ∏ (x y : V), x ⊗ F y --> F(x ⊗ y).

  Definition left_strength_laws
             {F : V ⟶ V}
             (tF : left_strength_data F)
    : UU
    := (∏ (x₁ x₂ y₁ y₂ : V)
          (f : x₁ --> x₂)
          (g : y₁ --> y₂),
        f #⊗ #F g· tF x₂ y₂
        =
        tF x₁ y₁ · #F(f #⊗ g))
       ×
       (∏ (x : V),
        tF I_{V} x · #F(mon_lunitor x)
        =
        mon_lunitor (F x))
       ×
       (∏ (x y z : V),
        tF (x ⊗ y) z · #F(mon_lassociator x y z)
        =
        mon_lassociator x y (F z) · identity x #⊗ tF y z · tF x (y ⊗ z)).

  Proposition isaprop_left_strength_laws
              {F : V ⟶ V}
              (tF : left_strength_data F)
    : isaprop (left_strength_laws tF).
  Proof.
    repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
  Qed.

  Definition left_strength
             (F : V ⟶ V)
    : UU
    := ∑ (tF : left_strength_data F), left_strength_laws tF.

  Definition left_strength_to_data
             {F : V ⟶ V}
             (tF : left_strength F)
             (x y : V)
    : x ⊗ F y --> F(x ⊗ y)
    := pr1 tF x y.

  Coercion left_strength_to_data : left_strength >-> Funclass.

  Section LeftStrengthLaws.
    Context {F : V ⟶ V}
            (tF : left_strength F).

    Proposition left_strength_natural
                {x₁ x₂ y₁ y₂ : V}
                (f : x₁ --> x₂)
                (g : y₁ --> y₂)
      : f #⊗ #F g· tF x₂ y₂
        =
        tF x₁ y₁ · #F(f #⊗ g).
    Proof.
      exact (pr12 tF x₁ x₂ y₁ y₂ f g).
    Qed.

    Proposition left_strength_mon_lunitor
                (x : V)
      : tF I_{V} x · #F(mon_lunitor x)
        =
        mon_lunitor (F x).
    Proof.
      exact (pr122 tF x).
    Qed.

    Proposition left_strength_mon_lassociator
                (x y z : V)
      : tF (x ⊗ y) z · #F(mon_lassociator x y z)
        =
        mon_lassociator x y (F z) · identity x #⊗ tF y z · tF x (y ⊗ z).
    Proof.
      exact (pr222 tF x y z).
    Qed.
  End LeftStrengthLaws.

  Definition left_strong_monad_laws
             {M : Monad V}
             (tM : left_strength M)
    : UU
    := (∏ (x y : V),
        identity x #⊗ η M y · tM x y
        =
        η M (x ⊗ y))
       ×
       (∏ (x y : V),
        identity x #⊗ μ M y · tM x y
        =
        tM x (M y) · #M (tM x y) · μ M (x ⊗ y)).

  Proposition isaprop_left_strong_monad_laws
              {M : Monad V}
              (tM : left_strength M)
    : isaprop (left_strong_monad_laws tM).
  Proof.
    use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
  Qed.

  Definition left_strong_monad
             (M : Monad V)
    : UU
    := ∑ (tM : left_strength M), left_strong_monad_laws tM.

  #[reversible=no] Coercion left_strong_monad_strength
           {M : Monad V}
           (tM : left_strong_monad M)
    : left_strength M
    := pr1 tM.

  Section LeftStrongMonadLaws.
    Context {M : Monad V}
            (tM : left_strong_monad M).

    Proposition left_strong_monad_unit
                (x y : V)
      : identity x #⊗ η M y · tM x y
        =
        η M (x ⊗ y).
    Proof.
      exact (pr12 tM x y).
    Qed.

    Proposition left_strong_monad_mu
                (x y : V)
      : identity x #⊗ μ M y · tM x y
        =
        tM x (M y) · #M (tM x y) · μ M (x ⊗ y).
    Proof.
      exact (pr22 tM x y).
    Qed.
  End LeftStrongMonadLaws.
End LeftStrength.
