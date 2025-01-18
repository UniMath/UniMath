(*****************************************************************

 Scott Continuity can be checked coordinatewise

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.FubiniTheorem.
Require Import UniMath.OrderTheory.DCPOs.Examples.BinaryProducts.

Local Open Scope dcpo.

Section Coordinates.
  Context {X Y Z : dcpo}
          (f : X × Y → Z)
          (Hf₁ : ∏ (x : X), is_scott_continuous Y Z (λ y, f (x ,, y)))
          (Hf₂ : ∏ (y : Y), is_scott_continuous X Z (λ x, f (x ,, y))).

  Lemma scott_continuous_map_coordinates_monotone
    : is_monotone (X × Y) Z f.
  Proof.
    intros xy₁ xy₂ pq.
    induction xy₁ as [ x₁ y₁ ].
    induction xy₂ as [ x₂ y₂ ].
    induction pq as [ p q ].
    pose (is_scott_continuous_monotone (Hf₁ x₁) _ _ q) as r₁.
    pose (is_scott_continuous_monotone (Hf₂ y₂) _ _ p) as r₂.
    cbn in *.
    exact (trans_PartialOrder Z r₁ r₂).
  Qed.

  Let F : monotone_function (X × Y) Z
    := _ ,, scott_continuous_map_coordinates_monotone.
  Let Fy (D : directed_set (X × Y)) : scott_continuous_map X Z
    := _ ,, Hf₂ (⨆ (π₂ {{ D }})).

  Lemma scott_continuous_map_coordinates_lub
        (D : directed_set (X × Y))
    : F (⨆ D) = ⨆ (F {{ D }}).
  Proof.
    rewrite prod_dcpo_lub.
    etrans.
    {
      exact (scott_continuous_map_on_lub (Fy D) (π₁ {{ D }})).
    }
    refine (_ @ !(monotone_prod_map_fubini_pair_l _ _)).
    use dcpo_lub_eq_pointwise.
    intro i ; cbn.
    etrans.
    {
      exact (scott_continuous_map_on_lub (_ ,, Hf₁ i) (π₂ {{ D }})).
    }
    use dcpo_lub_eq_pointwise.
    intro.
    apply idpath.
  Qed.

  Proposition scott_continuous_map_coordinates
    : scott_continuous_map (X × Y) Z.
  Proof.
    refine (f ,, _).
    use is_scott_continuous_chosen_lub.
    - exact scott_continuous_map_coordinates_monotone.
    - intros I D HD.
      exact (scott_continuous_map_coordinates_lub (I ,, D ,, HD)).
  Defined.
End Coordinates.

Proposition is_scott_continuous_coordinates
            {X Y Z : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (DZ : dcpo_struct Z)
            (f : X × Y → Z)
            (Hf₁ : ∏ (x : X), is_scott_continuous DY DZ (λ y, f (x ,, y)))
            (Hf₂ : ∏ (y : Y), is_scott_continuous DX DZ (λ x, f (x ,, y)))
  : is_scott_continuous
      (prod_dcpo_struct DX DY)
      DZ
      f.
Proof.
  exact (pr2 (@scott_continuous_map_coordinates
                (X ,, DX)
                (Y ,, DY)
                (Z ,, DZ)
                f
                Hf₁
                Hf₂)).
Qed.
