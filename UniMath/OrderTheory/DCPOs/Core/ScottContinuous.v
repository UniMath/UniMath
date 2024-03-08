(*****************************************************************

 Scott Continuous functions

 We define the notion of Scott continuous functions between DCPOs.
 Again we give both bundled and unbundled definitions: the former
 is more convenient to use while the latter is necessary in the
 setting of displayed categories.

 Contents
 1. Scott continuity
 2. Accessors for scott continuity
 3. Examples of Scott continuous maps
 4. Structure-identity
 5. Bundled approach
 6. Accessors and builders for the bundled approach
 7. Examples of Scott continuous maps (bundled)
 8. Scott continuous maps are continuous in the Scott topology
 9. Scott continuous maps reflect apartness
*****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Core.IntrinsicApartness.

Local Open Scope dcpo.

(**
 1. Scott continuity
 *)
Definition is_scott_continuous
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
           (f : X → Y)
  : UU
  := is_monotone DX DY f
     ×
     (∀ (I : UU)
        (D : I → X)
        (HD : is_directed DX D)
        (x : X)
        (Hx : is_least_upperbound DX D x),
      is_least_upperbound DY (λ i, f(D i)) (f x)).

Definition is_strict_scott_continuous
           {X Y : hSet}
           (DX : dcppo_struct X)
           (DY : dcppo_struct Y)
           (f : X → Y)
  : UU
  := is_scott_continuous DX DY f
     ×
     f (pointed_PartialOrder_to_point DX) = pointed_PartialOrder_to_point DY.

#[reversible=no] Coercion is_strict_scott_continuous_to_scott_continuous
         {X Y : hSet}
         {DX : dcppo_struct X}
         {DY : dcppo_struct Y}
         {f : X → Y}
         (Hf : is_strict_scott_continuous DX DY f)
  : is_scott_continuous DX DY f
  := pr1 Hf.

(**
 2. Accessors for scott continuity
 *)
Proposition isaprop_is_scott_continuous
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (f : X → Y)
  : isaprop (is_scott_continuous DX DY f).
Proof.
  use isapropdirprod.
  - apply isaprop_is_monotone.
  - apply propproperty.
Qed.

Proposition isaprop_is_strict_scott_continuous
            {X Y : hSet}
            (DX : dcppo_struct X)
            (DY : dcppo_struct Y)
            (f : X → Y)
  : isaprop (is_strict_scott_continuous DX DY f).
Proof.
  use isapropdirprod.
  - apply isaprop_is_scott_continuous.
  - apply setproperty.
Qed.

Proposition is_scott_continuous_monotone
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {f : X → Y}
            (Df : is_scott_continuous DX DY f)
  : is_monotone DX DY f.
Proof.
  exact (pr1 Df).
Qed.

Proposition is_scott_continuous_lub
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {f : X → Y}
            (Df : is_scott_continuous DX DY f)
            {I : UU}
            {D : I → X}
            (HD : is_directed DX D)
            (x : X)
            (Hx : is_least_upperbound DX D x)
  : is_least_upperbound DY (λ i, f(D i)) (f x).
Proof.
  exact (pr2 Df I D HD x Hx).
Qed.

Proposition is_scott_continuous_chosen_lub
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (f : X → Y)
            (Hf₁ : is_monotone DX DY f)
            (Hf₂ : ∏ (I : UU)
                     (D : I → X)
                     (HD : is_directed DX D),
                   f (dcpo_struct_lub DX D HD)
                   =
                   dcpo_struct_lub DY (λ i, f (D i)) (is_directed_comp f Hf₁ HD))
  : is_scott_continuous DX DY f.
Proof.
  split.
  - exact Hf₁.
  - intros I D HD x Hx.
    refine (transportb
              (λ z, is_least_upperbound _ _ z)
              (maponpaths f _ @ Hf₂ I D HD)
              _).
    + exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isaprop_lub DX D)
                  (x ,, Hx)
                  (dcpo_struct_lub DX D HD))).
    + apply dcpo_struct_lub.
Qed.

Proposition is_scott_continuous_on_lub
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {f : X → Y}
            (Hf : is_scott_continuous DX DY f)
            {I : UU}
            (D : I → X)
            (HD : is_directed DX D)
  : f (dcpo_struct_lub DX D HD)
    =
    dcpo_struct_lub DY (λ i, f (D i)) (is_directed_comp f (pr1 Hf) HD).
Proof.
  use (eq_lub DY (λ i, f(D i))).
  - use (is_scott_continuous_lub Hf HD).
    apply dcpo_struct_lub.
  - apply dcpo_struct_lub.
Qed.

Proposition is_strict_scott_continuous_on_bot
            {X Y : hSet}
            {DX : dcppo_struct X}
            {DY : dcppo_struct Y}
            {f : X → Y}
            (Hf : is_strict_scott_continuous DX DY f)
  : f (pointed_PartialOrder_to_point DX) = pointed_PartialOrder_to_point DY.
Proof.
  exact (pr2 Hf).
Qed.

(**
 3. Examples of Scott continuous maps
 *)
Proposition id_is_scott_continuous
            {X : hSet}
            (DX : dcpo_struct X)
  : is_scott_continuous DX DX (λ x, x).
Proof.
  split.
  - intros x₁ x₂ p.
    exact p.
  - intros I D HD x Hx.
    exact Hx.
Qed.

Proposition id_is_strict_scott_continuous
            {X : hSet}
            (DX : dcppo_struct X)
  : is_strict_scott_continuous DX DX (λ x, x).
Proof.
  split.
  - apply id_is_scott_continuous.
  - apply idpath.
Qed.

Proposition comp_is_scott_continuous
            {X Y Z : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {DZ : dcpo_struct Z}
            {f : X → Y}
            {g : Y → Z}
            (Df : is_scott_continuous DX DY f)
            (Dg : is_scott_continuous DY DZ g)
  : is_scott_continuous DX DZ (λ x, g(f x)).
Proof.
  split.
  - intros x₁ x₂ p.
    apply (is_scott_continuous_monotone Dg).
    apply (is_scott_continuous_monotone Df).
    exact p.
  - intros I D HD x Hx.
    use (is_scott_continuous_lub Dg).
    + exact (is_directed_comp _ (pr1 Df) HD).
    + use (is_scott_continuous_lub Df HD).
      exact Hx.
Qed.

Proposition comp_is_strict_scott_continuous
            {X Y Z : hSet}
            {DX : dcppo_struct X}
            {DY : dcppo_struct Y}
            {DZ : dcppo_struct Z}
            {f : X → Y}
            {g : Y → Z}
            (Df : is_strict_scott_continuous DX DY f)
            (Dg : is_strict_scott_continuous DY DZ g)
  : is_strict_scott_continuous DX DZ (λ x, g(f x)).
Proof.
  split.
  - exact (comp_is_scott_continuous Df Dg).
  - rewrite (is_strict_scott_continuous_on_bot Df).
    exact (is_strict_scott_continuous_on_bot Dg).
Qed.

Proposition is_scott_continuous_constant
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (y : Y)
  : is_scott_continuous
      DX
      DY
      (λ _, y).
Proof.
  split.
  - intros x₁ x₂ p.
    apply refl_PartialOrder.
  - intros I D HD x HX.
    split.
    + intro i.
      apply refl_PartialOrder.
    + intros z Hz.
      cbn in *.
      induction HD as [ i HD ].
      revert i.
      use factor_through_squash.
      {
        apply propproperty.
      }
      exact Hz.
Qed.

Proposition is_strict_scott_continuous_constant
            {X Y : hSet}
            (DX : dcppo_struct X)
            (DY : dcppo_struct Y)
  : is_strict_scott_continuous
      DX
      DY
      (λ _, pointed_PartialOrder_to_point DY).
Proof.
  split.
  - apply is_scott_continuous_constant.
  - apply idpath.
Qed.

(**
 4. Structure-identity
 *)
Proposition eq_dcpo_struct
            {X : hSet}
            (DX DX' : dcpo_struct X)
            (H₁ : is_scott_continuous DX DX' (λ x, x))
            (H₂ : is_scott_continuous DX' DX (λ x, x))
  : DX = DX'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_directed_complete_poset.
  }
  use eq_PartialOrder.
  - exact (is_scott_continuous_monotone H₁).
  - exact (is_scott_continuous_monotone H₂).
Qed.

Proposition eq_dcppo_struct
            {X : hSet}
            (DX DX' : dcppo_struct X)
            (H₁ : is_scott_continuous DX DX' (λ x, x))
            (H₂ : is_scott_continuous DX' DX (λ x, x))
  : DX = DX'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_bottom_element.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_directed_complete_poset.
  }
  use eq_PartialOrder.
  - exact (is_scott_continuous_monotone H₁).
  - exact (is_scott_continuous_monotone H₂).
Qed.

Proposition eq_dcppo_strict_struct
            {X : hSet}
            (DX DX' : dcppo_struct X)
            (H₁ : is_strict_scott_continuous DX DX' (λ x, x))
            (H₂ : is_strict_scott_continuous DX' DX (λ x, x))
  : DX = DX'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_bottom_element.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_directed_complete_poset.
  }
  use eq_PartialOrder.
  - exact (is_scott_continuous_monotone H₁).
  - exact (is_scott_continuous_monotone H₂).
Qed.

(**
 5. Bundled approach
 *)
Definition scott_continuous_map
           (X Y : dcpo)
  : UU
  := ∑ (f : X → Y), is_scott_continuous X Y f.

Definition strict_scott_continuous_map
           (X Y : dcppo)
  : UU
  := ∑ (f : X → Y), is_strict_scott_continuous X Y f.

#[reversible=no] Coercion strict_scott_continuous_map_to_scott_continuous_map
         {X Y : dcppo}
         (f : strict_scott_continuous_map X Y)
  : scott_continuous_map X Y
  := pr1 f ,, pr12 f.

(**
 6. Accessors and builders for the bundled approach
 *)
Definition scott_continuous_map_to_fun
           {X Y : dcpo}
           (f : scott_continuous_map X Y)
           (x : X)
  : Y
  := pr1 f x.

Coercion scott_continuous_map_to_fun : scott_continuous_map >-> Funclass.

Proposition is_monotone_scott_continuous_map
            {X Y : dcpo}
            (f : scott_continuous_map X Y)
            {x₁ x₂ : X}
            (p : x₁ ⊑ x₂)
  : f x₁ ⊑ f x₂.
Proof.
  exact (pr12 f x₁ x₂ p).
Qed.

Proposition eq_scott_continuous_map
            {X Y : dcpo}
            {f g : scott_continuous_map X Y}
            (p : ∏ (x : X), f x = g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_is_scott_continuous.
  }
  use funextsec.
  exact p.
Qed.

#[reversible=no] Coercion scott_continuous_map_to_monotone
         {X Y : dcpo}
         (f : scott_continuous_map X Y)
  : monotone_function X Y.
Proof.
  refine (pr1 f ,, _).
  intros x₁ x₂ p.
  exact (is_monotone_scott_continuous_map f p).
Defined.

Section MakeScottContinuous.
  Context {X Y : dcpo}
          (f : X → Y)
          (Hf₁ : ∏ (x₁ x₂ : X), x₁ ⊑ x₂ → f x₁ ⊑ f x₂).

  Definition make_dcpo_is_monotone
    : monotone_function X Y
    := f ,, Hf₁.

  Context (Hf₂ : ∏ (D : directed_set X), f (⨆ D) = ⨆_{D} (f ,, Hf₁)).

  Definition make_is_scott_continuous
    : is_scott_continuous X Y f.
  Proof.
    use is_scott_continuous_chosen_lub.
    - exact Hf₁.
    - intros I D HD.
      exact (Hf₂ (I ,, (D ,, HD))).
  Qed.
End MakeScottContinuous.

Proposition scott_continuous_map_on_lub
            {X Y : dcpo}
            (f : scott_continuous_map X Y)
            (D : directed_set X)
  : f (⨆ D) = ⨆_{D} f.
Proof.
  refine (is_scott_continuous_on_lub (pr2 f) _ (pr22 D) @ _).
  use (eq_lub Y (f {{ D }})).
  - use make_dcpo_is_least_upperbound.
    + cbn ; intro i.
      exact (lub_is_upperbound
               (dcpo_struct_lub
                  Y
                  _
                  (is_directed_comp (pr1 f) (pr12 f) (pr22 D)))
               i).
    + intros x Hx.
      exact (lub_is_least
               (dcpo_struct_lub
                  Y
                  _
                  (is_directed_comp (pr1 f) (pr12 f) (pr22 D)))
               x
               Hx).
  - apply is_least_upperbound_dcpo_comp_lub.
Qed.

Definition strict_scott_continuous_map_to_fun
           {X Y : dcppo}
           (f : strict_scott_continuous_map X Y)
           (x : X)
  : Y
  := pr1 f x.

Coercion strict_scott_continuous_map_to_fun
  : strict_scott_continuous_map >-> Funclass.

Proposition eq_strict_scott_continuous_map
            {X Y : dcppo}
            {f g : strict_scott_continuous_map X Y}
            (p : ∏ (x : X), f x = g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_is_strict_scott_continuous.
  }
  use funextsec.
  exact p.
Qed.

Section MakeStrictScottContinuous.
  Context {X Y : dcppo}
          (f : X → Y)
          (Hf₁ : ∏ (x₁ x₂ : X), x₁ ⊑ x₂ → f x₁ ⊑ f x₂)
          (Hf₂ : ∏ (D : directed_set X), f (⨆ D) = ⨆_{D} (f ,, Hf₁))
          (Hf₃ : f ⊥_{X} = ⊥_{Y}).

  Definition make_is_strict_scott_continuous
    : is_strict_scott_continuous X Y f.
  Proof.
    split.
    - use is_scott_continuous_chosen_lub.
      + exact Hf₁.
      + intros I D HD.
        exact (Hf₂ (I ,, (D ,, HD))).
    - exact Hf₃.
  Qed.
End MakeStrictScottContinuous.

Proposition strict_scott_continuous_map_on_point
            {X Y : dcppo}
            (f : strict_scott_continuous_map X Y)
  : f ⊥_{X} = ⊥_{Y}.
Proof.
  exact (pr22 f).
Qed.

(**
 7. Examples of Scott continuous maps (bundled)
 *)
Definition id_scott_continuous_map
           (X : dcpo)
  : scott_continuous_map X X
  := (λ x, x) ,, id_is_scott_continuous X.

Definition comp_scott_continuous_map
           {X Y Z : dcpo}
           (f : scott_continuous_map X Y)
           (g : scott_continuous_map Y Z)
  : scott_continuous_map X Z
  := (λ x, g(f x)) ,, comp_is_scott_continuous (pr2 f) (pr2 g).

Notation "f '·' g" := (comp_scott_continuous_map f g) : dcpo.

Definition constant_scott_continuous_map
           (X : dcpo)
           {Y : dcpo}
           (y : Y)
  : scott_continuous_map X Y
  := (λ x, y) ,, is_scott_continuous_constant _ _ _.

Definition id_strict_scott_continuous_map
           (X : dcppo)
  : strict_scott_continuous_map X X
  := (λ x, x) ,, id_is_strict_scott_continuous X.

Definition comp_strict_scott_continuous_map
           {X Y Z : dcppo}
           (f : strict_scott_continuous_map X Y)
           (g : strict_scott_continuous_map Y Z)
  : strict_scott_continuous_map X Z
  := (λ x, g(f x)) ,, comp_is_strict_scott_continuous (pr2 f) (pr2 g).

Definition constant_strict_scott_continuous_map
           (X : dcppo)
           {Y : dcppo}
  : strict_scott_continuous_map X Y
  := (λ x, ⊥_{Y}) ,, is_strict_scott_continuous_constant _ _.

(**
 8. Scott continuous maps are continuous in the Scott topology
 *)
Proposition preimage_scott_open
            {X Y : dcpo}
            (f : scott_continuous_map X Y)
            {P : Y → hProp}
            (HP : is_scott_open P)
  : is_scott_open (λ x, P (f x)).
Proof.
  split.
  - intros y₁ y₂ p q.
    use (is_scott_open_upper_set HP p).
    apply (is_monotone_scott_continuous_map f).
    exact q.
  - intros D H.
    rewrite scott_continuous_map_on_lub in H.
    assert (H' := is_scott_open_lub_inaccessible HP _ H).
    revert H'.
    use factor_through_squash_hProp.
    exact (λ ip, hinhpr ip).
Qed.

(**
 9. Scott contiuous maps reflect apartness
 *)
Proposition reflect_apartness
            {X Y : dcpo}
            (f : scott_continuous_map X Y)
            {x y : X}
  : f x # f y → x # y.
Proof.
  use factor_through_squash_hProp.
  intro p.
  induction p as [ p | p ].
  - revert p.
    use factor_through_squash_hProp.
    intros ( P & HP & HPfx & HPfy ).
    use hdisj_in1.
    use hinhpr.
    simple refine (_ ,, _ ,, _ ,, _).
    + exact (λ x, P(f x)).
    + exact (preimage_scott_open f HP).
    + exact HPfx.
    + exact HPfy.
  - revert p.
    use factor_through_squash_hProp.
    intros ( P & HP & HPfx & HPfy ).
    use hdisj_in2.
    use hinhpr.
    simple refine (_ ,, _ ,, _ ,, _).
    + exact (λ x, P(f x)).
    + exact (preimage_scott_open f HP).
    + exact HPfx.
    + exact HPfy.
Qed.
