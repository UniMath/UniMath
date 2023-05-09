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

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.Posets.PointedPosets.
Require Import UniMath.Combinatorics.DCPOs.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.DCPOBasics.

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

(**
 5. Bundled approach
 *)
Definition scott_continuous_map
           (X Y : dcpo)
  : UU
  := ∑ (f : X → Y), is_scott_continuous X Y f.

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
            (p : x₁ ≤ x₂)
  : f x₁ ≤ f x₂.
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

Coercion scott_continuous_map_to_monotone
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
          (Hf₁ : ∏ (x₁ x₂ : X), x₁ ≤ x₂ → f x₁ ≤ f x₂).

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
