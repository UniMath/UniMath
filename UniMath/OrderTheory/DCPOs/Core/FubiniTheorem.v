(*****************************************************************

 A Fubini-like Theorem for DCPOs

 Fubini's theorem in analysis allows one to swap double integrals.
 For DCPO's, we can state a similar theorem, namely that one can
 switch the order of double suprema.

 Contents
 1. Preliminary definitions
 2. Fubini's theorem

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Examples.BinaryProducts.

Local Open Scope dcpo.

(**
 1. Preliminary definitions
 *)
Definition monotone_function_app_l
           {X Y Z : dcpo}
           (f : monotone_function (X × Y) Z)
           (x : X)
  : monotone_function Y Z.
Proof.
  simple refine (_ ,, _).
  - exact (λ y, f (x ,, y)).
  - abstract
      (intros y₁ y₂ p ; cbn ;
       apply f ;
       exact (refl_PartialOrder X x ,, p)).
Defined.

Definition monotone_function_app_r
           {X Y Z : dcpo}
           (f : monotone_function (X × Y) Z)
           (y : Y)
  : monotone_function X Z.
Proof.
  simple refine (_ ,, _).
  - exact (λ x, f (x ,, y)).
  - abstract
      (intros y₁ y₂ p ; cbn ;
       apply f ;
       exact (p ,, refl_PartialOrder Y y)).
Defined.

Notation "f ·l x" := (monotone_function_app_l f x) (at level 60).
Notation "f ·r y" := (monotone_function_app_r f y) (at level 60).

Definition fubini_monotone_function_l
           {X Y Z : dcpo}
           (f : monotone_function (X × Y) Z)
           (D : directed_set (X × Y))
  : monotone_function X Z.
Proof.
  refine ((λ x, ⨆_{π₂ {{ D }}} (f ·l x)) ,, _).
  abstract
    (intros x₁ x₂ p ;
     use dcpo_lub_is_least ;
     cbn ;
     intro i ;
     use less_than_dcpo_lub ; [ exact i | ] ;
     cbn ;
     apply f ;
     split ; [ exact p | ] ;
     apply refl_PartialOrder).
Defined.

Definition fubini_monotone_function_r
           {X Y Z : dcpo}
           (f : monotone_function (X × Y) Z)
           (D : directed_set (X × Y))
  : monotone_function Y Z.
Proof.
  refine ((λ x, ⨆_{π₁ {{ D }}} (f ·r x)) ,, _).
  abstract
    (intros x₁ x₂ p ;
     use dcpo_lub_is_least ;
     cbn ;
     intro i ;
     use less_than_dcpo_lub ; [ exact i | ] ;
     cbn ;
     apply f ;
     split ; [ | exact p ] ;
     apply refl_PartialOrder).
Defined.

(**
 2. Fubini's theorem
 *)
Proposition monotone_prod_map_fubini_pair_l
            {X Y Z : dcpo}
            (f : monotone_function (X × Y) Z)
            (D : directed_set (X × Y))
  : ⨆_{D} f = ⨆_{π₁ {{D}}} fubini_monotone_function_l f D.
Proof.
  use (eq_lub Z (f {{ D }})).
  - apply is_least_upperbound_dcpo_comp_lub.
  - use make_dcpo_is_least_upperbound.
    + cbn ; intro i.
      use less_than_dcpo_lub.
      * exact i.
      * cbn.
        use less_than_dcpo_lub.
        ** exact i.
        ** apply refl_PartialOrder.
    + intros x' Hx'.
      use dcpo_lub_is_least ; cbn ; cbn in Hx'.
      intro i.
      use dcpo_lub_is_least ; cbn.
      intro j.
      assert (H := is_directed_top (directed_set_is_directed D) i j).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros kH.
      induction kH as [ k [ H₁ H₂ ]].
      refine (trans_PartialOrder Z _ (Hx' k)).
      apply f.
      split.
      * exact (pr1 H₁).
      * exact (pr2 H₂).
Qed.

Proposition monotone_prod_map_fubini_pair_r
            {X Y Z : dcpo}
            (f : monotone_function (X × Y) Z)
            (D : directed_set (X × Y))
  : ⨆_{D} f = ⨆_{π₂ {{D}}} fubini_monotone_function_r f D.
Proof.
  use (eq_lub Z (f {{ D }})).
  - apply is_least_upperbound_dcpo_comp_lub.
  - use make_dcpo_is_least_upperbound.
    + cbn ; intro i.
      use less_than_dcpo_lub.
      * exact i.
      * cbn.
        use less_than_dcpo_lub.
        ** exact i.
        ** apply refl_PartialOrder.
    + intros x' Hx'.
      use dcpo_lub_is_least ; cbn ; cbn in Hx'.
      intro i.
      use dcpo_lub_is_least ; cbn.
      intro j.
      assert (H := is_directed_top (directed_set_is_directed D) i j).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros kH.
      induction kH as [ k [ H₁ H₂ ]].
      refine (trans_PartialOrder Z _ (Hx' k)).
      apply f.
      use prod_dcpo_le ; cbn.
      * exact (pr1 H₂).
      * exact (pr2 H₁).
Qed.

Proposition monotone_fubini_swap
            {X Y Z : dcpo}
            (f : monotone_function (X × Y) Z)
            (D : directed_set (X × Y))
  : ⨆_{π₁ {{D}}} fubini_monotone_function_l f D
    =
    ⨆_{π₂ {{D}}} fubini_monotone_function_r f D.
Proof.
  rewrite <- monotone_prod_map_fubini_pair_l.
  rewrite <- monotone_prod_map_fubini_pair_r.
  apply idpath.
Qed.

Proposition monotone_fubini_swap'
            {X Y Z : dcpo}
            (D₁ : directed_set X)
            (D₂ : directed_set Y)
            (f : monotone_function (X × Y) Z)
  : ⨆_{D₁} (fubini_monotone_function_l f (prod_directed_set D₁ D₂))
    =
    ⨆_{D₂} (fubini_monotone_function_r f (prod_directed_set D₁ D₂)).
Proof.
  refine (_ @ monotone_fubini_swap f (prod_directed_set D₁ D₂) @ _).
  - use antisymm_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use dcpo_lub_is_least.
      cbn ; intro j.
      use less_than_dcpo_lub.
      * exact (i ,, pr2 j).
      * cbn.
        use less_than_dcpo_lub.
        ** exact (i ,, pr2 j).
        ** cbn.
           apply refl_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use dcpo_lub_is_least.
      cbn ; intro j.
      use less_than_dcpo_lub.
      * exact (pr1 i).
      * cbn.
        use less_than_dcpo_lub.
        ** exact j.
        ** cbn.
           apply refl_dcpo.
  - use antisymm_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use dcpo_lub_is_least.
      cbn ; intro j.
      use less_than_dcpo_lub.
      * exact (pr2 i).
      * cbn.
        use less_than_dcpo_lub.
        ** exact j.
        ** cbn.
           apply refl_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use dcpo_lub_is_least.
      cbn ; intro j.
      use less_than_dcpo_lub.
      * exact (pr1 j ,, i).
      * cbn.
        use less_than_dcpo_lub.
        ** exact (pr1 j ,, i).
        ** cbn.
           apply refl_dcpo.
Qed.
