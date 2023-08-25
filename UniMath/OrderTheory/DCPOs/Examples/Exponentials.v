(*****************************************************************

 Exponentials for DCPOs

 We construct exponentials for the category of DCPOs. Concretely,
 we show that the set of Scott continuous functions between DCPOs
 is a DCPO as well.

 Contents
 1. Lemmas for calculation purposes
 2. The exponential
 3. Completeness of the exponential
 4. Evaluation
 5. Abstraction

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.FubiniTheorem.
Require Import UniMath.OrderTheory.DCPOs.Core.CoordinateContinuity.
Require Import UniMath.OrderTheory.DCPOs.Examples.BinaryProducts.

Local Open Scope dcpo.

(**
 1. Lemmas for calculation purposes
 *)
Proposition prod_dcpo_monotone_lub_const_l
            {X Y Z : dcpo}
            (D : directed_set Y)
            (f : monotone_function (X × Y) Z)
            (x : X)
            {I : UU}
            (i : ∥ I ∥)
  : ⨆_{prod_directed_set_dcpo (const_directed_set X x I i) D} f
    =
    ⨆_{D} (f ·l x).
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    cbn ; intro j.
    use less_than_dcpo_lub ; cbn.
    + exact (pr2 j).
    + apply refl_dcpo.
  - revert i.
    use factor_dep_through_squash.
    {
      intro.
      apply propproperty.
    }
    intro i.
    use dcpo_lub_is_least.
    cbn ; intro j.
    use less_than_dcpo_lub ; cbn.
    + exact (i ,, j).
    + apply refl_dcpo.
Qed.

Proposition prod_dcpo_monotone_lub_const_r
            {X Y Z : dcpo}
            (D : directed_set X)
            (f : monotone_function (X × Y) Z)
            (y : Y)
            {I : UU}
            (i : ∥ I ∥)
  : ⨆_{prod_directed_set_dcpo D (const_directed_set Y y I i)} f
    =
    ⨆_{D} (f ·r y).
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    cbn ; intro j.
    use less_than_dcpo_lub ; cbn.
    + exact (pr1 j).
    + apply refl_dcpo.
  - revert i.
    use factor_dep_through_squash.
    {
      intro.
      apply propproperty.
    }
    intro i.
    use dcpo_lub_is_least.
    cbn ; intro j.
    use less_than_dcpo_lub ; cbn.
    + exact (j ,, i).
    + apply refl_dcpo.
Qed.

(**
 2. The exponential
 *)
Definition scott_continuous_map_hSet
           (X Y : dcpo)
  : hSet.
Proof.
  refine (scott_continuous_map X Y ,, _).
  use isaset_total2.
  - use funspace_isaset.
    apply setproperty.
  - intros f.
    apply isasetaprop.
    apply isaprop_is_scott_continuous.
Defined.

Definition scott_continuous_map_PartialOrder
           (X Y : dcpo)
  : PartialOrder (scott_continuous_map_hSet X Y).
Proof.
  use make_PartialOrder.
  - exact (λ f g, ∀ (x : X), pr1 f x ⊑ pr1 g x).
  - refine ((_ ,, _) ,, _).
    + abstract
        (intros f g h p q x ;
         exact (trans_dcpo (p x) (q x))).
    + abstract
        (intros f x ;
         exact (refl_dcpo (pr1 f x))).
    + abstract
        (intros f g p q ;
         use subtypePath ; [ intro ; apply isaprop_is_scott_continuous | ] ;
         use funextsec ;
         intro x ;
         exact (antisymm_dcpo (p x) (q x))).
Defined.

Definition scott_continuous_app
           (X Y : dcpo)
           (x : X)
  : monotone_function (scott_continuous_map_PartialOrder X Y) Y.
Proof.
  simple refine (_ ,, _).
  - exact (λ f, pr1 f x).
  - abstract
      (intros f₁ f₂ p ;
       exact (p x)).
Defined.

(**
 3. Completeness of the exponential
 *)
Section FunctionLub.
  Context {X Y : dcpo}
          (D : directed_set (scott_continuous_map_PartialOrder X Y)).

  Definition pointwise_lub
             (x : X)
    : Y
    := ⨆ (scott_continuous_app X Y x {{ D }}).

  Proposition is_monotone_pointwise_lub
              (x₁ x₂ : X)
              (p : x₁ ⊑ x₂)
    : pointwise_lub x₁ ⊑ pointwise_lub x₂.
  Proof.
    unfold pointwise_lub.
    use dcpo_lub_is_least ; cbn.
    intro i.
    use less_than_dcpo_lub.
    - exact i.
    - exact (is_monotone_scott_continuous_map (_ ,, pr2 (D i)) p).
  Qed.

  Proposition is_scott_continuous_pointwise_lub
    : is_scott_continuous X Y pointwise_lub.
  Proof.
    use make_is_scott_continuous.
    - exact is_monotone_pointwise_lub.
    - intros D' ; unfold pointwise_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least.
        cbn ; intro i.
        rewrite (scott_continuous_map_on_lub (D i)).
        use dcpo_lub_is_least.
        cbn ; intro j.
        use less_than_dcpo_lub.
        * exact j.
        * cbn.
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             apply refl_dcpo.
      + use dcpo_lub_is_least.
        cbn ; intro i.
        use dcpo_lub_is_least.
        cbn ; intro j.
        use less_than_dcpo_lub.
        * exact j.
        * cbn.
          rewrite (scott_continuous_map_on_lub (D j)).
          use less_than_dcpo_lub.
          ** exact i.
          ** cbn.
             apply refl_dcpo.
  Qed.

  Definition scott_continuous_lub_map
    : scott_continuous_map_hSet X Y
    := pointwise_lub ,, is_scott_continuous_pointwise_lub.

  Proposition scott_continuous_lub_map_is_least_upperbound
    : is_least_upperbound
        (scott_continuous_map_PartialOrder X Y)
        D
        scott_continuous_lub_map.
  Proof.
    split.
    - intros i x.
      use less_than_dcpo_lub.
      + exact i.
      + apply refl_dcpo.
    - intros f Hf x ; cbn.
      unfold pointwise_lub.
      use dcpo_lub_is_least.
      intro i ; cbn.
      exact (Hf i x).
  Qed.

  Definition scott_continuous_lub
    : lub (scott_continuous_map_PartialOrder X Y) D
    := scott_continuous_lub_map
       ,,
       scott_continuous_lub_map_is_least_upperbound.
End FunctionLub.

Definition dcpo_struct_funspace_order_complete
           (X Y : dcpo)
  : directed_complete_poset (scott_continuous_map_PartialOrder X Y)
  := λ I D HD, scott_continuous_lub (I ,, (D ,, HD)).

Definition dcpo_funspace
           (X Y : dcpo)
  : dcpo
  := _ ,, (_ ,, dcpo_struct_funspace_order_complete X Y).

Definition dcpo_struct_funspace
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
  : dcpo_struct (scott_continuous_map_hSet (X ,, DX) (Y ,, DY))
  := pr2 (dcpo_funspace (X ,,  DX) (Y ,, DY)).

Definition dcppo_struct_funspace
           {X Y : hSet}
           (DX : dcppo_struct X)
           (DY : dcppo_struct Y)
  : dcppo_struct (scott_continuous_map_hSet (X ,, pr1 DX) (Y ,, pr1 DY)).
Proof.
  refine (dcpo_struct_funspace DX DY ,, _).
  simple refine ((_ ,, _) ,, _).
  - exact (λ _, pr12 DY).
  - apply is_scott_continuous_constant.
  - intros f x ; cbn.
    apply (pr22 DY).
Defined.

(**
 4. Evaluation
 *)
Proposition is_scott_continuous_eval
            (X Y : dcpo)
  : is_scott_continuous
      (X × dcpo_funspace X Y)
      Y
      (λ xf, (pr12 xf) (pr1 xf)).
Proof.
  use is_scott_continuous_coordinates.
  - intros x.
    use make_is_scott_continuous.
    + intros f g p ; cbn in *.
      apply p.
    + intros D.
      cbn ; unfold pointwise_lub ; cbn.
      use dcpo_lub_eq_pointwise.
      intros f ; cbn.
      apply idpath.
  - intros f.
    use make_is_scott_continuous.
    + intros x₁ x₂ p ; cbn in *.
      exact (is_monotone_scott_continuous_map f p).
    + intros D.
      exact (scott_continuous_map_on_lub f D).
Qed.

Definition eval_scott_continuous_map
           (X Y : dcpo)
  : scott_continuous_map (X × dcpo_funspace X Y) Y
  := _ ,, is_scott_continuous_eval X Y.

(**
 5. Abstraction
 *)
Proposition is_scott_continuous_lam
            {X Y Z : dcpo}
            (f : scott_continuous_map (X × Z) Y)
            (H : ∏ (z : Z), is_scott_continuous (pr2 X) (pr2 Y) (λ x, f (x ,, z)))
  : is_scott_continuous
      Z
      (dcpo_funspace X Y)
      (λ z, (λ x, f(x ,, z)) ,, H z).
Proof.
  use make_is_scott_continuous.
  - abstract
      (intros z₁ z₂ p x ;
       apply (is_monotone_scott_continuous_map f) ;
       exact (prod_dcpo_le (x ,, z₁) (x ,, z₂) (refl_dcpo _) p)).
  - intros D.
    use eq_scott_continuous_map.
    intro x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(const_lub x D (directed_set_el D))).
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply prod_dcpo_lub'.
    }
    rewrite scott_continuous_map_on_lub.
    rewrite prod_dcpo_monotone_lub_const_l.
    unfold pointwise_lub.
    use antisymm_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use less_than_dcpo_lub ; cbn.
      * exact i.
      * apply refl_dcpo.
    + use dcpo_lub_is_least.
      cbn ; intro i.
      use less_than_dcpo_lub ; cbn.
      * exact i.
      * apply refl_dcpo.
Qed.

Definition lam_scott_continuous_map
           {X Y Z : dcpo}
           (f : scott_continuous_map (X × Z) Y)
  : scott_continuous_map Z (dcpo_funspace X Y).
Proof.
  refine (_ ,, is_scott_continuous_lam f _).
  abstract
    (intro z ;
     refine (comp_is_scott_continuous _ (pr2 f)) ;
     use is_scott_continuous_prodtofun ;
     [ apply id_is_scott_continuous
     | apply is_scott_continuous_constant ]).
Defined.
