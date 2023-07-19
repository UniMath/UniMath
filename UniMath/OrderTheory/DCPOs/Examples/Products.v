(*****************************************************************

 Type indexed products of DCPOs

 In this file, we construct type indexed products of DCPOs, and
 we prove the usual universal property. In addition, we use this
 construction to construct the DCPO whose inhabitants are subsets
 of a fixed set.

 Contents
 1. Type indexed products
 2. The universal property
 3. It is pointed
 4. Functions to a fixed DCPO
 5. The subtype DCPO

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Examples.Propositions.
Require Import UniMath.OrderTheory.DCPOs.Examples.SubDCPO.

Local Open Scope dcpo.

(**
 1. Type indexed products
 *)
Section TypeIndexedProductsDCPO.
  Context {I : UU}
          (D : I → dcpo).

  Definition app_directed_set_depfun
             (E : directed_set
                    (depfunction_poset (λ i, D i) (λ i, D i)))
             (i : I)
    : directed_set (D i).
  Proof.
    use make_directed_set.
    - exact E.
    - exact (λ e, E e i).
    - split.
      + exact (directed_set_el E).
      + abstract
          (intros e₁ e₂ ;
           assert (k := directed_set_top E e₁ e₂) ;
           revert k ;
           use factor_through_squash ; [ apply propproperty | ] ;
           intros k ;
           induction k as [ k [ H₁ H₂ ]] ;
           exact (hinhpr (k ,, (H₁ i ,, H₂ i)))).
  Defined.

  Section DepFunctionLub.
    Context (E : directed_set
                   (depfunction_poset (λ i, D i) (λ i, D i))).

    Definition type_prod_pointwise_lub
               (i : I)
      : D i
      := ⨆ (app_directed_set_depfun E i).

    Proposition is_lub_type_prod_pointwise_lub
      : is_least_upperbound
          (depfunction_poset (λ i : I, D i) (λ i : I, D i))
          E
          type_prod_pointwise_lub.
    Proof.
      split.
      - intros e i ; cbn.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      - intros f Hf i.
        use dcpo_lub_is_least.
        intro e ; cbn.
        exact (Hf e i).
    Qed.
  End DepFunctionLub.

  Definition directed_complete_depfunction
    : directed_complete_poset
        (depfunction_poset (λ i, D i) (λ i, D i)).
  Proof.
    intros J E HE.
    use make_lub.
    - exact (type_prod_pointwise_lub (J ,, (E ,, HE))).
    - exact (is_lub_type_prod_pointwise_lub (J ,, (E ,, HE))).
  Defined.

  Definition depfunction_dcpo_struct
    : dcpo_struct (∏ y, D y)%set
    := depfunction_poset _ (λ i, D i) ,, directed_complete_depfunction.

  Definition depfunction_dcpo
    : dcpo
    := _ ,, depfunction_dcpo_struct.

  (**
   2. The universal property
   *)
  Proposition is_scott_continuous_depfunction_pr
              (i : I)
    : is_scott_continuous
        depfunction_dcpo
        (D i)
        (λ f, f i).
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_depfunction_poset_pr (λ i, D i) (λ i, D i) i).
    - intros E.
      cbn ; unfold type_prod_pointwise_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
  Qed.

  Proposition is_scott_continuous_depfunction_map
              {W : dcpo}
              (fs : ∏ (i : I), scott_continuous_map W (D i))
    : is_scott_continuous W depfunction_dcpo (λ w i, fs i w).
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_depfunction_poset_pair fs (λ i, pr12 (fs i))).
    - intros E.
      use funextsec ; intro i.
      cbn ; unfold type_prod_pointwise_lub.
      rewrite scott_continuous_map_on_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
  Qed.
End TypeIndexedProductsDCPO.

(**
 3. It is pointed
 *)
Definition depfunction_dcppo_struct
           {I : UU}
           (D : I → dcppo)
  : dcppo_struct (∏ y, D y)%set.
Proof.
  simple refine (depfunction_dcpo_struct (λ i, D i) ,, _ ,, _).
  - exact (λ i, ⊥_{ D i }).
  - abstract
      (intros f i ; cbn ;
       apply is_min_bottom_dcppo).
Defined.

Definition depfunction_dcppo
           {I : UU}
           (D : I → dcppo)
  : dcppo
  := _ ,, depfunction_dcppo_struct D.

Proposition is_strict_scott_continuous_depfunction_pr
            {I : UU}
            (D : I → dcppo)
            (i : I)
  : is_strict_scott_continuous
      (depfunction_dcppo_struct D)
      (D i)
      (λ f, f i).
Proof.
  simple refine (_ ,, _).
  - exact (is_scott_continuous_depfunction_pr D i).
  - apply idpath.
Qed.

Proposition is_strict_scott_continuous_depfunction_map
            {I : UU}
            (D : I → dcppo)
            {W : dcppo}
            (fs : ∏ (i : I), strict_scott_continuous_map W (D i))
  : is_strict_scott_continuous
      W
      (depfunction_dcppo  D)
      (λ w i, fs i w).
Proof.
  simple refine (_ ,, _).
  - exact (is_scott_continuous_depfunction_map D fs).
  - use funextsec.
    intro.
    apply strict_scott_continuous_map_on_point.
Qed.

(**
 4. Functions to a fixed DCPO
 *)
Definition funset_dcpo
           (X : UU)
           (D : dcpo)
  : dcpo
  := @depfunction_dcpo X (λ _, D).

Definition funset_dcppo
           (X : UU)
           (D : dcppo)
  : dcppo
  := @depfunction_dcppo X (λ _, D).

(**
 5. The subtype DCPO
 *)
Definition subtype_dcppo
           (X : UU)
  : dcppo
  := funset_dcppo X hProp_dcppo.

(**
 6. The DCPO of monotone functions
 *)
Proposition lub_is_monotone
            {X Y : dcpo}
            (D : directed_set (funset_dcpo X Y))
            (HD : ∏ (d : D), is_monotone X Y (D d))
  : is_monotone X Y (⨆ D).
Proof.
  intros x y p.
  use dcpo_lub_is_least.
  intro d ; cbn in d ; cbn.
  use less_than_dcpo_lub.
  {
    exact d.
  }
  cbn.
  apply HD.
  exact p.
Qed.

Definition monotone_map_dcpo
           (X Y : dcpo)
  : dcpo
  := sub_dcpo
       (funset_dcpo X Y)
       (λ f, make_hProp (is_monotone X Y f) (isaprop_is_monotone _ _ _))
       lub_is_monotone.
