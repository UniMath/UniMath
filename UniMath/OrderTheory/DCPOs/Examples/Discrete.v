(*****************************************************************

 Discrete DCPOs

 Every set gives rise to a DCPO whose relation is given by
 equality.

 Contents
 1. Definition of the discrete DCPO
 2. Maps from the discrete DCPO
 3. Counit of the discrete DCPO adjunction
 4. A basis for the discrete DCPO

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. Definition of the discrete DCPO
 *)
Section DiscreteDCPO.
  Context (A : hSet).

  Definition directed_complete_poset_discrete_partial_order
    : directed_complete_poset (discrete_partial_order A).
  Proof.
    intros I D HD.
    assert (h := is_directed_el HD).
    revert h.
    use factor_through_squash.
    {
      apply isaprop_lub.
    }
    intro i.
    use make_lub.
    - exact (D i).
    - split.
      + intros j ; cbn.
        assert (h := is_directed_top HD i j).
        revert h.
        use factor_through_squash.
        {
          apply setproperty.
        }
        cbn.
        intros k.
        induction k as [ k [ p q ]].
        rewrite p, q.
        apply idpath.
      + intros a p ; cbn in *.
        apply p.
  Defined.

  Definition discrete_dcpo_struct
    : dcpo_struct A
    := discrete_partial_order A
       ,,
       directed_complete_poset_discrete_partial_order.

  Definition discrete_dcpo
    : dcpo
    := A ,, discrete_dcpo_struct.
End DiscreteDCPO.

Proposition discrete_dcpo_lub
            {A : hSet}
            (D : directed_set (discrete_dcpo A))
            (i : D)
  : ⨆ D = D i.
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intro j.
    cbn.
    assert (H := directed_set_top D i j).
    revert H.
    use factor_through_squash.
    {
      apply setproperty.
    }
    cbn ; intros H.
    induction H as [ k [ p q ]].
    rewrite p, q.
    apply idpath.
  - use less_than_dcpo_lub.
    + exact i.
    + apply refl_dcpo.
Qed.

(**
 2. Maps from the discrete DCPO
 *)
Definition monotone_function_discrete_dcpo
           {A : hSet}
           (X : dcpo)
           (f : A → X)
  : monotone_function (discrete_dcpo A) X.
Proof.
  refine (f ,, _).
  abstract
    (intros x₁ x₂ p ;
     induction p ;
     apply refl_dcpo).
Defined.

Proposition is_scott_continuous_map_from_discrete_dcpo
            {A : hSet}
            {X : dcpo}
            (f : A → X)
  : is_scott_continuous (pr2 (discrete_dcpo A)) (pr2 X) f.
Proof.
  use make_is_scott_continuous.
  - apply (pr2 (monotone_function_discrete_dcpo X f)).
  - intros D.
    assert (H := directed_set_el D).
    revert H.
    use factor_through_squash.
    {
      apply setproperty.
    }
    cbn ; intros i.
    rewrite (discrete_dcpo_lub D i).
    use antisymm_dcpo.
    + use less_than_dcpo_lub.
      * exact i.
      * cbn.
        apply refl_dcpo.
    + use dcpo_lub_is_least.
      intro j ; cbn.
      cbn in *.
      assert (H := directed_set_top D i j).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      cbn ; intros H.
      induction H as [ k [ p q ]].
      rewrite p, q.
      apply refl_dcpo.
Qed.

Definition map_from_discrete_dcpo
           {A : hSet}
           {X : dcpo}
           (f : A → X)
  : scott_continuous_map (discrete_dcpo A) X
  := f ,, is_scott_continuous_map_from_discrete_dcpo f.

Definition discrete_dcpo_mor
           {A B : hSet}
           (f : A → B)
  : is_scott_continuous (discrete_dcpo A) (discrete_dcpo B) f.
Proof.
  apply is_scott_continuous_map_from_discrete_dcpo.
Qed.

Definition monotone_function_discrete_dcpo_counit
           (A : dcpo)
  : monotone_function (discrete_dcpo A) A.
Proof.
  refine (idfun _ ,, _).
  abstract
    (cbn ;
     intros x₁ x₂ p ;
     induction p ;
     apply refl_dcpo).
Defined.

(**
 3. Counit of the discrete DCPO adjunction
 *)
Definition discrete_dcpo_counit
           (A : dcpo)
  : is_scott_continuous (discrete_dcpo A) A (λ z, z).
Proof.
  use make_is_scott_continuous.
  - exact (pr2 (monotone_function_discrete_dcpo_counit A)).
  - intro D.
    use antisymm_dcpo.
    + cbn.
      pose (@dcpo_lub_is_least
               (discrete_dcpo A)
               D
               (⨆_{D} (monotone_function_discrete_dcpo_counit A)))
        as p.
      rewrite p.
      * apply refl_dcpo.
      * intro i.
        use antisymm_dcpo.
        ** exact (@less_than_dcpo_lub
                    A
                    (directed_set_comp
                       (monotone_function_discrete_dcpo_counit A)
                       D)
                    (D i)
                    i
                    (refl_dcpo _)).
        ** use dcpo_lub_is_least.
           intro j.
           cbn.
           assert (h := directed_set_top D i j).
           revert h.
           use factor_through_squash.
           {
             apply propproperty.
           }
           cbn.
           intros k.
           induction k as [ k [ r r' ]].
           rewrite r, r'.
           apply refl_dcpo.
    + use dcpo_lub_is_least.
      intro i ; cbn.
      pose (@less_than_dcpo_lub
              (discrete_dcpo A)
              D
              (D i)
              i
              (refl_dcpo _))
        as p.
      cbn in p.
      rewrite p.
      apply refl_dcpo.
Qed.

(**
 4. A basis for the discrete DCPO
 *)
Section DiscreteDCPOBasis.
  Context (X : hSet).

  Proposition discrete_eq_to_way_below
              {x y : discrete_dcpo X}
              (p : x = y)
    : x ≪ y.
  Proof.
    induction p.
    intros D HD.
    assert (H := directed_set_el D).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros i.
    refine (hinhpr (i ,, _)).
    rewrite (less_than_dcpo_lub D (D i) i (refl_dcpo _)).
    exact HD.
  Qed.

  Proposition discrete_way_below_to_eq
              {x y : discrete_dcpo X}
              (p : x ≪ y)
    : x = y.
  Proof.
    exact (way_below_to_le p).
  Qed.

  Definition discrete_dcpo_basis_data
    : dcpo_basis_data (discrete_dcpo X).
  Proof.
    use make_dcpo_basis_data.
    - exact X.
    - exact (λ x, x).
  Defined.

  Proposition discrete_dcpo_basis_laws
    : dcpo_basis_laws (discrete_dcpo X) discrete_dcpo_basis_data.
  Proof.
    intro x.
    split.
    - split.
      + refine (hinhpr (x ,, _)).
        apply discrete_eq_to_way_below.
        apply idpath.
      + intros i j.
        induction i as [ y₁ p₁ ].
        induction j as [ y₂ p₂ ].
        simple refine (hinhpr ((_ ,, _) ,, _ ,, _)).
        * exact x.
        * apply discrete_eq_to_way_below.
          apply idpath.
        * apply discrete_way_below_to_eq.
          exact p₁.
        * apply discrete_way_below_to_eq.
          exact p₂.
    - split.
      + intros y.
        induction y as [ y p ].
        apply discrete_way_below_to_eq.
        exact p.
      + intros y Hy.
        refine (Hy (x ,, _)).
        apply discrete_eq_to_way_below.
        apply idpath.
  Qed.

  Definition discrete_dcpo_basis
    : dcpo_basis (discrete_dcpo X).
  Proof.
    use make_dcpo_basis.
    - exact discrete_dcpo_basis_data.
    - exact discrete_dcpo_basis_laws.
  Defined.

  Definition dcpo_continuous_struct_discrete
    : continuous_dcpo_struct (discrete_dcpo X).
  Proof.
    use continuous_struct_from_basis.
    exact discrete_dcpo_basis.
  Defined.
End DiscreteDCPOBasis.
