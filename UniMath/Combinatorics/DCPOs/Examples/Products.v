(*****************************************************************

 Constructions on DCPOs

 In this file, we define numerous constructions on DCPOs. These
 constructions show that the category of DCPOs is complete.

 In addition, we show that every set gives rise to a discrete
 DCPO, whose underlying set is the given set and whose order is
 given by the identity relation.

 Contents
 1. The unit DCPO
 2. Binary products of DCPOs
 2.1. Upperbounds in the product
 2.2. The DCPO
 2.3. The first projection
 2.4. The second projection
 2.5. Pairing of functions
 2.6. Lemmas on upperbounds in the product
 3. Equalizers
 4. Type indexed products
 5. Discrete DCPOs
 6. hProp

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.PointedPosets.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.DCPOs.Core.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.Core.Basics.
Require Import UniMath.Combinatorics.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

(**
 4. Type indexed products
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
