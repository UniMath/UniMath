(*****************************************************************

 Binary products of DCPOs

 The product of two DCPOs is again a DCPO, and this satisfies the
 usual universal property. In addition, we construct a basis for
 the product DCPO.

 Contents
 1. Upperbounds in the product
 2. The DCPO
 3. The first projection
 4. The second projection
 5. Pairing of functions
 6. Lemmas on upperbounds in the product
 7. A basis for the product

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
 1. Upperbounds in the product
 *)
Proposition is_least_upperbound_pair
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (I : UU)
            (D : I → (X × Y)%set)
            (x : X)
            (y : Y)
            (Hx : is_least_upperbound DX (λ i, pr1 (D i)) x)
            (Hy : is_least_upperbound DY (λ i, pr2 (D i)) y)
  : is_least_upperbound (prod_PartialOrder DX DY) D (x ,, y).
Proof.
  pose (x' := (x ,, Hx) : lub DX _).
  pose (y' := (y ,, Hy) : lub DY _).
  split.
  - intros i.
    exact (lub_is_upperbound x' i ,, lub_is_upperbound y' i).
  - intros z Hz.
    exact (lub_is_least x' _ (λ i, pr1 (Hz i))
           ,,
           lub_is_least y' _ (λ i, pr2 (Hz i))).
Qed.

Definition prod_lub
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
           (I : UU)
           (D : I → (X × Y)%set)
           (x : lub DX (λ i, pr1 (D i)))
           (y : lub DY (λ i, pr2 (D i)))
  : lub (prod_PartialOrder DX DY) D.
Proof.
  use make_lub.
  - exact (pr1 x ,, pr1 y).
  - use is_least_upperbound_pair.
    + exact (pr2 x).
    + exact (pr2 y).
Defined.

(**
 2. The DCPO
 *)
Definition prod_dcpo_struct
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
  : dcpo_struct (X × Y)%set.
Proof.
  use make_dcpo_struct.
  - exact (prod_PartialOrder DX DY).
  - intros I D HD.
    use prod_lub.
    + use (dcpo_struct_lub DX (λ i, pr1 (D i))).
      abstract
        (use (is_directed_comp _ _ HD) ;
         apply dirprod_pr1_is_monotone).
    + use (dcpo_struct_lub DY (λ i, pr2 (D i))).
      abstract
        (use (is_directed_comp _ _ HD) ;
         apply dirprod_pr2_is_monotone).
Defined.

Definition prod_dcppo_struct
           {X Y : hSet}
           (DX : dcppo_struct X)
           (DY : dcppo_struct Y)
  : dcppo_struct (X × Y)%set.
Proof.
  refine (prod_dcpo_struct DX DY ,, _).
  exact (pr2 (prod_pointed_PartialOrder DX DY)).
Defined.

Definition prod_dcpo
           (X Y : dcpo)
  : dcpo
  := _ ,, prod_dcpo_struct X Y.

Definition prod_dcppo
           (X Y : dcppo)
  : dcppo
  := _ ,, prod_dcppo_struct X Y.

Notation "X × Y" := (prod_dcpo X Y) : dcpo.

Proposition prod_dcpo_le
            {X Y : dcpo}
            (xy₁ xy₂ : (X × Y)%dcpo)
            (p : pr1 xy₁ ⊑ pr1 xy₂)
            (q : pr2 xy₁ ⊑ pr2 xy₂)
  : xy₁ ⊑ xy₂.
Proof.
  exact (p ,, q).
Qed.

(**
 3. The first projection
 *)
Proposition pr1_is_least_upperbound
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {I : UU}
            {D : I → X × Y}
            (xy : X × Y)
            (Hxy : is_least_upperbound (prod_dcpo_struct DX DY) D xy)
  : is_least_upperbound DX (λ i, pr1 (D i)) (pr1 xy).
Proof.
  split.
  - intros i.
    exact (pr1 (is_least_upperbound_is_upperbound Hxy i)).
  - intros x Hx.
    refine (pr1 (is_least_upperbound_is_least Hxy (x ,, pr2 xy) _)).
    intros i.
    split ; cbn.
    + exact (Hx i).
    + exact (pr2 (is_least_upperbound_is_upperbound Hxy i)).
Qed.

Proposition is_scott_continuous_dirprod_pr1
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
  : is_scott_continuous
      (prod_dcpo_struct DX DY)
      DX
      dirprod_pr1.
Proof.
  split.
  - apply dirprod_pr1_is_monotone.
  - intros I DI HD x Hx.
    split.
    + intros i.
      exact (pr1 (is_least_upperbound_is_upperbound Hx i)).
    + intros x' Hx'.
      refine (pr1 (is_least_upperbound_is_least Hx (x' ,, pr2 x) _)).
      intro i.
      split ; cbn.
      * exact (Hx' i).
      * exact (pr2 (is_least_upperbound_is_upperbound Hx i)).
Qed.

Proposition is_strict_scott_continuous_dirprod_pr1
            {X Y : hSet}
            (DX : dcppo_struct X)
            (DY : dcppo_struct Y)
  : is_strict_scott_continuous
      (prod_dcppo_struct DX DY)
      DX
      dirprod_pr1.
Proof.
  split.
  - apply is_scott_continuous_dirprod_pr1.
  - apply idpath.
Qed.

Definition dirprod_pr1_scott_continuous_map
           (X Y : dcpo)
  : scott_continuous_map (X × Y) X
  := _ ,, is_scott_continuous_dirprod_pr1 X Y.

Notation "'π₁'" := (dirprod_pr1_scott_continuous_map _ _) : dcpo.

(**
 4. The second projection
 *)
Proposition pr2_is_least_upperbound
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {I : UU}
            {D : I → X × Y}
            (xy : X × Y)
            (Hxy : is_least_upperbound (prod_dcpo_struct DX DY) D xy)
  : is_least_upperbound DY (λ i, pr2 (D i)) (pr2 xy).
Proof.
  split.
  - intros i.
    exact (pr2 (is_least_upperbound_is_upperbound Hxy i)).
  - intros y Hy.
    refine (pr2 (is_least_upperbound_is_least Hxy (pr1 xy ,, y) _)).
    intros i.
    split ; cbn.
    + exact (pr1 (is_least_upperbound_is_upperbound Hxy i)).
    + exact (Hy i).
Qed.

Proposition is_scott_continuous_dirprod_pr2
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
  : is_scott_continuous
      (prod_dcpo_struct DX DY)
      DY
      dirprod_pr2.
Proof.
  split.
  - apply dirprod_pr2_is_monotone.
  - intros I DI HD x Hx.
    split.
    + intros i.
      exact (pr2 (is_least_upperbound_is_upperbound Hx i)).
    + intros y' Hy'.
      refine (pr2 (is_least_upperbound_is_least Hx (pr1 x ,, y') _)).
      intro i.
      split ; cbn.
      * exact (pr1 (is_least_upperbound_is_upperbound Hx i)).
      * exact (Hy' i).
Qed.

Proposition is_strict_scott_continuous_dirprod_pr2
            {X Y : hSet}
            (DX : dcppo_struct X)
            (DY : dcppo_struct Y)
  : is_strict_scott_continuous
      (prod_dcppo_struct DX DY)
      DY
      dirprod_pr2.
Proof.
  split.
  - apply is_scott_continuous_dirprod_pr2.
  - apply idpath.
Qed.

Definition dirprod_pr2_scott_continuous_map
           (X Y : dcpo)
  : scott_continuous_map (X × Y) Y
  := _ ,, is_scott_continuous_dirprod_pr2 X Y.

Notation "'π₂'" := (dirprod_pr2_scott_continuous_map _ _) : dcpo.

(**
 5. Pairing of functions
 *)
Proposition is_scott_continuous_prodtofun
            {W X Y : hSet}
            {DW : dcpo_struct W}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {f : W → X}
            (Hf : is_scott_continuous DW DX f)
            {g : W → Y}
            (Hg : is_scott_continuous DW DY g)
  : is_scott_continuous
      DW
      (prod_dcpo_struct DX DY)
      (prodtofuntoprod (f ,, g)).
Proof.
  split.
  - apply prodtofun_is_monotone.
    + exact (is_scott_continuous_monotone Hf).
    + exact (is_scott_continuous_monotone Hg).
  - intros I D HD w Hw.
    split.
    + intro i.
      split ; cbn.
      * exact (is_least_upperbound_is_upperbound
                 (is_scott_continuous_lub Hf HD w Hw)
                 i).
      * exact (is_least_upperbound_is_upperbound
                 (is_scott_continuous_lub Hg HD w Hw)
                 i).
    + intros xy Hxy.
      split ; cbn.
      * use (is_least_upperbound_is_least
               (is_scott_continuous_lub Hf HD w Hw)
               (pr1 xy)).
        intro i.
        exact (pr1 (Hxy i)).
      * use (is_least_upperbound_is_least
               (is_scott_continuous_lub Hg HD w Hw)
               (pr2 xy)).
        intro i.
        exact (pr2 (Hxy i)).
Qed.

Proposition is_strict_scott_continuous_prodtofun
            {W X Y : hSet}
            {DW : dcppo_struct W}
            {DX : dcppo_struct X}
            {DY : dcppo_struct Y}
            {f : W → X}
            (Hf : is_strict_scott_continuous DW DX f)
            {g : W → Y}
            (Hg : is_strict_scott_continuous DW DY g)
  : is_strict_scott_continuous
      DW
      (prod_dcppo_struct DX DY)
      (prodtofuntoprod (f ,, g)).
Proof.
  split.
  - exact (is_scott_continuous_prodtofun Hf Hg).
  - use pathsdirprod.
    + apply Hf.
    + apply Hg.
Qed.

Definition pair_scott_continuous
           {W X Y : dcpo}
           (f : scott_continuous_map W X)
           (g : scott_continuous_map W Y)
  : scott_continuous_map W (X × Y)
  := _ ,, is_scott_continuous_prodtofun (pr2 f) (pr2 g).

Notation "⟨ f , g ⟩" := (pair_scott_continuous f g) : dcpo.

(**
 6. Lemmas on upperbounds in the product
 *)
Proposition prod_dcpo_lub
            {X Y : dcpo}
            (D : directed_set (X × Y))
  : ⨆ D = (⨆ (π₁ {{ D }}) ,, ⨆ (π₂ {{ D }})).
Proof.
  use (eq_lub (X × Y) D).
  - apply is_least_upperbound_dcpo_lub.
  - use is_least_upperbound_pair.
    + exact (is_least_upperbound_dcpo_comp_lub
               (dirprod_pr1_scott_continuous_map X Y)
               D).
    + exact (is_least_upperbound_dcpo_comp_lub
               (dirprod_pr2_scott_continuous_map X Y)
               D).
Qed.

Definition prod_directed_set_dcpo
           {X Y : dcpo}
           (D₁ : directed_set X)
           (D₂ : directed_set Y)
  : directed_set (X × Y)
  := prod_directed_set D₁ D₂.

Proposition prod_dcpo_lub'
            {X Y : dcpo}
            (D : directed_set X)
            (D' : directed_set Y)
  : ⨆ (prod_directed_set_dcpo D D') = (⨆ D ,, ⨆ D').
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intro i.
    use prod_dcpo_le ; cbn in *.
    + use less_than_dcpo_lub.
      * exact (pr1 i).
      * apply refl_dcpo.
    + use less_than_dcpo_lub.
      * exact (pr2 i).
      * apply refl_dcpo.
  - assert (Di := directed_set_el D).
    revert Di.
    use factor_through_squash ; [ apply propproperty | ].
    intro Di.
    assert (Di' := directed_set_el D').
    revert Di'.
    use factor_through_squash ; [ apply propproperty | ].
    intro Di'.
    use prod_dcpo_le.
    + use dcpo_lub_is_least.
      intro i.
      refine (pr1 (less_than_dcpo_lub
                     (prod_directed_set_dcpo D D')
                     (D i ,, D' Di')
                     (i ,, Di')
                     _)).
      use prod_dcpo_le ; cbn.
      * apply refl_dcpo.
      * apply refl_dcpo.
    + use dcpo_lub_is_least.
      intro i'.
      refine (pr2 (less_than_dcpo_lub
                     (prod_directed_set_dcpo D D')
                     (D Di ,, D' i')
                     (Di ,, i')
                     _)).
      use prod_dcpo_le ; cbn.
      * apply refl_dcpo.
      * apply refl_dcpo.
Qed.

(**
 7. A basis for the product
 *)
Section ProductBasis.
  Context {X Y : dcpo}
          (BX : dcpo_basis X)
          (BY : dcpo_basis Y).

  Proposition way_below_prod_pr1
              {xy₁ xy₂ : prod_dcpo X Y}
              (p : xy₁ ≪ xy₂)
    : pr1 xy₁ ≪ pr1 xy₂.
  Proof.
    intros D q.
    pose (D' := prod_directed_set_dcpo D (directed_set_from_basis BY (pr2 xy₂))).
    assert (HD : xy₂ ⊑ ⨆ D').
    {
      unfold D'.
      rewrite prod_dcpo_lub'.
      rewrite approximating_basis_lub.
      exact (q ,, refl_dcpo _).
    }
    assert (H := p D' HD).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ i H ].
    exact (hinhpr (pr1 i ,, pr1 H)).
  Qed.

  Proposition way_below_prod_pr2
              {xy₁ xy₂ : prod_dcpo X Y}
              (p : xy₁ ≪ xy₂)
    : pr2 xy₁ ≪ pr2 xy₂.
  Proof.
    intros D q.
    pose (D' := prod_directed_set_dcpo (directed_set_from_basis BX (pr1 xy₂)) D).
    assert (HD : xy₂ ⊑ ⨆ D').
    {
      unfold D'.
      rewrite prod_dcpo_lub'.
      rewrite approximating_basis_lub.
      exact (refl_dcpo _ ,, q).
    }
    assert (H := p D' HD).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ i H ].
    exact (hinhpr (pr2 i ,, pr2 H)).
  Qed.

  Proposition to_way_below_prod
              {xy₁ xy₂ : prod_dcpo X Y}
              (p : pr1 xy₁ ≪ pr1 xy₂)
              (q : pr2 xy₁ ≪ pr2 xy₂)
    : xy₁ ≪ xy₂.
  Proof.
    intros D r.
    rewrite prod_dcpo_lub in r.
    assert (H := p (directed_set_comp π₁ D) (pr1 r)).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ i s₁ ].
    assert (H := q (directed_set_comp π₂ D) (pr2 r)).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ j s₂ ].
    assert (H := directed_set_top D i j).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ t [ u₁ u₂ ]].
    simple refine (hinhpr (t ,, _ ,, _)).
    - exact (trans_dcpo s₁ (pr1 u₁)).
    - exact (trans_dcpo s₂ (pr2 u₂)).
  Qed.

  Proposition way_below_prod_weq
              (xy₁ xy₂ : prod_dcpo X Y)
    : xy₁ ≪ xy₂ ≃ ((pr1 xy₁ ≪ pr1 xy₂) ∧ (pr2 xy₁ ≪ pr2 xy₂)).
  Proof.
    use weqimplimpl.
    - intros p.
      split.
      + exact (way_below_prod_pr1 p).
      + exact (way_below_prod_pr2 p).
    - intros p.
      exact (to_way_below_prod (pr1 p) (pr2 p)).
    - apply propproperty.
    - apply propproperty.
  Qed.

  Definition prod_dcpo_basis_data
    : dcpo_basis_data (prod_dcpo X Y).
  Proof.
    use make_dcpo_basis_data.
    - exact (BX × BY)%type.
    - exact (dirprodf BX BY).
  Defined.

  Proposition prod_dcpo_basis_laws
    : dcpo_basis_laws (X × Y) prod_dcpo_basis_data.
  Proof.
    intros xy.
    split.
    - split.
      + assert (H := directed_set_el (directed_set_from_basis BX (pr1 xy))).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros a.
        induction a as [ a p ].
        assert (H := directed_set_el (directed_set_from_basis BY (pr2 xy))).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b q ].
        refine (hinhpr ((a ,, b) ,, _)).
        use to_way_below_prod.
        * exact p.
        * exact q.
      + intros ij₁ ij₂.
        assert (H := directed_set_top
                       (directed_set_from_basis BX (pr1 xy))
                       (pr11 ij₁ ,, way_below_prod_pr1 (pr2 ij₁))
                       (pr11 ij₂ ,, way_below_prod_pr1 (pr2 ij₂))).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros k.
        induction k as [ k [ p₁ p₂ ]].
        assert (H := directed_set_top
                       (directed_set_from_basis BY (pr2 xy))
                       (pr21 ij₁ ,, way_below_prod_pr2 (pr2 ij₁))
                       (pr21 ij₂ ,, way_below_prod_pr2 (pr2 ij₂))).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros l.
        induction l as [ l [ q₁ q₂ ]].
        simple refine (hinhpr (((_ ,, _) ,, _) ,, (_ ,, _) ,, (_ ,, _))).
        * exact (pr1 k).
        * exact (pr1 l).
        * use to_way_below_prod.
          ** exact (pr2 k).
          ** exact (pr2 l).
        * exact p₁.
        * exact q₁.
        * exact p₂.
        * exact q₂.
    - use is_least_upperbound_pair.
      + split.
        * intros a.
          refine (is_least_upperbound_is_upperbound
                    (is_least_upperbound_basis BX (pr1 xy))
                    (pr11 a ,, _)).
          apply (way_below_prod_pr1 (pr2 a)).
        * intros a Ha.
          apply (is_least_upperbound_is_least
                   (is_least_upperbound_basis BX (pr1 xy))).
          intros b.
          assert (H := basis_nullary_interpolation BY (pr2 xy)).
          revert H.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intro H.
          induction H as [ c p ].
          simple refine (Ha ((pr1 b ,, c) ,, _)).
          use to_way_below_prod.
          ** exact (pr2 b).
          ** exact p.
      + split.
        * intros a.
          refine (is_least_upperbound_is_upperbound
                    (is_least_upperbound_basis BY (pr2 xy))
                    (pr21 a ,, _)).
          apply (way_below_prod_pr2 (pr2 a)).
        * intros a Ha.
          apply (is_least_upperbound_is_least
                   (is_least_upperbound_basis BY (pr2 xy))).
          intros b.
          assert (H := basis_nullary_interpolation BX (pr1 xy)).
          revert H.
          use factor_through_squash.
          {
            apply propproperty.
          }
          intro H.
          induction H as [ c p ].
          simple refine (Ha ((c ,, pr1 b) ,, _)).
          use to_way_below_prod.
          ** exact p.
          ** exact (pr2 b).
  Qed.

  Definition prod_dcpo_basis
    : dcpo_basis (prod_dcpo X Y).
  Proof.
    use make_dcpo_basis.
    - exact prod_dcpo_basis_data.
    - exact prod_dcpo_basis_laws.
  Defined.
End ProductBasis.

Definition dcpo_continuous_struct_product
           {X Y : dcpo}
           (CX : continuous_dcpo_struct X)
           (CY : continuous_dcpo_struct Y)
  : continuous_dcpo_struct (prod_dcpo X Y).
Proof.
  use continuous_struct_from_basis.
  use prod_dcpo_basis.
  - use basis_from_continuous_struct.
    exact CX.
  - use basis_from_continuous_struct.
    exact CY.
Defined.
