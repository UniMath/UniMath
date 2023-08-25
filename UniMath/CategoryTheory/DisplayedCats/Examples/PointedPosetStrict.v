(*****************************************************************

 The category of pointed posets and strict functions

 We construct the category of pointed posets and strict monotone
 functions as a category of structured sets. In addition, we show
 that this category is monoidal closed via the smash product.

 Contents
 1. Structures of pointed posets
 2. The cartesian structure of pointed posets
 3. Limits of pointed posets
 4. Pointed posets form a pointed structure
 5. The smash product of pointed posets

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.

Local Open Scope cat.

(**
 1. Structures of pointed posets
 *)
Definition struct_pointed_poset_strict_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, pointed_PartialOrder X).
  - exact (λ X Y PX PY f, is_strict_and_monotone PX PY f).
Defined.

Definition struct_pointed_poset_strict_laws
  : hset_struct_laws struct_pointed_poset_strict_data.
Proof.
  split5.
  - intro X.
    use isaset_total2.
    + apply isaset_PartialOrder.
    + intro PX.
      use isaset_total2.
      * apply setproperty.
      * intro.
        use impred_isaset.
        intro.
        apply isasetaprop.
        apply propproperty.
  - intros X Y PX PY f.
    apply isapropdirprod.
    + apply isaprop_is_monotone.
    + apply setproperty.
  - intros X PX.
    apply idfun_is_strict_and_monotone.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_strict_and_monotone Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_pointed_PartialOrder_strict_and_monotone p q).
Qed.

Definition struct_pointed_poset_strict
  : hset_struct
  := struct_pointed_poset_strict_data ,, struct_pointed_poset_strict_laws.

Definition category_of_pointed_poset_strict
  : category
  := category_of_hset_struct struct_pointed_poset_strict.

(**
 2. The cartesian structure of pointed posets
 *)
Definition cartesian_struct_pointed_poset_strict_data
  : hset_cartesian_struct_data
  := struct_pointed_poset_strict
     ,,
     unit_pointed_PartialOrder
     ,,
     λ X Y PX PY, prod_pointed_PartialOrder PX PY.

Definition cartesian_struct_pointed_poset_strict_laws
  : hset_cartesian_struct_laws cartesian_struct_pointed_poset_strict_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X PX ; cbn in *.
    split.
    + intros x y p.
      exact tt.
    + apply idpath.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr1_is_strict_and_monotone.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr2_is_strict_and_monotone.
  - intros W X Y PW PY PZ f g Pf Pg ; cbn in *.
    exact (prodtofun_is_strict_and_monotone Pf Pg).
Qed.

Definition cartesian_struct_pointed_poset_strict
  : hset_cartesian_struct
  := cartesian_struct_pointed_poset_strict_data
     ,,
     cartesian_struct_pointed_poset_strict_laws.

(**
 3. Limits of pointed posets
 *)
Definition equalizers_struct_pointed_poset_strict
  : hset_equalizer_struct struct_pointed_poset_strict.
Proof.
  simple refine (_ ,, _).
  - intros X Y f g PX PY Pf Pg.
    exact (Equalizer_pointed_PartialOrder Pf Pg).
  - split.
    + abstract
        (intros X Y f g PX PY Pf Pg ; cbn in * ;
         exact (Equalizer_pr1_strict_and_monotone Pf Pg)).
    + abstract
        (intros X Y f g PX PY Pf Pg W PW h Ph q ;
         exact (Equalizer_map_strict_and_monotone Pf Pg PW Ph (eqtohomot q))).
Defined.

Definition type_products_struct_pointed_poset_strict
           (I : UU)
  : hset_struct_type_prod struct_pointed_poset_strict I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D fs, depfunction_pointed_poset _ fs).
  - split ; cbn.
    + abstract
        (intros D PD i ;
         apply is_strict_and_monotone_depfunction_pointed_poset_pr).
    + abstract
        (intros D PD W PW fs Hfs ;
         apply is_strict_and_monotone_depfunction_pointed_poset_pair ;
         exact Hfs).
Defined.

(**
 4. Pointed posets form a pointed structure
 *)
Definition pointed_struct_pointed_poset_strict_data
  : pointed_hset_struct_data struct_pointed_poset_strict
  := λ X RX, ⊥_{RX}.

Proposition pointed_struct_pointed_poset_strict_laws
  : pointed_hset_struct_laws
      pointed_struct_pointed_poset_strict_data.
Proof.
  split.
  - intros X Y RX RY.
    apply constant_is_strict_and_monotone.
  - intros X Y f PX PY Pf ; cbn in *.
    apply Pf.
Qed.

Definition pointed_struct_pointed_poset_strict
  : pointed_hset_struct struct_pointed_poset_strict
  := pointed_struct_pointed_poset_strict_data
     ,,
     pointed_struct_pointed_poset_strict_laws.

(**
 5. The smash product of pointed posets
 *)
Proposition pointed_poset_strict_smash_eqrel_equiv
            {X Y : hSet}
            (PX : pointed_PartialOrder X)
            (PY : pointed_PartialOrder Y)
            (xy₁ xy₂ : X × Y)
  : smash_eqrel
      cartesian_struct_pointed_poset_strict
      pointed_struct_pointed_poset_strict
      PX PY
      xy₁ xy₂
    <->
    @downward_closed_to_eqrel (X × Y)%set (smash_set PX PY) xy₁ xy₂.
Proof.
  induction xy₁ as [ x₁ y₁ ].
  induction xy₂ as [ x₂ y₂ ].
  split.
  - use factor_through_squash.
    {
      apply propproperty.
    }
    intro p.
    unfold product_point_coordinate in p.
    cbn in p.
    unfold pointed_struct_pointed_poset_strict_data in p.
    apply hinhpr.
    induction p as [ p | p ].
    + exact (inl p).
    + apply inr.
      split.
      * exact (hinhpr (pr1 p)).
      * exact (hinhpr (pr2 p)).
  - use factor_through_squash.
    {
      apply propproperty.
    }
    intro p.
    unfold smash_set in p ; cbn in p.
    induction p as [ p | p ].
    + exact (hinhpr (inl p)).
    + assert (p₁ := pr1 p).
      revert p₁.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p₁.
      assert (p₂ := pr2 p).
      revert p₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p₂.
      apply hinhpr.
      apply inr.
      unfold product_point_coordinate ; cbn.
      unfold pointed_struct_pointed_poset_strict_data.
      split.
      * exact p₁.
      * exact p₂.
Qed.

Definition struct_pointed_poset_strict_with_smash_data
  : hset_struct_with_smash_data
      cartesian_struct_pointed_poset_strict
      pointed_struct_pointed_poset_strict.
Proof.
  refine (_ ,, _).
  - exact pointed_PartialOrder_boolset.
  - intros X Y PX PY.
    use (pointed_quotient_poset
           (prod_pointed_PartialOrder PX PY)
           (smash_set PX PY)
           (smash_set_downward_closd PX PY)).
    exact (pointed_poset_strict_smash_eqrel_equiv PX PY).
Defined.

Proposition struct_pointed_poset_strict_with_smash_laws
  : hset_struct_with_smash_laws
      struct_pointed_poset_strict_with_smash_data.
Proof.
  repeat split.
  - intros b₁ b₂ p ; cbn in p.
    induction b₁, b₂.
    + apply refl_PartialOrder.
    + induction p.
    + apply pointed_PartialOrder_min_point.
    + apply refl_PartialOrder.
  - intros x y p .
    unfold pointed_hset_struct_unit_map ; cbn.
    unfold pointed_struct_pointed_poset_strict_data.
    assert (q := pr1 Pf x y p) ; cbn in q.
    induction (f x), (f y).
    + apply Pg.
      exact p.
    + induction q.
    + apply (pr2 PY).
    + apply (pr2 PY).
  - unfold pointed_hset_struct_unit_map.
    cbn.
    unfold pointed_struct_pointed_poset_strict_data.
    induction (f ⊥_{PX}).
    + apply Pg.
    + apply idpath.
  - intros x₁ x₂ p ; cbn.
    apply hinhpr.
    use inr.
    refine (p ,, _).
    apply refl_PartialOrder.
  - use iscompsetquotpr ; cbn.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_poset_strict_data.
    split.
    + exact (inl (idpath _)).
    + exact (inl (idpath _)).
  - intros y₁ y₂ p ; cbn.
    apply hinhpr.
    use inr.
    exact (refl_PartialOrder (pr1 PX) x ,, p).
  - use iscompsetquotpr ; cbn.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_poset_strict_data.
    split.
    + exact (inr (idpath _)).
    + exact (inr (idpath _)).
  - intros xy₁ xy₂ p ; cbn.
    apply hinhpr.
    use inr.
    exact p.
  - use setquotunivprop'.
    {
      intro.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros xy₁.
    use setquotunivprop'.
    {
      intro.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros xy₂.
    induction xy₁ as [ x₁ y₁ ].
    induction xy₂ as [ x₂ y₂ ] ; cbn.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro p.
    induction p as [ p | p].
    + revert p.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro p.
      induction p as [ p | p ] ; rewrite p.
      * assert (h ⊥_{PX} y₁ = ⊥_{PZ}) as q.
        {
          refine (!(hp₂ (⊥_{PX}) y₁) @ _).
          apply (pr2 Ph).
        }
        rewrite q.
        apply (pr2 PZ).
      * assert (h x₁ ⊥_{PY} = ⊥_{PZ}) as q.
        {
          refine (hp₂ x₁ (⊥_{PY}) @ _).
          apply (pr2 Ph).
        }
        rewrite q.
        apply (pr2 PZ).
    + exact (pr1 Ph (x₁ ,, y₁) (x₂ ,, y₂) p).
  - apply (pr2 Ph).
Qed.

Definition struct_pointed_poset_strict_with_smash
  : hset_struct_with_smash
      cartesian_struct_pointed_poset_strict
      pointed_struct_pointed_poset_strict
  := struct_pointed_poset_strict_with_smash_data
     ,,
     struct_pointed_poset_strict_with_smash_laws.

Definition struct_pointed_poset_strict_with_smash_closed_pointed_data
  : hset_struct_with_smash_closed_data
      struct_pointed_poset_strict_with_smash
  := λ X Y PX PY, strict_and_monotone_pointed_PartialOrder PX PY.

Proposition struct_pointed_poset_strict_with_smash_closed_pointed_laws
  : hset_struct_with_smash_closed_pointed_laws
      struct_pointed_poset_strict_with_smash_closed_pointed_data.
Proof.
  intros X Y PX PY x.
  apply idpath.
Qed.

Definition struct_pointed_poset_strict_with_smash_closed_pointed
  : hset_struct_with_smash_closed_pointed
      struct_pointed_poset_strict_with_smash
  := struct_pointed_poset_strict_with_smash_closed_pointed_data
     ,,
     struct_pointed_poset_strict_with_smash_closed_pointed_laws.

Proposition struct_pointed_poset_strict_with_smash_adj_laws
  : hset_struct_with_smash_closed_adj_laws
      struct_pointed_poset_strict_with_smash_closed_pointed.
Proof.
  split.
  - intros PX PY PZ f.
    induction PX as [ X RX ].
    induction PY as [ Y RY ].
    induction PZ as [ Z RZ ].
    induction f as [ f Hf ].
    split.
    + use setquotunivprop'.
      {
        intro.
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros xy₁.
      use setquotunivprop'.
      {
        intro.
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros xy₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      cbn in *.
      induction xy₁ as [ x₁ y₁ ], xy₂ as [ x₂ y₂ ].
      intro p.
      induction p as [ p | p ].
      * revert p.
        use factor_through_squash.
        {
          apply propproperty.
        }
        cbn.
        intro p.
        induction p as [ p | p ].
        ** assert (pr1 (f x₁) y₁ = ⊥_{RZ}) as r.
           {
             rewrite p.
             exact (eqtohomot (maponpaths pr1 (pr2 Hf)) y₁).
           }
           rewrite r.
           apply (pr2 RZ).
        ** assert (pr1 (f x₁) y₁ = ⊥_{RZ}) as r.
           {
             rewrite p.
             apply (pr2 (f x₁)).
           }
           rewrite r.
           apply (pr2 RZ).
      * cbn ; cbn in p.
        refine (trans_PartialOrder RZ _ _).
        ** exact (pr12 (f x₁) _ _ (pr2 p)).
        ** exact (pr1 Hf _ _ (pr1 p) y₂).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        exact (pr2 Hf).
      }
      apply idpath.
  - intros PX PY PZ f.
    induction PX as [ X RX ].
    induction PY as [ Y RY ].
    induction PZ as [ Z RZ ].
    induction f as [ f Hf ].
    split.
    + intros x₁ x₂ p y.
      apply (pr1 Hf).
      cbn in *.
      apply hinhpr.
      use inr.
      refine (p ,, _).
      apply refl_PartialOrder.
    + use eq_strict_and_monotone_function.
      intro y.
      cbn.
      refine (_ @ pr2 Hf).
      apply maponpaths.
      use iscompsetquotpr.
      apply hinhpr.
      use inr.
      unfold product_point_coordinate ; cbn.
      unfold pointed_struct_pointed_poset_strict_data.
      split.
      * exact (inl (idpath _)).
      * exact (inl (idpath _)).
Qed.

Definition struct_pointed_poset_strict_with_smash_adj
  : hset_struct_with_smash_closed_adj
      struct_pointed_poset_strict_with_smash
  := struct_pointed_poset_strict_with_smash_closed_pointed
     ,,
     struct_pointed_poset_strict_with_smash_adj_laws.

Proposition struct_pointed_poset_strict_with_smash_laws_enrich
  : hset_struct_with_smash_closed_laws_enrich
      struct_pointed_poset_strict_with_smash_adj.
Proof.
  split.
  - intros PX PY PZ.
    induction PX as [ X RX ].
    induction PY as [ Y RY ].
    induction PZ as [ Z RZ ].
    split.
    + intros f₁ f₂ p.
      use setquotunivprop'.
      {
        intro.
        apply propproperty.
      }
      intros xz.
      induction xz as [ x z ].
      cbn in *.
      apply p.
    + use eq_strict_and_monotone_function.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro x ; cbn in *.
      apply idpath.
  - intros PX PY PZ.
    induction PX as [ X RX ].
    induction PY as [ Y RY ].
    induction PZ as [ Z RZ ].
    split.
    + intros f₁ f₂ p x y.
      cbn in *.
      apply p.
    + use eq_strict_and_monotone_function.
      intro x.
      use eq_strict_and_monotone_function.
      intro z.
      cbn.
      apply idpath.
Qed.

Definition pointed_struct_pointed_poset_strict_with_smash_closed
  : hset_struct_with_smash_closed
  := cartesian_struct_pointed_poset_strict
     ,,
     pointed_struct_pointed_poset_strict
     ,,
     struct_pointed_poset_strict_with_smash
     ,,
     struct_pointed_poset_strict_with_smash_adj
     ,,
     struct_pointed_poset_strict_with_smash_laws_enrich.
