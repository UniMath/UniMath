(*****************************************************************

 Examples of structures

 In this file, we construct several classes of structured sets,
 and we prove some properties about them.

 Contents
 1. Sets
 2. Pointed sets
 3. Posets
 4. Pointed posets with strict functions
 5. Pointed posets with monotone functions
 6. Algebras on a monad

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

(**
 1. Sets
 *)
Definition struct_plain_hset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, unit).
  - exact (λ X Y x y f, unit).
Defined.

Definition struct_plain_hset_laws
  : hset_struct_laws struct_plain_hset_data.
Proof.
  repeat split.
  - intro X.
    apply isasetunit.
  - intros X Y px py f.
    apply isapropunit.
  - intros X px py f g.
    apply isapropunit.
Qed.

Definition struct_plain_hset
  : hset_struct
  := struct_plain_hset_data ,, struct_plain_hset_laws.

Definition cartesian_struct_plain_hset_data
  : hset_cartesian_struct_data
  := struct_plain_hset ,, tt ,, λ _ _ _ _, tt.

Definition cartesian_struct_plain_hset_laws
  : hset_cartesian_struct_laws cartesian_struct_plain_hset_data.
Proof.
  repeat split.
Qed.

Definition cartesian_struct_plain_hset
  : hset_cartesian_struct
  := cartesian_struct_plain_hset_data ,, cartesian_struct_plain_hset_laws.

Definition cartesian_closed_struct_plain_hset_data
  : hset_cartesian_closed_struct_data.
Proof.
  simple refine (cartesian_struct_plain_hset ,, _ ,, _).
  - exact (λ _ _ _ _ _, tt).
  - exact (λ _ _ _ _, tt).
Defined.

Definition cartesian_closed_struct_plain_hset_laws
  : closed_under_fun_laws cartesian_closed_struct_plain_hset_data.
Proof.
  repeat split.
Qed.

Definition cartesian_closed_struct_plain_hset
  : hset_cartesian_closed_struct
  := cartesian_closed_struct_plain_hset_data
     ,,
     cartesian_closed_struct_plain_hset_laws.

Definition equalizers_struct_plain_hset
  : hset_equalizer_struct struct_plain_hset.
Proof.
  refine ((λ _ _ _ _ _ _ _ _, tt) ,, _).
  abstract (repeat split).
Defined.

Definition coequalizers_struct_plain_hset
  : hset_coequalizer_struct struct_plain_hset.
Proof.
  refine ((λ _ _ _ _ _ _ _ _, tt) ,, _).
  abstract (repeat split).
Defined.

Definition type_products_struct_plain_hset
           (I : UU)
  : hset_struct_type_prod struct_plain_hset I.
Proof.
  simple refine ((λ _ _, tt) ,, _).
  abstract (repeat split).
Defined.

(**
 2. Pointed sets
 *)
Definition struct_pointed_hset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, X).
  - exact (λ X Y x y f, f x = y).
Defined.

Definition struct_pointed_hset_laws
  : hset_struct_laws struct_pointed_hset_data.
Proof.
  repeat split.
  - intro X.
    apply setproperty.
  - intros X Y px py f.
    apply setproperty.
  - intros X Y Z px py pz f g p q ; cbn in *.
    rewrite p, q.
    apply idpath.
  - intros X px px' p q ; cbn in *.
    exact p.
Qed.

Definition struct_pointed_hset
  : hset_struct
  := struct_pointed_hset_data ,, struct_pointed_hset_laws.

Definition cartesian_struct_pointed_hset_data
  : hset_cartesian_struct_data
  := struct_pointed_hset ,, tt ,, λ X Y x y, x ,, y.

Definition cartesian_struct_pointed_hset_laws
  : hset_cartesian_struct_laws cartesian_struct_pointed_hset_data.
Proof.
  repeat split.
  intros W X Y pw px py f g p q ; cbn in *.
  unfold prodtofuntoprod ; cbn.
  rewrite p, q.
  apply idpath.
Qed.

Definition cartesian_struct_pointed_hset
  : hset_cartesian_struct
  := cartesian_struct_pointed_hset_data ,, cartesian_struct_pointed_hset_laws.

Definition equalizers_struct_pointed_hset
  : hset_equalizer_struct struct_pointed_hset.
Proof.
  simple refine (_ ,, _).
  - refine (λ X Y f g px py p q, px ,, _).
    abstract (exact (p @ !q)).
  - abstract
      (repeat split ; cbn ;
       intros X Y f g px py p q W pw h r s ;
       use subtypePath ; [ intro ; apply setproperty | ] ;
       exact r).
Defined.

Definition coequalizers_struct_pointed_hset
  : hset_coequalizer_struct struct_pointed_hset.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y f g px py p q, setquotpr _ py).
  - abstract
      (repeat split ; cbn ;
       intros X Y f g px py p q W pw h r s ;
       exact r).
Defined.

Definition type_products_struct_pointed_hset
           (I : UU)
  : hset_struct_type_prod struct_pointed_hset I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D fs, fs).
  - abstract
      (repeat split ; cbn ;
       intros D PD W pw fs pq ;
       use funextsec ;
       exact pq).
Defined.

Definition pointed_struct_pointed_hset_data
  : pointed_hset_struct_data struct_pointed_hset
  := λ X x, x.

Proposition pointed_struct_pointed_hset_laws
  : pointed_hset_struct_laws pointed_struct_pointed_hset_data.
Proof.
  split.
  - intros X Y PX PY ; cbn.
    apply idpath.
  - intros X Y f PX PY Pf ; cbn in *.
    exact Pf.
Qed.

Definition pointed_struct_pointed_hset
  : pointed_hset_struct struct_pointed_hset
  := pointed_struct_pointed_hset_data ,, pointed_struct_pointed_hset_laws.

Definition pointed_struct_pointed_hset_with_smash_data
  : hset_struct_with_smash_data
      cartesian_struct_pointed_hset
      pointed_struct_pointed_hset.
Proof.
  split.
  - exact false.
  - exact (λ X Y x y, setquotpr _ (x ,, y)).
Defined.

Proposition pointed_struct_pointed_hset_with_smash_laws
  : hset_struct_with_smash_laws
      pointed_struct_pointed_hset_with_smash_data.
Proof.
  repeat split.
  - intros X Y x y f pf g pg.
    cbn in *.
    unfold pointed_hset_struct_unit_map.
    rewrite pf.
    apply idpath.
  - intro y.
    use iscompsetquotpr.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split.
    + exact (inl (idpath _)).
    + exact (inl (idpath _)).
  - intro x.
    use iscompsetquotpr.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split.
    + exact (inr (idpath _)).
    + exact (inr (idpath _)).
  - intros Z z h Ph hp₁ hp₂ hp₃ ; cbn in *.
    exact Ph.
Qed.

Definition pointed_struct_pointed_hset_with_smash
  : hset_struct_with_smash
      cartesian_struct_pointed_hset
      pointed_struct_pointed_hset.
Proof.
  use make_hset_struct_with_smash.
  - exact pointed_struct_pointed_hset_with_smash_data.
  - exact pointed_struct_pointed_hset_with_smash_laws.
Defined.

Definition pointed_struct_pointed_hset_with_smash_closed_pointed
  : hset_struct_with_smash_closed_pointed
      pointed_struct_pointed_hset_with_smash.
Proof.
  refine ((λ X Y x y, (λ _, y) ,, idpath _) ,, _).
  intro ; intros.
  apply idpath.
Defined.

Proposition pointed_struct_pointed_hset_with_smash_adj_laws
  : hset_struct_with_smash_closed_adj_laws
      pointed_struct_pointed_hset_with_smash_closed_pointed.
Proof.
  split.
  - intros X Y Z f.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    induction f as [ f p ].
    cbn in *.
    exact (eqtohomot (maponpaths pr1 p) y).
  - intros X Y Z f.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    induction f as [ f p ].
    use subtypePath.
    {
      intro.
      apply setproperty.
    }
    use funextsec.
    intro a.
    refine (_ @ p).
    refine (maponpaths f _).
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split ; use inl ; apply idpath.
Qed.

Definition pointed_struct_pointed_hset_with_smash_adj
  : hset_struct_with_smash_closed_adj
      pointed_struct_pointed_hset_with_smash
  := pointed_struct_pointed_hset_with_smash_closed_pointed
     ,,
     pointed_struct_pointed_hset_with_smash_adj_laws.

Proposition pointed_struct_pointed_hset_with_smash_laws_enrich
  : hset_struct_with_smash_closed_laws_enrich
      pointed_struct_pointed_hset_with_smash_adj.
Proof.
  split.
  - intros X Y Z.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    use setquotunivprop'.
    {
      intro ; apply setproperty.
    }
    intro xz.
    cbn in *.
    apply idpath.
  - intros X Y Z.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    intro a.
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    intro b.
    cbn in *.
    apply idpath.
Qed.

Definition pointed_struct_pointed_hset_with_smash_closed
  : hset_struct_with_smash_closed
  := cartesian_struct_pointed_hset
     ,,
     pointed_struct_pointed_hset
     ,,
     pointed_struct_pointed_hset_with_smash
     ,,
     pointed_struct_pointed_hset_with_smash_adj
     ,,
     pointed_struct_pointed_hset_with_smash_laws_enrich.

(**
 3. Posets
 *)
Definition struct_poset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, PartialOrder X).
  - exact (λ X Y PX PY f, is_monotone PX PY f).
Defined.

Definition struct_poset_laws
  : hset_struct_laws struct_poset_data.
Proof.
  repeat split.
  - intro X.
    apply isaset_PartialOrder.
  - intros X Y px py f.
    apply isaprop_is_monotone.
  - intros X PX ; cbn in *.
    apply idfun_is_monotone.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_monotone Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_PartialOrder p q).
Qed.

Definition struct_poset
  : hset_struct
  := struct_poset_data ,, struct_poset_laws.

Definition cartesian_struct_poset_data
  : hset_cartesian_struct_data
  := struct_poset
     ,,
     unit_PartialOrder
     ,,
     λ X Y PX PY, prod_PartialOrder PX PY.

Definition cartesian_struct_poset_laws
  : hset_cartesian_struct_laws cartesian_struct_poset_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X PX x y p ; cbn in *.
    exact tt.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr1_is_monotone.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr2_is_monotone.
  - intros W X Y PW PY PZ f g Pf Pg ; cbn in *.
    exact (prodtofun_is_monotone Pf Pg).
Qed.

Definition cartesian_struct_poset
  : hset_cartesian_struct
  := cartesian_struct_poset_data ,, cartesian_struct_poset_laws.

Definition equalizers_struct_poset
  : hset_equalizer_struct struct_poset.
Proof.
  simple refine (_ ,, _).
  - intros X Y f g PX PY Pf Pg.
    exact (Equalizer_order PX _ f g).
  - repeat split.
    + abstract
        (intros X Y f g PX PY Pf Pg ; cbn in * ;
         exact (Equalizer_pr1_monotone PX Y f g)).
    + abstract
        (intros X Y f g PX PY Pf Pg W PW h Ph q ;
         exact (Equalizer_map_monotone PX Y f g PW Ph (eqtohomot q))).
Defined.

Definition type_products_struct_poset
           (I : UU)
  : hset_struct_type_prod struct_poset I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D fs, depfunction_poset _ fs).
  - repeat split ; cbn.
    + abstract
        (intros D PD i ;
         apply is_monotone_depfunction_poset_pr).
    + abstract
        (intros D PD W PW fs Hfs i ;
         apply is_monotone_depfunction_poset_pair ;
         exact Hfs).
Defined.

(**
 4. Pointed posets with strict functions
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

(**
 5. Pointed posets with monotone functions
 *)
Definition struct_pointed_poset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, pointed_PartialOrder X).
  - exact (λ X Y PX PY f, is_monotone PX PY f).
Defined.

Definition struct_pointed_poset_laws
  : hset_struct_laws struct_pointed_poset_data.
Proof.
  split5.
  - intro X.
    use isaset_total2.
    + apply isaset_PartialOrder.
    + intro PX.
      apply isasetaprop.
      apply isaprop_bottom_element.
  - intros X Y PX PY f.
    apply isaprop_is_monotone.
  - intros X PX.
    apply idfun_is_monotone.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_monotone Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_pointed_PartialOrder_monotone p q).
Qed.

Definition struct_pointed_poset
  : hset_struct
  := struct_pointed_poset_data ,, struct_pointed_poset_laws.

Definition cartesian_struct_pointed_poset_data
  : hset_cartesian_struct_data
  := struct_pointed_poset
     ,,
     unit_pointed_PartialOrder
     ,,
     λ X Y PX PY, prod_pointed_PartialOrder PX PY.

Definition cartesian_struct_pointed_poset_laws
  : hset_cartesian_struct_laws cartesian_struct_pointed_poset_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X PX ; cbn in *.
    intros x y p.
    exact tt.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr1_is_monotone.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr2_is_monotone.
  - intros W X Y PW PY PZ f g Pf Pg ; cbn in *.
    exact (prodtofun_is_monotone Pf Pg).
Qed.

Definition cartesian_struct_pointed_poset
  : hset_cartesian_struct
  := cartesian_struct_pointed_poset_data
     ,,
     cartesian_struct_pointed_poset_laws.

(**
 6. Algebras on a monad
 *)
Section MonadToStruct.
  Context (M : Monad SET).

  Definition Monad_algebra_laws
             {X : SET}
             (f : M X --> X)
    : UU
    := (η M X · f = identity X)
       ×
       (μ M X · f = #M f · f).

  Definition Monad_algebra
             (X : SET)
    : UU
    := ∑ (f : M X --> X), Monad_algebra_laws f.

  Definition make_Monad_algebra
             {X : SET}
             (f : M X --> X)
             (p : Monad_algebra_laws f)
    : Monad_algebra X
    := f ,, p.

  Coercion Monad_algebra_struct_to_mor
           {X : hSet}
           (f : Monad_algebra X)
    : M X --> X
    := pr1 f.

  Proposition Monad_algebra_unit
              {X : hSet}
              (f : Monad_algebra X)
    : η M X · f = identity _.
  Proof.
    exact (pr12 f).
  Qed.

  Proposition Monad_algebra_mu
              {X : hSet}
              (f : Monad_algebra X)
    : μ M X · f = #M f · f.
  Proof.
    exact (pr22 f).
  Qed.

  Definition Monad_to_hset_struct_data
    : hset_struct_data.
  Proof.
    simple refine (_ ,, _).
    - exact Monad_algebra.
    - exact (λ X Y f g h, f · h = #M h · g).
  Defined.

  Proposition Monad_to_hset_struct_laws
    : hset_struct_laws Monad_to_hset_struct_data.
  Proof.
    repeat split.
    - intro X.
      use isaset_total2.
      + apply homset_property.
      + intro f.
        apply isasetaprop.
        apply isapropdirprod ; apply homset_property.
    - intros X Y f g h.
      apply homset_property.
    - intros X f ; cbn.
      rewrite (functor_id M).
      apply idpath.
    - intros X Y Z fX fY fZ h₁ h₂ Mh₁ Mh₂ ; cbn in *.
      use funextsec.
      intro x.
      rewrite (eqtohomot Mh₁).
      rewrite (eqtohomot Mh₂).
      rewrite (eqtohomot (functor_comp M h₁ h₂)).
      apply idpath.
    - intros X fX fX' p q.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      cbn in *.
      use funextsec.
      intro x.
      refine (eqtohomot p x @ _).
      apply maponpaths.
      exact (eqtohomot (functor_id M X) x).
  Qed.

  Definition Monad_to_hset_struct
    : hset_struct
    := Monad_to_hset_struct_data ,, Monad_to_hset_struct_laws.

  Proposition unit_Monad_algebra_laws
    : @Monad_algebra_laws unitHSET (λ _, tt).
  Proof.
    split.
    - cbn.
      use funextsec.
      intro x.
      apply isapropunit.
    - apply idpath.
  Qed.

  Definition unit_Monad_algebra
    : Monad_algebra unitHSET.
  Proof.
    use make_Monad_algebra.
    - exact (λ _, tt).
    - exact unit_Monad_algebra_laws.
  Defined.

  Section ProdAlgebra.
    Context {X Y : SET}
            (f : Monad_algebra X)
            (g : Monad_algebra Y).

    Let XY : SET := (X × Y)%set.
    Let π₁ : XY --> X := dirprod_pr1.
    Let π₂ : XY --> Y := dirprod_pr2.

    Definition prod_Monad_algebra_map
      : M XY --> XY
      := BinProductArrow _ (BinProductsHSET X Y) (#M π₁ · f) (#M π₂ · g).

    Proposition prod_Monad_algebra_laws
      : Monad_algebra_laws prod_Monad_algebra_map.
    Proof.
      split.
      - use (BinProductArrowsEq _ _ _ (BinProductsHSET X Y)).
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite id_left.
          rewrite <- (nat_trans_ax (η M) _ _ π₁).
          rewrite !assoc'.
          rewrite (Monad_algebra_unit f).
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite id_left.
          rewrite <- (nat_trans_ax (η M) _ _ π₂).
          rewrite !assoc'.
          rewrite (Monad_algebra_unit g).
          apply idpath.
      - use (BinProductArrowsEq _ _ _ (BinProductsHSET X Y)).
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite <- (nat_trans_ax (μ M) _ _ π₁).
          rewrite functor_comp.
          rewrite !assoc'.
          rewrite (Monad_algebra_mu f).
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite <- (nat_trans_ax (μ M) _ _ π₂).
          rewrite functor_comp.
          rewrite !assoc'.
          rewrite (Monad_algebra_mu g).
          apply idpath.
    Qed.

    Definition prod_Monad_algebra
      : Monad_algebra XY.
    Proof.
      use make_Monad_algebra.
      - exact prod_Monad_algebra_map.
      - exact prod_Monad_algebra_laws.
    Defined.
  End ProdAlgebra.

  Definition Monad_to_hset_cartesian_struct_data
    : hset_cartesian_struct_data
    := Monad_to_hset_struct ,, unit_Monad_algebra ,, λ X Y f g, prod_Monad_algebra f g.

  Proposition Monad_to_hset_cartesian_struct_laws
    : hset_cartesian_struct_laws Monad_to_hset_cartesian_struct_data.
  Proof.
    split4.
    - intros X f ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros W X Y fW fX fY g₁ g₂ Mg₁ Mg₂ ; cbn in *.
      use funextsec.
      intro x.
      use pathsdirprod ; cbn.
      + refine (eqtohomot Mg₁ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (eqtohomot (functor_comp M _ _)).
        }
        apply idpath.
      + refine (eqtohomot Mg₂ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (eqtohomot (functor_comp M _ _)).
        }
        apply idpath.
  Qed.

  Definition Monad_to_hset_cartesian_struct
    : hset_cartesian_struct
    := Monad_to_hset_cartesian_struct_data
       ,,
       Monad_to_hset_cartesian_struct_laws.

  Section EqualizerAlgebra.
    Context {X Y : SET}
            {f g : X --> Y}
            (hX : Monad_algebra X)
            (hY : Monad_algebra Y)
            (Mf : hX · f = #M f · hY)
            (Mg : hX · g = #M g · hY).

    Let E : SET := (∑ x, hProp_to_hSet (eqset (f x) (g x)))%set.
    Let π : E --> X := λ z, pr1 z.

    Definition eqalizer_algebra_map
      : M E --> E.
    Proof.
      use (EqualizerIn (Equalizers_in_HSET X Y f g)).
      - exact (#M π · hX).
      - abstract
          (rewrite !assoc' ;
           rewrite Mf, Mg ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           rewrite <- !functor_comp ;
           apply maponpaths ;
           apply (EqualizerEqAr (Equalizers_in_HSET X Y f g))).
    Defined.

    Proposition eqalizer_algebra_laws
      : Monad_algebra_laws eqalizer_algebra_map.
    Proof.
      split.
      - use (EqualizerInsEq (Equalizers_in_HSET X Y f g)).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite !id_left.
        rewrite !assoc.
        rewrite <- (nat_trans_ax (η M) _ _ π).
        rewrite !assoc'.
        rewrite Monad_algebra_unit.
        rewrite id_right.
        apply idpath.
      - use (EqualizerInsEq (Equalizers_in_HSET X Y f g)).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite <- (nat_trans_ax (μ M) _ _ π).
        rewrite functor_comp.
        rewrite !assoc'.
        rewrite (Monad_algebra_mu hX).
        apply idpath.
    Qed.

    Definition equalizer_algebra
      : Monad_algebra E.
    Proof.
      use make_Monad_algebra.
      - exact eqalizer_algebra_map.
      - exact eqalizer_algebra_laws.
    Defined.
  End EqualizerAlgebra.

  Definition Monad_to_hset_equalizer_struct_data
    : hset_equalizer_struct_data Monad_to_hset_struct
    := λ X Y f g hX hY Mf Mg, equalizer_algebra hX hY Mf Mg.

  Proposition Monad_to_hset_equalizer_struct_laws
    : hset_equalizer_struct_laws Monad_to_hset_equalizer_struct_data.
  Proof.
    split.
    - intros X Y f g hX hY Mf Mg.
      apply idpath.
    - intros X Y f g hX hY Mf Mg W hW k Mk q.
      use funextsec.
      intro x.
      use subtypePath.
      {
        intro.
        apply setproperty.
      }
      cbn in *.
      refine (eqtohomot Mk x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition Monad_to_hset_equalizer_struct
    : hset_equalizer_struct Monad_to_hset_struct
    := Monad_to_hset_equalizer_struct_data
       ,,
       Monad_to_hset_equalizer_struct_laws.

  Section TypeProdAlgebra.
    Context {J : UU}
            {D : J → hSet}
            (p : ∏ (i : J), Monad_algebra (D i)).

    Let prod : Product J SET D := ProductsHSET J D.

    Definition Monad_type_prod_map
      : M prod --> prod
      := ProductArrow _ _ prod (λ i, #M (ProductPr _ _ _ i) · p i).

    Proposition Monad_type_prod_laws
      : Monad_algebra_laws Monad_type_prod_map.
    Proof.
      split.
      - use (ProductArrow_eq _ _ _ prod).
        intro i.
        rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite !assoc.
        rewrite <- (nat_trans_ax (η M)).
        rewrite !assoc'.
        rewrite (Monad_algebra_unit (p i)).
        rewrite id_right.
        apply idpath.
      - use (ProductArrow_eq _ _ _ prod).
        intro i.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite <- (nat_trans_ax (μ M)).
        rewrite functor_comp.
        rewrite !assoc'.
        rewrite (Monad_algebra_mu (p i)).
        apply idpath.
    Qed.
  End TypeProdAlgebra.

  Definition Monad_to_hset_struct_type_prod_data
             (J : UU)
    : hset_struct_type_prod_data Monad_to_hset_struct J.
  Proof.
    intros D p.
    use make_Monad_algebra.
    - exact (Monad_type_prod_map p).
    - exact (Monad_type_prod_laws p).
  Defined.

  Proposition Monad_to_hset_struct_type_prod_laws
              (J : UU)
    : hset_struct_type_prod_laws (Monad_to_hset_struct_type_prod_data J).
  Proof.
    split.
    - intros D PD i.
      apply idpath.
    - intros D PD W hW ps Mps.
      cbn in *.
      use funextsec ; intro x.
      use funextsec ; intro i.
      refine (eqtohomot (Mps i) x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition Monad_to_hset_struct_type_prod
             (J : UU)
    : hset_struct_type_prod Monad_to_hset_struct J
    := Monad_to_hset_struct_type_prod_data J
       ,,
       Monad_to_hset_struct_type_prod_laws J.
End MonadToStruct.
