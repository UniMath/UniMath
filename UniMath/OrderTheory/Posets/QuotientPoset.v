(*****************************************************************

 Quotients of posets

 If we have a poset and a downward closed set in that poset, then
 we can collapse that subset (i.e., identify all its elements) and
 acquire a new poset.

 Contents
 1. Downward closed sets
 2. The quotient of posets
 3. Lower set for smash product
 4. Quotients of posets

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.

(**
 1. Downward closed sets
 *)
Definition downward_closed
           {X : hSet}
           (RX : PartialOrder X)
           (I : X → hProp)
  : UU
  := ∏ (x₁ x₂ : X), RX x₁ x₂ → I x₂ → I x₁.

(**
 2. The quotient of posets
 *)
Section PosetQuotientLowerSet.
  Context {X : hSet}
          (RX : PartialOrder X)
          (I : X → hProp)
          (I_down : downward_closed RX I).

  Definition downward_closed_to_hrel
    : hrel X
    := λ x₁ x₂, eqset x₁ x₂ ∨ I x₁ ∧ I x₂.

  Proposition iseqrel_downward_closed_to_hrel
    : iseqrel downward_closed_to_hrel.
  Proof.
    refine ((_ ,, _) ,, _).
    - intros x₁ x₂ x₃.
      use factor_through_squash.
      {
        use impred ; intro.
        apply propproperty.
      }
      intros p₁.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p₂.
      apply hinhpr.
      induction p₁ as [ p₁ | p₁ ] ; induction p₂ as [ p₂ | p₂ ] ; cbn in *.
      + exact (inl (p₁ @ p₂)).
      + induction p₁.
        exact (inr p₂).
      + induction p₂.
        exact (inr p₁).
      + exact (inr (pr1 p₁ ,, pr2 p₂)).
    - intros x ; cbn in *.
      exact (hinhpr (inl (idpath x))).
    - intros x₁ x₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p.
      apply hinhpr.
      induction p as [ p | p ] ; cbn in *.
      + exact (inl (!p)).
      + exact (inr (pr2 p ,, pr1 p)).
  Qed.

  Definition downward_closed_to_eqrel
    : eqrel X.
  Proof.
    use make_eqrel.
    - exact downward_closed_to_hrel.
    - exact iseqrel_downward_closed_to_hrel.
  Defined.

  Local Definition quotient_lower_set_order_on_el
    : hrel X
    := λ x₁ x₂, I x₁ ∨ RX x₁ x₂.

  Proposition quotient_lower_set_order_on_el_comprel
    : iscomprelrel downward_closed_to_eqrel quotient_lower_set_order_on_el.
  Proof.
    intros x₁ x₂ y₁ y₂.
    use factor_through_squash.
    {
      use impred ; intro.
      apply hProp_set.
    }
    intros p₁.
    use factor_through_squash.
    {
      apply hProp_set.
    }
    intros p₂.
    induction p₁ as [ p₁ | p₁ ] ;
      induction p₂ as [ p₂ | p₂ ] ;
      use hPropUnivalence ;
      (use factor_through_squash ; [ apply propproperty | ]) ;
      cbn in * ;
      intro q ;
      apply hinhpr.
    - induction p₁, p₂.
      exact q.
    - induction p₁, p₂.
      exact q.
    - induction p₁.
      destruct q as [ q | q ].
      + exact (inl q).
      + refine (inl _).
        exact (I_down x₁ y₁ q (pr1 p₂)).
    - induction p₁.
      induction q as [ q | q ].
      + exact (inl q).
      + refine (inl _).
        exact (I_down x₁ y₂ q (pr2 p₂)).
    - exact (inl (pr2 p₁)).
    - exact (inl (pr1 p₁)).
    - exact (inl (pr2 p₁)).
    - exact (inl (pr1 p₁)).
  Qed.

  Definition quotient_lower_set_order
    : hrel (setquotinset downward_closed_to_eqrel).
  Proof.
    use quotrel.
    - exact quotient_lower_set_order_on_el.
    - exact quotient_lower_set_order_on_el_comprel.
  Defined.

  Proposition istrans_quotient_lower_set_order
    : istrans quotient_lower_set_order.
  Proof.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₁.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₂.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₃.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply propproperty.
    }
    intro p₁.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply propproperty.
    }
    intro p₂.
    cbn in *.
    apply hinhpr.
    induction p₁ as [ p₁ | p₁ ].
    - exact (inl p₁).
    - induction p₂ as [ p₂ | p₂ ].
      + apply inl.
        exact (I_down x₁ x₂ p₁ p₂).
      + apply inr.
        exact (trans_PartialOrder RX p₁ p₂).
  Qed.

  Proposition isrefl_quotient_lower_set_order
    : isrefl quotient_lower_set_order.
  Proof.
    use setquotunivprop.
    intro x ; cbn in *.
    apply hinhpr.
    exact (inr (refl_PartialOrder RX x)).
  Qed.

  Proposition isantisymm_quotient_lower_set_order
    : isantisymm quotient_lower_set_order.
  Proof.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intros x₁.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intros x₂.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply setproperty.
    }
    intro p₁.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intro p₂.
    use iscompsetquotpr ; cbn in *.
    apply hinhpr.
    induction p₁ as [ p₁ | p₁ ] ; induction p₂ as [ p₂ | p₂ ].
    - exact (inr (p₁ ,, p₂)).
    - refine (inr (p₁ ,, _)).
      exact (I_down x₂ x₁ p₂ p₁).
    - refine (inr (_ ,, _)).
      + exact (I_down x₁ x₂ p₁ p₂).
      + exact p₂.
    - apply inl.
      exact (antisymm_PartialOrder RX p₁ p₂).
  Qed.

  Definition quotient_lower_set
    : PartialOrder (setquotinset downward_closed_to_eqrel).
  Proof.
    use make_PartialOrder.
    - exact quotient_lower_set_order.
    - refine ((_ ,, _) ,, _).
      + exact istrans_quotient_lower_set_order.
      + exact isrefl_quotient_lower_set_order.
      + exact isantisymm_quotient_lower_set_order.
  Defined.

  Proposition is_monotone_lower_set_setquot_pr
    : is_monotone RX quotient_lower_set (setquotpr _).
  Proof.
    intros x₁ x₂ p.
    apply hinhpr ; cbn.
    exact (inr p).
  Qed.

  Definition quotient_lower_set_bottom
             (pX : bottom_element RX)
    : bottom_element quotient_lower_set.
  Proof.
    simple refine (_ ,, _).
    - exact (setquotpr _ (pr1 pX)).
    - abstract
        (use setquotunivprop' ;
         [ intro ;
           apply propproperty
         | ] ;
         intro y ;
         exact (hinhpr (inr (pr2 pX y)))).
  Defined.
End PosetQuotientLowerSet.

Definition pointed_quotient_lower_set
           {X : hSet}
           (RX : pointed_PartialOrder X)
           (I : X → hProp)
           (I_down : downward_closed RX I)
  : pointed_PartialOrder (setquotinset (downward_closed_to_eqrel I))
  := quotient_lower_set RX I I_down ,, quotient_lower_set_bottom _ _ _ (pr2 RX).

(**
 3. Lower set for smash product
 *)
Section SmashLowerSet.
  Context {X Y : hSet}
          (RX : pointed_PartialOrder X)
          (RY : pointed_PartialOrder Y).

  Definition smash_set
    : X × Y → hProp
    := λ xy, pr1 xy = ⊥_{RX} ∨ pr2 xy = ⊥_{RY}.

  Definition smash_set_downward_closd
    : downward_closed (prod_pointed_PartialOrder RX RY) smash_set.
  Proof.
    intros xy₁ xy₂ p.
    induction xy₁ as [ x₁ y₁ ].
    induction xy₂ as [ x₂ y₂ ].
    induction p as [ p₁ p₂ ].
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro q.
    induction q as [ q | q ] ; cbn in *.
    - apply hinhpr.
      use inl.
      use (antisymm_PartialOrder RX).
      + induction q.
        exact p₁.
      + apply pointed_PartialOrder_min_point.
    - apply hinhpr.
      use inr.
      use (antisymm_PartialOrder RY).
      + induction q.
        exact p₂.
      + apply pointed_PartialOrder_min_point.
  Qed.
End SmashLowerSet.

(**
 4. Quotients of posets
 *)
Section QuotientEquivRel.
  Context {X : hSet}
          (RX : PartialOrder X)
          (I : X → hProp)
          (I_down : downward_closed RX I)
          (eqX : eqrel X)
          (H : ∏ (x₁ x₂ : X), eqX x₁ x₂ <-> downward_closed_to_eqrel I x₁ x₂).

  Definition quotient_poset_hrel_on_el
    : hrel X
    := λ x₁ x₂, I x₁ ∨ RX x₁ x₂.

  Proposition quotient_poset_hrel_comp
    : iscomprelrel eqX quotient_poset_hrel_on_el.
  Proof.
    intros x₁ x₂ y₁ y₂ p q.
    assert (p' := pr1 (H x₁ x₂) p).
    revert p'.
    use factor_through_squash.
    {
      apply hPropset.
    }
    intros p'.
    assert (q' := pr1 (H y₁ y₂) q).
    revert q'.
    use factor_through_squash.
    {
      apply hPropset.
    }
    intros q'.
    induction p' as [ p' | p' ] ;
      induction q' as [ q' | q' ] ;
      use hPropUnivalence ;
      (use factor_through_squash ; [ apply propproperty | ]) ;
      cbn in * ;
      intro r ;
      apply hinhpr.
    - induction p', q'.
      exact r.
    - induction p', q'.
      exact r.
    - induction p'.
      induction r as [ r | r ].
      + exact (inl r).
      + refine (inl _).
        exact (I_down x₁ y₁ r (pr1 q')).
    - induction p'.
      induction r as [ r | r ].
      + exact (inl r).
      + refine (inl _).
        exact (I_down x₁ y₂ r (pr2 q')).
    - exact (inl (pr2 p')).
    - exact (inl (pr1 p')).
    - exact (inl (pr2 p')).
    - exact (inl (pr1 p')).
  Qed.

  Definition quotient_poset_hrel
    : hrel (setquotinset eqX).
  Proof.
    use quotrel.
    - exact quotient_poset_hrel_on_el.
    - exact quotient_poset_hrel_comp.
  Defined.

  Proposition istrans_quotient_poset
    : istrans quotient_poset_hrel.
  Proof.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₁.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₂.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply propproperty.
    }
    intros x₃.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply propproperty.
    }
    intro p₁.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply propproperty.
    }
    intro p₂.
    cbn in *.
    apply hinhpr.
    induction p₁ as [ p₁ | p₁ ].
    - exact (inl p₁).
    - induction p₂ as [ p₂ | p₂ ].
      + apply inl.
        exact (I_down x₁ x₂ p₁ p₂).
      + apply inr.
        exact (trans_PartialOrder RX p₁ p₂).
  Qed.

  Proposition isrefl_quotient_poset
    : isrefl quotient_poset_hrel.
  Proof.
    use setquotunivprop.
    intro x ; cbn in *.
    apply hinhpr.
    exact (inr (refl_PartialOrder RX x)).
  Qed.

  Proposition isantisymm_quotient_poset
    : isantisymm quotient_poset_hrel.
  Proof.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intros x₁.
    use setquotunivprop'.
    {
      intro x.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intros x₂.
    use factor_through_squash.
    {
      repeat (use impred ; intro).
      apply setproperty.
    }
    intro p₁.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intro p₂.
    use iscompsetquotpr ; cbn in *.
    apply (pr2 (H x₁ x₂)).
    apply hinhpr.
    induction p₁ as [ p₁ | p₁ ] ; induction p₂ as [ p₂ | p₂ ].
    - exact (inr (p₁ ,, p₂)).
    - refine (inr (p₁ ,, _)).
      exact (I_down x₂ x₁ p₂ p₁).
    - refine (inr (_ ,, _)).
      + exact (I_down x₁ x₂ p₁ p₂).
      + exact p₂.
    - apply inl.
      exact (antisymm_PartialOrder RX p₁ p₂).
  Qed.

  Definition quotient_poset
    : PartialOrder (setquotinset eqX).
  Proof.
    use make_PartialOrder.
    - exact quotient_poset_hrel.
    - refine ((_ ,, _) ,, _).
      + exact istrans_quotient_poset.
      + exact isrefl_quotient_poset.
      + exact isantisymm_quotient_poset.
  Defined.

  Proposition is_monotone_quotient_setquot_pr
    : is_monotone RX quotient_poset (setquotpr _).
  Proof.
    intros x₁ x₂ p.
    apply hinhpr ; cbn.
    exact (inr p).
  Qed.

  Definition quotient_poset_bottom
             (pX : bottom_element RX)
    : bottom_element quotient_poset.
  Proof.
    simple refine (_ ,, _).
    - exact (setquotpr _ (pr1 pX)).
    - abstract
        (use setquotunivprop' ;
         [ intro ;
           apply propproperty
         | ] ;
         intro y ;
         exact (hinhpr (inr (pr2 pX y)))).
  Defined.
End QuotientEquivRel.

Definition pointed_quotient_poset
           {X : hSet}
           (RX : pointed_PartialOrder X)
           (I : X → hProp)
           (I_down : downward_closed RX I)
           (eqX : eqrel X)
           (H : ∏ (x₁ x₂ : X), eqX x₁ x₂ <-> downward_closed_to_eqrel I x₁ x₂)
  : pointed_PartialOrder (setquotinset eqX)
  := quotient_poset RX I I_down eqX H ,, quotient_poset_bottom _ _ _ _ _ (pr2 RX).
