(*****************************************************************

 Quotients of posets

 If we have a poset and a downward closed set in that poset, then
 we can collapse that subset (i.e., identify all its elements) and
 acquire a new poset.

 Contents
 1. Downward closed sets
 2. The quotient of posets

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.Posets.PointedPosets.

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
Section QuotientPoset.
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

  Local Definition quotient_poset_order_on_el
    : hrel X
    := λ x₁ x₂, I x₁ ∨ RX x₁ x₂.

  Proposition quotient_poset_order_on_el_comprel
    : iscomprelrel downward_closed_to_eqrel quotient_poset_order_on_el.
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

  Definition quotient_poset_order
    : hrel (setquotinset downward_closed_to_eqrel).
  Proof.
    use quotrel.
    - exact quotient_poset_order_on_el.
    - exact quotient_poset_order_on_el_comprel.
  Defined.

  Proposition istrans_quotient_poset_order
    : istrans quotient_poset_order.
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

  Proposition isrefl_quotient_poset_order
    : isrefl quotient_poset_order.
  Proof.
    use setquotunivprop.
    intro x ; cbn in *.
    apply hinhpr.
    exact (inr (refl_PartialOrder RX x)).
  Qed.

  Proposition isantisymm_quotient_poset_order
    : isantisymm quotient_poset_order.
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

  Definition quotient_poset
    : PartialOrder (setquotinset downward_closed_to_eqrel).
  Proof.
    use make_PartialOrder.
    - exact quotient_poset_order.
    - refine ((_ ,, _) ,, _).
      + exact istrans_quotient_poset_order.
      + exact isrefl_quotient_poset_order.
      + exact isantisymm_quotient_poset_order.
  Defined.

  Proposition is_monotone_setquot_pr
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
End QuotientPoset.
