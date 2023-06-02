(****************************************************************

 Coproducts of partial orders

 We construct coproducts of partial orders, and we show that the
 inclusion functions are monotone. In addition, we show that the
 map coming from the universal property is monotone.

 Contents
 1. Coproduct of partial orders
 2. Monotonicity of inclusion
 3. The sum of monotone maps is monotone

 ****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.

Section CoproductOfPartialOrder.
  Context {X Y : hSet}
          (PX : PartialOrder X)
          (PY : PartialOrder Y).

  (**
   1. Coproduct of partial orders
   *)
  Definition coproduct_hrel
    : hrel (setcoprod X Y).
  Proof.
    intros xy₁ xy₂.
    induction xy₁ as [ x₁ | y₁ ] ; induction xy₂ as [ x₂ | y₂ ].
    - exact (PX x₁ x₂).
    - exact hfalse.
    - exact hfalse.
    - exact (PY y₁ y₂).
  Defined.

  Proposition isPartialOrder_coproduct_hrel
    : isPartialOrder coproduct_hrel.
  Proof.
    repeat split.
    - intros xy₁ xy₂ xy₃ p q.
      induction xy₁ as [ x₁ | y₁ ] ;
        induction xy₂ as [ x₂ | y₂ ] ;
        induction xy₃ as [ x₃ | y₃ ] ;
        cbn ; cbn in p, q ;
        try (apply (fromempty p)) ;
        try (apply (fromempty q)).
      + exact (trans_PartialOrder PX p q).
      + exact (trans_PartialOrder PY p q).
    - intros xy ; induction xy as [ x | y ] ; cbn.
      + exact (refl_PartialOrder PX x).
      + exact (refl_PartialOrder PY y).
    - intros xy₁ xy₂ p q.
      induction xy₁ as [ x₁ | y₁ ] ;
        induction xy₂ as [ x₂ | y₂ ] ;
        cbn in p, q ;
        try (apply (fromempty p)) ;
        try (apply (fromempty q)).
      + exact (maponpaths inl (antisymm_PartialOrder PX p q)).
      + exact (maponpaths inr (antisymm_PartialOrder PY p q)).
  Qed.

  Definition coproduct_PartialOrder
    : PartialOrder (setcoprod X Y).
  Proof.
    use make_PartialOrder.
    - exact coproduct_hrel.
    - exact isPartialOrder_coproduct_hrel.
  Defined.

  (**
   2. Monotonicity of inclusion
   *)
  Definition is_monotone_inl
    : is_monotone PX coproduct_PartialOrder inl.
  Proof.
    intros x₁ x₂ p.
    exact p.
  Qed.

  Definition inl_monotone_function
    : monotone_function PX coproduct_PartialOrder
    := _ ,, is_monotone_inl.

  Definition is_monotone_inr
    : is_monotone PY coproduct_PartialOrder inr.
  Proof.
    intros x₁ x₂ p.
    exact p.
  Qed.

  Definition inr_monotone_function
    : monotone_function PY coproduct_PartialOrder
    := _ ,, is_monotone_inr.

  (**
   3. The sum of monotone maps is monotone
   *)
  Definition is_monotone_sumofmaps
             {Z : hSet}
             {PZ : PartialOrder Z}
             {f : X → Z}
             (Pf : is_monotone PX PZ f)
             {g : Y → Z}
             (Pg : is_monotone PY PZ g)
    : is_monotone coproduct_PartialOrder PZ (sumofmaps f g).
  Proof.
    intros xy₁ xy₂ p.
    induction xy₁ as [ x₁ | y₁ ] ; induction xy₂ as [ x₂ | y₂ ] ; cbn in *.
    - apply Pf.
      exact p.
    - apply fromempty.
      exact p.
    - apply fromempty.
      exact p.
    - apply Pg.
      exact p.
  Qed.
End CoproductOfPartialOrder.
