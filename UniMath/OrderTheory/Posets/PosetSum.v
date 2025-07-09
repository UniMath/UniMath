(****************************************************************

 Coproducts of partial orders

 We construct coproducts of partial orders, and we show that the
 inclusion functions are monotone. In addition, we show that the
 map coming from the universal property is monotone. We consider
 both the case of binary coproducts and set-indexed coproducts.

 Contents
 1. Coproduct of partial orders
 2. Monotonicity of inclusion
 3. The sum of monotone maps is monotone
 4. Set indexed coproducts of partial order
 5. Monotonicity of the set-indexed inclusion
 6. The set-indexed sum of monotope maps is monotone

 ****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.

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

Section CoproductOfPartialOrder.
  Context {X : hSet}
          (Y : X → hSet)
          (PY : ∏ (x : X), PartialOrder (Y x)).

  (**
   4. Set indexed coproducts of partial order
   *)
  Definition set_coproduct_hrel
    : hrel (∑ (x : X), Y x)%set
    := λ xy₁ xy₂,
       let x₁ := pr1 xy₁ in
       let x₂ := pr1 xy₂ in
       let y₁ := pr2 xy₁ in
       let y₂ := pr2 xy₂ in
       (∑ (p : eqset x₁ x₂), PY x₂ (transportf Y p y₁) y₂)%prop.

  Proposition isPartialOrder_set_coproduct_hrel
    : isPartialOrder set_coproduct_hrel.
  Proof.
    repeat split.
    - intros xy₁ xy₂ xy₃ pq₁ pq₂.
      induction xy₁ as [ x₁ y₁ ].
      induction xy₂ as [ x₂ y₂ ].
      induction xy₃ as [ x₃ y₃ ].
      induction pq₁ as [ p₁ q₁ ].
      induction pq₂ as [ p₂ q₂ ].
      cbn in *.
      induction p₁, p₂ ; cbn in *.
      refine (idpath _ ,, _) ; cbn.
      exact (trans_PartialOrder (PY _) q₁ q₂).
    - intros xy.
      induction xy as [ x y ] ; cbn.
      refine (idpath _ ,, _).
      exact (refl_PartialOrder (PY x) y).
    - intros xy₁ xy₂ pq₁ pq₂.
      induction xy₁ as [ x₁ y₁ ].
      induction xy₂ as [ x₂ y₂ ].
      induction pq₁ as [ p₁ q₁ ].
      induction pq₂ as [ p₂ q₂ ].
      cbn in *.
      induction p₁ ; cbn in *.
      assert (p₂ = idpath _) as r.
      {
        apply setproperty.
      }
      rewrite r in q₂ ; clear p₂ r.
      cbn in q₂.
      apply maponpaths.
      exact (antisymm_PartialOrder (PY _) q₁ q₂).
  Qed.

  Definition coproduct_set_PartialOrder
    : PartialOrder (∑ (x : X), Y x)%set.
  Proof.
    use make_PartialOrder.
    - exact set_coproduct_hrel.
    - exact isPartialOrder_set_coproduct_hrel.
  Defined.

  (**
   5. Monotonicity of the set-indexed inclusion
   *)
  Definition is_monotone_set_in
             (x : X)
    : is_monotone (PY x) coproduct_set_PartialOrder (λ (y : Y x), x ,, y).
  Proof.
    intros x₁ x₂ p ; cbn.
    exact (idpath _ ,, p).
  Qed.

  Definition set_in_monotone_function
             (x : X)
    : monotone_function (PY x) coproduct_set_PartialOrder
    := _ ,, is_monotone_set_in x.

  (**
   6. The set-indexed sum of monotope maps is monotone
   *)
  Definition is_monotone_set_coproduct_map
             {Z : hSet}
             {PZ : PartialOrder Z}
             {f : ∏ (x : X), Y x → Z}
             (Pf : ∏ (x : X), is_monotone (PY x) PZ (f x))
    : is_monotone
        coproduct_set_PartialOrder
        PZ
        (λ xy, f (pr1 xy) (pr2 xy)).
  Proof.
    intros xy₁ xy₂ p.
    induction xy₁ as [ x₁ y₁ ].
    induction xy₂ as [ x₂ y₂ ].
    induction p as [ p q ].
    cbn in *.
    induction p.
    cbn in q.
    apply Pf.
    exact q.
  Qed.
End CoproductOfPartialOrder.
