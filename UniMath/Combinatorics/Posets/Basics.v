(*****************************************************************

 Posets

 In this file, we some basic constructions and theory on posets.

 Contents
 1. Accessors for posets
 2. The unit poset
 3. The product of posets
 4. Type indexed products of posets
 5. The equalizer of posets
 6. The booleans as partial order
 7. Discrete partial orders

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.

(**
 1. Accessors for posets
 *)
Proposition trans_PartialOrder
            {X : hSet}
            (R : PartialOrder X)
            {x₁ x₂ x₃ : X}
            (p : R x₁ x₂)
            (q : R x₂ x₃)
  : R x₁ x₃.
Proof.
  exact (pr112 R _ _ _ p q).
Qed.

Proposition refl_PartialOrder
            {X : hSet}
            (R : PartialOrder X)
            (x : X)
  : R x x.
Proof.
  exact (pr212 R x).
Qed.

Proposition antisymm_PartialOrder
            {X : hSet}
            (R : PartialOrder X)
            {x y : X}
            (p : R x y)
            (q : R y x)
  : x = y.
Proof.
  exact (pr22 R _ _ p q).
Qed.

(**
 2. The unit poset
 *)
Definition unit_PartialOrder
  : PartialOrder unitset.
Proof.
  use make_PartialOrder.
  - exact (λ _ _, htrue).
  - repeat split.
    intros x y p q.
    apply isapropunit.
Defined.

(**
 3. The product of posets
 *)
Section ProdOrder.
  Context {X₁ X₂ : hSet}
          (R₁ : PartialOrder X₁)
          (R₂ : PartialOrder X₂).

  Let R : hrel (X₁ × X₂)%set := λ x y, R₁ (pr1 x) (pr1 y) ∧ R₂ (pr2 x) (pr2 y).

  Proposition prod_PartialOrderLaws
    : isPartialOrder R.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - refine (λ x y z p q, _ ,, _).
      + exact (trans_PartialOrder R₁ (pr1 p) (pr1 q)).
      + exact (trans_PartialOrder R₂ (pr2 p) (pr2 q)).
    - refine (λ x, _ ,, _).
      + exact (refl_PartialOrder R₁ (pr1 x)).
      + exact (refl_PartialOrder R₂ (pr2 x)).
    - refine (λ x y p q, _).
      use pathsdirprod.
      + exact (antisymm_PartialOrder R₁ (pr1 p) (pr1 q)).
      + exact (antisymm_PartialOrder R₂ (pr2 p) (pr2 q)).
  Qed.

  Definition prod_PartialOrder
    : PartialOrder (X₁ × X₂)%set.
  Proof.
    use make_PartialOrder.
    - exact R.
    - exact prod_PartialOrderLaws.
  Defined.
End ProdOrder.

(**
 4. Type indexed products of posets
 *)
Definition depfunction_poset
           {X : UU}
           (Y : X → hSet)
           (RY : ∏ (x : X), PartialOrder (Y x))
  : PartialOrder (forall_hSet Y).
Proof.
  use make_PartialOrder.
  - exact (λ f g, ∀ (x : X), RY x (f x) (g x)).
  - repeat split.
    + abstract
        (intros f g h p q x ;
         exact (trans_PartialOrder (RY x) (p x) (q x))).
    + abstract
        (intros f x ;
         exact (refl_PartialOrder (RY x) (f x))).
    + abstract
        (intros f g p q ;
         use funextsec ;
         intro x ;
         exact (antisymm_PartialOrder (RY x) (p x) (q x))).
Defined.

(**
 5. The equalizer of posets
 *)
Section Equalizer.
  Context {X : hSet}
          (RX : PartialOrder X)
          (Y : hSet)
          (f g : X → Y).

  Let Eq : hSet
    := (∑ (x : X), f x = g x) ,, isaset_total2 _ (pr2 X) (λ _, isasetaprop (pr2 Y _ _)).

  Definition Equalizer_order
    : PartialOrder Eq.
  Proof.
    simple refine (_ ,, ((_ ,, _) ,, _)).
    - exact (λ x y, RX (pr1 x) (pr1 y)).
    - abstract
        (exact (λ x y z p q, trans_PartialOrder RX p q)).
    - abstract
        (exact (λ x, refl_PartialOrder RX (pr1 x))).
    - abstract
        (intros x y p q ;
         use subtypePath ; [ intro ; apply (pr2 Y) | ] ;
         exact (antisymm_PartialOrder RX p q)).
  Defined.
End Equalizer.

(**
 6. The booleans as partial order
 *)
Definition PartialOrder_boolset
  : PartialOrder boolset.
Proof.
  use make_PartialOrder.
  - exact (λ b₁ b₂, if b₁ then if b₂ then htrue else hfalse else htrue).
  - repeat split.
    + abstract
        (intros b₁ b₂ b₃ p q ;
         induction b₁, b₂, b₃ ; induction p ; induction q ;
         apply tt).
    + abstract
        (intros b ;
         induction b ; exact tt).
    + abstract
        (intros b₁ b₂ p q ;
         induction b₁, b₂ ; induction p ; induction q ;
         apply idpath).
Defined.

(**
 7. Discrete partial orders
 *)
Section DiscretePartialOrder.
  Context (A : hSet).

  Definition discrete_hrel
    : hrel A
    := λ x y, (x = y)%logic.

  Proposition isPartialOrder_discrete_hrel
    : isPartialOrder discrete_hrel.
  Proof.
    refine ((_ ,, _) ,, _).
    - intros x y z p q.
      exact (p @ q).
    - exact (λ x, idpath _).
    - exact (λ x y p q, p).
  Qed.

  Definition discrete_partial_order
    : PartialOrder A.
  Proof.
    use make_PartialOrder.
    - exact discrete_hrel.
    - exact isPartialOrder_discrete_hrel.
  Defined.
End DiscretePartialOrder.
