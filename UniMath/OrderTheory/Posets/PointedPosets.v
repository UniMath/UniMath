(*****************************************************************

 Pointed posets

 We look at posets with a bottom element. This bottom element can
 either be part of the structure or it can be required to only
 merely exist.

 Contents
 1. Pointed posets
 2. Basic constructions on pointed posets
 3. Strict and monotone functions
 4. Equality of pointed posets
 5. Examples of strict and monotone functions
 6. The equalizer of pointed posets
 7. Type indexed products of pointed posets
 8. Function spaces of pointed posets

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.

(**
 1. Pointed posets
 *)
Definition bottom_element
           {X : hSet}
           (RX : PartialOrder X)
  : UU
  := ∑ (x : X), ∏ (y : X), RX x y.

Proposition bottom_element_eq
            {X : hSet}
            (RX : PartialOrder X)
            (b₁ b₂ : bottom_element RX)
  : b₁ = b₂.
Proof.
  use subtypePath.
  {
    intro.
    use impred ; intro.
    apply propproperty.
  }
  use (antisymm_PartialOrder RX).
  - apply b₁.
  - apply b₂.
Qed.

Proposition isaprop_bottom_element
            {X : hSet}
            (RX : PartialOrder X)
  : isaprop (bottom_element RX).
Proof.
  use invproofirrelevance.
  exact (bottom_element_eq RX).
Qed.

Definition pointed_PartialOrder
           (X : hSet)
  : UU
  := ∑ (RX : PartialOrder X), bottom_element RX.

Definition make_pointed_PartialOrder
           {X : hSet}
           (RX : PartialOrder X)
           (x : X)
           (p : ∏ (y : X), RX x y)
  : pointed_PartialOrder X
  := RX ,, x ,, p.

#[reversible=no] Coercion pointed_PartialOrder_to_Partial_order
         {X : hSet}
         (RX : pointed_PartialOrder X)
  : PartialOrder X
  := pr1 RX.

Definition pointed_PartialOrder_to_point
           {X : hSet}
           (RX : pointed_PartialOrder X)
  : X
  := pr12 RX.

Notation "⊥_{ RX }" := (pointed_PartialOrder_to_point RX).

Proposition pointed_PartialOrder_min_point
            {X : hSet}
            (RX : pointed_PartialOrder X)
            (y : X)
  : RX ⊥_{RX} y.
Proof.
  exact (pr22 RX y).
Qed.

(**
 2. Basic constructions on pointed posets
 *)
Definition unit_pointed_PartialOrder
  : pointed_PartialOrder unitset.
Proof.
  use make_pointed_PartialOrder.
  - exact unit_PartialOrder.
  - exact tt.
  - exact (λ _, tt).
Defined.

Definition prod_pointed_PartialOrder
           {X Y : hSet}
           (RX : pointed_PartialOrder X)
           (RY : pointed_PartialOrder Y)
  : pointed_PartialOrder (X × Y)%set.
Proof.
  use make_pointed_PartialOrder.
  - exact (prod_PartialOrder RX RY).
  - exact (⊥_{RX} ,, ⊥_{RY}).
  - intro y.
    refine (_ ,, _).
    + apply pointed_PartialOrder_min_point.
    + apply pointed_PartialOrder_min_point.
Defined.

Definition bottom_PartialOrder_boolset
  : bottom_element PartialOrder_boolset.
Proof.
  refine (false ,, _).
  abstract
    (intro b ;
     induction b ; cbn ;
     exact tt).
Defined.

Definition pointed_PartialOrder_boolset
  : pointed_PartialOrder boolset
  := PartialOrder_boolset
     ,,
     bottom_PartialOrder_boolset.

(**
 3. Strict and monotone functions
 *)
Definition is_strict_and_monotone
           {X Y : hSet}
           (RX : pointed_PartialOrder X)
           (RY : pointed_PartialOrder Y)
           (f : X → Y)
  : UU
  := is_monotone RX RY f × f ⊥_{RX} = ⊥_{RY}.

#[reversible=no] Coercion is_strict_and_monotone_function_to_is_monotone
         {X Y : hSet}
         {RX : pointed_PartialOrder X}
         {RY : pointed_PartialOrder Y}
         {f : X → Y}
         (Hf : is_strict_and_monotone RX RY f)
  : is_monotone RX RY f
  := pr1 Hf.

Definition strict_function_on_point
           {X Y : hSet}
           {RX : pointed_PartialOrder X}
           {RY : pointed_PartialOrder Y}
           {f : X → Y}
           (Hf : is_strict_and_monotone RX RY f)
  : f ⊥_{RX} = ⊥_{RY}
  := pr2 Hf.

Proposition isaprop_is_strict_and_monotone
            {X Y : hSet}
            (RX : pointed_PartialOrder X)
            (RY : pointed_PartialOrder Y)
            (f : X → Y)
  : isaprop (is_strict_and_monotone RX RY f).
Proof.
  apply isapropdirprod.
  - apply isaprop_is_monotone.
  - apply setproperty.
Qed.

Definition strict_and_monotone_function
           {X Y : hSet}
           (RX : pointed_PartialOrder X)
           (RY : pointed_PartialOrder Y)
  : UU
  := ∑ (f : X → Y), is_strict_and_monotone RX RY f.

Definition strict_and_monotone_function_set
           {X Y : hSet}
           (RX : pointed_PartialOrder X)
           (RY : pointed_PartialOrder Y)
  : hSet.
Proof.
  use make_hSet.
  - exact (strict_and_monotone_function RX RY).
  - abstract
      (use isaset_total2 ;
       [ use funspace_isaset ;
         apply Y
       | intro f ;
         apply isasetaprop ;
         apply isaprop_is_strict_and_monotone ]).
Defined.

Definition strict_and_monotone_function_to_fun
           {X Y : hSet}
           {RX : pointed_PartialOrder X}
           {RY : pointed_PartialOrder Y}
           (f : strict_and_monotone_function RX RY)
  : X → Y
  := pr1 f.

Coercion strict_and_monotone_function_to_fun
  : strict_and_monotone_function >-> Funclass.

Proposition eq_strict_and_monotone_function
            {X Y : hSet}
            {RX : pointed_PartialOrder X}
            {RY : pointed_PartialOrder Y}
            {f g : strict_and_monotone_function RX RY}
            (p : ∏ (x : X), f x = g x)
  : f = g.
Proof.
  use subtypePath ; [ intro ; apply isaprop_is_strict_and_monotone | ].
  use funextsec.
  exact p.
Qed.

(**
 4. Equality of pointed posets
 *)
Proposition transportf_bottom_element
            {X : hSet}
            {PX PX' : PartialOrder X}
            (p : PX = PX')
            (x : bottom_element PX)
  : pr1 (transportf
           bottom_element
           p
           x)
    =
    pr1 x.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition eq_pointed_PartialOrder_monotone
            {X : hSet}
            {PX PX' : pointed_PartialOrder X}
            (p : is_monotone PX PX' (λ x, x))
            (q : is_monotone PX' PX (λ x, x))
  : PX = PX'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_bottom_element.
  }
  use eq_PartialOrder.
  - apply p.
  - apply q.
Qed.

Proposition eq_pointed_PartialOrder_strict_and_monotone
            {X : hSet}
            {PX PX' : pointed_PartialOrder X}
            (p : is_strict_and_monotone PX PX' (λ x, x))
            (q : is_strict_and_monotone PX' PX (λ x, x))
  : PX = PX'.
Proof.
  use eq_pointed_PartialOrder_monotone.
  - apply p.
  - apply q.
Qed.

(**
 5. Examples of strict and monotone functions
 *)
Proposition idfun_is_strict_and_monotone
            {X : hSet}
            (RX : pointed_PartialOrder X)
  : is_strict_and_monotone RX RX (idfun X).
Proof.
  split.
  - apply idfun_is_monotone.
  - apply idpath.
Qed.

Proposition comp_is_strict_and_monotone
            {X₁ X₂ X₃ : hSet}
            {R₁ : pointed_PartialOrder X₁}
            {R₂ : pointed_PartialOrder X₂}
            {R₃ : pointed_PartialOrder X₃}
            {f : X₁ → X₂}
            {g : X₂ → X₃}
            (Hf : is_strict_and_monotone R₁ R₂ f)
            (Hg : is_strict_and_monotone R₂ R₃ g)
  : is_strict_and_monotone R₁ R₃ (λ z, g(f z)).
Proof.
  split.
  - exact (comp_is_monotone (pr1 Hf) (pr1 Hg)).
  - rewrite (strict_function_on_point Hf).
    rewrite (strict_function_on_point Hg).
    apply idpath.
Qed.

Proposition dirprod_pr1_is_strict_and_monotone
            {X₁ X₂ : hSet}
            (R₁ : pointed_PartialOrder X₁)
            (R₂ : pointed_PartialOrder X₂)
  : is_strict_and_monotone
      (prod_pointed_PartialOrder R₁ R₂)
      R₁
      dirprod_pr1.
Proof.
  split.
  - apply dirprod_pr1_is_monotone.
  - apply idpath.
Qed.

Proposition dirprod_pr2_is_strict_and_monotone
            {X₁ X₂ : hSet}
            (R₁ : pointed_PartialOrder X₁)
            (R₂ : pointed_PartialOrder X₂)
  : is_strict_and_monotone
      (prod_pointed_PartialOrder R₁ R₂)
      R₂
      dirprod_pr2.
Proof.
  split.
  - apply dirprod_pr2_is_monotone.
  - apply idpath.
Qed.

Proposition prodtofun_is_strict_and_monotone
            {W X₁ X₂ : hSet}
            {RW : pointed_PartialOrder W}
            {R₁ : pointed_PartialOrder X₁}
            {R₂ : pointed_PartialOrder X₂}
            {f : W → X₁}
            {g : W → X₂}
            (Hf : is_strict_and_monotone RW R₁ f)
            (Hg : is_strict_and_monotone RW R₂ g)
  : is_strict_and_monotone
      RW
      (prod_pointed_PartialOrder R₁ R₂)
      (prodtofuntoprod (f,, g)).
Proof.
  split.
  - exact (prodtofun_is_monotone Hf Hg).
  - use pathsdirprod ; cbn.
    + exact (strict_function_on_point Hf).
    + exact (strict_function_on_point Hg).
Qed.

Proposition constant_is_strict_and_monotone
            {X : hSet}
            {Y : hSet}
            (RX : pointed_PartialOrder X)
            (RY : pointed_PartialOrder Y)
  : is_strict_and_monotone
      RX
      RY
      (λ _, ⊥_{RY}).
Proof.
  split.
  - intros ? ? p.
    apply refl_PartialOrder.
  - apply idpath.
Qed.

(**
 6. The equalizer of pointed posets
 *)
Section Equalizer.
  Context {X Y : hSet}
          {RX : pointed_PartialOrder X}
          {RY : pointed_PartialOrder Y}
          {f g : X → Y}
          (Hf : is_strict_and_monotone RX RY f)
          (Hg : is_strict_and_monotone RX RY g).

  Let Eq : hSet
    := (∑ (x : X), f x = g x) ,, isaset_total2 _ (pr2 X) (λ _, isasetaprop (pr2 Y _ _)).

  Definition Equalizer_pointed_PartialOrder
    : pointed_PartialOrder Eq.
  Proof.
    use make_pointed_PartialOrder.
    - exact (Equalizer_order RX Y f g).
    - refine (⊥_{RX} ,, _).
      abstract
        (rewrite (strict_function_on_point Hf) ;
         rewrite (strict_function_on_point Hg) ;
         apply idpath).
    - intros x.
      apply pointed_PartialOrder_min_point.
  Defined.

  Proposition Equalizer_pr1_strict_and_monotone
    : is_strict_and_monotone
        Equalizer_pointed_PartialOrder
        RX
        (λ z, pr1 z).
  Proof.
    split.
    - apply Equalizer_pr1_monotone.
    - apply idpath.
  Qed.

  Proposition Equalizer_map_strict_and_monotone
              {W : hSet}
              (RW : pointed_PartialOrder W)
              {h : W → X}
              (Rh : is_strict_and_monotone RW RX h)
              (p : ∏ (w : W), f(h w) = g(h w))
    : is_strict_and_monotone
        RW
        Equalizer_pointed_PartialOrder
        (λ w, h w ,, p w).
  Proof.
    split.
    - apply Equalizer_map_monotone.
      exact Rh.
    - use subtypePath.
      {
        intro.
        apply setproperty.
      }
      cbn.
      apply (strict_function_on_point Rh).
  Qed.
End Equalizer.

(**
 7. Type indexed products of pointed posets
 *)
Definition depfunction_pointed_poset
           {X : UU}
           (Y : X → hSet)
           (RY : ∏ (x : X), pointed_PartialOrder (Y x))
  : pointed_PartialOrder (forall_hSet Y).
Proof.
  use make_pointed_PartialOrder.
  - exact (depfunction_poset Y RY).
  - exact (λ x, ⊥_{RY x}).
  - intros y x.
    apply pointed_PartialOrder_min_point.
Defined.

Proposition is_strict_and_monotone_depfunction_pointed_poset_pr
            {X : UU}
            (Y : X → hSet)
            (RY : ∏ (x : X), pointed_PartialOrder (Y x))
            (x : X)
  : is_strict_and_monotone
      (depfunction_pointed_poset Y RY)
      (RY x)
      (λ f, f x).
Proof.
  split.
  - apply (is_monotone_depfunction_poset_pr Y).
  - apply idpath.
Qed.

Proposition is_strict_and_monotone_depfunction_pointed_poset_pair
            {W : hSet}
            {X : UU}
            {Y : X → hSet}
            {RW : pointed_PartialOrder W}
            {RY : ∏ (x : X), pointed_PartialOrder (Y x)}
            (fs : ∏ (x : X), W → Y x)
            (Hfs : ∏ (x : X), is_strict_and_monotone RW (RY x) (fs x))
  : is_strict_and_monotone
      RW
      (depfunction_pointed_poset Y RY)
      (λ w x, fs x w).
Proof.
  split.
  - apply is_monotone_depfunction_poset_pair.
    intro x.
    exact (Hfs x).
  - use funextsec.
    intro x ; cbn.
    apply (strict_function_on_point (Hfs x)).
Qed.

(**
 8. Function spaces of pointed posets
 *)
Section FunctionPoset.
  Context {X Y : hSet}
          (PX : pointed_PartialOrder X)
          (PY : pointed_PartialOrder Y).

  Definition strict_and_monotone_PartialOrder
    : PartialOrder (strict_and_monotone_function_set PX PY).
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ f g, ∀ (x : X), PY (f x) (g x)).
    - refine ((_ ,, _) ,, _).
      + abstract
          (intros f g h p q x ;
           exact (trans_PartialOrder PY (p x) (q x))).
      + abstract
          (intros f x ;
           exact (refl_PartialOrder PY (f x))).
      + abstract
          (intros f g p q ;
           use eq_strict_and_monotone_function ;
           intro x ;
           exact (antisymm_PartialOrder PY (p x) (q x))).
  Defined.

  Definition strict_and_monotone_PartialOrder_bottom
    : bottom_element strict_and_monotone_PartialOrder.
  Proof.
    refine ((_ ,, constant_is_strict_and_monotone PX PY) ,, _).
    abstract
      (intros f x ; cbn ;
       apply (pr2 PY)).
  Defined.

  Definition strict_and_monotone_pointed_PartialOrder
    : pointed_PartialOrder (strict_and_monotone_function_set PX PY)
    := strict_and_monotone_PartialOrder
       ,,
       strict_and_monotone_PartialOrder_bottom.
End FunctionPoset.
