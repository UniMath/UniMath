(*****************************************************************

 Monotone functions between posets

 We define the notion of monotone function and we give some basic
 examples of them

 Contents
 1. Monotone functions
 2. Equality of posets via monotone functions
 3. Examples of monotone functions
 4. The poset of monotone functions

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.

(**
 1. Monotone functions
 *)
Definition is_monotone
           {X₁ X₂ : hSet}
           (R₁ : PartialOrder X₁)
           (R₂ : PartialOrder X₂)
           (f : X₁ → X₂)
  : UU
  := ∏ (x₁ x₂ : X₁), R₁ x₁ x₂ → R₂ (f x₁) (f x₂).

Proposition isaprop_is_monotone
            {X₁ X₂ : hSet}
            (R₁ : PartialOrder X₁)
            (R₂ : PartialOrder X₂)
            (f : X₁ → X₂)
  : isaprop (is_monotone R₁ R₂ f).
Proof.
  repeat (use impred ; intro).
  apply (pr1 R₂).
Qed.

Definition monotone_function
           {X₁ X₂ : hSet}
           (R₁ : PartialOrder X₁)
           (R₂ : PartialOrder X₂)
  : UU
  := ∑ (f : X₁ → X₂), is_monotone R₁ R₂ f.

Definition monotone_function_to_function
           {X₁ X₂ : hSet}
           {R₁ : PartialOrder X₁}
           {R₂ : PartialOrder X₂}
           (f : monotone_function R₁ R₂)
  : X₁ → X₂
  := pr1 f.

Coercion monotone_function_to_function : monotone_function >-> Funclass.

Proposition eq_monotone_function
            {X₁ X₂ : hSet}
            {R₁ : PartialOrder X₁}
            {R₂ : PartialOrder X₂}
            (f g : monotone_function R₁ R₂)
            (p : ∏ (x : X₁), f x = g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_is_monotone.
  }
  use funextsec.
  exact p.
Qed.

Definition monotone_function_hSet
           {X₁ X₂ : hSet}
           (R₁ : PartialOrder X₁)
           (R₂ : PartialOrder X₂)
  : hSet.
Proof.
  use make_hSet.
  - exact (monotone_function R₁ R₂).
  - use isaset_total2.
    + use funspace_isaset.
      exact (pr2 X₂).
    + intro f.
      apply isasetaprop.
      apply isaprop_is_monotone.
Defined.

(**
 2. Equality of posets via monotone functions
 *)
Proposition eq_PartialOrder
            {X : hSet}
            {PX PX' : PartialOrder X}
            (p : is_monotone PX PX' (λ x, x))
            (q : is_monotone PX' PX (λ x, x))
  : PX = PX'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_isPartialOrder.
  }
  use funextsec ; intro.
  use funextsec ; intro.
  use weqtopathshProp.
  use weqimplimpl.
  - apply p.
  - apply q.
  - apply (pr1 PX).
  - apply (pr1 PX').
Defined.

(**
 3. Examples of monotone functions
 *)
Proposition idfun_is_monotone
            {X : hSet}
            (R : PartialOrder X)
  : is_monotone R R (idfun X).
Proof.
  exact (λ x₁ x₂ p, p).
Qed.

Definition id_monotone_function
           {X : hSet}
           (R : PartialOrder X)
  : monotone_function R R
  := _ ,, idfun_is_monotone R.

Proposition comp_is_monotone
            {X₁ X₂ X₃ : hSet}
            {R₁ : PartialOrder X₁}
            {R₂ : PartialOrder X₂}
            {R₃ : PartialOrder X₃}
            {f : X₁ → X₂}
            {g : X₂ → X₃}
            (Hf : is_monotone R₁ R₂ f)
            (Hg : is_monotone R₂ R₃ g)
  : is_monotone R₁ R₃ (λ z, g(f z)).
Proof.
  exact (λ x₁ x₂ p, Hg _ _ (Hf _ _ p)).
Qed.

Definition comp_monotone_function
           {X₁ X₂ X₃ : hSet}
           {R₁ : PartialOrder X₁}
           {R₂ : PartialOrder X₂}
           {R₃ : PartialOrder X₃}
           (f : monotone_function R₁ R₂)
           (g : monotone_function R₂ R₃)
  : monotone_function R₁ R₃
  := _ ,, comp_is_monotone (pr2 f) (pr2 g).

Proposition dirprod_pr1_is_monotone
            {X₁ X₂ : hSet}
            (R₁ : PartialOrder X₁)
            (R₂ : PartialOrder X₂)
  : is_monotone (prod_PartialOrder R₁ R₂) R₁ pr1.
Proof.
  exact (λ x₁ x₂ p, pr1 p).
Qed.

Definition pr1_monotone_function
           {X₁ X₂ : hSet}
           (R₁ : PartialOrder X₁)
           (R₂ : PartialOrder X₂)
  : monotone_function (prod_PartialOrder R₁ R₂) R₁
  := _ ,, dirprod_pr1_is_monotone R₁ R₂.

Proposition dirprod_pr2_is_monotone
            {X₁ X₂ : hSet}
            (R₁ : PartialOrder X₁)
            (R₂ : PartialOrder X₂)
  : is_monotone (prod_PartialOrder R₁ R₂) R₂ pr2.
Proof.
  exact (λ x₁ x₂ p, pr2 p).
Qed.

Definition pr2_monotone_function
           {X₁ X₂ : hSet}
           (R₁ : PartialOrder X₁)
           (R₂ : PartialOrder X₂)
  : monotone_function (prod_PartialOrder R₁ R₂) R₂
  := _ ,, dirprod_pr2_is_monotone R₁ R₂.

Proposition prodtofun_is_monotone
            {W X₁ X₂ : hSet}
            {RW : PartialOrder W}
            {R₁ : PartialOrder X₁}
            {R₂ : PartialOrder X₂}
            {f : W → X₁}
            {g : W → X₂}
            (Hf : is_monotone RW R₁ f)
            (Hg : is_monotone RW R₂ g)
  : is_monotone RW (prod_PartialOrder R₁ R₂) (prodtofuntoprod (f,, g)).
Proof.
  exact (λ x y p, Hf _ _ p ,, Hg _ _ p).
Qed.

Definition prodtofun_monotone_function
           {W X₁ X₂ : hSet}
           {RW : PartialOrder W}
           {R₁ : PartialOrder X₁}
           {R₂ : PartialOrder X₂}
           (f : monotone_function RW R₁)
           (g : monotone_function RW R₂)
  : monotone_function RW (prod_PartialOrder R₁ R₂)
  := _ ,, prodtofun_is_monotone (pr2 f) (pr2 g).

Proposition Equalizer_pr1_monotone
            {X : hSet}
            (RX : PartialOrder X)
            (Y : hSet)
            (f g : X → Y)
  : is_monotone
      (Equalizer_order RX Y f g)
      RX
      (λ z, pr1 z).
Proof.
  intros x y p.
  exact p.
Qed.

Definition Equalizer_monotone_function
           {X Y : hSet}
           (RX : PartialOrder X)
           (RY : PartialOrder Y)
           (f g : X → Y)
  : monotone_function (Equalizer_order RX Y f g) RX
  := (λ z, pr1 z) ,, Equalizer_pr1_monotone RX Y f g.

Proposition Equalizer_map_monotone
            {X : hSet}
            (RX : PartialOrder X)
            (Y : hSet)
            (f g : X → Y)
            {W : hSet}
            (RW : PartialOrder W)
            {h : W → X}
            (Rh : is_monotone RW RX h)
            (p : ∏ (w : W), f(h w) = g(h w))
  : is_monotone
      RW
      (Equalizer_order RX Y f g)
      (λ w, h w ,, p w).
Proof.
  intros w₁ w₂ q.
  apply Rh.
  exact q.
Qed.

Proposition is_monotone_depfunction_poset_pr
            {X : UU}
            (Y : X → hSet)
            (RY : ∏ (x : X), PartialOrder (Y x))
            (x : X)
  : is_monotone (depfunction_poset Y RY) (RY x) (λ f, f x).
Proof.
  intros f g p.
  exact (p x).
Qed.

Proposition is_monotone_depfunction_poset_pair
            {W : hSet}
            {X : UU}
            {Y : X → hSet}
            {RW : PartialOrder W}
            {RY : ∏ (x : X), PartialOrder (Y x)}
            (fs : ∏ (x : X), W → Y x)
            (Hfs : ∏ (x : X), is_monotone RW (RY x) (fs x))
  : is_monotone RW (depfunction_poset Y RY) (λ w x, fs x w).
Proof.
  intros w₁ w₂ p x.
  exact (Hfs x _ _ p).
Qed.

(**
 4. The poset of monotone functions
 *)
Section FunctionOrder.
  Context {X Y : hSet}
          (RX : PartialOrder X)
          (RY : PartialOrder Y).

  Definition monotone_function_order
    : hrel (monotone_function_hSet RX RY).
  Proof.
    intros f g ; cbn in *.
    use make_hProp.
    - exact (∏ (x : X), RY (f x) (g x)).
    - abstract
        (use impred ; intro ;
         apply (pr1 RY)).
  Defined.

  Proposition monotone_function_isPartialOrder
    : isPartialOrder monotone_function_order.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (λ f g h p q x, trans_PartialOrder RY (p x) (q x)).
    - exact (λ f x, refl_PartialOrder RY (pr1 f x)).
    - intros f g p q.
      use eq_monotone_function.
      intro x.
      exact (antisymm_PartialOrder RY (p x) (q x)).
  Qed.

  Definition monotone_function_PartialOrder
    : PartialOrder (monotone_function_hSet RX RY).
  Proof.
    use make_PartialOrder.
    - exact monotone_function_order.
    - exact monotone_function_isPartialOrder.
  Defined.

  Definition eval_monotone_function
    : monotone_function
        (prod_PartialOrder RX monotone_function_PartialOrder)
        RY.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ xf, pr2 xf (pr1 xf)).
    - abstract
        (intros xf yg pq ;
         induction xf as [ x f ] ;
         induction yg as [ y g ] ;
         induction pq as [ p q ] ;
         cbn in * ;
         exact (trans_PartialOrder RY (q x) (pr2 g x y p))).
  Defined.

  Definition lam_monotone_function
             {Z : hSet}
             {RZ : PartialOrder Z}
             (f : monotone_function (prod_PartialOrder RX RZ) RY)
    : monotone_function RZ monotone_function_PartialOrder.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - intro z.
      simple refine (_ ,, _).
      + exact (λ x, f (x ,, z)).
      + abstract
          (intros x₁ x₂ p ;
           apply f ; cbn ;
           refine (p ,, _) ;
           apply refl_PartialOrder).
    - abstract
        (intros z₁ z₂ p x ; cbn ;
         apply f ; cbn ;
         exact (refl_PartialOrder RX x ,, p)).
  Defined.
End FunctionOrder.
