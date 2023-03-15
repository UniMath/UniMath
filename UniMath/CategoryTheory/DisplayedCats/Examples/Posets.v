(*****************************************************************

 The category of posets

 We construct the category of posets as a displayed category over
 the category of sets. In addition, we equip this category with a
 terminal object and with binary products. We also construct
 equalizers and exponentials for this category.

 Contents
 1. The category of posets
 2. Terminal object
 3. Binary products
 4. Equalizers
 5. Exponentials

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Local Open Scope cat.

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

Definition unit_PartialOrder
  : PartialOrder unitHSET.
Proof.
  use make_PartialOrder.
  - exact (λ _ _, htrue).
  - repeat split.
    intros x y p q.
    apply isapropunit.
Defined.

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

Definition  monotone_function_to_function
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

Proposition idfun_is_monotone
            {X : hSet}
            (R : PartialOrder X)
  : is_monotone R R (idfun X).
Proof.
  exact (λ x₁ x₂ p, p).
Qed.

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

Proposition dirprod_pr1_is_monotone
            {X₁ X₂ : hSet}
            (R₁ : PartialOrder X₁)
            (R₂ : PartialOrder X₂)
  : is_monotone (prod_PartialOrder R₁ R₂) R₁ pr1.
Proof.
  exact (λ x₁ x₂ p, pr1 p).
Qed.

Proposition dirprod_pr2_is_monotone
            {X₁ X₂ : hSet}
            (R₁ : PartialOrder X₁)
            (R₂ : PartialOrder X₂)
  : is_monotone (prod_PartialOrder R₁ R₂) R₂ pr2.
Proof.
  exact (λ x₁ x₂ p, pr2 p).
Qed.

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

  Proposition Equalizer_pr1_monotone
    : is_monotone
        Equalizer_order
        RX
        (λ z, pr1 z).
  Proof.
    intros x y p.
    exact p.
  Qed.

  Proposition Equalizer_map_monotone
              {W : hSet}
              (RW : PartialOrder W)
              {h : W → X}
              (Rh : is_monotone RW RX h)
              (p : ∏ (w : W), f(h w) = g(h w))
    : is_monotone
        RW
        Equalizer_order
        (λ w, h w ,, p w).
  Proof.
    intros w₁ w₂ q.
    apply Rh.
    exact q.
  Qed.
End Equalizer.

(**
 1. The category of posets
 *)
Definition poset_disp_cat
  : disp_cat SET.
Proof.
  use disp_struct.
  - exact (λ X, PartialOrder X).
  - exact (λ X₁ X₂ R₁ R₂ f, is_monotone R₁ R₂ f).
  - exact (λ X₁ X₂ R₁ R₂ f, isaprop_is_monotone R₁ R₂ f).
  - exact (λ X R, idfun_is_monotone R).
  - exact (λ X₁ X₂ X₃ R₁ R₂ R₃ f g Hf Hg, comp_is_monotone Hf Hg).
Defined.

Proposition is_univalent_poset_disp_cat
  : is_univalent_disp poset_disp_cat.
Proof.
  use is_univalent_disp_from_SIP_data.
  - exact (λ X, isaset_PartialOrder X).
  - cbn.
    refine (λ X R₁ R₂ p q, _).
    use subtypePath.
    {
      intro.
      apply isaprop_isPartialOrder.
    }
    use funextsec ; intro.
    use funextsec ; intro.
    use weqtopathshProp.
    use weqimplimpl.
    + apply p.
    + apply q.
    + apply (pr1 R₁).
    + apply (pr1 R₂).
Qed.

Definition category_of_posets
  : category
  := total_category poset_disp_cat.

Definition is_univalent_category_of_posets
  : is_univalent category_of_posets.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_HSET.
  - exact is_univalent_poset_disp_cat.
Defined.

(**
 2. Terminal object
 *)
Definition dispTerminal_poset_disp_cat
  : dispTerminal poset_disp_cat TerminalHSET.
Proof.
  simple refine (_ ,, _).
  - exact unit_PartialOrder.
  - intros X RX.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros f g ;
         apply isaprop_is_monotone).
    + exact (λ x y p, tt).
Defined.

Definition Terminal_category_of_posets
  : Terminal category_of_posets.
Proof.
  use total_category_Terminal.
  - exact TerminalHSET.
  - exact dispTerminal_poset_disp_cat.
Defined.

(**
 3. Binary products
 *)
Definition dispBinProducts_poset_disp_cat
  : dispBinProducts poset_disp_cat BinProductsHSET.
Proof.
  intros X₁ X₂ R₁ R₂.
  simple refine ((_ ,, _) ,, _).
  - exact (prod_PartialOrder R₁ R₂).
  - split ; cbn.
    + exact (dirprod_pr1_is_monotone R₁ R₂).
    + exact (dirprod_pr2_is_monotone R₁ R₂).
  - cbn.
    intros W f g RW Hf Hg.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ;
           apply isapropdirprod ;
           apply poset_disp_cat
         | ] ;
         apply isaprop_is_monotone).
    + simple refine (_ ,, _ ,, _).
      * exact (prodtofun_is_monotone Hf Hg).
      * apply isaprop_is_monotone.
      * apply isaprop_is_monotone.
Defined.

Definition BinProducts_category_of_posets
  : BinProducts category_of_posets.
Proof.
  use total_category_Binproducts.
  - exact BinProductsHSET.
  - exact dispBinProducts_poset_disp_cat.
Defined.

(**
 4. Equalizers
 *)
Definition Equalizers_category_of_posets
  : Equalizers category_of_posets.
Proof.
  intros X Y f g.
  simple refine ((_ ,, _) ,, (_ ,, _)).
  - exact (_ ,, Equalizer_order (pr2 X) (pr1 Y) (pr1 f) (pr1 g)).
  - exact (_ ,, Equalizer_pr1_monotone (pr2 X) (pr1 Y) (pr1 f) (pr1 g)).
  - abstract
      (use eq_monotone_function ;
       intro w ; cbn in w ; cbn ;
       exact (pr2 w)).
  - simpl.
    intros W h p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use eq_monotone_function ;
         intro w ;
         use subtypePath ; [ intro ; apply (pr1 Y) | ] ;
         refine (eqtohomot (maponpaths pr1 (pr2 φ₁)) w @ !_) ;
         exact (eqtohomot (maponpaths pr1 (pr2 φ₂)) w)).
    + simple refine (_ ,, _).
      * exact (_ ,, Equalizer_map_monotone _ _ _ _ _ (pr2 h) (eqtohomot (maponpaths pr1 p))).
      * abstract
          (use eq_monotone_function ;
           intro w ;
           apply idpath).
Defined.

(**
 5. Exponentials
 *)
Definition Exponentials_category_of_posets
  : Exponentials BinProducts_category_of_posets.
Proof.
  intros X.
  use left_adjoint_from_partial.
  - exact (λ Y, _ ,, monotone_function_PartialOrder (pr2 X) (pr2 Y)).
  - exact (λ Y, eval_monotone_function (pr2 X) (pr2 Y)).
  - refine (λ Y Z f, _).
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros g₁ g₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use eq_monotone_function ; intro z ;
         use eq_monotone_function ; intro x ;
         refine (!(eqtohomot (maponpaths pr1 (pr2 g₁)) (x ,, z)) @ _) ;
         exact (eqtohomot (maponpaths pr1 (pr2 g₂)) (x ,, z))).
    + simple refine (_ ,, _).
      * exact (lam_monotone_function (pr2 X) (pr2 Y) f).
      * abstract
          (use subtypePath ; [ intro ; apply isaprop_is_monotone | ] ;
           apply idpath).
Defined.
