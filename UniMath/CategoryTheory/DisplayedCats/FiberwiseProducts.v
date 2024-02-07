(***************************************************************************************

 Fiberwise products

 In this file, we define fiberwise binary products for fibrations. We also define when
 a displayed functor preserves fiberwise products.

 Contents
 1. Fiberwise products
 2. Preservation of fiberwise products

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Fiberwise products *)
Definition fiberwise_binproducts
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := (∏ (x : C),
      BinProducts (D[{x}]))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_binproduct (fiber_functor_from_cleaving D HD f)).

Definition binprod_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_binproducts HD)
           {x : C}
           (xx yy : D x)
  : BinProduct (D[{x}]) xx yy
  := pr1 P x xx yy.

Definition preserves_binproduct_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_binproducts HD)
           {x y : C}
           (f : x --> y)
  : preserves_binproduct (fiber_functor_from_cleaving D HD f)
  := pr2 P x y f.

Proposition isaprop_fiberwise_binproducts
            {C : category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_binproducts HD).
Proof.
  use isapropdirprod.
  - do 3 (use impred ; intro).
    use isaprop_BinProduct.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_binproduct.
Qed.

(** * 2. Preservation of fiberwise products *)
Definition preserves_fiberwise_binproducts
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     preserves_binproduct (fiber_functor FF x).

Proposition isaprop_preserves_fiberwise_binproducts
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_fiberwise_binproducts FF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_binproduct.
Qed.

Definition id_preserves_fiberwise_binproducts
           {C : category}
           (D : disp_cat C)
  : preserves_fiberwise_binproducts (disp_functor_identity D).
Proof.
  intros x y₁ y₂ z p q H.
  exact H.
Defined.

Definition comp_preserves_fiberwise_binproducts
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           (HFF : preserves_fiberwise_binproducts FF)
           {GG : disp_functor G D₂ D₃}
           (HGG : preserves_fiberwise_binproducts GG)
  : preserves_fiberwise_binproducts (disp_functor_composite FF GG).
Proof.
  intros x y₁ y₂ z p q H.
  use (isBinProduct_eq_arrow _ _ (HGG _ _ _ _ _ _ (HFF _ _ _ _ _ _ H))) ; cbn.
  - abstract
      (rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
  - abstract
      (rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
Defined.
