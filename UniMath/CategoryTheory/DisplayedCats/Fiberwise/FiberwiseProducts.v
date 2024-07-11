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

Section FiberwiseBinProductPoset.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          (HD' : locally_propositional D)
          (and : ∏ (Γ : C), D[{Γ}] → D[{Γ}] → D[{Γ}])
          (and_pr1 : ∏ (Γ : C) (φ ψ : D[{Γ}]),
                     and _ φ ψ -->[ identity _ ] φ)
          (and_pr2 : ∏ (Γ : C) (φ ψ : D[{Γ}]),
                     and _ φ ψ -->[ identity _ ] ψ)
          (and_in : ∏ (Γ : C) (φ ψ χ : D[{Γ}]),
                    χ -->[ identity _ ] φ
                    → χ -->[ identity _ ] ψ
                    → χ -->[ identity _ ] and _ φ ψ)
          (and_sub : ∏ (Γ₁ Γ₂ : C)
                       (s : Γ₁ --> Γ₂)
                       (φ ψ : D[{Γ₂}]),
                     and Γ₁ (pr1 (HD Γ₂ Γ₁ s φ)) (pr1 (HD Γ₂ Γ₁ s ψ))
                     -->
                     pr1 (HD Γ₂ Γ₁ s (and Γ₂ φ ψ))).

  Definition make_binproduct_fiber_locally_propositional
             (Γ : C)
    : BinProducts D[{Γ}].
  Proof.
    intros φ ψ.
    use make_BinProduct.
    - exact (and Γ φ ψ).
    - exact (and_pr1 Γ φ ψ).
    - exact (and_pr2 Γ φ ψ).
    - intros χ p₁ p₂.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros q₁ q₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           apply HD').
      + simple refine (_ ,, _ ,, _) ; [ | apply HD' | apply HD' ].
        exact (and_in Γ φ ψ χ p₁ p₂).
  Defined.

  Definition make_fiberwise_binproducts_locally_propositional
    : fiberwise_binproducts HD.
  Proof.
    split.
    - exact make_binproduct_fiber_locally_propositional.
    - intros Γ₁ Γ₂ s.
      use preserves_binproduct_if_preserves_chosen.
      + apply make_binproduct_fiber_locally_propositional.
      + abstract
          (intros φ ψ ;
           use (isBinProduct_z_iso
                  (isBinProduct_BinProduct
                     _
                     (make_binproduct_fiber_locally_propositional
                        Γ₁
                        (fiber_functor_from_cleaving D HD s φ)
                        (fiber_functor_from_cleaving D HD s ψ)))) ;
           [ | apply HD' | apply HD' ] ;
           use make_z_iso ; [ | apply and_sub | split ; apply HD' ] ;
           apply BinProductArrow ;
           [ exact (#(fiber_functor_from_cleaving D HD s) (BinProductPr1 _ _))
           | exact (#(fiber_functor_from_cleaving D HD s) (BinProductPr2 _ _)) ]).
  Defined.
End FiberwiseBinProductPoset.

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
