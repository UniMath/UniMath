(***************************************************************************************

 Fiberwise coproducts

 In this file, we define fiberwise binary coproducts for fibrations. We also define when
 a displayed functor preserves fiberwise coproducts.

 Contents
 1. Fiberwise coproducts
 2. Preservation of fiberwise coproducts

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Fiberwise products *)
Definition fiberwise_bincoproducts
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := (∏ (x : C),
      BinCoproducts (D[{x}]))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_bincoproduct (fiber_functor_from_cleaving D HD f)).

Definition bincoprod_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_bincoproducts HD)
           {x : C}
           (xx yy : D x)
  : @BinCoproduct (D[{x}]) xx yy
  := pr1 P x xx yy.

Definition preserves_bincoproduct_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_bincoproducts HD)
           {x y : C}
           (f : x --> y)
  : preserves_bincoproduct (fiber_functor_from_cleaving D HD f)
  := pr2 P x y f.

Proposition isaprop_fiberwise_bincoproducts
            {C : category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_bincoproducts HD).
Proof.
  use isapropdirprod.
  - do 3 (use impred ; intro).
    use isaprop_BinCoproduct.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_bincoproduct.
Qed.

Section FiberwiseBinCoproductPoset.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          (HD' : locally_propositional D)
          (or : ∏ (Γ : C), D[{Γ}] → D[{Γ}] → D[{Γ}])
          (or_in1 : ∏ (Γ : C) (φ ψ : D[{Γ}]),
                    φ -->[ identity _ ] or _ φ ψ)
          (or_in2 : ∏ (Γ : C) (φ ψ : D[{Γ}]),
                    ψ -->[ identity _ ] or _ φ ψ)
          (or_out : ∏ (Γ : C)
                      (φ ψ χ : D[{Γ}])
                      (p₁ : φ --> χ)
                      (p₂ : ψ --> χ),
                    or Γ φ ψ --> χ)
          (or_sub : ∏ (Γ₁ Γ₂ : C)
                      (s : Γ₁ --> Γ₂)
                      (φ ψ : D[{Γ₂}]),
                    pr1 (HD Γ₂ Γ₁ s (or Γ₂ φ ψ))
                    =
                    or Γ₁ (pr1 (HD Γ₂ Γ₁ s φ)) (pr1 (HD Γ₂ Γ₁ s ψ))).

  Definition make_bincoproduct_fiber_locally_propositional
             (Γ : C)
    : BinCoproducts D[{Γ}].
  Proof.
    intros φ ψ.
    use make_BinCoproduct.
    - exact (or Γ φ ψ).
    - exact (or_in1 Γ φ ψ).
    - exact (or_in2 Γ φ ψ).
    - intros χ p₁ p₂.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros q₁ q₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           apply HD').
      + simple refine (_ ,, _ ,, _) ; [ | apply HD' | apply HD' ].
        exact (or_out Γ φ ψ χ p₁ p₂).
  Defined.

  Definition make_fiberwise_bincoproducts_locally_propositional
    : fiberwise_bincoproducts HD.
  Proof.
    split.
    - exact make_bincoproduct_fiber_locally_propositional.
    - intros Γ₁ Γ₂ s.
      use preserves_bincoproduct_if_preserves_chosen.
      + apply make_bincoproduct_fiber_locally_propositional.
      + abstract
          (intros φ ψ ;
           use (isBinCoproduct_z_iso
                  (isBinCoproduct_BinCoproduct
                     _
                     (make_bincoproduct_fiber_locally_propositional
                        Γ₁
                        (fiber_functor_from_cleaving D HD s φ)
                        (fiber_functor_from_cleaving D HD s ψ)))) ;
           [ | apply HD' | apply HD' ] ;
           use idtoiso ;
           cbn ;
           refine (!_) ;
           apply or_sub).
  Defined.
End FiberwiseBinCoproductPoset.

(** * 2. Preservation of fiberwise coproducts *)
Definition preserves_fiberwise_bincoproducts
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     preserves_bincoproduct (fiber_functor FF x).

Proposition isaprop_preserves_fiberwise_bincoproducts
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_fiberwise_bincoproducts FF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_bincoproduct.
Qed.

Definition id_preserves_fiberwise_bincoproducts
           {C : category}
           (D : disp_cat C)
  : preserves_fiberwise_bincoproducts (disp_functor_identity D).
Proof.
  intros x y₁ y₂ z p q H.
  exact H.
Defined.

Definition comp_preserves_fiberwise_bincoproducts
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           (HFF : preserves_fiberwise_bincoproducts FF)
           {GG : disp_functor G D₂ D₃}
           (HGG : preserves_fiberwise_bincoproducts GG)
  : preserves_fiberwise_bincoproducts (disp_functor_composite FF GG).
Proof.
  intros x y₁ y₂ z p q H.
  use (isBinCoproduct_eq_arrow _ _ (HGG _ _ _ _ _ _ (HFF _ _ _ _ _ _ H))) ; cbn.
  - abstract
      (rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
  - abstract
      (rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
Defined.
