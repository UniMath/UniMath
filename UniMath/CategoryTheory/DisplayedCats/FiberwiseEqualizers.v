(***************************************************************************************

 Fiberwise equalizers

 In this file, we define fiberwise equalizers for fibrations. We also define when a
 displayed functor preserves fiberwise equalizers.

 Contents
 1. Fiberwise equalizers
 2. Preservation of fiberwise equalizers

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Fiberwise products *)
Definition fiberwise_equalizers
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := (∏ (x : C),
      Equalizers (D[{x}]))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_equalizer (fiber_functor_from_cleaving D HD f)).

Definition equalizer_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_equalizers HD)
           {x : C}
           {xx yy : D[{x}]}
           (ff gg : xx --> yy)
  : Equalizer ff gg
  := pr1 P x xx yy ff gg.

Definition preserves_equalizer_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : fiberwise_equalizers HD)
           {x y : C}
           (f : x --> y)
  : preserves_equalizer (fiber_functor_from_cleaving D HD f)
  := pr2 P x y f.

Proposition isaprop_fiberwise_equalizers
            {C : category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_equalizers HD).
Proof.
  use isapropdirprod.
  - do 5 (use impred ; intro).
    use isaprop_Equalizer.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_equalizer.
Qed.

(** * 2. Preservation of fiberwise equalizers *)
Definition preserves_fiberwise_binproducts
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     preserves_equalizer (fiber_functor FF x).

Proposition isaprop_preserves_fiberwise_binproducts
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_fiberwise_binproducts FF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_equalizer.
Qed.

Definition id_preserves_fiberwise_binproducts
           {C : category}
           (D : disp_cat C)
  : preserves_fiberwise_binproducts (disp_functor_identity D).
Proof.
  intros x y₁ y₂ e f g h p q H.
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
  intros x y₁ y₂ e f g h p q H.
  use (isEqualizer_eq _ _ _ _ _ (HGG _ _ _ _ _ _ _ _ _ (HFF _ _ _ _ _ _ _ _ _ H))).
  - abstract
      (cbn in q ; cbn ;
       rewrite !disp_functor_transportf ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !mor_disp_transportf_prewhisker in q ;
       rewrite !mor_disp_transportf_postwhisker ;
       rewrite !mor_disp_transportf_postwhisker in q ;
       rewrite !transport_f_f ;
       rewrite !transport_f_f in q ;
       refine (_ @ q @ _) ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (cbn ;
       rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !mor_disp_transportf_postwhisker ;
       rewrite <- !disp_functor_comp_var ;
       rewrite !transport_f_f ;
       do 2 apply maponpaths ;
       cbn in p ;
       refine (!_ @ maponpaths (λ z, transportb (λ f, _ -->[ f ] _) _ z) p @ _) ;
       apply transportbfinv).
Defined.
