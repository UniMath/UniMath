(***************************************************************************************

 Fiberwise subobject classifiers

 In this file, we define fiberwise binary subobject classifiers for fibrations. We also
 define when a displayed functor preserves fiberwise subobject classifiers.

 Contents
 1. Fiberwise subobject classifiers
 2. Preservation of fiberwise subobject classifiers

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Local Open Scope cat.

(** * 1. Fiberwise subobject classifiers *)
Definition fiberwise_subobject_classifier
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (TD : fiberwise_terminal HD)
  : UU
  := (∏ (x : C), subobject_classifier (terminal_in_fib TD x))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_subobject_classifier
        (fiber_functor_from_cleaving D HD f)
        (terminal_in_fib TD y)
        (terminal_in_fib TD x)
        (preserves_terminal_in_fib TD f)).

Definition subobject_classifier_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {TD : fiberwise_terminal HD}
           (ΩD : fiberwise_subobject_classifier TD)
           (x : C)
  : subobject_classifier (terminal_in_fib TD x)
  := pr1 ΩD x.

Definition preserves_subobject_classifier_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {TD : fiberwise_terminal HD}
           (ΩD : fiberwise_subobject_classifier TD)
           {x y : C}
           (f : x --> y)
  : preserves_subobject_classifier
      (fiber_functor_from_cleaving D HD f)
      (terminal_in_fib TD y)
      (terminal_in_fib TD x)
      (preserves_terminal_in_fib TD f)
  := pr2 ΩD x y f.

Proposition isaprop_fiberwise_subobject_classifier
            {C : category}
            {D : disp_univalent_category C}
            {HD : cleaving D}
            (TD : fiberwise_terminal HD)
  : isaprop (fiberwise_subobject_classifier TD).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isaprop_subobject_classifier'.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_subobject_classifier.
Qed.

(** * 2. Preservation of fiberwise subobject classifiers *)
Definition preserves_fiberwise_subobject_classifier
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {HD₁ : cleaving D₁}
           {HD₂ : cleaving D₂}
           (TD₁ : fiberwise_terminal HD₁)
           (TD₂ : fiberwise_terminal HD₂)
           (FF : disp_functor F D₁ D₂)
           (HFF : preserves_fiberwise_terminal FF)
  : UU
  := ∏ (x : C₁),
     preserves_subobject_classifier
       (fiber_functor FF x)
       (terminal_in_fib TD₁ x)
       (terminal_in_fib TD₂ (F x))
       (HFF x).

Proposition isaprop_preserves_fiberwise_subobject_classifier
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {HD₁ : cleaving D₁}
            {HD₂ : cleaving D₂}
            (TD₁ : fiberwise_terminal HD₁)
            (TD₂ : fiberwise_terminal HD₂)
            (FF : disp_functor F D₁ D₂)
            (HFF : preserves_fiberwise_terminal FF)
  : isaprop (preserves_fiberwise_subobject_classifier TD₁ TD₂ FF HFF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_subobject_classifier.
Qed.

Definition id_preserves_fiberwise_subobject_classifier
           {C : category}
           (D : disp_cat C)
           (HD : cleaving D)
           (TD : fiberwise_terminal HD)
  : preserves_fiberwise_subobject_classifier
      TD TD
      (disp_functor_identity D)
      (id_preserves_fiberwise_terminal D).
Proof.
  intros x xx t H.
  refine (transportf
            (is_subobject_classifier _ _)
            _
            H).
  refine (!(id_left _) @ _).
  apply maponpaths_2.
  apply TerminalArrowEq.
Qed.

Definition comp_preserves_fiberwise_subobject_classifier
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {HD₁ : cleaving D₁}
           {HD₂ : cleaving D₂}
           {HD₃ : cleaving D₃}
           {TD₁ : fiberwise_terminal HD₁}
           {TD₂ : fiberwise_terminal HD₂}
           {TD₃ : fiberwise_terminal HD₃}
           {FF : disp_functor F D₁ D₂}
           {HFF₁ : preserves_fiberwise_terminal FF}
           (HFF₂ : preserves_fiberwise_subobject_classifier
                     TD₁ TD₂
                     FF
                     HFF₁)
           {GG : disp_functor G D₂ D₃}
           {HGG₁ : preserves_fiberwise_terminal GG}
           (HGG₂ : preserves_fiberwise_subobject_classifier
                     TD₂ TD₃
                     GG
                     HGG₁)
  : preserves_fiberwise_subobject_classifier
      TD₁ TD₃
      (disp_functor_composite FF GG)
      (comp_preserves_fiberwise_terminal HFF₁ HGG₁).
Proof.
  intros x xx t H.
  refine (transportf
            (is_subobject_classifier _ _)
            _
            (HGG₂ _ _ _ (HFF₂ x xx t H))).
  rewrite functor_comp.
  rewrite !assoc.
  assert (# (fiber_functor GG (F x)) (# (fiber_functor FF x) t)
          =
          # (fiber_functor (disp_functor_composite FF GG) x) t)
    as p.
  {
    cbn.
    rewrite disp_functor_transportf.
    rewrite transport_f_f.
    apply idpath.
  }
  etrans.
  {
    apply maponpaths.
    exact p.
  }
  apply maponpaths_2.
  apply (TerminalArrowEq
           (T := preserves_terminal_to_terminal
                   (fiber_functor (disp_functor_composite FF GG) x)
                   (comp_preserves_fiberwise_terminal HFF₁ HGG₁ x)
                   (terminal_in_fib TD₁ x))).
Qed.
