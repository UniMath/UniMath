(***************************************************************************************

 Fiberwise initial objects

 A fibration has a fiberwise initial object if
 - Every fiber has a initial object
 - These initial objects are preserved under reindexing
 In this file, we define the notion of fiberwise initial objects.

 We also define when a displayed functor preserves fiberwise initial objects. For this,
 it suffices to say that it preserves initial objects for every fiber.

 Contents
 1. Fiberwise initial objects
 2. Preservation of fiberwise initial objects

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Fiberwise initial objects *)
Definition fiberwise_initial
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := (∏ (x : C),
      Initial (D[{x}]))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_initial (fiber_functor_from_cleaving D HD f)).

Definition initial_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_initial HD)
           (x : C)
  : Initial (D[{x}])
  := pr1 T x.

Definition initial_obj_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_initial HD)
           (x : C)
  : D[{x}]
  := initial_in_fib T x.

Definition isInitial_initial_obj_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_initial HD)
           (x : C)
  : isInitial _ (initial_obj_in_fib T x)
  := pr2 (pr1 T x).

Definition preserves_initial_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_initial HD)
           {x y : C}
           (f : x --> y)
  : preserves_initial (fiber_functor_from_cleaving D HD f)
  := pr2 T x y f.

Definition lift_initial_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_initial HD)
           {x y : C}
           (f : x --> y)
  : Initial (D[{x}])
  := make_Initial
       _
       (preserves_initial_in_fib T f _ (isInitial_initial_obj_in_fib T y)).

Proposition isaprop_fiberwise_initial
            {C : category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_initial HD).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isaprop_Initial.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_initial.
Qed.

Section FiberwiseInitialPoset.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          (HD' : locally_propositional D)
          (false : ∏ (Γ : C), D[{Γ}])
          (false_out : ∏ (Γ : C) (φ : D[{Γ}]), false Γ -->[ identity _ ] φ)
          (false_sub : ∏ (Γ₁ Γ₂ : C) (s : Γ₁ --> Γ₂),
                       false Γ₁ = pr1 (HD Γ₂ Γ₁ s (false Γ₂))).

  Definition make_initial_fiber_locally_propositional
             (Γ : C)
    : Initial D[{Γ}].
  Proof.
    use make_Initial.
    - exact (false Γ).
    - intros φ.
      use iscontraprop1.
      + apply HD'.
      + apply false_out.
  Defined.

  Definition make_fiberwise_initial_locally_propositional
    : fiberwise_initial HD.
  Proof.
    split.
    - exact make_initial_fiber_locally_propositional.
    - intros Γ₁ Γ₂ s.
      use preserves_initial_if_preserves_chosen.
      + apply make_initial_fiber_locally_propositional.
      + abstract
          (unfold preserves_chosen_initial ;
           use (iso_to_Initial
                  (make_initial_fiber_locally_propositional Γ₁)) ;
           use idtoiso ;
           apply false_sub).
  Defined.
End FiberwiseInitialPoset.

(** * 2. Preservation of fiberwise initial objects *)
Definition preserves_fiberwise_initial
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     preserves_initial (fiber_functor FF x).

Proposition isaprop_preserves_fiberwise_initial
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_fiberwise_initial FF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_initial.
Qed.

Definition id_preserves_fiberwise_initial
           {C : category}
           (D : disp_cat C)
  : preserves_fiberwise_initial (disp_functor_identity D).
Proof.
  intros x y Hy.
  exact Hy.
Defined.

Definition comp_preserves_fiberwise_initial
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           (HFF : preserves_fiberwise_initial FF)
           {GG : disp_functor G D₂ D₃}
           (HGG : preserves_fiberwise_initial GG)
  : preserves_fiberwise_initial (disp_functor_composite FF GG).
Proof.
  intros x y Hy ; cbn.
  apply HGG.
  apply HFF.
  exact Hy.
Defined.
