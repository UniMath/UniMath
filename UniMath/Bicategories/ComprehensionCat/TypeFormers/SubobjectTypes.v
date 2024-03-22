(*******************************************************************************************

 DFL Comprehension categories with subobject classifier types

 In this file, we define when a DFL comprehension category supports subobject classifier types.
 Such types are expressed by having fiberwise subobject classifiers.

 One observation in "Modular correspondence between dependent type theories and categories
 including pretopoi and topoi" by Maietti is that mono types (i.e., types `A` in context `Γ`
 such that the projection `π : Γ & A --> Γ` is a monomorphism) correspond to types for which
 we have `Γ & x : A & y : A ⊢ x = y`, which are also known as homotopy propositions. If we
 have a comprehension category with fiberwise subobject classifiers meaning that we have types
 `Γ ⊢ Ω`, then terms `Γ ⊢ A : Ω` correspond to monomorphisms and thus to homotopy propositions.
 As such, a subobject classifier functions as a universe of propositions (see the figure
 named "Alternative formulation of the Omega type" in the paper by Maietti).

 One important thing to realize here, is that we do not implement this as a local property.
 The reason for this is not conceptual, but technical. We implemented local properties via
 the displayed bicategory of fibrations, and we could instantiate that with suitable properties
 on categories. However, subobject classifier are only defined in categories equipped with
 a terminal object so that `true` can be expressed as a global element. For this reason, the
 formulation of subobject classifier types require more structure than just being a fibration.

 References
 - "Modular correspondence between dependent type theories and categories including pretopoi
   and topoi" by Maietti

 Contents
 1. The displayed bicategory of subobject_classifier types
 2. The univalence of this displayed bicategory
 3. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseSubobjectClassifier.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.

(** * 1. The displayed bicategory of subobject_classifier types *)
Definition disp_bicat_of_subobject_classifier_type
  : disp_bicat bicat_of_dfl_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : dfl_full_comp_cat),
           fiberwise_subobject_classifier
             (fiberwise_terminal_dfl_full_comp_cat C)).
  - exact (λ (C₁ C₂ : dfl_full_comp_cat)
             (T₁ : fiberwise_subobject_classifier
                     (fiberwise_terminal_dfl_full_comp_cat C₁))
             (T₂ : fiberwise_subobject_classifier
                     (fiberwise_terminal_dfl_full_comp_cat C₂))
             (F : dfl_full_comp_cat_functor C₁ C₂),
           preserves_fiberwise_subobject_classifier
             (fiberwise_terminal_dfl_full_comp_cat C₁)
             (fiberwise_terminal_dfl_full_comp_cat C₂)
             (comp_cat_type_functor F)
             (preserves_terminal_dfl_full_comp_cat_functor F)).
  - abstract
      (intros C ΩC x xx t H ;
       refine (transportf
                 (is_subobject_classifier _ _)
                 _
                 H) ;
       refine (!(id_left _) @ _) ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - abstract
      (intros C₁ C₂ C₃ ΩC₁ ΩC₂ ΩC₃ F G HF HG x xx t H ;
       pose (FF := comp_cat_type_functor (F : dfl_full_comp_cat_functor _ _)) ;
       pose (GG := comp_cat_type_functor (G : dfl_full_comp_cat_functor _ _)) ;
       refine (transportf
                 (is_subobject_classifier _ _)
                 _
                 (HG _ _ _ (HF x xx t H))) ;
       rewrite functor_comp ;
       rewrite !assoc ;
       assert (# (fiber_functor GG _) (# (fiber_functor FF _) t)
               =
               # (fiber_functor (disp_functor_composite FF GG) _) t)
         as p ;
       [ cbn ;
         rewrite disp_functor_transportf ;
         rewrite transport_f_f ;
         apply idpath
       | ] ;
       refine (maponpaths (λ z, _ · z) p @ _) ;
       apply maponpaths_2 ;
       apply (TerminalArrowEq
                (T := preserves_terminal_to_terminal
                        (fiber_functor (comp_cat_type_functor _) x)
                        (preserves_terminal_dfl_full_comp_cat_functor (F · G) x)
                        (terminal_in_fib (fiberwise_terminal_dfl_full_comp_cat C₁) x)))).
Defined.

(** * 2. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_subobject_classifier_type
  : disp_univalent_2_1 disp_bicat_of_subobject_classifier_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  apply isaprop_preserves_fiberwise_subobject_classifier.
Qed.

Definition univalent_2_0_disp_bicat_of_subobject_classifier_type
  : disp_univalent_2_0 disp_bicat_of_subobject_classifier_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
  - intro C.
    apply isaprop_fiberwise_subobject_classifier.
  - intros C₁ C₂ T₁ T₂ f.
    apply isaprop_preserves_fiberwise_subobject_classifier.
Qed.

Definition univalent_2_disp_bicat_of_subobject_classifier_type
  : disp_univalent_2 disp_bicat_of_subobject_classifier_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_subobject_classifier_type.
  - exact univalent_2_1_disp_bicat_of_subobject_classifier_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_subobject_classifier_type
  : disp_2cells_isaprop disp_bicat_of_subobject_classifier_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_subobject_classifier_type
  : disp_locally_groupoid disp_bicat_of_subobject_classifier_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type
  : disp_2cells_iscontr disp_bicat_of_subobject_classifier_type.
Proof.
  apply disp_2cells_iscontr_subbicat.
Defined.

(** * 3. Adjoint equivalences *)
Definition disp_adjoint_equiv_disp_bicat_of_subobject_classifier_type_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {T₁ : disp_bicat_of_subobject_classifier_type C₁}
           {T₂ : disp_bicat_of_subobject_classifier_type C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F T₁ T₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  - intros C T₁ T₂ FF.
    use disp_left_adjoint_equivalence_subbicat_alt.
    exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_subobject_classifier_type
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_subobject_classifier_type C₁}
           {T₂ : disp_bicat_of_subobject_classifier_type C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_subobject_classifier_type_help (F ,, HF) FF).
Defined.
