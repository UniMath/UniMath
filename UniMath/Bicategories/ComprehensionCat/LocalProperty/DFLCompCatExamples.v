(**

 Local properties in DFL full comprehension categories

 Local properties are used to express that a comprehension categories support a certain
 type former. For instance, fiberwise initial objects are used to express that a
 comprehension category is equipped with an empty types, and fiberwise regularity is used
 to express that a comprehension is equipped with a propositional truncation operation.
 In this file, we give accessors for comprehension categories that support some local
 property. Specifically, we look at the type former, preservation under substitution, and
 functoriality operations.

 Contents
 1. Accessors for basic constructions of local properties
 2. Accessors for DFL comprehension categories with a fiberwise strict initial object
 3. Accessors for DFL comprehension categories with fiberwise binary coproducts
 4. Accessors for DFL comprehension categories with a fiberwise subobject classifier
 5. Accessors for DFL comprehension categories with a fiberwise parameterized NNO
 6. Accessors for DFL comprehension categories that are fiberwise regular

                                                                                         *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Accessors for basic constructions of local properties *)
Definition local_property_conj_left
           {C : dfl_full_comp_cat}
           {P₁ P₂ : local_property}
           (HC : fiberwise_cat_property
                   (local_property_conj P₁ P₂)
                   C)
  : fiberwise_cat_property P₁ C.
Proof.
  use make_fiberwise_cat_property.
  - exact (λ Γ, pr1 (fiberwise_cat_property_ob HC Γ)).
  - exact (λ Γ Δ s, pr1 (fiberwise_cat_property_mor HC s)).
Defined.

Definition local_property_conj_right
           {C : dfl_full_comp_cat}
           {P₁ P₂ : local_property}
           (HC : fiberwise_cat_property
                   (local_property_conj P₁ P₂)
                   C)
  : fiberwise_cat_property P₂ C.
Proof.
  use make_fiberwise_cat_property.
  - exact (λ Γ, pr2 (fiberwise_cat_property_ob HC Γ)).
  - exact (λ Γ Δ s, pr2 (fiberwise_cat_property_mor HC s)).
Defined.

Definition local_property_sub_left
           {C : dfl_full_comp_cat}
           {P : local_property}
           {Q : sub_property_of_local_property P}
           (HC : fiberwise_cat_property
                   (sub_local_property P Q)
                   C)
  : fiberwise_cat_property P C.
Proof.
  use make_fiberwise_cat_property.
  - exact (λ Γ, pr1 (fiberwise_cat_property_ob HC Γ)).
  - exact (λ Γ Δ s, fiberwise_cat_property_mor HC s).
Defined.

Definition local_property_sub_right
           {C : dfl_full_comp_cat}
           {P : local_property}
           {Q : sub_property_of_local_property P}
           (HC : fiberwise_cat_property
                   (sub_local_property P Q)
                   C)
           (Γ : C)
  : Q (dfl_full_comp_cat_fiber Γ) (fiberwise_cat_property_ob (local_property_sub_left HC) Γ)
  := pr2 (fiberwise_cat_property_ob HC Γ).

Definition local_property_functor_conj_left
           {C₁ C₂ : dfl_full_comp_cat}
           {P₁ P₂ : local_property}
           {HC₁ : fiberwise_cat_property
                    (local_property_conj P₁ P₂)
                    C₁}
           {HC₂ : fiberwise_cat_property
                    (local_property_conj P₁ P₂)
                    C₂}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : fiberwise_cat_property_functor F HC₁ HC₂)
  : fiberwise_cat_property_functor
      F
      (local_property_conj_left HC₁)
      (local_property_conj_left HC₂)
  := λ Γ, pr1 (HF Γ).

Definition local_property_functor_conj_right
           {C₁ C₂ : dfl_full_comp_cat}
           {P₁ P₂ : local_property}
           {HC₁ : fiberwise_cat_property
                    (local_property_conj P₁ P₂)
                    C₁}
           {HC₂ : fiberwise_cat_property
                    (local_property_conj P₁ P₂)
                    C₂}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : fiberwise_cat_property_functor F HC₁ HC₂)
  : fiberwise_cat_property_functor
      F
      (local_property_conj_right HC₁)
      (local_property_conj_right HC₂)
  := λ Γ, pr2 (HF Γ).

Definition local_property_functor_sub_left
           {C₁ C₂ : dfl_full_comp_cat}
           {P : local_property}
           {Q : sub_property_of_local_property P}
           {HC₁ : fiberwise_cat_property
                    (sub_local_property P Q)
                    C₁}
           {HC₂ : fiberwise_cat_property
                    (sub_local_property P Q)
                    C₂}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : fiberwise_cat_property_functor F HC₁ HC₂)
  : fiberwise_cat_property_functor
      F
      (local_property_sub_left HC₁)
      (local_property_sub_left HC₂)
  := HF.

(** * 2. Accessors for DFL comprehension categories with a fiberwise strict initial object *)
Definition strict_initial_local_property_strict_initial
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   strict_initial_local_property
                   C)
           (Γ : C)
  : strict_initial_object (dfl_full_comp_cat_fiber Γ)
  := fiberwise_cat_property_ob HC Γ.

Definition strict_initial_local_property_empty
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   strict_initial_local_property
                   C)
           (Γ : C)
  : ty Γ
  := InitialObject (strict_initial_local_property_strict_initial HC Γ).

Proposition initial_local_property_subst_preserve_initial
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property
                   strict_initial_local_property
                   C)
            {Γ Δ : C}
            (s : Γ --> Δ)
  : preserves_initial (dfl_full_comp_cat_fiber_functor s).
Proof.
  exact (fiberwise_cat_property_mor HC s).
Qed.

Definition initial_local_property_subst_z_iso
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   strict_initial_local_property
                   C)
           {Γ Δ : C}
           (s : Γ --> Δ)
  : z_iso
      (C := fiber_category _ _)
      (strict_initial_local_property_empty HC Δ [[ s ]])
      (strict_initial_local_property_empty HC Γ).
Proof.
  apply (preserves_initial_to_z_iso
           _
           (initial_local_property_subst_preserve_initial HC s)).
Defined.

(** * 3. Accessors for DFL comprehension categories with fiberwise binary coproducts *)
Definition coprod_local_property_bincoproduct
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           (A B : ty Γ)
  : BinCoproduct (C := fiber_category _ _) A B
  := pr1 (fiberwise_cat_property_ob HC Γ) A B.

Definition coprod_local_property_sum
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           (A B : ty Γ)
  : ty Γ
  := BinCoproductObject (coprod_local_property_bincoproduct HC A B).

Definition coprod_local_property_inl
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           (A B : ty Γ)
           (t : tm Γ A)
  : tm Γ (coprod_local_property_sum HC A B).
Proof.
  use make_comp_cat_tm.
  - exact (t · comp_cat_comp_mor
                 (BinCoproductIn1 (coprod_local_property_bincoproduct HC A B))).
  - abstract
      (rewrite !assoc' ;
       rewrite comp_cat_comp_mor_comm ;
       apply comp_cat_tm_eq).
Defined.

Definition coprod_local_property_inr
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           (A B : ty Γ)
           (t : tm Γ B)
  : tm Γ (coprod_local_property_sum HC A B).
Proof.
  use make_comp_cat_tm.
  - exact (t · comp_cat_comp_mor
                 (BinCoproductIn2 (coprod_local_property_bincoproduct HC A B))).
  - abstract
      (rewrite !assoc' ;
       rewrite comp_cat_comp_mor_comm ;
       apply comp_cat_tm_eq).
Defined.

Definition coprod_local_property_sum_functor
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           {A A' B B' : ty Γ}
           (f : A <: A')
           (g : B <: B')
  : coprod_local_property_sum HC A B <: coprod_local_property_sum HC A' B'.
Proof.
  use BinCoproductArrow.
  - exact (f · BinCoproductIn1 _).
  - exact (g · BinCoproductIn2 _).
Defined.

Definition coprod_local_property_sum_functor_on_id
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           (A B : ty Γ)
  : coprod_local_property_sum_functor HC (identity _) (identity _)
    =
    identity (C := fiber_category _ _) (coprod_local_property_sum HC A B).
Proof.
  unfold coprod_local_property_sum_functor.
  use BinCoproductArrowsEq.
  - rewrite BinCoproductIn1Commutes.
    rewrite id_left, id_right.
    apply idpath.
  - rewrite BinCoproductIn2Commutes.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Definition coprod_local_property_sum_functor_on_comp
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           {A₁ A₂ A₃ B₁ B₂ B₃ : ty Γ}
           (f₁ : A₁ <: A₂)
           (f₂ : A₂ <: A₃)
           (g₁ : B₁ <: B₂)
           (g₂ : B₂ <: B₃)
  : coprod_local_property_sum_functor HC (f₁ · f₂) (g₁ · g₂)
    =
    coprod_local_property_sum_functor HC f₁ g₁
    · coprod_local_property_sum_functor HC f₂ g₂.
Proof.
  unfold coprod_local_property_sum_functor.
  use BinCoproductArrowsEq.
  - rewrite !assoc.
    rewrite !BinCoproductIn1Commutes.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply BinCoproductIn1Commutes.
    }
    rewrite !assoc'.
    rewrite BinCoproductIn1Commutes.
    apply idpath.
  - rewrite !assoc.
    rewrite !BinCoproductIn2Commutes.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply BinCoproductIn2Commutes.
    }
    rewrite !assoc'.
    rewrite BinCoproductIn2Commutes.
    apply idpath.
Qed.

Proposition coprod_local_property_subst_preserve_bincoproduct
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
            {Γ Δ : C}
            (s : Γ --> Δ)
  : preserves_bincoproduct (dfl_full_comp_cat_fiber_functor s).
Proof.
  exact (fiberwise_cat_property_mor HC s).
Qed.

Definition coprod_local_property_subst_z_iso
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A B : ty Δ)
  : z_iso
      (C := fiber_category _ _)
      ((coprod_local_property_sum HC A B) [[ s ]])
      (coprod_local_property_sum HC (A [[ s ]]) (B [[ s ]])).
Proof.
  exact (preserves_bincoproduct_to_z_iso
           _
           (coprod_local_property_subst_preserve_bincoproduct HC s)
           (coprod_local_property_bincoproduct HC A B)
           (coprod_local_property_bincoproduct HC (A [[ s ]]) (B [[ s ]]))).
Defined.

(** * 4. Accessors for DFL comprehension categories with a fiberwise subobject classifier *)
Definition subobj_classifier_local_property_subobj_classifier
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   subobject_classifier_local_property
                   C)
           (Γ : C)
  : subobject_classifier
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ))
  := fiberwise_cat_property_ob HC Γ.

Definition subobj_classifier_local_property_type
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   subobject_classifier_local_property
                   C)
           (Γ : C)
  : ty Γ
  := subobject_classifier_object (subobj_classifier_local_property_subobj_classifier HC Γ).

Proposition subobj_classifier_local_property_preserves_subobj_classifier
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property
                   subobject_classifier_local_property
                   C)
            {Γ Δ : C}
            (s : Γ --> Δ)
  : preserves_subobject_classifier
      _
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber Δ))
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ))
      (functor_finlim_preserves_terminal (dfl_full_comp_cat_fiber_functor s)).
Proof.
  exact (fiberwise_cat_property_mor HC s).
Qed.

Definition subobj_classifier_local_property_subst_z_iso
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   subobject_classifier_local_property
                   C)
           {Γ Δ : C}
           (s : Γ --> Δ)
  : z_iso
      (C := fiber_category _ _)
      (subobj_classifier_local_property_type HC Δ [[ s ]])
      (subobj_classifier_local_property_type HC Γ).
Proof.
  apply (preserves_subobject_classifier_z_iso
           (subobj_classifier_local_property_preserves_subobj_classifier HC s)).
Defined.

(** * 5. Accessors for DFL comprehension categories with a fiberwise parameterized NNO *)
Definition pnno_local_property_pnno
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   parameterized_NNO_local_property
                   C)
           (Γ : C)
  : parameterized_NNO
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ))
      (binproducts_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ))
  := fiberwise_cat_property_ob HC Γ.

Definition pnno_local_property_type
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   parameterized_NNO_local_property
                   C)
           (Γ : C)
  : ty Γ
  := parameterized_NNO_carrier (pnno_local_property_pnno HC Γ).

Proposition pnno_local_property_preserves_pnno
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property
                   parameterized_NNO_local_property
                   C)
            {Γ Δ : C}
            (s : Γ --> Δ)
  : preserves_parameterized_NNO
      (pnno_local_property_pnno HC Δ)
      (pnno_local_property_pnno HC Γ)
      _
      (functor_finlim_preserves_terminal (dfl_full_comp_cat_fiber_functor s)).
Proof.
  exact (fiberwise_cat_property_mor HC s).
Qed.

Definition pnno_local_property_subst_z_iso
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   parameterized_NNO_local_property
                   C)
           {Γ Δ : C}
           (s : Γ --> Δ)
  : z_iso
      (C := fiber_category _ _)
      (pnno_local_property_type HC Δ [[ s ]])
      (pnno_local_property_type HC Γ).
Proof.
  use z_iso_inv.
  refine (_ ,, _).
  exact (pnno_local_property_preserves_pnno HC s).
Defined.

(** * 6. Accessors for DFL comprehension categories that are fiberwise regular *)
Definition regular_local_property_fiber_regular
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           (Γ : C)
  : is_regular_category (dfl_full_comp_cat_fiber Γ).
Proof.
  repeat split.
  - exact (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ)).
  - exact (pullbacks_univ_cat_with_finlim (dfl_full_comp_cat_fiber Γ)).
  - exact (pr1 (fiberwise_cat_property_ob HC Γ)).
  - exact (pr2 (fiberwise_cat_property_ob HC Γ)).
Defined.

Proposition regular_local_property_subst_preserves_regular_epi
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {A B : ty Δ}
            {f : A <: B}
            (Hf : is_regular_epi f)
  : is_regular_epi (#(dfl_full_comp_cat_fiber_functor s) f).
Proof.
  exact (fiberwise_cat_property_mor HC s _ _ _ Hf).
Qed.

Definition regular_local_property_subst_preserves_monic
           {C : dfl_full_comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           {A B : ty Δ}
           (f : Monic (fiber_category _ _) A B)
  : Monic (fiber_category _ _) (A [[ s ]]) (B [[ s ]])
  := functor_preserves_pb_on_monic
       (functor_finlim_preserves_pullback (dfl_full_comp_cat_fiber_functor s))
       f.

Definition regular_local_property_trunc
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           (A : ty Γ)
  : ty Γ
  := regular_category_im
       (regular_local_property_fiber_regular HC Γ)
       (TerminalArrow
          (dfl_full_comp_cat_terminal (Γ : C))
          A).

Proposition is_hprop_ty_trunc
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ : C}
            (A : ty Γ)
  : is_hprop_ty (regular_local_property_trunc HC A).
Proof.
  use mono_ty_to_hprop_ty.
  use subsingleton_to_mono_ty.
  refine (transportf
            (λ f, isMonic f)
            _
            (MonicisMonic
               _
               (regular_category_im_Monic
                  (regular_local_property_fiber_regular HC Γ)
                  (TerminalArrow
                     (dfl_full_comp_cat_terminal (Γ : C))
                     A)))).
  apply TerminalArrowEq.
Qed.

Definition regular_local_property_trunc_stable
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : ty Δ)
  : (regular_local_property_trunc HC A) [[ s ]]
    <:
    regular_local_property_trunc HC (A [[ s ]]).
Proof.
  pose (H := regular_local_property_fiber_regular HC Γ).
  pose (regular_local_property_subst_preserves_regular_epi
          HC
          s
          (is_regular_epi_regular_category_to_im
             (regular_local_property_fiber_regular HC Δ)
             (TerminalArrow
                (dfl_full_comp_cat_terminal (Δ : C))
                A)))
    as Hf.
  use (pr11 (is_strong_epi_regular_epi
               Hf
               _ _
               (regular_category_im_Monic _ _)
               _ _ _
               (MonicisMonic _ _))).
  - apply regular_category_to_im.
  - apply TerminalArrow.
  - apply TerminalArrowEq.
Defined.

Definition regular_local_property_trunc_stable_inv
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : ty Δ)
  : regular_local_property_trunc HC (A [[ s ]])
    <:
    (regular_local_property_trunc HC A) [[ s ]].
Proof.
  pose (is_regular_epi_regular_category_to_im
          (regular_local_property_fiber_regular HC Γ)
          (TerminalArrow
             (dfl_full_comp_cat_terminal (Γ : C))
             (A [[ s ]])))
    as Hf.
  pose (regular_local_property_subst_preserves_monic
          s
          (regular_category_im_Monic
             (regular_local_property_fiber_regular HC Δ)
             (TerminalArrow
                (dfl_full_comp_cat_terminal (Δ : C))
                A)))
    as m.
  pose (preserves_terminal_to_terminal
          _
          (functor_finlim_preserves_terminal (dfl_full_comp_cat_fiber_functor s))
          (dfl_full_comp_cat_terminal (Δ : C)))
    as T.
  use (pr11 (is_strong_epi_regular_epi
               Hf
               _ _
               m
               _ _ _
               (MonicisMonic _ _))).
  - use coerce_subst_ty.
    apply regular_category_to_im.
  - apply (TerminalArrow T).
  - apply (TerminalArrowEq (T := T)).
Defined.

Definition regular_local_property_trunc_functor
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           {A B : ty Γ}
           (f : A <: B)
  : regular_local_property_trunc HC A
    <:
    regular_local_property_trunc HC B.
Proof.
  use regular_category_im_map.
  - exact f.
  - apply identity.
  - abstract
      (apply TerminalArrowEq).
Defined.

Proposition regular_local_property_trunc_id
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ : C}
            (A : ty Γ)
  : regular_local_property_trunc_functor HC (identity (C := fiber_category _ _) A)
    =
    identity _.
Proof.
  apply regular_category_im_map_on_id.
Qed.

Definition regular_local_property_trunc_functor_comp
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           {A₁ A₂ A₃ : ty Γ}
           (f : A₁ <: A₂)
           (g : A₂ <: A₃)
  : regular_local_property_trunc_functor HC (f · g)
    =
    regular_local_property_trunc_functor HC f
    · regular_local_property_trunc_functor HC g.
Proof.
  refine (!_).
  unfold regular_local_property_trunc_functor.
  etrans.
  {
    use (regular_category_im_map_on_comp _).
    apply TerminalArrowEq.
  }
  use (regular_category_mor_to_im_eq (regular_local_property_fiber_regular HC _)).
  - exact (f · g).
  - apply identity.
  - apply TerminalArrowEq.
  - apply TerminalArrowEq.
  - apply TerminalArrowEq.
  - rewrite regular_category_im_map_right.
    apply idpath.
  - rewrite regular_category_im_map_right.
    apply idpath.
Qed.
