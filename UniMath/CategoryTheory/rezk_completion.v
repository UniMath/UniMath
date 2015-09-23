
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Rezk completion

 - Construction of the Rezk completion via Yoneda

 - Universal property of the Rezk completion

************************************************************)


Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.hProp.
Require Import UniMath.Foundations.hSet.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.precomp_fully_faithful.
Require Import UniMath.CategoryTheory.precomp_ess_surj.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Construction of the Rezk completion via Yoneda *)

Section rezk.

Variable A : precategory.
Hypothesis hsA: has_homsets A.

Definition Rezk_completion : category.
Proof.
  exists (full_img_sub_precategory (yoneda A hsA)).
  apply is_category_full_subcat.
  apply is_category_functor_category.
Defined.

Definition Rezk_eta : functor A Rezk_completion.
Proof.
  apply (functor_full_img (yoneda A hsA)).
Defined.

Lemma Rezk_eta_is_fully_faithful : fully_faithful Rezk_eta.
Proof.
  apply (functor_full_img_fully_faithful_if_fun_is _ _ (yoneda A hsA)).
  apply yoneda_fully_faithful.
Defined.

Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
Proof.
  apply (functor_full_img_essentially_surjective _ _ (yoneda A hsA)).
Defined.

End rezk.

(** * Universal property of the Rezk completion *)

Section rezk_universal_property.

Variables A C : precategory.
Hypothesis hsA: has_homsets A.
Hypothesis Ccat : is_category C.

Lemma pre_comp_rezk_eta_is_fully_faithful :
    fully_faithful (pre_composition_functor A (Rezk_completion A hsA) C 
                (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat) ((Rezk_eta A hsA))).
Proof.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Defined.

Lemma pre_comp_rezk_eta_is_ess_surj :
   essentially_surjective (pre_composition_functor A (Rezk_completion A hsA) C 
   (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat)
   (Rezk_eta A hsA)).
Proof.
  apply pre_composition_essentially_surjective.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Defined.

Theorem Rezk_eta_Universal_Property : 
  isweq (pre_composition_functor A (Rezk_completion A hsA) C 
   (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat) (Rezk_eta A hsA)).
Proof.
  apply (equiv_of_cats_is_weq_of_objects _ _ (functor_category_has_homsets _ _ _  )
                                         (functor_category_has_homsets _ _ _ )).
  - apply is_category_functor_category; 
    assumption.
  - apply is_category_functor_category; 
    assumption. 
  - pose (T:=@rad_equivalence_of_precats 
           [Rezk_completion A hsA, C, pr2 Ccat]
           [A, C, pr2 Ccat]
           (is_category_functor_category _ _ _ )
           _ 
           (pre_comp_rezk_eta_is_fully_faithful)
           (pre_comp_rezk_eta_is_ess_surj)).
  apply T.
Defined.

End rezk_universal_property.
  
  














