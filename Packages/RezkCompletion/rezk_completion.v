
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Rezk completion

 - Construction of the Rezk completion via Yoneda

 - Universal property of the Rezk completion

************************************************************)


Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.yoneda.
Require Import RezkCompletion.sub_precategories.
Require Import RezkCompletion.equivalences.
Require Import RezkCompletion.whiskering.
Require Import RezkCompletion.precomp_fully_faithful.
Require Import RezkCompletion.precomp_ess_surj.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Construction of the Rezk completion via Yoneda *)

Section rezk.

Variable A : precategory.

Definition Rezk_completion : category.
Proof.
  exists (full_img_sub_precategory (yoneda A)).
  apply is_category_full_subcat.
  apply is_category_functor_category.
  apply is_category_HSET.
Defined.

Definition Rezk_eta : functor A Rezk_completion.
Proof.
  apply (functor_full_img (yoneda A)).
Defined.

Lemma Rezk_eta_is_fully_faithful : fully_faithful Rezk_eta.
Proof.
  apply (functor_full_img_fully_faithful_if_fun_is _ _ (yoneda A)).
  apply yoneda_fully_faithful.
Qed.

Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
Proof.
  apply (functor_full_img_essentially_surjective _ _ (yoneda A)).
Qed.

End rezk.

(** * Universal property of the Rezk completion *)

Section rezk_universal_property.

Variables A C : precategory.
Hypothesis Ccat : is_category C.

Lemma pre_comp_rezk_eta_is_fully_faithful :
    fully_faithful (pre_composition_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Qed.

Lemma pre_comp_rezk_eta_is_ess_surj :
   essentially_surjective (pre_composition_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply pre_composition_essentially_surjective.
  assumption.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Qed.

Theorem Rezk_eta_Universal_Property : 
  isweq (pre_composition_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply equiv_of_cats_is_weq_of_objects.
  apply is_category_functor_category; 
  assumption.
  apply is_category_functor_category; 
  assumption.
  
  apply rad_equivalence_of_precats.
  apply is_category_functor_category; 
  assumption.
  apply pre_comp_rezk_eta_is_fully_faithful.
  apply pre_comp_rezk_eta_is_ess_surj.
Qed.

End rezk_universal_property.
  
  














