(** Constructs the action of the endomorphisms by precomposition on a fixed hom-category of a bicategory

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.Bicategories.MonoidalCategories.MonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.Actions.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Import Bicat.Notations.

Local Open Scope cat.

Section Action_From_Precomposition.

Context {C : bicat}.
Context (c0 d0: ob C).

(* swapping is needed in the following due to the unconventional argument order of the action functor in the def. of actions *)
Local Definition Mon_endo: monoidal_cat := swapping_of_monoidal_cat (monoidal_cat_from_bicat_and_ob c0).

Local Definition homcat : category := hom c0 d0.

Definition precomp_odot : homcat ⊠ Mon_endo ⟶ homcat
  := functor_composite binswap_pair_functor hcomp_functor.

Definition precomp_right_unitor_nat_trans : odot_I_functor Mon_endo homcat precomp_odot ⟹ functor_identity homcat
  := lunitor_transf c0 d0.

Definition precomp_right_unitor : action_right_unitor Mon_endo homcat precomp_odot.
Proof.
  exists precomp_right_unitor_nat_trans.
  intro f. apply is_z_iso_lunitor.
Defined.

(* I would like to know how to use the library results better, but there are problems with the order of arguments *)
Definition precomp_convertor_nat_trans_data : nat_trans_data (odot_x_odot_y_functor Mon_endo homcat precomp_odot) (odot_x_otimes_y_functor Mon_endo homcat precomp_odot).
Proof.
  intro x.
  induction x as [x12 x3]. induction x12 as [x1 x2].
  apply lassociator.
Defined.

Lemma precomp_convertor_data_is_nat_trans : is_nat_trans _ _ precomp_convertor_nat_trans_data.
Proof.
  red. intros x x' f.
  unfold odot_x_odot_y_functor, odot_x_otimes_y_functor, precomp_odot.
  cbn.
  apply hcomp_lassoc.
Qed.

Definition precomp_convertor_nat_trans :
  odot_x_odot_y_functor Mon_endo homcat precomp_odot ⟹ odot_x_otimes_y_functor Mon_endo homcat precomp_odot
  := (precomp_convertor_nat_trans_data,,precomp_convertor_data_is_nat_trans).

Definition precomp_convertor : action_convertor Mon_endo homcat precomp_odot.
Proof.
  exists precomp_convertor_nat_trans.
  intro x.
  apply is_z_iso_lassociator.
Defined.

Lemma action_from_precomp_laws :
  action_triangle_eq Mon_endo homcat precomp_odot precomp_right_unitor precomp_convertor
                     × action_pentagon_eq Mon_endo homcat precomp_odot precomp_convertor.
Proof.
  split.
  - red. cbn. intros a x.
    rewrite hcomp_identity_right.
    rewrite hcomp_identity_left.
    apply pathsinv0. apply runitor_rwhisker.
  - red. cbn. intros a x y z.
    rewrite hcomp_identity_left.
    rewrite hcomp_identity_right.
    apply pathsinv0. apply lassociator_lassociator.
Qed.

Definition action_from_precomp : action Mon_endo homcat.
Proof.
  exists precomp_odot.
  exists precomp_right_unitor.
  exists precomp_convertor.
  exact action_from_precomp_laws.
Defined.

End Action_From_Precomposition.

Section Instantiation_To_Bicategory_Of_Categories.

  Context (C D : category).

  Local Definition actfromprecomp : action (Mon_endo(C:=bicat_of_cats) C)
                                           (homcat(C:=bicat_of_cats) C D)
    := action_from_precomp(C:=bicat_of_cats) C D.


  (* the following is not possible since the notions for functor the functor are not precise instances of the bicategorical ones:
  Lemma actfromprecomp_odot_ok : pr1 actfromprecomp = binswap_pair_functor ∙ (functorial_composition C C D hs hsD).
  Proof.
    UniMath.MoreFoundations.Tactics.show_id_type.
    cbn.
    unfold precomp_odot.
    apply idpath.
   *)

  Lemma actfromprecomp_odot_pointwise_ok (g : functor C D) (f: functor C C) : pr1 actfromprecomp (g,,f) = (binswap_pair_functor ∙ (functorial_composition _ _ _)) (g,,f).
  Proof.
    cbn.
    apply idpath.
  Qed.

End Instantiation_To_Bicategory_Of_Categories.
