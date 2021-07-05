(** Constructs the action of the endomorphisms by precomposition on a fixed hom-category of a bicategory

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal.

Import Bicat.Notations.

Local Open Scope cat.

Section Action_From_Precomposition.

Context {C : bicat}.
Context (c0 d0: ob C).

(* swapping is needed in the following due to the unconventional argument order of the action functor in the def. of actions *)
Local Definition Mon_endo: monoidal_precat := swapping_of_monoidal_precat (monoidal_precat_from_prebicat_and_ob c0).

Local Definition homprecat : precategory := hom c0 d0.

Definition precomp_odot : homprecat ⊠ Actions.V Mon_endo ⟶ homprecat
  := functor_composite binswap_pair_functor hcomp_functor.

Definition precomp_right_unitor_nat_trans : odot_I_functor Mon_endo precomp_odot ⟹ functor_identity homprecat
  := lunitor_transf c0 d0.

Definition precomp_right_unitor : action_right_unitor Mon_endo precomp_odot.
Proof.
  exists precomp_right_unitor_nat_trans.
  intro f. apply is_z_iso_lunitor.
Defined.

(* I would like to know how to use the library results better, but there are problems with the order of arguments *)
Definition precomp_convertor_nat_trans :
  odot_x_odot_y_functor Mon_endo precomp_odot ⟹ odot_x_otimes_y_functor Mon_endo precomp_odot.
Proof.
   use make_nat_trans.
   - intro x. cbn.
     induction x as [x12 x3]. induction x12 as [x1 x2]. cbn.
     apply lassociator.
   - red. intros x x' f.
     unfold odot_x_odot_y_functor, odot_x_otimes_y_functor, precomp_odot.
     cbn.
     apply hcomp_lassoc.
Defined.

Definition precomp_convertor : action_convertor Mon_endo precomp_odot.
Proof.
  exists precomp_convertor_nat_trans.
  intro x.
  apply is_z_iso_lassociator.
Defined.

Definition action_from_precomp : action Mon_endo.
Proof.
  exists homprecat.
  exists precomp_odot.
  exists precomp_right_unitor.
  exists precomp_convertor.
  split.
  - red. cbn. intros a x.
    rewrite hcomp_identity_right.
    rewrite hcomp_identity_left.
    apply pathsinv0. apply runitor_rwhisker.
  - red. cbn. intros a x y z.
    rewrite hcomp_identity_left.
    rewrite hcomp_identity_right.
    apply pathsinv0. apply lassociator_lassociator.
Defined.


End Action_From_Precomposition.
