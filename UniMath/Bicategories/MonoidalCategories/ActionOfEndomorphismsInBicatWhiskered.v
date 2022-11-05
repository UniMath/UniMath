(** Constructs the actegory with the action of the endomorphisms by precomposition on a fixed hom-category of a bicategory

Author: Ralph Matthes 2022

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Import Bicat.Notations.
Import BifunctorNotations.

Local Open Scope cat.

Section Action_From_Precomposition.

Context {C : bicat}.
Context (c0 d0 : ob C).

Local Definition endocat : category := hom c0 c0.
Local Definition Mon_endo: monoidal endocat := monoidal_from_bicat_and_ob c0.
Local Definition homcat : category := hom c0 d0.

Definition action_from_precomp : bifunctor endocat homcat homcat.
Proof.
  use make_bifunctor.
  - use make_bifunctor_data.
    + intros v f. exact (v · f).
    + intros v f1 f2 β. exact (v ◃ β).
    + intros f v1 v2 α. exact (α ▹ f).
  - repeat split.
    + intros v f. cbn. apply lwhisker_id2.
    + intros f v. cbn. apply id2_rwhisker.
    + intros v f1 f2 f3 β1 β2. cbn. apply pathsinv0, lwhisker_vcomp.
    + intros f v1 v2 v3 α1 α2. cbn. apply pathsinv0, rwhisker_vcomp.
    + intros v1 v2 f1 f2 α β. cbn. apply vcomp_whisker.
Defined.

Definition actegory_from_precomp_data : actegory_data Mon_endo homcat.
Proof.
  exists action_from_precomp.
  repeat split.
  - intro f. cbn. apply lunitor.
  - intro f. cbn. apply linvunitor.
  - intros v w f. cbn. apply rassociator.
  - intros v w f. cbn. apply lassociator.
Defined.

Definition actegory_from_precomp : actegory Mon_endo homcat.
Proof.
  exists actegory_from_precomp_data.
  repeat split.
  - intros f g β. cbn. apply vcomp_lunitor.
  - cbn. apply lunitor_linvunitor.
  - cbn. apply linvunitor_lunitor.
  - intros v w f f' β. cbn. apply lwhisker_lwhisker_rassociator.
  - intros v v' w f α. cbn. apply pathsinv0, rwhisker_rwhisker_alt.
  - intros v w w' f α. cbn. apply rwhisker_lwhisker_rassociator.
  - cbn. apply rassociator_lassociator.
  - cbn. apply lassociator_rassociator.
  - intros v f. cbn. apply lunitor_lwhisker.
  - intros w v v' f. cbn. apply rassociator_rassociator.
Defined.

End Action_From_Precomposition.

Section Instantiation_To_Bicategory_Of_Categories.

  Context (C D : category).

  Definition actegoryfromprecomp : actegory (Mon_endo(C:=bicat_of_cats) C)
                                           (homcat(C:=bicat_of_cats) C D)
    := actegory_from_precomp(C:=bicat_of_cats) C D.

  Lemma actegoryfromprecomp_action_pointwise_ok (v : functor C C) (f : functor C D) : v ⊗_{actegoryfromprecomp} f = functor_compose v f.
  Proof.
    cbn.
    apply idpath.
  Qed.

End Instantiation_To_Bicategory_Of_Categories.
