(**

use constructions and results for bicategories for the instance of the bicategory of (small) categories (with homsets, but without univalence)

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Import Bicat.Notations.

Local Open Scope cat.

Local Definition CAT : bicat := bicat_of_cats.

Local Definition lwhisker := @lwhisker CAT.

Local Lemma pre_whisker_as_lwhisker (A B C: category) (F: A ⟶ B)(G H: B ⟶ C)(γ: G ⟹ H):
  pre_whisker F γ = lwhisker A B C F G H γ.
Proof.
  apply idpath.
Qed.

Local Definition rwhisker := @rwhisker CAT.

Local Lemma post_whisker_as_rwhisker (B C D: category) (G H: B ⟶ C) (γ: G ⟹ H) (K: C ⟶ D):
  post_whisker γ K = rwhisker B C D G H K γ.
Proof.
  apply idpath.
Qed.

Local Definition hcomp := @hcomp CAT.
Local Definition hcomp' := @hcomp' CAT.

(** demonstrates the mismatch: [horcomp] only corresponds to [hcomp'] *)
Local Lemma horcomp_as_hcomp'_pointwise (C D E : category) (F F' : C ⟶ D) (G G' : D ⟶ E) (α : F ⟹ F') (β: G ⟹ G'):
  horcomp α β = hcomp' C D E F F' G G' α β.
Proof.
  apply (nat_trans_eq (homset_property E)).
  intro c.
  apply idpath.
Qed.

Local Definition hcomp_functor_data := @hcomp_functor_data CAT.
Local Definition hcomp_functor := @hcomp_functor CAT.

(** no more mismatch when using [functorial_composition] *)
Local Lemma functorial_composition_as_hcomp_functor (A B C : category):
  functorial_composition_data A B C = hcomp_functor_data A B C.
Proof.
  apply idpath.
Qed.

(** as a corollary: *)
Local Lemma functorial_composition_as_hcomp_functor_datawise (A B C : category):
  functorial_composition A B C = hcomp_functor A B C.
Proof.
  use functor_eq.
  - apply functor_category_has_homsets.
  - apply functorial_composition_as_hcomp_functor.
Qed.

Local Definition hcomp_vcomp := @hcomp_vcomp CAT.

(** here, we obtain the result by inheriting from the abstract bicategorical development *)
Lemma interchange_functorial_composition (A B C: category) (F1 G1 H1: A ⟶ B) (F2 G2 H2: B ⟶ C)
  (α1 : F1 ⟹ G1) (α2: F2 ⟹ G2) (β1: G1 ⟹ H1) (β2: G2 ⟹ H2):
  # (functorial_composition A B C)
    (catbinprodmor ((α1:(functor_category A B)⟦F1,G1⟧) · β1)
                      ((α2:(functor_category B C)⟦F2,G2⟧) · β2)) =
    # (functorial_composition A B C)
      (catbinprodmor(C:=functor_category A B)(D:=functor_category B C) α1 α2) ·
      # (functorial_composition A B C)
      (catbinprodmor(C:=functor_category A B)(D:=functor_category B C) β1 β2).
Proof.
  exact (hcomp_vcomp A B C F1 G1 H1 F2 G2 H2 α1 α2 β1 β2).
Qed.
