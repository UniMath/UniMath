Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Foundations.All.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.


Definition disp_disp_cat (C : category) : UU
  := ∑ (D : disp_cat C), disp_cat (total_category D).

Definition base_disp_cat {C : category} (E : disp_disp_cat C) : disp_cat C
  := pr1 E.

Definition top_disp_cat {C : category} (E : disp_disp_cat C)
  : disp_cat (total_category (base_disp_cat E))
  := pr2 E.

Definition comp_disp_cat {C : category} (E : disp_disp_cat C) : disp_cat C.
Proof.
Admitted.

Definition fiber_disp_cat {C : category} (E: disp_disp_cat C) (c : C)
  : disp_cat (fiber_category (base_disp_cat E) c).
Proof.
Admitted.
