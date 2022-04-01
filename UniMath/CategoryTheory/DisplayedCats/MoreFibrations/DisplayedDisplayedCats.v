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

Definition composite_disp_cat {C : category} (DD : disp_disp_cat C) : disp_cat C.
Proof.
  destruct DD as [D E].
  use tpair.
  - unfold disp_cat_data.
    use tpair.
    + unfold disp_cat_ob_mor.
      use tpair.
      * intro c.
        exact (∑ (cc : D c), E (c ,, cc)).
      * simpl.
        intros c c' [cc ccc] [cc' ccc'] f.
        exact (∑ (ff : cc -->[f] cc'), ccc -->[(f ,, ff)] ccc').
    + simpl.
      split.
      * simpl.
        intros c [cc ccc].
        exists (id_disp cc).
        exact (id_disp ccc).
      * simpl.
        intros c c' c'' f g [cc ccc] [cc' ccc'] [cc'' ccc''] [ff fff] [gg ggg].
        exists (comp_disp ff gg).
        exact (comp_disp fff ggg).
  - split.
    + simpl.
      intros c c' f [cc ccc] [cc' ccc'] [ff fff].


      admit.
    + simpl.
      split.
      *
        admit.
      * split.
        --
           admit.
        --
           admit.
Admitted.

Definition fiber_disp_cat {C : category} (DD: disp_disp_cat C) (c : C)
  : disp_cat (fiber_category (base_disp_cat DD) c).
Proof.
  destruct DD as [D E]. simpl.

Admitted.
