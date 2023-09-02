(*
In this file, we define displayed left universal arrows and show how they define a left universal arrow for the corresponding total pseudo-functor.
Created by Kobe Wullaert at 06/12/2022.

Contents
1. Definition of a displayed universal arrow.
2. A make constructor when the 2-cells of the displayed bicategories are propositional.
3. A make constructor when the 2-cells of the displayed bicategories are propositional and groupoidal.
4. A make constructor when the 2-cells of the displayed bicategories are contractible.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Lemma fiber_paths_transposed
      {A : UU} {B : A → UU} {a1 : A} {a2 : A} (b1 : B a1)  (b2 : B a2)
  : ∏ p : a1,, b1 = a2,, b2, b1 = transportb B (base_paths _ _ p) b2 .
Proof.
  intro q.
  use transportb_transpose_right.
  apply (fiber_paths q).
Qed.

Section DisplayedLeftUniversalArrow.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R).

  Definition disp_left_universal_arrow0 : UU
    := ∑ (LL : ∏ x : B2, D2 x → D1 (L x)),
       ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx)).

  Context (dLUR : disp_left_universal_arrow0).

  Let LL := pr1 dLUR.
  Let ηη := pr2 dLUR.

  Let η0 : ∏ x0 : total_bicat D2, total_bicat D2 ⟦ x0, (total_psfunctor D1 D2 R RR) (_,,LL (pr1 x0) (pr2 x0)) ⟧
    := λ x, η (pr1 x) ,, ηη _ (pr2 x).

  Definition disp_left_universal_arrow_functor_data
             {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : disp_functor_data (left_universal_arrow_functor R x y η) (disp_hom (LL _ xx) yy) (disp_hom xx (RR _ yy)).
  Proof.
    exists (λ f ff, ηη _ xx ;; (disp_psfunctor_mor _ _ _ RR ff)).
    intros f g ff gg α αα.
    exact (disp_lwhisker (ηη _ xx) (disp_psfunctor_cell _ _ _ RR αα)).
  Defined.

  Lemma disp_left_universal_arrow_is_functor
        {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : disp_functor_axioms (disp_left_universal_arrow_functor_data xx yy).
  Proof.
    set (lur := left_universal_arrow_functor (total_psfunctor _ _ _ RR) (x,,xx) (y,,yy) η0).
    split.
    - intros f ff.
      set (p := pr12 lur (f,,ff)).
      refine (fiber_paths_transposed _ _ p @ _).
      apply maponpaths_2.
      apply cellset_property.
    - intros f g h ff gg hh α β αα ββ.
      set (p := pr22 lur (f,,ff) (g,,gg) (h,,hh) (α,,αα) (β,,ββ)).
      set (s := fiber_paths_transposed _ _ p).
      refine (s @ _).
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition disp_left_universal_arrow_functor
             {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : disp_functor (left_universal_arrow_functor R x y η) (disp_hom (LL _ xx) yy) (disp_hom xx (RR _ yy))
    := _ ,, disp_left_universal_arrow_is_functor xx yy.

  Definition disp_left_universal_arrow_universality : UU
    := ∏ (x : B2) (xx : D2 x) (y : B1) (yy : D1 y),
      is_equiv_over (_ ,, adj x y) (disp_left_universal_arrow_functor xx yy).

  Definition total_disp_left_universal_arrow
             (dLURu : disp_left_universal_arrow_universality)
    : left_universal_arrow (total_psfunctor D1 D2 R RR).
  Proof.
    exists (λ x, L (pr1 x),, LL _ (pr2 x)).
    exists (λ x, η (pr1 x) ,, ηη _ (pr2 x)).
    intros [x xx] [y yy].

    use nat_iso_adj_equivalence_of_cats.
    - exact (total_functor (disp_left_universal_arrow_functor xx yy)).
    - apply nat_trans_id.
    - use is_nat_z_iso_nat_trans_id.
    - exact (total_adj_equivalence_of_cats (dLURu x xx y yy)).
  Defined.

End DisplayedLeftUniversalArrow.

Section DisplayedLeftUniversalArrowDef.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Definition disp_left_universal_arrow : UU
    := ∑ (LL : ∏ x : B2, D2 x → D1 (L x)),
      ∑ ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx)),
        ∏ (x : B2) (xx : D2 x) (y : B1) (yy : D1 y),
        is_equiv_over (_ ,, adj x y)
                      (disp_left_universal_arrow_functor LUR RR (LL,,ηη) xx yy).

  Definition total_left_universal_arrow
             (dLUR : disp_left_universal_arrow)
    : left_universal_arrow (total_psfunctor D1 D2 R RR)
    := total_disp_left_universal_arrow LUR RR (pr1 dLUR ,, pr12 dLUR) (pr22 dLUR).

End DisplayedLeftUniversalArrowDef.

Section MakeDisplayedLeftUniversalArrowIfPropositional.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R)
          (D1_2cells_prop : disp_2cells_isaprop D1)
          (D2_2cells_prop : disp_2cells_isaprop D2).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context (LL : ∏ x : B2, D2 x → D1 (L x))
    (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))).

  Context (LL_mor : ∏ x xx y yy f (ff : xx -->[ f] RR y yy),
              LL x xx -->[ right_adjoint ((pr22 LUR) x y) f] yy).
  Context (LL_2cell : ∏ x xx y yy (f1 f2 : B2 ⟦ x, R y ⟧)
                      (ff1 : xx -->[ f1] RR y yy) (ff2 : xx -->[ f2] RR y yy)
                      (α : f1 ==> f2),
              ff1 ==>[α] ff2
              → (LL_mor x xx y yy f1 ff1) ==>[(# (right_adjoint ((pr22 LUR) x y)))%Cat α]
                  (LL_mor x xx y yy f2 ff2)).
  Context (LL_unit : ∏ x xx y yy f ff,
              ff ==>[adjunit (adj x y) f]
                (LL_mor x xx y yy (η x · (# R)%Cat f) (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR ff))).

  Context (LL_unit_inv : ∏ x xx y yy f ff,
        (LL_mor x xx y yy ((pr12 LUR) x · (# R)%Cat f) (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR ff))
          ==>[inv_from_z_iso (unit_pointwise_z_iso_from_adj_equivalence (adj x y) _)] ff).

  Context (LL_counit : ∏ x xx y yy f ff,
              (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR (LL_mor x xx y yy f ff))
                ==>[adjcounit (adj x y) f] ff).

  Context (LL_counit_inv : ∏ x xx y yy f ff,
              ff ==>[inv_from_z_iso (counit_pointwise_z_iso_from_adj_equivalence (adj x y) _)]
                (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR (LL_mor x xx y yy f ff))).

  Definition make_disp_functor_data_if_prop
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : disp_functor_data
        (right_adjoint ((pr22 LUR) x y))
        (disp_hom xx (RR y yy))
        (disp_hom (LL x xx) yy).
  Proof.
    simple refine (_ ,, _).
    - exact (LL_mor x xx y yy).
    - exact (LL_2cell x xx y yy).
  Defined.

  Definition make_disp_functor_if_prop
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : disp_functor
        (right_adjoint ((pr22 LUR) x y))
        (disp_hom xx (RR y yy))
        (disp_hom (LL x xx) yy).
  Proof.
    simple refine (make_disp_functor_data_if_prop xx yy ,, _).
    abstract (split ; intros ; apply D1_2cells_prop).
  Defined.

  Definition make_disp_univ_arrow_if_prop_equiv
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : is_equiv_over
        (left_universal_arrow_functor R x y (pr12 LUR),, (pr22 LUR) x y)
        (disp_left_universal_arrow_functor LUR RR (LL,, ηη) xx yy).
  Proof.
    simple refine (((_ ,, (_,,_)) ,, _) ,, (_ ,, _)).
    - exact (make_disp_functor_if_prop xx yy).
    - simple refine (_ ,, _).
      + exact (LL_unit x xx y yy).
      + abstract (intro ; intros ; apply D1_2cells_prop).
    - simple refine (_ ,, _).
      + exact (LL_counit x xx y yy).
      + abstract (
            intro ; intros ;
            apply D2_2cells_prop).
    - abstract (split ; intro ; intros;
                [ apply D2_2cells_prop
                | apply D1_2cells_prop ]).
    - intros f ff.
      simple refine (_ ,, (_ ,, _)).
      + exact (LL_unit_inv x xx y yy f ff).
      + abstract (apply D1_2cells_prop).
      + abstract (apply D1_2cells_prop).
    - intros f ff.
      simple refine (_ ,, (_ ,, _)).
      + exact (LL_counit_inv x xx y yy f ff).
      + abstract (apply D2_2cells_prop).
      + abstract (apply D2_2cells_prop).
  Defined.

  Definition make_disp_univ_arrow_if_prop
    : disp_left_universal_arrow LUR RR.
  Proof.
    refine (LL ,, ηη ,, _).
    intros x xx y yy.
    exact (make_disp_univ_arrow_if_prop_equiv xx yy).
  Defined.

End MakeDisplayedLeftUniversalArrowIfPropositional.

Section MakeDisplayedLeftUniversalArrowIfGroupoidalAndProp.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R)
          (D1_2cells_grp : disp_locally_groupoid D1)
          (D2_2cells_grp : disp_locally_groupoid D2)
          (D1_2cells_prop : disp_2cells_isaprop D1)
          (D2_2cells_prop : disp_2cells_isaprop D2).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context (LL : ∏ x : B2, D2 x → D1 (L x))
    (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))).

  Context (LL_mor : ∏ x xx y yy f (ff : xx -->[ f] RR y yy),
              LL x xx -->[ right_adjoint ((pr22 LUR) x y) f] yy).
  Context (LL_2cell : ∏ x xx y yy (f1 f2 : B2 ⟦ x, R y ⟧)
                      (ff1 : xx -->[ f1] RR y yy) (ff2 : xx -->[ f2] RR y yy)
                      (α : f1 ==> f2),
              ff1 ==>[α] ff2
              → (LL_mor x xx y yy f1 ff1) ==>[(# (right_adjoint ((pr22 LUR) x y)))%Cat α]
                  (LL_mor x xx y yy f2 ff2)
          ).
  Context (LL_unit : ∏ x xx y yy f ff,
        ff ==>[adjunit (adj x y) f]
    (LL_mor x xx y yy (η x · (# R)%Cat f) (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR ff))).

  Context (LL_counit : ∏ x xx y yy f ff,
        (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR (LL_mor x xx y yy f ff))
          ==>[adjcounit (adj x y) f] ff).

   Definition make_disp_univ_arrow_if_groupoid_and_prop
    : disp_left_universal_arrow LUR RR.
   Proof.
     use make_disp_univ_arrow_if_prop.
     - exact D1_2cells_prop.
     - exact D2_2cells_prop.
     - exact LL.
     - exact ηη.
     - exact LL_mor.
     - exact LL_2cell.
     - exact LL_unit.
     - intros x xx y yy f ff.
       use (pr1 (disp_hom_disp_invertible_2cell_to_z_iso _ _)).
       + apply LL_unit.
       + apply (D1_2cells_grp _ _ _ _  (_ ,, (pr12 (adj x y)) f)).
     - exact LL_counit.
     - intros x xx y yy f ff.
       use (pr1 (disp_hom_disp_invertible_2cell_to_z_iso _ _)).
       + apply LL_counit.
       + apply (D2_2cells_grp _ _ _ _  (_ ,, (pr22 (adj x y)) f)).
   Defined.

End MakeDisplayedLeftUniversalArrowIfGroupoidalAndProp.

Section MakeDisplayedLeftUniversalArrowIfContractible.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R)
          (D1_2cells_contr : disp_2cells_iscontr D1)
          (D2_2cells_contr : disp_2cells_iscontr D2).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context (LL : ∏ x : B2, D2 x → D1 (L x))
    (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))).

  Context (LL_mor : ∏ x xx y yy f (ff : xx -->[ f] RR y yy),
              LL x xx -->[ right_adjoint ((pr22 LUR) x y) f] yy).

  Definition make_disp_univ_arrow_if_contr
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_univ_arrow_if_groupoid_and_prop.
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ D1_2cells_contr).
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ D1_2cells_contr).
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact LL.
    - exact ηη.
    - exact LL_mor.
    - abstract (intro ; intros ; apply D1_2cells_contr).
    - abstract (intro ; intros ; apply D1_2cells_contr).
    - abstract (intro ; intros ; apply D2_2cells_contr).
  Defined.

End MakeDisplayedLeftUniversalArrowIfContractible.
