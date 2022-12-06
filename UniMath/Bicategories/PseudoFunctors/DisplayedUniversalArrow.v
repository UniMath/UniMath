(*
In this file, we define displayed left universal arrows and show how they define a left universal arrow for the corresponding total pseudo-functor.
Created by Kobe Wullaert at 06/12/2022.
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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

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

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.


Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Lemma total2_paths2_b'
      {A : UU} {B : A → UU} {a1 : A} {a2 : A} (b1 : B a1)  (b2 : B a2)
  : ∏ p : a1,, b1 = a2,, b2, isaset A -> b1 = transportb B (base_paths _ _ p) b2 .
Proof.
  intros q Aset.
  use transportb_transpose_right.
  set(t := fiber_paths q).
  cbn in t.
  refine (_ @ t).
  cbn.
  unfold base_paths.
  apply maponpaths_2.
  apply Aset.
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
      set (s := total2_paths2_b' _ _ p).
      set (ss := s (cellset_property _ _)).
      refine (ss @ _).
      apply maponpaths_2.
      apply cellset_property.
    - intros f g h ff gg hh α β αα ββ.
      set (p := pr22 lur (f,,ff) (g,,gg) (h,,hh) (α,,αα) (β,,ββ)).
      set (s := total2_paths2_b' _ _ p).
      set (ss := s (cellset_property _ _)).
      refine (ss @ _).
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
    use tpair.
    {
      intros [x xx].
      exact (L x,, LL _ xx).
    }
    use tpair.
    {
      cbn.
      intros [x xx].
      exact (η x ,, ηη _ xx).
    }
    intros [x xx] [y yy].

    use nat_iso_adj_equivalence_of_cats.
    { exact (total_functor (disp_left_universal_arrow_functor xx yy)). }
    { apply nat_trans_id. }
    { use is_nat_z_iso_nat_trans_id. }
    exact (total_adj_equivalence_of_cats (dLURu x xx y yy)).
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
