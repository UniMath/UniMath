Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Section ProductOfDisplayedFunctorsOverFixedBase.

  Context {C1 C2 : category} {F : functor C1 C2}
          {D1 D1' : disp_cat C1} {D2 D2' : disp_cat C2}
          (FF : disp_functor F D1 D2)
          (FF' : disp_functor F D1' D2').

  Definition disp_prod_functor_over_fixed_base_data
    : disp_functor_data F (D1 × D1')%disp_cat (D2 × D2')%disp_cat.
  Proof.
    exists (λ x, dirprodf (FF x) (FF' x)).
    intros x y xx yy f ff.
    exists (pr21 FF x y (pr1 xx) (pr1 yy) f (pr1 ff)).
    exact (pr21 FF' x y (pr2 xx) (pr2 yy) f (pr2 ff)).
  Defined.

  Lemma disp_prod_functor_over_fixed_base_is_functor
    : disp_functor_axioms disp_prod_functor_over_fixed_base_data.
  Proof.
    split.
    - intros x xx.
      use total2_paths_f.
      + refine (pr12 FF x (pr1 xx) @ _).
        apply pathsinv0, pr1_transportf.
      + rewrite transportf_const.
        refine (pr12 FF' x (pr2 xx) @ _).
        apply pathsinv0, pr2_transportf.
    - intros x y z xx yy zz f g ff gg.
      use total2_paths_f.
      + refine (pr22 FF x y z (pr1 xx) (pr1 yy) (pr1 zz) f g (pr1 ff) (pr1 gg) @ _).
        apply pathsinv0, pr1_transportf.
      + rewrite transportf_const.
        refine (pr22 FF' x y z (pr2 xx) (pr2 yy) (pr2 zz) f g (pr2 ff) (pr2 gg) @ _).
        apply pathsinv0, pr2_transportf.
  Qed.

  Definition disp_prod_functor_over_fixed_base
    : disp_functor F (D1 × D1')%disp_cat (D2 × D2')%disp_cat
    := _ ,, disp_prod_functor_over_fixed_base_is_functor.

End ProductOfDisplayedFunctorsOverFixedBase.
