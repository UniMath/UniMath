Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope mor_disp_scope.

Section DisplayedToTotalEsoFF.

  Context {C1 C2 : category}
          {F : functor C1 C2}
          {D1 : disp_cat C1} {D2 : disp_cat C2}
          {FF : disp_functor F D1 D2}.

  Definition disp_functor_ff_to_total_ff
             (F_ff : fully_faithful F)
             (FF_ff : disp_functor_ff FF)
    : fully_faithful (total_functor FF).
  Proof.
  Admitted.

  Definition disp_functor_eso_to_total_eso
             (F_eso : essentially_surjective F)
             (FF_eso : disp_functor_disp_ess_split_surj FF)
    : essentially_surjective (total_functor FF).
  Proof.
  Admitted.

End DisplayedToTotalEsoFF.

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

  Definition disp_prod_functor_over_fixed_base_ff
             (FF_ff : disp_functor_ff FF)
             (FF'_ff : disp_functor_ff FF')
    : disp_functor_ff disp_prod_functor_over_fixed_base.
  Proof.
  Admitted.

  Definition disp_prod_functor_over_fixed_base_eso
             (FF_ff : disp_functor_disp_ess_split_surj FF)
             (FF'_ff : disp_functor_disp_ess_split_surj FF')
    : disp_functor_disp_ess_split_surj disp_prod_functor_over_fixed_base.
  Proof.
  Admitted.

End ProductOfDisplayedFunctorsOverFixedBase.
