(* In this file, we have formalized the result that a fully faithful functor into a dagger category induces a unique dagger on the domain such that the functor is dagger preserving.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.

Local Open Scope cat.


Local Lemma functor_on_fully_faithful_inv_hom {C D : category} {F : functor C D} (ff : fully_faithful F)
    : ∏ (x y : C) (f : D⟦F x, F y⟧),
      # F (fully_faithful_inv_hom ff x y f) = f.
Proof.
  intros x y f.

  set (fandf := fully_faithful_implies_full_and_faithful _ _ _ ff).
  set (fu := pr1 fandf).
  set(f_f := fu x y f).

  transparent assert (pp : hProp).
  {
    exists (# F (fully_faithful_inv_hom ff x y f) = f).
    apply homset_property.
  }

  use (factor_through_squash_hProp pp _ f_f).
  clear f_f ; intro f_f.
  refine (_ @ pr2 f_f).
  apply (maponpaths (# F)).
  refine (_ @ homotinvweqweq (weq_from_fully_faithful ff x y) (pr1 f_f)).
  apply maponpaths.
  exact (! (pr2 f_f)).
Qed.

Section FullyFaithful.

  Definition fully_faithful_reflect_dagger_structure
             {C D : category}
             {F : functor C D} (dagD : dagger D)
             (ff : fully_faithful F)
    : dagger_structure C.
  Proof.
    intros x y f.
    apply (fully_faithful_inv_hom ff y x).
    exact (pr1 dagD _ _ (#F f)).
  Defined.

  Definition fully_faithful_reflect_dagger_laws
             {C D : category}
             {F : functor C D} (dagD : dagger D)
             (ff : fully_faithful F)
    : dagger_laws (fully_faithful_reflect_dagger_structure dagD ff).
  Proof.
    repeat split ; intro ; intros ; use invmap_eq.
    - etrans.
      1: apply maponpaths, functor_id.
      etrans.
      1: apply dagger_to_law_id.
      apply pathsinv0, functor_id.
    - etrans.
      1: apply maponpaths, functor_comp.
      etrans.
      1: apply dagger_to_law_comp.
      etrans.
      2: apply pathsinv0, functor_comp.
      etrans.
      2: apply maponpaths_2, pathsinv0, functor_on_fully_faithful_inv_hom.
      apply maponpaths, pathsinv0, functor_on_fully_faithful_inv_hom.
    - etrans.
      1: apply maponpaths, functor_on_fully_faithful_inv_hom.
      apply dagger_to_law_idemp.
  Qed.

  Definition fully_faithful_reflect_dagger
             {C D : category}
             {F : functor C D} (dagD : dagger D)
             (ff : fully_faithful F)
    : dagger C
    := _ ,, fully_faithful_reflect_dagger_laws dagD ff.

  Definition fully_faithful_is_dagger_functor
             {C D : category}
             {F : functor C D} (dagD : dagger D)
             (ff : fully_faithful F)
    : is_dagger_functor (fully_faithful_reflect_dagger dagD ff) dagD F.
  Proof.
    intros x y f.
    apply functor_on_fully_faithful_inv_hom.
  Qed.

  Lemma fully_faithful_reflect_dagger_uniquely
        {C D : category}
        {F : functor C D} (dagD : dagger D)
        (ff : fully_faithful F)
    : ∃! dagC : dagger C, is_dagger_functor dagC dagD F.
  Proof.
    exists (fully_faithful_reflect_dagger dagD ff ,, fully_faithful_is_dagger_functor dagD ff).
    intro dag.

    use total2_paths_f.
    2: apply isaprop_is_dagger_functor.
    use total2_paths_f.
    2: apply isaprop_dagger_laws.
    apply funextsec ; intro c.
    apply funextsec ; intro d.
    apply funextsec ; intro f.
    apply pathsweq1.
    apply (pr2 dag).
  Defined.

End FullyFaithful.
