(* In this file, we have formalized some results on fully faithful functors between (the underlying categories) of dagger categories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerFunctors.

Local Open Scope cat.

(* TODO::Has to be renamed and moved *)
Lemma bla {C D : category} {F : functor C D} (ff : fully_faithful F)
    : ∏ (x y : C) (f : D⟦F x, F y⟧),
      # F (invmap (weq_from_fully_faithful ff _ _) f) = f.
Proof.
Admitted.

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
      2: apply maponpaths_2, pathsinv0, bla.
      apply maponpaths, pathsinv0, bla.
    - etrans.
      1: apply maponpaths, bla.
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
    apply bla.
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
