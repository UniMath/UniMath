#[local] Unset Universe Checking.
(* In this file, we have formalized the result that a fully faithful functor into a dagger category induces a unique dagger on the domain such that the functor is dagger preserving.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.

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

Lemma fully_faithful_reflects_is_unitary {C D : category}
      {dagC : dagger C} {dagD : dagger D}
      {F : functor C D}
      (dagF : is_dagger_functor dagC dagD F)
      (ff : fully_faithful F)
  : ∏ c c' : C, ∏ f : C⟦c,c'⟧, is_unitary dagD (#F f) -> is_unitary dagC f.
Proof.
  intros c c' f u.
  set (i := pr2 (fully_faithful_reflects_iso_proof _ _ _ ff c c' (Isos.make_z_iso _ _ u))).
  cbn in i.
  split.
  - refine (_ @ pr1 i).
    use maponpaths_compose.
    + apply pathsinv0, homotinvweqweq.
    + refine (! homotinvweqweq  (weq_from_fully_faithful ff c' c) (dagC _ _ f) @ _).
      apply maponpaths.
      apply dagF.
  - refine (_ @ pr2 i).
    use maponpaths_compose.
    + refine (! homotinvweqweq  (weq_from_fully_faithful ff c' c) (dagC _ _ f) @ _).
      apply maponpaths.
      apply dagF.
    + apply pathsinv0, homotinvweqweq.
Qed.

Lemma fully_faithful_reflects_unitary {C D : category}
      {dagC : dagger C} {dagD : dagger D}
      {F : functor C D}
      (dagF : is_dagger_functor dagC dagD F)
      (ff : fully_faithful F)
  : ∏ c c' : C, unitary dagD (F c) (F c') -> unitary dagC c c'.
Proof.
  intros c c' u.
  exists (fully_faithful_inv_hom ff c c' (pr1 u)).
  apply (fully_faithful_reflects_is_unitary dagF ff c c' (fully_faithful_inv_hom ff c c' (pr1 u))).
  set (p := ! maponpaths (is_unitary dagD) (functor_on_fully_faithful_inv_hom ff _ _ (pr1 u))).
  exact (path_to_fun p (pr2 u)).
Defined.

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
      { apply maponpaths, functor_id. }
      etrans.
      { apply dagger_to_law_id. }
      apply pathsinv0, functor_id.
    - etrans.
      { apply maponpaths, functor_comp. }
      etrans.
      { apply dagger_to_law_comp. }
      etrans.
      { apply maponpaths, pathsinv0, (functor_on_fully_faithful_inv_hom ff). }
      refine (_ @ ! functor_comp _ _ _).
      apply maponpaths_2, pathsinv0, functor_on_fully_faithful_inv_hom.
    - etrans.
      { apply maponpaths, functor_on_fully_faithful_inv_hom. }
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
    use subtypePath.
    { intro ; apply isaprop_is_dagger_functor. }
    use subtypePath.
    { intro ; apply isaprop_dagger_laws. }
    do 3 (apply funextsec ; intro).
    apply pathsweq1.
    apply (pr2 dag).
  Defined.

End FullyFaithful.
