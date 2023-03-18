Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.

Local Open Scope cat.

Section DaggerFunctors.

  Definition is_dagger_functor {C D : category}
             (dagC : dagger C) (dagD : dagger D)
             (F : functor C D)
    : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), #F (dagC _ _ f) = dagD _ _ (#F f).

  Identity Coercion is_dagger_functor_to_family_of_equalities
    : is_dagger_functor >-> Funclass.

  Lemma isaprop_is_dagger_functor
        {C D : category}
        (dagC : dagger C) (dagD : dagger D)
        (F : functor C D)
    : isaprop (is_dagger_functor dagC dagD F).
  Proof.
    repeat (apply impred_isaprop ; intro) ; apply homset_property.
  Qed.

  Definition dagger_functor_id
             {C : category} (dag : dagger C)
    : is_dagger_functor dag dag (functor_identity C).
  Proof.
    intro ; intros ; apply idpath.
  Qed.

  Definition is_dagger_functor_comp {C D E : category}
             {dagC : dagger C} {dagD : dagger D} {dagE : dagger E}
             {F : functor C D} {G : functor D E}
             (dF : is_dagger_functor dagC dagD F)
             (dG : is_dagger_functor dagD dagE G)
    : is_dagger_functor dagC dagE (functor_composite F G).
  Proof.
    intros x y f.
    refine (maponpaths #G (dF _ _ _) @ _).
    apply dG.
  Qed.

  Definition dagger_functor
             {C D : category}
             (dagC : dagger C) (dagD : dagger D)
    : UU
    := ∑ F : functor C D, is_dagger_functor dagC dagD F.

  Lemma dagger_functor_equality
        {C D : category}
        {dagC : dagger C} {dagD : dagger D}
        (F G : dagger_functor dagC dagD)
    : pr11 F = pr11 G -> F = G.
  Proof.
    intro p.
    use subtypePath.
    { intro ; apply isaprop_is_dagger_functor. }
    use (functor_eq _ _ (homset_property D)).
    exact p.
  Defined.

  Definition dagger_functor_to_functor
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             (F : dagger_functor dagC dagD)
    : functor C D
    := pr1 F.
  Coercion dagger_functor_to_functor : dagger_functor >-> functor.

  Definition dagger_functor_to_is_dagger_functor
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             (F : dagger_functor dagC dagD)
    : is_dagger_functor dagC dagD F
    := pr2 F.

  Definition make_dagger_functor
    {C D : category}
    {F : functor C D}
    {dagC : dagger C} {dagD : dagger D}
    (dagF : is_dagger_functor dagC dagD F)
    : dagger_functor dagC dagD
    := F ,, dagF.

End DaggerFunctors.
