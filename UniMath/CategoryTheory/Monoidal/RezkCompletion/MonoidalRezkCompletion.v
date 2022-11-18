Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedMonoidal.
Require Import UniMath.CategoryTheory.rezk_completion.

Local Open Scope cat.

Section MonoidalRezkCompletion.

  Context (M : monoidal_cat)
          {D : univalent_category}
          {H : functor M D}
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Definition RezkCompletion_monoidal_cat
    : monoidal_cat
    := TransportedMonoidal
         (univalent_category_is_univalent D)
         H_eso H_ff
         _ _ _ _ _
         (monoidal_cat_triangle_eq M)
         (monoidal_cat_pentagon_eq M).

  Definition RezkCompletion_monoidal_functor
    : functor_monoidal_cat
        (monoidal_cat_left_unitor M)
        (monoidal_cat_left_unitor RezkCompletion_monoidal_cat)
        (monoidal_cat_right_unitor M)
        (monoidal_cat_right_unitor RezkCompletion_monoidal_cat)
        (monoidal_cat_associator M)
        (monoidal_cat_associator RezkCompletion_monoidal_cat)
    := H_monoidal
         (univalent_category_is_univalent D)
         H_eso H_ff
         _ _
         (monoidal_cat_left_unitor M)
         (monoidal_cat_right_unitor M)
         (monoidal_cat_associator M).

  Definition RezkCompletion_monoidal_universalproperty
    : ∏ (E : monoidal_cat) (Euniv : is_univalent E),
      adj_equivalence_of_cats
         (total_functor
            (precompMonoidal
               (univalent_category_is_univalent D)
               H_eso H_ff
               _ _
               (monoidal_cat_left_unitor M) (monoidal_cat_right_unitor M)
               (monoidal_cat_associator M)
               _ _
               (monoidal_cat_left_unitor E)
               (monoidal_cat_right_unitor E) (monoidal_cat_associator E)))
    := λ E Euniv,
      precomp_monoidal_adj_equiv
        (univalent_category_is_univalent D)
        H_eso H_ff
        _ _
        (monoidal_cat_left_unitor M)
        (monoidal_cat_right_unitor M)
        (monoidal_cat_associator M)
        Euniv
        _ _
        (monoidal_cat_left_unitor E)
        (monoidal_cat_right_unitor E)
        (monoidal_cat_associator E).

End MonoidalRezkCompletion.

Section MonoidalRezkCompletionUsingRepresentableCopresheaves.

  Context {M : monoidal_cat}.

  Definition Copresheaf_RezkCompletion_monoidal_cat
    : monoidal_cat
    := RezkCompletion_monoidal_cat
         M
         (Rezk_eta_essentially_surjective M)
         (Rezk_eta_fully_faithful M).

  Definition Copresheaf_RezkCompletion_monoidal_functor
    : functor_monoidal_cat
        (monoidal_cat_left_unitor M)
        (monoidal_cat_left_unitor Copresheaf_RezkCompletion_monoidal_cat)
        (monoidal_cat_right_unitor M)
        (monoidal_cat_right_unitor Copresheaf_RezkCompletion_monoidal_cat)
        (monoidal_cat_associator M)
        (monoidal_cat_associator Copresheaf_RezkCompletion_monoidal_cat)
    := RezkCompletion_monoidal_functor
         M
         (Rezk_eta_essentially_surjective M)
         (Rezk_eta_fully_faithful M).

  Definition Copresheaf_RezkCompletion_monoidal_universalproperty
    : ∏ (E : monoidal_cat) (Euniv : is_univalent E),
      adj_equivalence_of_cats
        (total_functor
           (precompMonoidal
              (univalent_category_is_univalent (Rezk_completion M))
              (Rezk_eta_essentially_surjective M) (Rezk_eta_fully_faithful M)
              _ _
              (monoidal_cat_left_unitor M) (monoidal_cat_right_unitor M)
              (monoidal_cat_associator M)
              _ _
              (monoidal_cat_left_unitor E)
              (monoidal_cat_right_unitor E) (monoidal_cat_associator E)))
    := λ E Euniv, RezkCompletion_monoidal_universalproperty
                    M
                    (Rezk_eta_essentially_surjective M)
                    (Rezk_eta_fully_faithful M) E Euniv.

End MonoidalRezkCompletionUsingRepresentableCopresheaves.
