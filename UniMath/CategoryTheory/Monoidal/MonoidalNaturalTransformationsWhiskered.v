Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MonoidalNaturalTransformation.

  Import BifunctorNotations.
  Import MonoidalNotations.

  Check fmonoidal_preservesunit.

  Definition preservesunit_commutes
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G : functor C D}
             (MF : fmonoidal M N F)
             (MG : fmonoidal M N G )
             (α : nat_trans F G)
    : UU := (fmonoidal_preservesunit MF)  · α I_{M} = (fmonoidal_preservesunit MG).

  Definition preservestensor_commutes
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G : functor C D}
             (MF : fmonoidal M N F)
             (MG : fmonoidal M N G)
             (α : nat_trans F G)
    : UU := ∏ (x y : C),
    (fmonoidal_preservestensordata MF x y) ·  α (x ⊗_{M} y)
      = (α x) ⊗^{N} (α y) · (fmonoidal_preservestensordata MG x y).

  Definition nmonoidal
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G : functor C D}
             (MF : fmonoidal M N F)
             (MG : fmonoidal M N G)
             (α : nat_trans F G)
    : UU := preservesunit_commutes MF MG α × preservestensor_commutes MF MG α.

  Definition nmonoidal_preservescommutingunit
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G : functor C D}
             {MF : fmonoidal M N F}
             {MG : fmonoidal M N G}
             {α : nat_trans F G}
             (Mα : nmonoidal MF MG α)
    : preservesunit_commutes MF MG α := pr1 Mα.
  Definition nmonoidal_preservescommutingtensor
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G : functor C D}
             {MF : fmonoidal M N F}
             {MG : fmonoidal M N G}
             {α : nat_trans F G}
             (Mα : nmonoidal MF MG α)
    : preservestensor_commutes MF MG α := pr2 Mα.

  Lemma nmonoidal_identity
        {C D : category}
        {M : monoidal C}
        {N : monoidal D}
        {F : functor C D}
        (MF : fmonoidal M N F)
    : nmonoidal MF MF (nat_trans_id F).
  Proof.
    use tpair.
    - apply id_right.
    - intros x y.
      rewrite id_right.
      unfold nat_trans_id.
      simpl.
      rewrite bifunctor_distributes_over_id.
      + rewrite id_left.
        apply idpath.
      + apply bifunctor_leftid.
      + apply bifunctor_rightid.
  Defined.

  Lemma nmonoidal_composition
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F G H: functor C D}
             {MF : fmonoidal M N F}
             {MG : fmonoidal M N G}
             {MH : fmonoidal M N H}
             {α : nat_trans F G}
             {β : nat_trans G H}
             (Mα : nmonoidal MF MG α)
             (Mβ : nmonoidal MG MH β)
    : nmonoidal MF MH (nat_trans_comp _ _ _ α β).
  Proof.
    use tpair.
    - unfold preservesunit_commutes.
      unfold nat_trans_comp.
      simpl.
      rewrite assoc.
      rewrite (nmonoidal_preservescommutingunit Mα).
      apply (nmonoidal_preservescommutingunit Mβ).
    - intros x y.
      simpl.
      rewrite assoc.
      rewrite (nmonoidal_preservescommutingtensor Mα).
      rewrite assoc'.
      rewrite (nmonoidal_preservescommutingtensor Mβ).
      rewrite assoc.
      rewrite bifunctor_distributes_over_comp.
      + apply idpath.
      + apply bifunctor_leftcomp.
      + apply bifunctor_rightcomp.
      + apply bifunctor_equalwhiskers.
  Defined.

End MonoidalNaturalTransformation.
