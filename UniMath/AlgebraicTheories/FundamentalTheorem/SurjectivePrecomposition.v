(**************************************************************************************************

  Precomposition with a fully faithful functor is split essentially surjective

  If D is a category with colimits and F: C → C' is a fully faithful functor, one can use left Kan
  extension to show that the functor F ∙ (⋅): [C', D] → [C, D] is split essentially surjective.

  Contents
  1. Precomposition with F is split essentially surjective [pre_comp_split_essentially_surjective]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

Section PrecompositionEssentiallySurjective.

  Context {C C' : category}.
  Context (F : C ⟶ C').
  Context (H : fully_faithful F).

  Context (D : category).
  Context (HD : Colims D).

  Let Fweq := weq_from_fully_faithful H.

  Section Iso.

    Context (P : C ⟶ D).
    Context (c : C).

    Definition pre_comp_z_iso_inv
      : D⟦(lan_functor HD F P : C' ⟶ D) (F c), P c⟧.
    Proof.
      use (colimArrow _ _ (make_cocone _ _)).
      - intros v.
        exact (#(P : _ ⟶ _) (invmap (Fweq _ _) (pr2 v))).
      - abstract (
          intros u v e;
          refine (!functor_comp P _ _ @ _);
          apply (maponpaths (# (P : _ ⟶ _)));
          refine (!invmap_eq _ _ _ (!_));
          refine (functor_comp _ _ _ @ _);
          refine (maponpaths _ (homotweqinvweq (Fweq _ _) _) @ _);
          exact (!pr2 e @ id_right _)
        ).
    Defined.

    Lemma pre_comp_z_iso_is_inverse
      : is_inverse_in_precat (C := D)
        ((unit_from_right_adjoint (is_right_adjoint_precomposition HD F) P : _ ⟹ _) c)
        pre_comp_z_iso_inv.
    Proof.
      split.
      - refine (_ @ functor_id P _).
        refine (colimArrowCommutes (lan_colim HD F P (F c)) _ _ ((c ,, tt) ,, identity (F c)) @ _).
        refine (maponpaths (λ f, # (P : _ ⟶ _) f) (_ : invmap (Fweq c c) _ = _)).
        apply invmap_eq.
        exact (!functor_id F _).
      - apply colim_mor_eq.
        intro v.
        refine (assoc _ _ _ @ _).
        match goal with
        | [ |- _ · ?a = _ ] => refine (maponpaths (λ x, x · a) (colimArrowCommutes _ _ _ _) @ _)
        end.
        use (colimInCommutes _ v ((c ,, tt) ,, identity (F c)) ((make_dirprod _ _) ,, _) @ _).
        + now induction (pr21 v).
        + refine (maponpaths (λ x, x · _) _).
          exact (!homotweqinvweq (Fweq _ _) _).
        + exact (!id_right _).
    Qed.

    Definition pre_comp_is_z_iso
      : is_z_isomorphism ((unit_from_right_adjoint (is_right_adjoint_precomposition HD F) P : _ ⟹ _) c)
      := make_is_z_isomorphism _ _ pre_comp_z_iso_is_inverse.

  End Iso.

  Definition pre_comp_after_lan_iso
    (P : [C, D])
    : z_iso P (pre_comp_functor F (lan_functor HD F P))
    := z_iso_from_nat_z_iso _ (make_nat_z_iso _ _ _ (pre_comp_is_z_iso _)).

  Definition pre_comp_split_essentially_surjective
    : split_essentially_surjective (pre_comp_functor F)
    := λ c, lan_functor HD F c ,, (z_iso_inv (pre_comp_after_lan_iso c)).

End PrecompositionEssentiallySurjective.
