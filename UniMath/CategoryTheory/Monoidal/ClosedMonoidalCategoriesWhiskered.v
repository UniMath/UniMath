Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.BraidedMonoidalCategoriesWhiskered.

Local Open Scope cat.

Section ClosedMonoidalCategories.

  Definition monoidal_leftclosed {C : category} (M : monoidal C) : UU
    := ∏ X : C, ∑ homX : functor C C,
          are_adjoints
            (rightwhiskering_functor M X)
            homX.

  Definition monoidal_leftclosed_exp {C : category} {M : monoidal C}
             (LC : monoidal_leftclosed M) : C -> functor C C
    := λ X, pr1 (LC X).

  Definition monoidal_rightclosed {C : category} (M : monoidal C) : UU
    := ∏ X : C, ∑ homX : functor C C,
          are_adjoints
            (leftwhiskering_functor M X)
            homX.

  Definition monoidal_biclosed {C : category} (M : monoidal C) : UU
    := monoidal_leftclosed M × monoidal_rightclosed M.

  Lemma adj_unique_up_to_nat_z_iso
        {C D : category} {F1 F2 : functor C D} (α : nat_z_iso F1 F2) (G : functor D C)
    : are_adjoints F2 G -> are_adjoints F1 G.
  Proof.
    intro adj.
    repeat (use tpair).
    - exact (λ x, (pr1 (pr1 adj) x) · #G (pr1 (pr2 α x))).
    - intros x y f.
      etrans. {
        rewrite assoc.
        apply cancel_postcomposition.
        exact (pr211 adj x y f).
      }

      etrans. {
        rewrite assoc'.
        apply maponpaths.
        simpl.
        apply (! functor_comp _ _ _).
      }

      use pathscomp0.
      3: {
        rewrite assoc'.
        apply maponpaths.
        simpl.
        apply (functor_comp _ _ _).
      }

      do 2 apply maponpaths.

      etrans. {
        apply maponpaths.
        rewrite (! id_right _).
        apply maponpaths.
        exact (! pr12 (pr2 α y)).
      }
      etrans. {
        rewrite assoc.
        apply assoc.
      }

      use pathscomp0.
      3: {
        apply maponpaths.
        rewrite (! id_right _).
        apply maponpaths.
        exact (pr12 (pr2 α y)).
      }

      use pathscomp0.
      3: {
        rewrite assoc.
        rewrite (assoc ( pr1 (pr2 α x) · # F1 f)).
        apply idpath.
      }
      apply cancel_postcomposition.
      use pathscomp0.
      3: {
        rewrite assoc'.
        apply maponpaths.
        exact (! (pr21 α) x y f).
      }

      etrans. {
        rewrite assoc'.
        apply maponpaths.
        apply (pr22 (pr2 α y)).
      }

      use pathscomp0.
      3: {
        rewrite assoc.
        apply cancel_postcomposition.
        apply (! pr22 (pr2 α x)).
      }
      rewrite id_left.
      apply id_right.
    - exact (λ x, (pr1 α (G x)) · (pr2 (pr1 adj) x)).
    - intros x y f.

      etrans. {
        rewrite assoc.
        apply cancel_postcomposition.
        apply (pr21 α).
      }

      etrans. { apply assoc'. }
      use pathscomp0.
      3: { apply assoc. }
      apply maponpaths.
      exact (pr2 (pr21 adj) _ _ f).
    - intro x.
      simpl.

      etrans. {
        rewrite assoc.
        apply cancel_postcomposition.
        rewrite functor_comp.
        rewrite assoc'.
        apply cancel_precomposition.
        apply (pr21 α).
      }

      etrans. {
        rewrite assoc'.
        apply cancel_precomposition.
        rewrite assoc'.
        apply cancel_precomposition.
        apply (pr221 adj).
      }

      etrans. {
        rewrite assoc.
        apply cancel_postcomposition.
        apply (pr21 α).
      }

      etrans. {
        rewrite assoc.
        apply cancel_postcomposition.
        rewrite assoc'.
        apply cancel_precomposition.
        apply ((pr12 adj) x).
      }
      rewrite id_right.
      apply (pr2 α).
    - intro x.
      refine (_ @ (pr22 adj x)).
      cbn.
      rewrite assoc'.
      apply maponpaths.

      rewrite (! functor_comp _ _ _).
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply cancel_postcomposition.
        apply (pr2 α).
      }
      apply maponpaths.
      apply id_left.
  Defined.

  Lemma leftclosed_symmetric_is_rightclosed {C : category} (M : monoidal C)
    : symmetric M -> monoidal_leftclosed M -> monoidal_rightclosed M.
  Proof.
    intros B LC.
    intro x.
    exists (monoidal_leftclosed_exp LC x).
    apply (adj_unique_up_to_nat_z_iso (F2 := rightwhiskering_functor M x)).
    - apply symmetric_whiskers_swap_nat_z_iso.
      exact B.
    - exact (pr2 (LC x)).
  Defined.

  Lemma leftclosed_symmetric_is_biclosed {C : category} (M : monoidal C)
    : symmetric M -> monoidal_leftclosed M -> monoidal_biclosed M.
  Proof.
    exact (λ S LC, LC ,, leftclosed_symmetric_is_rightclosed M S LC).
  Defined.

End ClosedMonoidalCategories.
