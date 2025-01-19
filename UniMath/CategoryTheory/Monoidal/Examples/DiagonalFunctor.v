(**
Let V be a symmetric monoidal category,
we show how the "diagonal functor" V → V : x ↦ x ⊗ x is part of a strong monoidal functor.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section DiagFunctor.

  Context (V : monoidal_cat).

  Definition diag_functor_data
    : functor_data V V.
  Proof.
    use make_functor_data.
    - exact (λ x, x ⊗ x).
    - exact (λ _ _ f, f #⊗ f).
  Defined.

  Lemma diag_is_functor
    : is_functor diag_functor_data.
  Proof.
    split ; intro ; intros.
    - apply tensor_id_id.
    - apply tensor_comp_mor.
  Qed.

  Definition diag_functor
    : functor V V.
  Proof.
    exists diag_functor_data.
    exact diag_is_functor.
  Defined.

End DiagFunctor.

Section DiagFunctorMonoidal.

  Context (V : sym_monoidal_cat).

  Let diag := diag_functor V.

  Definition diag_preserves_tensor_data
    : preserves_tensordata V V diag.
  Proof.
    exact (λ x y, inner_swap V x x y y).
  Defined.

  Definition diag_preserves_unit
    : preserves_unit V V diag.
  Proof.
    apply mon_linvunitor.
  Defined.

  Definition diag_functor_fmonoidal_data
    : fmonoidal_data V V diag.
  Proof.
    exists diag_preserves_tensor_data.
    exact diag_preserves_unit.
  Defined.

  Lemma diag_functor_fmonoidal_nat_left
    : preserves_tensor_nat_left (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros y x1 x2 f.
    apply pathsinv0.
    refine (_ @ naturality_inner_swap V (identity y) (identity y) f f @ _).
    - apply maponpaths.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0, (when_bifunctor_becomes_leftwhiskering V).
      }
      cbn ; apply maponpaths_2.
      apply pathsinv0, (when_bifunctor_becomes_leftwhiskering V).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering V).
      do 2 apply maponpaths_2.
      apply tensor_id_id.
  Qed.

  Lemma diag_functor_fmonoidal_nat_right
    : preserves_tensor_nat_right (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros x1 x2 y f.
    apply pathsinv0.
    refine (_ @ naturality_inner_swap V f f (identity y) (identity y) @ _).
    - apply maponpaths.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
      }
      cbn ; apply maponpaths_2.
      apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering V).
      apply maponpaths_2.
      apply maponpaths.
      apply tensor_id_id.
  Qed.

  Lemma diag_functor_fmonoidal_assoc
    : preserves_associativity (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros x y z.
    refine (_ @ inner_swap_hexagon'_3 V x y z @ _).
    - now rewrite <- (when_bifunctor_becomes_rightwhiskering V).
    - now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
  Qed.

  Lemma diag_functor_fmonoidal_leftunitality
    : preserves_leftunitality
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
  Proof.
    intro x.

    etrans. {
      apply maponpaths.
      apply (! precompose_inner_swap_with_lunitors_on_right V x x).
    }
    etrans. {
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply inner_swap_is_z_isomorphism.
    }
    rewrite id_right.
    etrans. {
      apply maponpaths_2.
      refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply monoidal_leftunitorisolaw.
    }
    rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Lemma diag_functor_fmonoidal_rightunitality
    : preserves_rightunitality
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
  Proof.
    intro x.
    cbn.
    unfold diag_preserves_unit.
    unfold diag_preserves_tensor_data.
    etrans. {
      apply maponpaths.
      apply pathsinv0.
      apply precompose_inner_swap_with_lunitors_and_runitor.
    }
    etrans. {
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply inner_swap_is_z_isomorphism.
    }
    rewrite id_right.
    etrans. {
      apply maponpaths_2.
      refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply monoidal_leftunitorisolaw.
    }
    rewrite (bifunctor_leftid V).
    apply id_left.
  Qed.

  Lemma diag_functor_fmonoidal_laxlaws
    : fmonoidal_laxlaws diag_functor_fmonoidal_data.
  Proof.
    repeat split.
    - exact diag_functor_fmonoidal_nat_left.
    - exact diag_functor_fmonoidal_nat_right.
    - exact diag_functor_fmonoidal_assoc.
    - exact diag_functor_fmonoidal_leftunitality.
    - exact diag_functor_fmonoidal_rightunitality.
  Qed.

  Definition diag_functor_fmonoidal_lax
    : fmonoidal_lax V V diag.
  Proof.
    exists diag_functor_fmonoidal_data.
    exact diag_functor_fmonoidal_laxlaws.
  Defined.

  Definition diag_functor_is_strong_fmonoidal
    : fmonoidal_stronglaws
         (fmonoidal_preservestensordata diag_functor_fmonoidal_lax)
         (fmonoidal_preservesunit diag_functor_fmonoidal_lax).
  Proof.
    unfold fmonoidal_stronglaws.
    split.
    - intro ; intro.
      apply inner_swap_is_z_isomorphism.
    - refine (_ ,, _).
      split ; apply (monoidal_leftunitorisolaw V I_{V}).
  Defined.

  Definition diag_functor_fmonoidal
    : fmonoidal V V diag.
  Proof.
    exists diag_functor_fmonoidal_lax.
    exact diag_functor_is_strong_fmonoidal.
  Defined.

  Definition diag_functor_is_symmetric
    : is_symmetric_monoidal_functor V V diag_functor_fmonoidal.
  Proof.
    intro ; intro.
    apply pathsinv0.
    apply (inner_swap_commute_with_swap V).
  Defined.

  (* Definition diag_functor_lax_monoidal_functor
    : lax_monoidal_functor V V.
  Proof.
    use make_lax_monoidal_functor.
    - exact diag.
    - exact diag_preserves_tensor_data.
    - exact diag_preserves_unit.
    - . *)

End DiagFunctorMonoidal.
