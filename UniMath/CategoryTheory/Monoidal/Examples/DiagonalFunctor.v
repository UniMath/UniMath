nner_swap
(**
nner_swap
Let V be a symmetric monoidal category,
nner_swap
we show how the "diagonal functor" V → V : x ↦ x ⊗ x is part of a strong monoidal functor.
nner_swap

nner_swap
*)
nner_swap

nner_swap
Require Import UniMath.Foundations.All.
nner_swap
Require Import UniMath.MoreFoundations.All.
nner_swap
Require Import UniMath.CategoryTheory.Core.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Core.Functors.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Functors.
nner_swap
Import BifunctorNotations.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
nner_swap

nner_swap
Local Open Scope cat.
nner_swap

nner_swap
Import MonoidalNotations.
nner_swap

nner_swap
Section DiagFunctor.
nner_swap

nner_swap
  Context (V : monoidal_cat).
nner_swap

nner_swap
  Definition diag_functor_data
nner_swap
    : functor_data V V.
nner_swap
  Proof.
nner_swap
    use make_functor_data.
nner_swap
    - exact (λ x, x ⊗_{V} x).
nner_swap
    - exact (λ _ _ f, f ⊗^{V} f).
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma diag_is_functor
nner_swap
    : is_functor diag_functor_data.
nner_swap
  Proof.
nner_swap
    split ; intro ; intros.
nner_swap
    - apply tensor_id_id.
nner_swap
    - apply tensor_comp_mor.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition diag_functor
nner_swap
    : functor V V.
nner_swap
  Proof.
nner_swap
    exists diag_functor_data.
nner_swap
    exact diag_is_functor.
nner_swap
  Defined.
nner_swap

nner_swap
End DiagFunctor.
nner_swap

nner_swap
Section DiagFunctorMonoidal.
nner_swap

nner_swap
  Context (V : sym_monoidal_cat).
nner_swap

nner_swap
  Let diag := diag_functor V.
nner_swap

nner_swap
  Definition diag_preserves_tensor_data
nner_swap
    : preserves_tensordata V V diag.
nner_swap
  Proof.
nner_swap
    exact (λ x y, rearrange_prod V x x y y).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition diag_preserves_unit
nner_swap
    : preserves_unit V V diag.
nner_swap
  Proof.
nner_swap
    apply mon_linvunitor.
nner_swap
  Defined.
nner_swap

nner_swap
  Definition diag_functor_fmonoidal_data
nner_swap
    : fmonoidal_data V V diag.
nner_swap
  Proof.
nner_swap
    exists diag_preserves_tensor_data.
nner_swap
    exact diag_preserves_unit.
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_nat_left
nner_swap
    : preserves_tensor_nat_left (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
nner_swap
  Proof.
nner_swap
    intros y x1 x2 f.
nner_swap
    apply pathsinv0.
nner_swap
    refine (_ @ precompose_rearrange_prod V (identity y) (identity y) f f @ _).
nner_swap
    - apply maponpaths.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0, (when_bifunctor_becomes_leftwhiskering V).
nner_swap
      }
nner_swap
      cbn ; apply maponpaths_2.
nner_swap
      apply pathsinv0, (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    - rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply tensor_id_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_nat_right
nner_swap
    : preserves_tensor_nat_right (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
nner_swap
  Proof.
nner_swap
    intros x1 x2 y f.
nner_swap
    apply pathsinv0.
nner_swap
    refine (_ @ precompose_rearrange_prod V f f (identity y) (identity y) @ _).
nner_swap
    - apply maponpaths.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
nner_swap
      }
nner_swap
      cbn ; apply maponpaths_2.
nner_swap
      apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    - rewrite <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
      apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply tensor_id_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_assoc
nner_swap
    : preserves_associativity (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
nner_swap
  Proof.
nner_swap
    intros x y z.
nner_swap
    refine (_ @ rearrange_hexagon'_3 (pr2 V) x y z @ _).
nner_swap
    - now rewrite <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    - now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_leftunitality
nner_swap
    : preserves_leftunitality
nner_swap
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
nner_swap
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
nner_swap
  Proof.
nner_swap
    intro x.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply (! precompose_rearrange_prod_with_lunitors_on_right V x x).
nner_swap
    }
nner_swap
    etrans. {
nner_swap
      rewrite ! assoc.
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply rearrange_prod_is_z_isomorphism.
nner_swap
    }
nner_swap
    rewrite id_right.
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
nner_swap
      apply maponpaths.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    }
nner_swap
    rewrite bifunctor_rightid.
nner_swap
    apply id_left.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_rightunitality
nner_swap
    : preserves_rightunitality
nner_swap
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
nner_swap
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
nner_swap
  Proof.
nner_swap
    intro x.
nner_swap
    cbn.
nner_swap
    unfold diag_preserves_unit.
nner_swap
    unfold diag_preserves_tensor_data.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      apply precompose_rearrange_prod_with_lunitors_and_runitor.
nner_swap
    }
nner_swap
    etrans. {
nner_swap
      rewrite ! assoc.
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply rearrange_prod_is_z_isomorphism.
nner_swap
    }
nner_swap
    rewrite id_right.
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _).
nner_swap
      apply maponpaths.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    }
nner_swap
    rewrite (bifunctor_leftid V).
nner_swap
    apply id_left.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma diag_functor_fmonoidal_laxlaws
nner_swap
    : fmonoidal_laxlaws diag_functor_fmonoidal_data.
nner_swap
  Proof.
nner_swap
    repeat split.
nner_swap
    - exact diag_functor_fmonoidal_nat_left.
nner_swap
    - exact diag_functor_fmonoidal_nat_right.
nner_swap
    - exact diag_functor_fmonoidal_assoc.
nner_swap
    - exact diag_functor_fmonoidal_leftunitality.
nner_swap
    - exact diag_functor_fmonoidal_rightunitality.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition diag_functor_fmonoidal_lax
nner_swap
    : fmonoidal_lax V V diag.
nner_swap
  Proof.
nner_swap
    exists diag_functor_fmonoidal_data.
nner_swap
    exact diag_functor_fmonoidal_laxlaws.
nner_swap
  Defined.
nner_swap

nner_swap
  Definition diag_functor_is_strong_fmonoidal
nner_swap
    : fmonoidal_stronglaws
nner_swap
         (fmonoidal_preservestensordata diag_functor_fmonoidal_lax)
nner_swap
         (fmonoidal_preservesunit diag_functor_fmonoidal_lax).
nner_swap
  Proof.
nner_swap
    unfold fmonoidal_stronglaws.
nner_swap
    split.
nner_swap
    - intro ; intro.
nner_swap
      apply rearrange_prod_is_z_isomorphism.
nner_swap
    - refine (_ ,, _).
nner_swap
      split ; apply (monoidal_leftunitorisolaw V I_{V}).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition diag_functor_fmonoidal
nner_swap
    : fmonoidal V V diag.
nner_swap
  Proof.
nner_swap
    exists diag_functor_fmonoidal_lax.
nner_swap
    exact diag_functor_is_strong_fmonoidal.
nner_swap
  Defined.
nner_swap

nner_swap
  Definition diag_functor_is_symmetric
nner_swap
    : is_symmetric_monoidal_functor V V diag_functor_fmonoidal.
nner_swap
  Proof.
nner_swap
    intro ; intro.
nner_swap
    apply pathsinv0.
nner_swap
    apply (rearrange_commute_with_swap V).
nner_swap
  Defined.
nner_swap

nner_swap
  (* Definition diag_functor_lax_monoidal_functor
nner_swap
    : lax_monoidal_functor V V.
nner_swap
  Proof.
nner_swap
    use make_lax_monoidal_functor.
nner_swap
    - exact diag.
nner_swap
    - exact diag_preserves_tensor_data.
nner_swap
    - exact diag_preserves_unit.
nner_swap
    - . *)
nner_swap

nner_swap
End DiagFunctorMonoidal.
