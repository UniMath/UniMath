(** the Eilenberg-Moore category for a symmetric monoidal comonad
    as a symmetric monoidal category

author: Ralph Matthes, August 2023

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalDialgebras.
Require Import UniMath.CategoryTheory.categories.CoEilenbergMoore.


Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section Construction.

  Context {C : category} {M : monoidal C} {HM : symmetric M}
    (T : symmetric_monoidal_comonad HM).

  Definition mon_cat_co_eilenberg_moore_base
    : monoidal (dialgebra (functor_identity C) T)
    := dialgebra_monoidal (identity_fmonoidal M)
         (lax_monoidal_from_symmetric_monoidal_comonad HM T).

  Definition sym_mon_cat_co_eilenberg_moore_base
    : symmetric mon_cat_co_eilenberg_moore_base.
  Proof.
    apply (dialgebra_symmetric_monoidal(Fm:=identity_fmonoidal M)
             (is_symmetric_monoidal_identity HM) (pr221 T)).
  Defined.

  Definition mon_cat_co_eilenberg_moore_extra_condition
    : dialgebra (functor_identity C) T -> UU
    := fun f => pr1 (co_eilenberg_moore_cat_pred T f).

  Definition cat_co_eilenberg_moore : category
    := full_subcat (dialgebra (functor_identity C) T)
           mon_cat_co_eilenberg_moore_extra_condition.

  Local Lemma unit_case : mon_cat_co_eilenberg_moore_extra_condition
                            I_{ mon_cat_co_eilenberg_moore_base}.
  Proof.
    split.
    - cbn. unfold dialgebra_disp_unit. cbn.
      rewrite id_left.
      assert (H := symmetric_monoidal_comonad_extra_laws HM T).
      destruct H as [_ [_ H]].
      exact H.
    - cbn. unfold dialgebra_disp_unit. cbn.
      rewrite id_left.
      assert (H := symmetric_monoidal_comonad_extra_laws HM T).
      destruct H as [[_ H] _].
      exact H.
  Qed.

  Local Lemma tensor_case : ∏ (f g : dialgebra (functor_identity C) T)
    (Hf : mon_cat_co_eilenberg_moore_extra_condition f)
    (Hg : mon_cat_co_eilenberg_moore_extra_condition g),
    mon_cat_co_eilenberg_moore_extra_condition
      (f ⊗_{mon_cat_co_eilenberg_moore_base} g).
  Proof.
    intros.
    split.
    - cbn. unfold dialgebra_disp_tensor_op. cbn.
      rewrite id_left.
      assert (H := symmetric_monoidal_comonad_extra_laws HM T).
      destruct H as [_ [H _]].
      red in H.
      rewrite assoc'.
      rewrite H. clear H.
      cbn.
      rewrite id_right.
      destruct Hf as [Hf _]. destruct Hg as [Hg _].
      etrans.
      { apply pathsinv0, bifunctor_distributes_over_comp.
        + exact (bifunctor_leftcomp M).
        + exact (bifunctor_rightcomp M).
        + exact (bifunctor_equalwhiskers M). }
      etrans.
      { apply maponpaths_12.
        - exact Hf.
        - exact Hg.
      }
      apply bifunctor_distributes_over_id.
        + exact (bifunctor_leftid M).
        + exact (bifunctor_rightid M).
    - cbn. unfold dialgebra_disp_tensor_op. cbn.
      rewrite id_left.
      assert (H := symmetric_monoidal_comonad_extra_laws HM T).
      destruct H as [[H _] _].
      red in H.
      rewrite assoc'.
      rewrite H. clear H.
      cbn.
      destruct Hf as [_ Hf]. destruct Hg as [_ Hg].
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        etrans.
        { apply pathsinv0, bifunctor_distributes_over_comp.
          + exact (bifunctor_leftcomp M).
          + exact (bifunctor_rightcomp M).
          + exact (bifunctor_equalwhiskers M). }
        etrans.
        { apply maponpaths_12.
          - exact Hf.
          - exact Hg. }
        apply bifunctor_distributes_over_comp.
          + exact (bifunctor_leftcomp M).
          + exact (bifunctor_rightcomp M).
          + exact (bifunctor_equalwhiskers M).
      }
      clear Hf Hg.
      repeat rewrite assoc'.
      apply maponpaths.
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply (preservestensor_is_nattrans_full
               (fmonoidal_preservestensornatleft
                  (lax_monoidal_from_symmetric_monoidal_comonad HM T))
               (fmonoidal_preservestensornatright
                  (lax_monoidal_from_symmetric_monoidal_comonad HM T))).
  Qed.

  Definition mon_cat_co_eilenberg_moore_category : category :=
    full_subcat (dialgebra (functor_identity C) T)
      mon_cat_co_eilenberg_moore_extra_condition.

  Definition monoidal_cat_co_eilenberg_moore : monoidal _ :=
    monoidal_fullsubcat mon_cat_co_eilenberg_moore_base
      mon_cat_co_eilenberg_moore_extra_condition unit_case tensor_case.

  (* slow:
     Check (monoidal_cat_co_eilenberg_moore : monoidal cat_co_eilenberg_moore).
   *)

  Definition symmetric_monoidal_cat_co_eilenberg_moore :
    symmetric monoidal_cat_co_eilenberg_moore.
  Proof.
    apply (symmetric_monoidal_fullsubcat
             mon_cat_co_eilenberg_moore_base
             mon_cat_co_eilenberg_moore_extra_condition
             unit_case
             tensor_case
             sym_mon_cat_co_eilenberg_moore_base).
  Defined.

  Definition sym_monoidal_cat_co_eilenberg_moore : sym_monoidal_cat.
  Proof.
    use tpair.
    - use tpair.
      + exact mon_cat_co_eilenberg_moore_category.
      + exact monoidal_cat_co_eilenberg_moore.
    - apply symmetric_monoidal_cat_co_eilenberg_moore.
  Defined.

End Construction.
