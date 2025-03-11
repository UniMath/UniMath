Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Section IdempotentsSplitInFullSubCats.

  Context {X : category} (P : X → hProp)
    (Xs : idempotents_split X).

  Lemma split_in_fullsub_to_base {x : full_subcat X (λ x : X, P x)}
    {e : X⟦pr1 x, pr1 x⟧}
    {g : is_idempotent e}
    (ei : is_split_idempotent e)
    : is_split_idempotent (C := full_subcat _ _) (e ,, tt)
      → is_split_idempotent e.
  Proof.
    intro s.
    induction s as [[y ?] [[[r ?] [[s ?] ss]] p]].
    cbn in *.
    exists y.
    simple refine ((_ ,, (_,,_)) ,, _).
    - exact r.
    - exact s.
    - exact (base_paths _ _ ss).
    - exact (base_paths _ _ p).
  Defined.

  Proposition idempotents_split_in_full_subcat
    (cl : ∏ x : full_subcat _ P, ∏ c : X, retraction c (pr1 x) → P c)
    : idempotents_split (full_subcat _ P).
  Proof.
    intros x f.
    use (factor_through_squash _ _ (Xs (pr1 x) (pr11 f ,, base_paths _ _ (pr2 f)))).
    { apply isapropishinh. }
    intro ei.
    apply hinhpr.
    exists (pr1 ei ,, cl x (pr1 ei) (pr12 ei)).
    simple refine ((_ ,, _ ,, _) ,, _) ; simpl.
    - exact (pr112 ei ,, tt).
    - exact (pr1 (pr212 ei) ,, tt).
    - use subtypePath.
      { intro ; apply isapropifcontr, iscontrunit. }
      exact (pr2 (pr212 ei)).
    - use subtypePath.
      { intro ; apply isapropifcontr, iscontrunit. }
      exact (pr22 ei).
  Defined.

End IdempotentsSplitInFullSubCats.
