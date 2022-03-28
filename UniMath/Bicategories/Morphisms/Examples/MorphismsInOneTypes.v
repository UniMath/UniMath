(**
 Morphisms in the bicat of univalent categories

 Contents:
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

(**
 1. Faithful 1-cells
 *)
Definition one_types_is_incl_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
  : faithful_1cell f.
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  use funextsec.
  intro x.
  cbn in * ; unfold homotfun in *.
  pose (Hf (g₁ x) (g₂ x) (maponpaths f (α₂ x))) as i.
  pose (proofirrelevance _ i (α₁ x ,, eqtohomot p x) (α₂ x ,, idpath _)) as k.
  exact (maponpaths pr1 k).
Qed.

Definition one_types_faithful_1cell_is_incl
           {X Y : one_types}
           (f : X --> Y)
           (Hf : faithful_1cell f)
  : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y).
Proof.
  intros x y ; cbn in *.
  use isinclweqonpaths.
  intros p q.
  use isweqimplimpl.
  - intros α.
    pose (eqtohomot
            (Hf X (λ _, x) (λ _, y)
                (λ _, p) (λ _, q)
                (funextsec _ _ _ (λ _, α)))
            x)
      as fp.
    exact fp.
  - use invproofirrelevance.
    intros ? ?.
    apply X.
  - use invproofirrelevance.
    intros ? ?.
    apply Y.
Qed.

Definition one_types_is_incl_weq_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
  : (∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
    ≃
    faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_is_incl_faithful_1cell f).
  - exact (one_types_faithful_1cell_is_incl f).
  - do 2 (use impred ; intro).
    apply isapropisincl.
  - apply isaprop_faithful_1cell.
Qed.

(**
 2. Fully faithful 1-cells
 *)
Definition one_types_isInjective_fully_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : isInjective f)
  : fully_faithful_1cell f.
Proof.
  use make_fully_faithful.
  - apply one_types_is_incl_faithful_1cell.
    intros x y.
    apply isinclweq.
    apply Hf.
  - intros Z g₁ g₂ αf ; cbn in * ; unfold homotfun in *.
    simple refine (_ ,, _).
    + intro x.
      apply (invmap (make_weq _ (Hf (g₁ x) (g₂ x)))).
      exact (αf x).
    + use funextsec.
      intro x.
      apply (homotweqinvweq (make_weq _ (Hf (g₁ x) (g₂ x)))).
Qed.

Definition one_types_fully_faithful_isInjective
           {X Y : one_types}
           (f : X --> Y)
           (Hf : fully_faithful_1cell f)
  : isInjective f.
Proof.
  intros x y ; cbn in *.
  use gradth.
  - intro p.
    exact (pr1 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p)) x).
  - intro p ; simpl.
    pose (pr1 Hf
               _ _ _
               (pr1 (pr2 Hf X (λ _ : X, x) (λ _ : X, y) (λ _ : X, maponpaths f p)))
               (λ _, p))
      as q.
    cbn in q.
    refine (eqtohomot (q _) x).
    unfold homotfun.
    use funextsec.
    intro ; cbn.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, maponpaths f p))) _).
  - intros p.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p))) x).
Qed.

Definition one_types_isInjective_weq_fully_faithful
           {X Y : one_types}
           (f : X --> Y)
  : isInjective f ≃ fully_faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_isInjective_fully_faithful_1cell f).
  - exact (one_types_fully_faithful_isInjective f).
  - apply isaprop_isInjective.
  - apply isaprop_fully_faithful_1cell.
Qed.
