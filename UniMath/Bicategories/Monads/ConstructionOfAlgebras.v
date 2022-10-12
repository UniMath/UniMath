(****************************************************************************************

 Construction of algebras

 In the 'Formal Theory of Monads' by Street, the core definition is when a 2-category
 has the construction of algebras, which says that the inclusion of that 2-category
 into the monads has a right adjoint.

 We take a slightly different approach: instead, we define this notion using limits.
 More specifically, we look at Eilenberg-Moore objects. In this file, we show that these
 two notions are indeed equivalent.

 Contents
 1. Definition
 2. Equivalence with having Eilenberg-Moore objects

 ****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

(**
 1. Definition
 *)
Definition has_construction_of_algs
           (B : bicat)
  : UU
  := right_universal_arrow (mnd_incl B).

(**
 2. Equivalence with having Eilenberg-Moore objects
 *)
Section ConstructionOfAlgsToEM.
  Context {B : bicat}
          (HB : has_construction_of_algs B).

  Definition has_construction_of_algs_cone
             (m : mnd B)
    : em_cone m
    := pr1 HB m ,, pr12 HB m.

  Definition has_construction_of_algs_to_em_mnd_cell_data
             {x : B}
             {m : mnd B}
             (f : x --> pr1 HB m)
    : mnd_cell_data
        (# (mnd_incl B) f · (pr12 HB) m)
        (em_hom_functor m (has_construction_of_algs_cone m) x f)
    := id2 _.

  Definition has_construction_of_algs_to_em_is_mnd_cell
             {x : B}
             {m : mnd B}
             (f : x --> pr1 HB m)
    : is_mnd_cell (has_construction_of_algs_to_em_mnd_cell_data f).
  Proof.
    unfold is_mnd_cell ; cbn.
    unfold has_construction_of_algs_to_em_mnd_cell_data.
    rewrite id2_rwhisker, lwhisker_id2.
    rewrite id2_left, id2_right.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocr.
    rewrite runitor_rwhisker.
    rewrite !vassocl.
    rewrite linvunitor_assoc.
    apply idpath.
  Qed.

  Definition has_construction_of_algs_to_em_mnd_cell
             {x : B}
             {m : mnd B}
             (f : x --> pr1 HB m)
    : # (mnd_incl B) f · pr12 HB m
      ==>
      em_hom_functor m (has_construction_of_algs_cone m) x f.
  Proof.
    use make_mnd_cell.
    - exact (has_construction_of_algs_to_em_mnd_cell_data f).
    - exact (has_construction_of_algs_to_em_is_mnd_cell f).
  Defined.

  Definition has_construction_of_algs_to_em_is_nat_trans
             (x : B)
             (m : mnd B)
    : is_nat_trans
        (right_universal_arrow_functor (mnd_incl B) x m (pr12 HB))
        (em_hom_functor m (pr1 HB m,, (pr12 HB) m) x)
        has_construction_of_algs_to_em_mnd_cell.
  Proof.
    intros f₁ f₂ α.
    use eq_mnd_cell ; cbn.
    exact (id2_right _ @ !(id2_left _)).
  Qed.

  Definition has_construction_of_algs_to_em_nat_trans
             (x : B)
             (m : mnd B)
    : right_universal_arrow_functor (mnd_incl B) x m (pr12 HB)
      ⟹
      em_hom_functor m (pr1 HB m,, (pr12 HB) m) x.
  Proof.
    use make_nat_trans.
    - exact has_construction_of_algs_to_em_mnd_cell.
    - exact (has_construction_of_algs_to_em_is_nat_trans x m).
  Defined.

  Definition has_construction_of_algs_to_em
    : bicat_has_em B.
  Proof.
    intro m.
    simple refine (_ ,, _).
    - exact (has_construction_of_algs_cone m).
    - apply is_universal_has_em_ump.
      intros x.
      use (nat_iso_adj_equivalence_of_cats _ _ (pr22 HB x m)).
      + exact (has_construction_of_algs_to_em_nat_trans x m).
      + intro f.
        use is_inv2cell_to_is_z_iso.
        use is_invertible_mnd_2cell.
        cbn ; unfold has_construction_of_algs_to_em_mnd_cell_data.
        is_iso.
  Defined.
End ConstructionOfAlgsToEM.

Section EMToConstructionOfAlgs.
  Context {B : bicat}
          (HB : bicat_has_em B).

  Definition em_to_has_construction_of_algs_nat_mnd_cell_data
             {m : mnd B}
             {x : B}
             (f : x --> pr1 (HB m))
    : mnd_cell_data
        (em_hom_functor m (pr1 (HB m)) x f)
        (right_universal_arrow_functor (mnd_incl B) x m (λ m0 : mnd B, pr21 (HB m0)) f)
    := id2 _.

  Definition em_to_has_construction_of_algs_nat_is_mnd_cell
             {m : mnd B}
             {x : B}
             (f : x --> pr1 (HB m))
    : is_mnd_cell (em_to_has_construction_of_algs_nat_mnd_cell_data f).
  Proof.
    unfold is_mnd_cell.
    unfold em_to_has_construction_of_algs_nat_mnd_cell_data.
    etrans.
    {
      apply maponpaths.
      apply lwhisker_id2.
    }
    refine (id2_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply id2_rwhisker.
    }
    refine (id2_left _ @ _).
    refine (!_).
    do 2 refine (vassocl _ _ _ @ _).
    cbn.
    do 3 refine (_ @ vassocr _ _ _).
    do 2 apply maponpaths.
    refine (!_).
    refine (vassocr _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply rwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      apply runitor_rwhisker.
    }
    refine (vassocl _ _ _ @ _).
    apply maponpaths.
    refine (!_).
    apply linvunitor_assoc.
  Qed.

  Definition em_to_has_construction_of_algs_nat_mnd_cell
             {m : mnd B}
             {x : B}
             (f : x --> pr1 (HB m))
    : em_hom_functor m (pr1 (HB m)) x f
      ==>
      right_universal_arrow_functor (mnd_incl B) x m (λ m0 : mnd B, pr21 (HB m0)) f.
  Proof.
    use make_mnd_cell.
    - exact (em_to_has_construction_of_algs_nat_mnd_cell_data f).
    - exact (em_to_has_construction_of_algs_nat_is_mnd_cell f).
  Defined.

  Definition em_to_has_construction_of_algs_is_nat_trans
             (m : mnd B)
             (x : B)
    : is_nat_trans
        (em_hom_functor m (pr1 (HB m)) x)
        (right_universal_arrow_functor (mnd_incl B) x m (λ m0 : mnd B, pr21 (HB m0)))
        em_to_has_construction_of_algs_nat_mnd_cell.
  Proof.
    intros f₁ f₂ α.
    use eq_mnd_cell.
    exact (id2_right _ @ !(id2_left _)).
  Qed.

  Definition em_to_has_construction_of_algs_nat_trans
             (m : mnd B)
             (x : B)
    : em_hom_functor m (pr1 (HB m)) x
      ⟹
      right_universal_arrow_functor (mnd_incl B) x m (λ m0 : mnd B, pr21 (HB m0)).
  Proof.
    use make_nat_trans.
    - exact em_to_has_construction_of_algs_nat_mnd_cell.
    - exact (em_to_has_construction_of_algs_is_nat_trans m x).
  Defined.

  Definition em_to_has_construction_of_algs
    : has_construction_of_algs B.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (λ m, pr1 (HB m)).
    - exact (λ m, pr21 (HB m)).
    - intros x m.
      use (nat_iso_adj_equivalence_of_cats
             _ _
             (has_em_ump_is_universal m (pr2 (HB m)) x)).
      + exact (em_to_has_construction_of_algs_nat_trans m x).
      + intro f.
        use is_inv2cell_to_is_z_iso.
        use is_invertible_mnd_2cell.
        cbn ; unfold em_to_has_construction_of_algs_nat_mnd_cell_data.
        is_iso.
  Defined.
End EMToConstructionOfAlgs.

Definition has_construction_of_algs_weq_has_em_inv₁
           {B : bicat}
           (HB₁ : is_univalent_2_1 B)
           (HB₂ : has_construction_of_algs B)
  : em_to_has_construction_of_algs (has_construction_of_algs_to_em HB₂) = HB₂.
Proof.
  refine (maponpaths (λ z, _ ,, _ ,, z) _).
  use funextsec ; intro x.
  use funextsec ; intro m.
  enough (isaprop
            (adj_equivalence_of_cats
               (right_universal_arrow_functor (mnd_incl B) x m (pr12 HB₂))))
    as X.
  {
    apply X.
  }
  use isofhlevelweqf.
  - exact (@left_adjoint_equivalence
             bicat_of_univ_cats
             (univ_hom HB₁ x (pr1 HB₂ m))
             (univ_hom (is_univalent_2_1_mnd _ HB₁) (mnd_incl B x) m)
             (right_universal_arrow_functor (mnd_incl B) x m (pr12 HB₂))).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom _ _ _)
               _
               _).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
Qed.

Definition has_construction_of_algs_weq_has_em_inv₂
           {B : bicat}
           (HB₁ : is_univalent_2_1 B)
           (HB₂ : bicat_has_em B)
  : has_construction_of_algs_to_em (em_to_has_construction_of_algs HB₂) = HB₂.
Proof.
  use funextsec ; intro m.
  refine (maponpaths (λ z, _ ,, z) _).
  apply isaprop_has_em_ump.
  exact HB₁.
Qed.

Definition has_construction_of_algs_weq_has_em
           (B : bicat)
           (HB : is_univalent_2_1 B)
  : has_construction_of_algs B ≃ bicat_has_em B.
Proof.
  use make_weq.
  - exact has_construction_of_algs_to_em.
  - use gradth.
    + exact em_to_has_construction_of_algs.
    + apply has_construction_of_algs_weq_has_em_inv₁.
      exact HB.
    + apply has_construction_of_algs_weq_has_em_inv₂.
      exact HB.
Defined.
