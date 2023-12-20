(* In this file, we combine the results that any bicategory is weak biequivalent to a locally univalent bicategory and
   that any locally univalent bicategory is weak biequivalent to a global univalent bicategory.
   This shows how any bicategory admits a Rezk completion.
   We also instantiate the result with the construction of the Rezk completion of categories using representable presheaves in order to do the "local Rezk completion".
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.YonedaLemma.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Properties.

Require Import UniMath.Bicategories.RezkCompletions.BicatToLocalUnivalentBicat.
Require Import UniMath.CategoryTheory.rezk_completion.
Require Import UniMath.CategoryTheory.RezkCompletion.

Local Open Scope cat.

Section RezkCompletionBicategory.

  Definition rezk_completion_2_1
             (R : RezkCat) (B : bicat)
    : ∑ RB : bicat,
        ∑ HB : psfunctor B RB,
          is_univalent_2_1 RB × weak_biequivalence HB.
  Proof.
    exists (LRB R B).
    exists (psfunctor_B_to_LRB R B).
    exists (LRB_is_locally_univalent R B).
    exact (psfunctor_B_to_LRB_is_weak_biequivalence R B).
  Defined.

  Definition rezk_completion_2 (R : RezkCat) (B : bicat)
    : ∑ RB : bicat,
        ∑ HB : psfunctor B RB,
          is_univalent_2 RB × weak_biequivalence HB.
  Proof.
    set (r := rezk_completion_2_0 (LRB R B) (LRB_is_locally_univalent R B)).
    exists (pr1 r).
    exists (comp_psfunctor (pr12 r) (psfunctor_B_to_LRB R B)).
    exists (pr122 r).
    use comp_weak_biequivalence.
    - apply psfunctor_B_to_LRB_is_weak_biequivalence.
    - exact (weak_equivalence_to_is_weak_biequivalence _ (pr222 r)).
  Defined.

End RezkCompletionBicategory.

Definition rezk_completion_2_presheaves
           (B : bicat)
  : ∑ RB : bicat,
        ∑ HB : psfunctor B RB,
        is_univalent_2 RB × weak_biequivalence HB.
Proof.
  use rezk_completion_2.
  exact (λ C, _ ,, _ ,, Rezk_eta_essentially_surjective C ,, Rezk_eta_fully_faithful C).
Defined.
