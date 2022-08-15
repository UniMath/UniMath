(*******************************************************************

 Every locally groupoidal category with pullback gives rise to
 a comprehension bicategory

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

Section PullbackComprehension.
  Context (B : bicat)
          (B_pb : has_pb B).

  Definition pb_comprehension
    : comprehension_bicat_structure B.
  Proof.
    use make_comprehension_bicat_structure.
    - exact (cod_disp_bicat B).
    - exact (disp_pseudo_id (cod_disp_bicat B)).
    - exact (cod_global_cleaving B B_pb).
    - exact (global_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Context (HB : locally_groupoid B).

  Definition locally_grpd_pb_comprehension_is_covariant
    : is_covariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_opcleaving _ HB).
    - exact (cod_cleaving_lwhisker_opcartesian _ HB).
    - exact (cod_cleaving_rwhisker_opcartesian _ HB).
    - exact (local_opcartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Definition locally_grpd_pb_comprehension_is_contravariant
    : is_contravariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_cleaving _ HB).
    - exact (cod_cleaving_lwhisker_cartesian _ HB).
    - exact (cod_cleaving_rwhisker_cartesian _ HB).
    - exact (local_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Definition locally_grpd_comprehension_bicat
    : comprehension_bicat
    := _ ,, _ ,, locally_grpd_pb_comprehension_is_covariant.

  Definition locally_grpd_contravariant_comprehension_bicat
    : contravariant_comprehension_bicat
    := _ ,, _ ,, locally_grpd_pb_comprehension_is_contravariant.
End PullbackComprehension.
