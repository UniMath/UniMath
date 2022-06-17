(******************************************************************

 Preservation of biinitial and bifinal objects by biadjoints

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Limits.Final.

Local Open Scope cat.

Section BiadjunctionPreservation.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L).

  Definition left_biadj_preserves_biinitial
    : preserves_biinitial L.
  Proof.
    intros x Hx.
    use is_biinitial_repr_to_is_biinitial.
    intro y.
    use nat_iso_adj_equivalence_of_cats.
    - exact (biadj_right_hom R x y ∙ functor_to_unit _).
    - use make_nat_trans.
      + exact (λ _, idpath _).
      + abstract
          (intros f g α ;
           apply isapropunit).
    - intros f.
      use is_iso_qinv ; cbn.
      + apply idpath.
      + abstract (split ; apply idpath).
    - use comp_adj_equivalence_of_cats.
      + exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y)).
      + exact (is_biinitial_to_is_biinitial_repr Hx (R y)).
  Defined.

  (**
   2. Preservation of bifinal objects
   *)
  Definition right_biadj_preserves_bifinal
    : preserves_bifinal R.
  Proof.
    intros y Hy.
    use is_bifinal_repr_to_is_bifinal.
    intro x.
    use nat_iso_adj_equivalence_of_cats.
    - exact (biadj_left_hom R x y ∙ functor_to_unit _).
    - use make_nat_trans.
      + exact (λ _, idpath _).
      + abstract
          (intros f g α ;
           apply isapropunit).
    - intros f.
      use is_iso_qinv ; cbn.
      + apply idpath.
      + abstract (split ; apply idpath).
    - use comp_adj_equivalence_of_cats.
      + exact (biadj_hom_equiv R x y).
      + exact (is_bifinal_to_is_bifinal_repr Hy (L x)).
  Defined.
End BiadjunctionPreservation.
