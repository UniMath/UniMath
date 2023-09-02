(************************************************************************

 Every natural transformation gives rise to an indexed transformation

 We prove that every displayed natural transformation between two
 cartesian functors gives rise to a indexed transformation between the
 corresponding indexed functors. The data of the indexed transformation
 can directly be constructed from the displayed transformation, and the
 only work is proving the laws.

 Contents
 1. The data
 2. The naturality
 3. The indexed natural transformation

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformation.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.CartesianToIndexedFunctor.

Section NatTransToIndexedNatTrans.
  Context {C : category}
          {D₁ D₂ : disp_univalent_category C}
          (HD₁ : cleaving D₁)
          (HD₂ : cleaving D₂)
          {F G : cartesian_disp_functor (functor_identity C) D₁ D₂}
          (τ : disp_nat_trans (nat_trans_id _) F G).

  (**
   1. The data
   *)
  Definition disp_nat_trans_to_indexed_nat_trans_data
    : indexed_nat_trans_data
        (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F)
        (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ G).
  Proof.
    intro x.
    use make_nat_trans.
    - exact (λ xx, τ x xx).
    - abstract
        (intros xx yy ff ; cbn ;
         refine (maponpaths (transportf _ _) (disp_nat_trans_ax τ ff) @ _) ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
  Defined.

  (**
   2. The naturality
   *)
  Proposition disp_nat_trans_to_indexed_nat_trans_law
    : indexed_nat_trans_law disp_nat_trans_to_indexed_nat_trans_data.
  Proof.
    intros x y f xx ; cbn.
    refine (!_).
    use (cartesian_factorisation_unique
           (cartesian_disp_functor_on_cartesian G (HD₁ _ _ _ _))).
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite transport_f_f.
    refine (!_).
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply (disp_nat_trans_ax_var τ).
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  (**
   3. The indexed natural transformation
   *)
  Definition disp_nat_trans_to_indexed_nat_trans
    : indexed_nat_trans
        (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F)
        (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ G).
  Proof.
    use make_indexed_nat_trans.
    - exact disp_nat_trans_to_indexed_nat_trans_data.
    - exact disp_nat_trans_to_indexed_nat_trans_law.
  Defined.
End NatTransToIndexedNatTrans.
