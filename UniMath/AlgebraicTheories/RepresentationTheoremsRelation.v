(**************************************************************************************************

  The Relation Between the Representation Theorems

  Scott's and Hyland's representation theorems for a lambda theory L are related by a diagram of
  embeddings and equivalences:

         R                            ≃                   set_karoubi (L 1)
                                                                ↓
  presheaf_cat L ≃ PreShv (lawvere L) ≃ PreShv (L 1) ↩ univalent_karoubi (L 1)

  Moreover, when the reflexive object U of Scott's proof is chased along this diagram, the result is
  isomorphic to Hyland's reflexive object theory_presheaf L.

  Contents
  1. The diagram [scott_to_hyland]
  2. The isomorphism between the reflexive objects [scott_to_hyland_U_to_L]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.Core.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.RezkCompletion.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.SetKaroubi.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.UnivalentKaroubi.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.OppositeCategory.LimitsAsColimits.
Require Import UniMath.CategoryTheory.OppositeCategory.OppositeEquivalence.
Require Import UniMath.CategoryTheory.OppositeCategory.OppositeOfFunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.RezkCompletions.RezkCompletions.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToLawvereTheory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToMonoid.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.PresheafCategoryCore.
Require Import UniMath.AlgebraicTheories.PresheafEquivalence.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope cat.

Section Diagram.

  Context (L : β_lambda_theory).


(** * 1. The diagram *)

  Let C0 : setcategory := algebraic_theory_monoid_category L.
  Let C1 : setcategory := algebraic_theory_to_lawvere (L : algebraic_theory).

  Let D1 : category := R (n := 0) L (β_lambda_theory_has_β L).
  Let D2 : category := set_karoubi C0.
  Let D3 : category := univalent_karoubi C0.
  Let D4 : category := PreShv C0.
  Let D4': category := [C0, HSET^opp]^opp.
  Let D5': category := [C1, HSET^opp]^opp.
  Let D5 : category := PreShv C1.
  Let D6 : category := presheaf_cat L.

  Let F1 : adj_equiv D1 D2  := algebraic_theory_retracts_equiv_set_karoubi L.
  Let F2 : D2 ⟶ D3          := rezk_completion_functor (karoubi_rezk_completion _).
  Let F3 : D3 ⟶ D4          := pr1_category _.
  Let F4': adj_equiv D4 D4' := _ ,, opfunctorcat_adjequiv_functorcatofoppcats _ (HSET^opp).
  Let F4 : adj_equiv D4' D5':= adj_equiv_opposite (lawvere_theory_presheaf_equiv_monoid_presheaf L (HSET^opp) (Lims_op LimsHSET)).
  Let F5': adj_equiv D5 D5' := _ ,, opfunctorcat_adjequiv_functorcatofoppcats _ (HSET^opp).
  Let F5 : adj_equiv D6 D5  := _ ,, algebraic_presheaf_weq_lawere_presheaf L.

  Definition scott_to_hyland
    : R L (β_lambda_theory_has_β L) ⟶ presheaf_cat L
    := F1 ∙ F2 ∙ F3 ∙ F4' ∙ F4 ∙ adj_equiv_inv F5' ∙ adj_equiv_inv F5.

  Definition scott_to_hyland_fully_faithful
    : fully_faithful scott_to_hyland.
  Proof.
    refine (comp_ff_is_ff _ _ _ _ _ _ (fully_faithful_from_equivalence _ _ _ (adj_equiv_inv _))).
    refine (comp_ff_is_ff _ _ _ _ _ _ (fully_faithful_from_equivalence _ _ _ (adj_equiv_inv _))).
    refine (comp_ff_is_ff _ _ _ _ _ _ (fully_faithful_from_equivalence _ _ _ (adj_equiv_opposite _))).
    refine (comp_ff_is_ff _ _ _ _ _ _ (fully_faithful_from_equivalence _ _ _ F4')).
    refine (comp_ff_is_ff _ _ _ _ _ _ (full_subcat_pr1_fully_faithful _ _)).
    refine (comp_ff_is_ff _ _ _ _ _ _ (rezk_completion_fully_faithful (karoubi_rezk_completion _))).
    exact (fully_faithful_from_equivalence _ _ _ F1).
  Defined.

(** * 2. The isomorphism between the reflexive objects *)

  Let U := U (n := 0) L (β_lambda_theory_has_β L).

  Let X := yoneda _ (set_karoubi_ob_object _ (F1 U)).
  Let f := identity X.
  Let g := #(yoneda _) (set_karoubi_ob_idempotent _ (F1 U)).
  Let E := Equalizers_PreShv X X f g.

  Local Definition left_hand_iso_mor
    : D4⟦E, X⟧
    := EqualizerArrow E.

  Local Definition left_hand_iso_inv
    : D4⟦X, E⟧.
  Proof.
    use (EqualizerIn E X g).
    abstract (
      refine (id_right _ @ _);
      refine (_ @ functor_comp _ _ _);
      apply (maponpaths (# _));
      exact (!idempotent_is_idempotent _)
    ).
  Defined.

  Local Lemma left_hand_iso_is_iso
    : is_inverse_in_precat left_hand_iso_mor left_hand_iso_inv.
  Proof.
    split.
    - apply EqualizerInsEq.
      refine (_ @ !id_left _).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (EqualizerCommutes _ _ _ _) @ _).
      refine (!EqualizerEqAr _ @ _).
      apply id_right.
    - refine (EqualizerCommutes _ _ _ _ @ _).
      refine (_ @ functor_id (yoneda _) _).
      refine (maponpaths (# _) _).
      refine (β_lambda_theory_has_β L _ _).
  Qed.

  Local Definition left_hand_iso
    : z_iso E X
    := make_z_iso
      left_hand_iso_mor
      left_hand_iso_inv
      left_hand_iso_is_iso.

  Local Definition right_hand_iso
    : z_iso X ((F5 ∙ F5' ∙ adj_equiv_inv F4 ∙ adj_equiv_inv F4') (theory_presheaf L)).
  Proof.
    use make_z_iso.
    - use make_nat_trans.
      * exact (λ x y, y).
      * easy.
    - use make_nat_trans.
      * exact (λ x y, y).
      * easy.
    - split;
        apply nat_trans_eq_alt;
        easy.
  Defined.

  Lemma scott_to_hyland_U_to_L
    : z_iso (scott_to_hyland U) (theory_presheaf L).
  Proof.
    do 2 apply adj_equiv_inv_transpose_left.
    do 2 apply adj_equiv_transpose_left.
    exact (z_iso_comp left_hand_iso right_hand_iso).
  Defined.

End Diagram.
