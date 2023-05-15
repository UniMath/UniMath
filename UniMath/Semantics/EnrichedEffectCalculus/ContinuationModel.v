(**********************************************************************

 The continuation model of the enriched effect calculus

 In this file, we formalize Example 6.10 from the following paper:

   http://www.itu.dk/people/mogel/papers/eec.pdf

 The example considers a specific model of the enriched effect calculus
 such that the monad associated to the adjunction is the continuation
 monad. Most of the building blocks of the model are already present in
 other files, namely limits and colimits in the self-enriched category
 and limits and colimits in the opposite enriched category. The only
 missing part is the construction of the required adjunction.

 Contents:
 1. Continuation adjunction
 1.1. The functors
 1.2. The unit and counit
 1.3. The adjunction
 2. The continuation model

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentAdjunction.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.Examples.SelfEnrichedLimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.Examples.OppositeEnrichedLimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.Examples.SelfEnrichedColimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.Examples.OppositeEnrichedColimits.
Require Import UniMath.Semantics.EnrichedEffectCalculus.EECModel.

Import MonoidalNotations.
Local Open Scope moncat.
Local Open Scope cat.

Opaque sym_mon_braiding.

(**
 1. Continuation adjunction
 *)
Section ContinuationAdjunction.
  Context (VC : category)
          (TV : Terminal VC)
          (VP : BinProducts VC)
          (IV : Initial VC)
          (VCP : BinCoproducts VC)
          (expV : Exponentials VP)
          (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
          (r : V).

  Opaque V.

  (**
   1.1. The functors
   *)
  Definition continuation_functor_data
    : functor_data V (V^opp).
  Proof.
    use make_functor_data.
    - exact (λ y, y ⊸ r).
    - exact (λ x y f, internal_precomp f r).
  Defined.

  Proposition continuation_functor_laws
    : is_functor continuation_functor_data.
  Proof.
    split.
    - intros y.
      apply internal_precomp_id.
    - intros y₁ y₂ y₃ f g.
      apply internal_precomp_comp.
  Qed.

  Definition continuation_functor
    : V ⟶ V^opp.
  Proof.
    use make_functor.
    - exact continuation_functor_data.
    - exact continuation_functor_laws.
  Defined.

  Proposition continuation_functor_enrichment_laws
    : @is_functor_enrichment
        V V (V ^opp)
        continuation_functor
        (self_enrichment V)
        (op_enrichment V (self_enrichment V))
        (λ x y, internal_lam (sym_mon_braiding V _ _ · internal_comp x y r)).
  Proof.
    repeat split ; cbn.
    - intro x.
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      etrans.
      {
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_id.
        rewrite internal_beta.
        rewrite tensor_lunitor.
        apply idpath.
      }
      use internal_funext.
      intros a' h'.
      refine (!_).
      rewrite !tensor_comp_r_id_r.
      unfold internal_comp.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_r_id_r.
      rewrite id_right.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        unfold internal_id.
        rewrite internal_beta.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- mon_triangle.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite sym_mon_braiding_runitor.
      apply idpath.
    - intros x y z.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply internal_beta.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_mor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite internal_beta.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      rewrite tensor_split.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear a h.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          unfold internal_comp.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        unfold internal_comp.
        rewrite internal_beta.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !tensor_comp_l_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_split.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear a h.
      rewrite mon_lassociator_lassociator.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite <- !tensor_comp_id_r.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply sym_mon_hexagon_lassociator.
      }
      apply lassociator_hexagon_two.
    - intros x y f.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite !internal_beta.
      use internal_funext.
      intros a' h'.
      rewrite !tensor_comp_r_id_r.
      unfold internal_precomp.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite !internal_beta.
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        rewrite <- tensor_comp_mor.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_r_id_r.
        rewrite id_right.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite internal_beta.
        rewrite id_right.
        rewrite tensor_comp_l_id_r.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite <- mon_triangle.
      rewrite !assoc.
      rewrite <- !tensor_comp_mor.
      rewrite !id_right.
      apply maponpaths_2.
      rewrite sym_mon_braiding_runitor.
      rewrite tensor_lunitor.
      apply idpath.
  Qed.

  Definition continuation_functor_enrichment
    : functor_enrichment
        continuation_functor
        (self_enrichment V)
        (op_enrichment V (self_enrichment V)).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, internal_lam (sym_mon_braiding _ _ _ · internal_comp _ _ _)).
    - exact continuation_functor_enrichment_laws.
  Defined.

  Definition continuation_functor_op_data
    : functor_data (V^opp) V.
  Proof.
    use make_functor_data ; cbn.
    - exact (λ y, y ⊸ r).
    - exact (λ x y f, internal_precomp f r).
  Defined.

  Proposition continuation_functor_op_laws
    : is_functor continuation_functor_op_data.
  Proof.
    split.
    - intros y ; cbn.
      apply internal_precomp_id.
    - intros y₁ y₂ y₃ f g ; cbn.
      apply internal_precomp_comp.
  Qed.

  Definition continuation_functor_op
    : V^opp ⟶ V.
  Proof.
    use make_functor.
    - exact continuation_functor_op_data.
    - exact continuation_functor_op_laws.
  Defined.

  Proposition continuation_functor_op_enrichment_laws
    : @is_functor_enrichment
        V (V ^opp) V
        continuation_functor_op
        (op_enrichment V (self_enrichment V))
        (self_enrichment V)
        (λ x y, internal_lam (sym_mon_braiding V _ _ · internal_comp _ _ _)).
  Proof.
    repeat split.
    - intro x.
      exact (pr1 continuation_functor_enrichment_laws x).
    - intros x y z.
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (pr12 continuation_functor_enrichment_laws z y x).
      }
      cbn.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite sym_mon_braiding_inv.
      apply id_right.
    - intros x y f.
      exact (pr22 continuation_functor_enrichment_laws y x f).
  Qed.

  Definition continuation_functor_op_enrichment
    : functor_enrichment
        continuation_functor_op
        (op_enrichment V (self_enrichment V))
        (self_enrichment V).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, internal_lam (sym_mon_braiding _ _ _ · internal_comp _ _ _)).
    - exact continuation_functor_op_enrichment_laws.
  Defined.

  (**
   1.2. The unit and counit
   *)
  Definition continuation_adjunction_unit_data
    : nat_trans_data
        (functor_identity V)
        (continuation_functor ∙ continuation_functor_op)
    := λ x, internal_lam (sym_mon_braiding _ _ _ · internal_eval _ _).

  Proposition continuation_adjunction_unit_laws
    : is_nat_trans _ _ continuation_adjunction_unit_data.
  Proof.
    intros x y f ; cbn ; unfold continuation_adjunction_unit_data.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_precomp.
    rewrite !internal_beta.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    refine (!_).
    etrans.
    {
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.

  Definition continuation_adjunction_unit
    : functor_identity V
      ⟹
      continuation_functor ∙ continuation_functor_op.
  Proof.
    use make_nat_trans.
    - exact continuation_adjunction_unit_data.
    - exact continuation_adjunction_unit_laws.
  Defined.

  Proposition continuation_adjunction_unit_enrichment
    : nat_trans_enrichment
        continuation_adjunction_unit
        (functor_id_enrichment (self_enrichment V))
        (functor_comp_enrichment
           continuation_functor_enrichment
           continuation_functor_op_enrichment).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    unfold continuation_adjunction_unit_data.
    rewrite self_enrichment_precomp.
    rewrite self_enrichment_postcomp.
    rewrite id_left.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite internal_beta.
    refine (!_).
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    }
    use internal_funext.
    intros a' h'.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    etrans.
    {
      do 2 apply maponpaths.
      unfold internal_comp.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite !tensor_sym_mon_braiding.
    rewrite id_right.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left, !id_right.
      rewrite internal_beta.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      cbn.
      rewrite tensor_comp_l_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_split.
    refine (!_).
    rewrite <- tensor_sym_mon_braiding.
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    clear a h a' h'.
    refine (!_).
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    apply maponpaths_2.
    rewrite <- sym_mon_hexagon_lassociator.
    cbn.
    apply lassociator_hexagon_two.
  Qed.

  Proposition continuation_adjunction_counit_laws
    : is_nat_trans
        (continuation_functor_op ∙ continuation_functor)
        (functor_identity (V^opp))
        continuation_adjunction_unit_data.
  Proof.
    intros x y f ; cbn ; unfold continuation_adjunction_unit_data.
    refine (!_).
    apply continuation_adjunction_unit_laws.
  Qed.

  Definition continuation_adjunction_counit
    : continuation_functor_op ∙ continuation_functor
      ⟹
      functor_identity (V^opp).
  Proof.
    use make_nat_trans.
    - exact continuation_adjunction_unit_data.
    - exact continuation_adjunction_counit_laws.
  Defined.

  Proposition continuation_adjunction_counit_enrichment
    : nat_trans_enrichment
        continuation_adjunction_counit
        (functor_comp_enrichment
           continuation_functor_op_enrichment
           continuation_functor_enrichment)
        (functor_id_enrichment (op_enrichment V (self_enrichment V))).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y.
    pose (nat_trans_enrichment_to_comp
            continuation_adjunction_unit_enrichment
            y x)
      as p.
    cbn ; cbn in p.
    rewrite op_enrichment_postcomp.
    rewrite op_enrichment_precomp.
    exact (!p).
  Qed.

  (**
   1.3. The adjunction
   *)
  Definition continuation_adjunction_data
    : adjunction_data V (V^opp).
  Proof.
    use make_adjunction_data.
    - exact continuation_functor.
    - exact continuation_functor_op.
    - exact continuation_adjunction_unit.
    - exact continuation_adjunction_counit.
  Defined.

  Proposition continuation_adjunction_triangle
              (x : V)
    : continuation_adjunction_unit_data (x ⊸ r)
      · internal_precomp (continuation_adjunction_unit_data x) r
      =
      identity _.
  Proof.
    cbn.
    unfold continuation_adjunction_unit_data.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_precomp.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite sym_mon_braiding_inv.
    apply id_right.
  Qed.

  Proposition continuation_adjunction_laws
    : form_adjunction' continuation_adjunction_data.
  Proof.
    split.
    - intro x.
      exact (continuation_adjunction_triangle x).
    - intro x.
      exact (continuation_adjunction_triangle x).
  Qed.

  Definition continuation_adjunction
    : adjunction V (V^opp).
  Proof.
    use make_adjunction.
    - exact continuation_adjunction_data.
    - exact continuation_adjunction_laws.
  Defined.

  Definition continuation_adjunction_enrichment
    : adjunction_enrichment
        continuation_adjunction
        (self_enrichment V)
        (op_enrichment V (self_enrichment V)).
  Proof.
    use make_adjunction_enrichment.
    - exact continuation_functor_enrichment.
    - exact continuation_functor_op_enrichment.
    - exact continuation_adjunction_unit_enrichment.
    - exact continuation_adjunction_counit_enrichment.
  Defined.

  Definition continuation_enriched_adjunction
    : enriched_adjunction
        (self_enrichment V)
        (op_enrichment V (self_enrichment V))
    := continuation_adjunction ,, continuation_adjunction_enrichment.
End ContinuationAdjunction.

(**
 2. The continuation model
 *)
Section ContinuationModel.
  Context (VC : category)
          (TV : Terminal VC)
          (VP : BinProducts VC)
          (IV : Initial VC)
          (VCP : BinCoproducts VC)
          (expV : Exponentials VP)
          (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
          (r : V).

  Definition continuation_eec_model
    : eec_model
    := VC
       ,,
       TV
       ,,
       VP
       ,,
       expV
       ,,
       (VC^opp)
       ,,
       op_enrichment _ (self_enrichment V)
       ,,
       continuation_enriched_adjunction V TV VP expV r
       ,,
       opposite_terminal_enriched _ (self_enrichment_initial V IV)
       ,,
       opposite_initial_enriched _ (self_enrichment_terminal V TV)
       ,,
       opposite_enrichment_power _ (self_enrichment_copowers V)
       ,,
       opposite_enrichment_copower _ (self_enrichment_powers V)
       ,,
       (opposite_enrichment_binary_prod
          (self_enrichment V)
          (self_enrichment_binary_coproducts V VCP))
       ,,
       (opposite_enrichment_binary_coprod
          (self_enrichment V)
          (self_enrichment_binary_products V VP)).

  Definition continuation_eec_plus_model
    : eec_plus_model
    := continuation_eec_model ,, IV ,, VCP.
End ContinuationModel.
