(******************************************************************************************

 Composition of enriched profunctors

 In this file, we define the composition of enriched profunctors. Given enriched profunctors
 `P : E₁ ↛e E₂` and `Q : E₂ ↛e E₃`, their composition is defined to be the profunctor that
 sends objects `x : E₁` and `z : E₃` to the enriched coend `∫^{y : E₂} P x y ⊗ Q y z`. Note
 that we need to assume that the category `V` over which we enrich, is cocomplete. Concretely,
 we take the following steps to define the composition.
 1. First we define the functor over which we take the coend ([comp_enriched_profunctor_coend]).
    This functor is defined for every `x : E₁` and `z : E₃`.
 2. Since we assume `V` to be cocomplete, we can take the coend ([comp_enriched_profunctor_ob]).
    We also define suitable accessors for the projections and the universal property.
 3. The left action and right action are defined via the universal property of the coend.
    To prove the laws, we again use the universal property of the coend, but this time the
    uniqueness of maps from the coend.

 There are two interesting technical aspects in this proof. First of all, there is a
 constraint of the universe levels of the involved enriched categories `E₁` and `E₂` and
 the monoidal category `V`. Colimits indexed by objects and by morphisms in `E₁` and `E₂`
 need to exist in `V`, which means that `E₁` and `E₂` must be sufficiently small compared
 to `V`. In the literature, one defines the composition for profunctors over small categories,
 and this is reflected in the universe level constraints for the involved categories.

 Secondly, when we define the left action and right action, we need to give a morphism from
 `E₃ ⦃ z₂ , z₁ ⦄ ⊗ comp_enriched_profunctor_ob z₁ x` to `comp_enriched_profunctor_ob z₂ x`
 for all `z₁ z₂ : C₃` and `x : C₁` and similar for the right action. However, in order to
 use the universal property of the coend, the domain of the morphism should instead be
 `comp_enriched_profunctor_ob z₁ x`, so, more concretely, we would give a morphism
 `comp_enriched_profunctor_ob z₁ x --> E₃ ⦃ z₂ , z₁ ⦄ ⊸ comp_enriched_profunctor_ob z₂ x`.
 For this reason, the left action and the right action are defined using suitable transposes.
 Note that if we were to use whiskered bifunctors instead, then we would be asked to give
 `E₃ ⦃ z₂ , z₁ ⦄ --> comp_enriched_profunctor_ob z₁ x ⊸ comp_enriched_profunctor_ob z₂ x`,
 and then we would still need to do some work before we can use the universal property of
 the coend.

 Content
 1. The functor over which we take the coend
 2. The coend used to define composition
 3. The left action
 4. The right action
 5. The data
 6. The laws
 7. Composition of enriched profunctors
 8. Additional laws for action on morphisms

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coends.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Coend.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section Composition.
  Context {V : benabou_cosmos}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (P : E₁ ↛e E₂)
          (Q : E₂ ↛e E₃).

  (** * 1. The functor over which we take the coend *)
  Section CoendProfunctor.
    Context (z : C₃)
            (x : C₁).

    Definition comp_enriched_profunctor_coend_data
      : enriched_profunctor_data E₂ E₂.
    Proof.
      use make_enriched_profunctor_data.
      - exact (λ y₁ y₂, P y₁ x ⊗ Q z y₂).
      - exact (λ _ _ _,
               mon_rassociator _ _ _
               · (lmap_e P _ _ _ #⊗ identity _)).
      - exact (λ _ _ _,
               sym_mon_braiding _ _ _
               · mon_lassociator _ _ _
               · (identity _ #⊗ (sym_mon_braiding _ _ _ · rmap_e Q _ _ _))).
    Defined.

    Proposition comp_enriched_profunctor_coend_laws
      : enriched_profunctor_laws
          comp_enriched_profunctor_coend_data.
    Proof.
      repeat split ; cbn.
      - intros y₁ y₂.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_r.
        rewrite lmap_e_id.
        rewrite <- mon_lunitor_triangle.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        apply id_left.
      - intros y₁ y₂.
        etrans.
        {
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite <- tensor_comp_id_l.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite rmap_e_id.
          apply idpath.
        }
        rewrite tensor_comp_id_l.
        rewrite sym_mon_tensor_lassociator.
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !assoc.
          rewrite mon_rassociator_lassociator.
          rewrite id_left.
          apply idpath.
        }
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          apply id_left.
        }
        rewrite <- mon_triangle.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_runitor.
        rewrite <- mon_lunitor_triangle.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        apply id_left.
      - intros y₁ y₂ y₃ y₄ ; cbn.
        etrans.
        {
          rewrite <- tensor_id_id.
          rewrite !assoc.
          rewrite tensor_rassociator.
          rewrite !assoc'.
          rewrite <- tensor_comp_id_r.
          rewrite lmap_e_comp.
          rewrite !tensor_comp_id_r.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite tensor_comp_id_l.
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_rassociator.
          apply idpath.
        }
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!(id_left _) @ _).
        rewrite <- mon_rassociator_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_lassociator.
        etrans.
        {
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite mon_lassociator_rassociator.
          rewrite tensor_id_id.
          apply id_left.
        }
        rewrite mon_lassociator_rassociator.
        apply id_right.
      - intros y₁ y₂ y₃ y₄ ; cbn.
        etrans.
        {
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite <- tensor_comp_id_l.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite rmap_e_comp.
          rewrite !tensor_comp_id_l.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite tensor_comp_id_r.
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite <- tensor_comp_id_l.
          rewrite tensor_comp_id_r.
          rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !assoc.
            rewrite tensor_sym_mon_braiding.
            apply idpath.
          }
          rewrite !tensor_comp_id_l.
          apply idpath.
        }
        rewrite tensor_comp_id_r.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        generalize (E₂ ⦃ y₃ , y₄ ⦄).
        generalize (E₂ ⦃ y₂ , y₃ ⦄).
        generalize (P y₁ x).
        generalize (Q z y₂).
        intros v₁ v₂ v₃ v₄.
        rewrite !assoc'.
        etrans.
        {
          do 5 apply maponpaths.
          rewrite <- tensor_comp_id_l.
          rewrite tensor_sym_mon_braiding.
          rewrite tensor_comp_id_l.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_tensor_lassociator.
          rewrite !assoc'.
          rewrite mon_rassociator_lassociator.
          rewrite id_right.
          rewrite !assoc.
          rewrite tensor_comp_id_l.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          do 3 apply maponpaths.
          pose (maponpaths
                  (λ z, z · identity _ #⊗ mon_rassociator _ _ _)
                  (@mon_lassociator_lassociator V v₂ v₁ v₃ v₄)) as p.
          cbn in p.
          rewrite !assoc' in p.
          rewrite <- tensor_comp_id_l in p.
          rewrite mon_lassociator_rassociator in p.
          rewrite tensor_id_id in p.
          rewrite id_right in p.
          exact (!p).
        }
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        etrans.
        {
          do 6 apply maponpaths.
          rewrite sym_mon_tensor_rassociator.
          rewrite !assoc.
          rewrite mon_rassociator_lassociator.
          rewrite id_left.
          apply idpath.
        }
        rewrite !tensor_comp_id_l.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_lassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_id_id.
        generalize (v₂ ⊗ v₁).
        clear v₁ v₂.
        intros v₂.
        rewrite !assoc'.
        rewrite sym_mon_tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        refine (!(id_left _) @ _).
        rewrite <- mon_rassociator_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_hexagon_lassociator.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_right.
        apply idpath.
      - intros y₁ y₂ y₃ y₄ ; cbn.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite tensor_comp_id_l.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite tensor_id_id.
          rewrite <- tensor_split'.
          rewrite tensor_comp_l_id_l.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite !tensor_comp_id_l.
          rewrite !assoc'.
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_rassociator.
          rewrite !assoc'.
          rewrite tensor_id_id.
          rewrite <- tensor_split.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        generalize (E₂ ⦃ y₂ , y₁ ⦄).
        generalize (E₂ ⦃ y₃ , y₄ ⦄).
        generalize (P y₁ x).
        generalize (Q z y₃).
        intros v₁ v₂ v₃ v₄.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        rewrite tensor_id_id.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(id_right _) @ _).
        rewrite <- mon_rassociator_lassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite mon_rassociator_rassociator.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite <- tensor_comp_id_l.
          rewrite mon_lassociator_rassociator.
          rewrite tensor_id_id.
          rewrite id_right.
          apply idpath.
        }
        refine (_ @ id_right _).
        rewrite <- mon_lassociator_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite assoc.
          apply sym_mon_hexagon_lassociator.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition comp_enriched_profunctor_coend
      : enriched_profunctor E₂ E₂.
    Proof.
      use make_enriched_profunctor.
      - exact comp_enriched_profunctor_coend_data.
      - exact comp_enriched_profunctor_coend_laws.
    Defined.

    (** * 2. The coend used to define composition *)
    Definition comp_enriched_profunctor_ob
      : V
      := enriched_profunctor_coend comp_enriched_profunctor_coend.

    Definition comp_enriched_profunctor_in
              (y : C₂)
      : P y x ⊗ Q z y --> comp_enriched_profunctor_ob
      := enriched_profunctor_coend_in
           comp_enriched_profunctor_coend
           y.

    Proposition comp_enriched_profunctor_comm
                (y₁ y₂ : C₂)
      : lmap_e P y₂ y₁ x #⊗ identity _
        · comp_enriched_profunctor_in y₁
        =
        mon_lassociator _ _ _
        · sym_mon_braiding V _ _
        · mon_lassociator _ _ _
        · identity _ #⊗ (sym_mon_braiding V _ _ · rmap_e Q z y₁ y₂)
        · comp_enriched_profunctor_in y₂.
    Proof.
      refine (!(id_left _) @ _).
      rewrite <- mon_lassociator_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      exact (enriched_profunctor_coend_comm
               comp_enriched_profunctor_coend
               y₁ y₂).
    Qed.

    Proposition comp_enriched_profunctor_comm'
                (y₁ y₂ : C₂)
      : identity _ #⊗ rmap_e Q z y₁ y₂
        · comp_enriched_profunctor_in y₂
        =
        identity _ #⊗ sym_mon_braiding V _ _
        · mon_rassociator _ _ _
        · sym_mon_braiding V _ _
        · mon_rassociator _ _ _
        · (lmap_e P y₂ y₁ x #⊗ identity _)
        · comp_enriched_profunctor_in y₁.
    Proof.
      rewrite !assoc'.
      rewrite comp_enriched_profunctor_comm.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      apply idpath.
    Qed.

    Proposition comp_enriched_profunctor_comm_arr
                {y₁ y₂ : C₂}
                (g : y₁ --> y₂)
      : identity (P y₂ x) #⊗ rmap_e_arr Q g z
        · comp_enriched_profunctor_in y₂
        =
        lmap_e_arr P x g #⊗ identity (Q z y₁)
        · comp_enriched_profunctor_in y₁.
    Proof.
      pose (enriched_profunctor_coend_comm_arr
              comp_enriched_profunctor_coend
              g)
        as p.
      unfold lmap_e_arr, rmap_e_arr in p.
      cbn in p.
      refine (_ @ !p @ _).
      - unfold rmap_e_arr.
        etrans.
        {
          rewrite !tensor_comp_id_l.
          rewrite !assoc'.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite !tensor_comp_id_l.
          apply idpath.
        }
        rewrite !assoc.
        do 3 apply maponpaths_2.
        rewrite <- mon_linvunitor_triangle.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite sym_mon_hexagon_lassociator.
          rewrite !assoc'.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          rewrite id_right.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_linvunitor.
        rewrite mon_inv_triangle.
        apply idpath.
      - unfold lmap_e_arr.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_rassociator.
          rewrite !assoc'.
          apply maponpaths.
          apply idpath.
        }
        rewrite !assoc.
        rewrite !tensor_comp_id_r.
        do 3 apply maponpaths_2.
        rewrite <- mon_linvunitor_triangle.
        rewrite !assoc'.
        rewrite mon_lassociator_rassociator.
        apply id_right.
    Qed.

    Definition from_comp_enriched_profunctor_ob
               {v : V}
               (fs : ∏ (y : C₂), P y x ⊗ Q z y --> v)
               (ps : ∏ (y₁ y₂ : C₂),
                     lmap_e P y₂ y₁ x #⊗ identity (Q z y₁) · fs y₁
                     =
                      sym_mon_braiding V _ _ #⊗ identity (Q z y₁)
                      · mon_lassociator _ _ _
                      · identity (P y₂ x) #⊗ rmap_e Q z y₁ y₂
                      · fs y₂)
      : comp_enriched_profunctor_ob --> v.
    Proof.
      use from_enriched_profunctor_coend.
      - exact fs.
      - abstract
          (cbn ;
           intros y₁ y₂ ;
           rewrite sym_mon_tensor_lassociator ;
           rewrite !assoc' ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ · (_ · (_ · z))) (assoc _ _ _)) ;
           rewrite mon_rassociator_lassociator ;
           rewrite id_left ;
           rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)) ;
           rewrite <- tensor_comp_id_l ;
           rewrite !assoc ;
           rewrite sym_mon_braiding_inv ;
           rewrite id_left ;
           apply ps).
    Defined.

    Proposition from_comp_enriched_profunctor_ob_comm
                (y : C₂)
                {v : V}
                (fs : ∏ (y : C₂), P y x ⊗ Q z y --> v)
                (ps : ∏ (y₁ y₂ : C₂),
                      lmap_e P y₂ y₁ x #⊗ identity (Q z y₁) · fs y₁
                      =
                      sym_mon_braiding V _ _ #⊗ identity (Q z y₁)
                      · mon_lassociator _ _ _
                      · identity (P y₂ x) #⊗ rmap_e Q z y₁ y₂
                      · fs y₂)
      : comp_enriched_profunctor_in y · from_comp_enriched_profunctor_ob fs ps
        =
        fs y.
    Proof.
      apply (from_enriched_profunctor_coend_comm
               comp_enriched_profunctor_coend).
    Qed.

    Proposition from_comp_enriched_profunctor_eq
                 {v : V}
                 {f g : comp_enriched_profunctor_ob --> v}
                 (ps : ∏ (y : C₂),
                       comp_enriched_profunctor_in y · f
                       =
                       comp_enriched_profunctor_in y · g)
      : f = g.
    Proof.
      use enriched_profunctor_coend_eq_mor.
      exact ps.
    Qed.
  End CoendProfunctor.

  (** * 3. The left action *)
  Section LeftAction.
    Context (z₁ z₂ : C₃)
            (x : C₁).

    Definition comp_enriched_profunctor_lmap_mor
               (y : C₂)
      : E₃ ⦃ z₂ , z₁ ⦄ ⊗ (P y x ⊗ Q z₁ y)
        -->
        comp_enriched_profunctor_ob z₂ x
      := sym_mon_braiding _ _ _
         · mon_lassociator _ _ _
         · (identity _ #⊗ (sym_mon_braiding _ _ _ · lmap_e Q z₁ z₂ y))
         · comp_enriched_profunctor_in z₂ x y.

    Proposition comp_enriched_profunctor_lmap_eq
                (y₁ y₂ : C₂)
      : lmap_e P y₂ y₁ x #⊗ identity _
        · internal_transpose (comp_enriched_profunctor_lmap_mor y₁)
        =
        sym_mon_braiding V _ _ #⊗ identity _
        · mon_lassociator _ _ _
        · identity _ #⊗ rmap_e Q z₁ y₁ y₂
        · internal_transpose (comp_enriched_profunctor_lmap_mor y₂).
    Proof.
      unfold comp_enriched_profunctor_lmap_mor, internal_transpose.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite comp_enriched_profunctor_comm.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite lmap_e_rmap_e'.
        rewrite !tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      generalize (E₂ ⦃ y₁ , y₂ ⦄).
      generalize (P y₂ x).
      generalize (Q z₁ y₁).
      generalize (E₃ ⦃ z₂ , z₁ ⦄).
      intros v₁ v₂ v₃ v₄.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        pose (maponpaths
                (λ z, z · identity _ #⊗ mon_rassociator _ _ _)
                (@mon_lassociator_lassociator V v₃ v₄ v₂ v₁)) as p.
        cbn in p.
        rewrite !assoc' in p.
        rewrite <- tensor_comp_id_l in p.
        rewrite mon_lassociator_rassociator in p.
        rewrite tensor_id_id in p.
        rewrite id_right in p.
        exact (!p).
      }
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 4 apply maponpaths_2.
        apply sym_mon_hexagon_lassociator.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply idpath.
      }
      rewrite tensor_id_id.
      apply maponpaths.
      rewrite <- tensor_id_id.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_id_l.
      apply maponpaths.
      clear v₃.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- sym_mon_hexagon_rassociator.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      rewrite id_right.
      apply idpath.
    Qed.

    Definition comp_enriched_profunctor_lmap
      : comp_enriched_profunctor_ob z₁ x
        -->
        E₃ ⦃ z₂ , z₁ ⦄ ⊸ comp_enriched_profunctor_ob z₂ x.
    Proof.
      use from_comp_enriched_profunctor_ob.
      - exact (λ y, internal_transpose (comp_enriched_profunctor_lmap_mor y)).
      - exact comp_enriched_profunctor_lmap_eq.
    Defined.

    Proposition comp_enriched_profunctor_lmap_comm
                (y : C₂)
      : (comp_enriched_profunctor_in z₁ x y · comp_enriched_profunctor_lmap) #⊗ identity _
        · internal_eval _ _
        =
        sym_mon_braiding _ _ _ · comp_enriched_profunctor_lmap_mor y.
    Proof.
      unfold comp_enriched_profunctor_lmap, internal_transpose.
      rewrite from_comp_enriched_profunctor_ob_comm.
      rewrite internal_beta.
      apply idpath.
    Qed.
  End LeftAction.

  (** * 4. The right action *)
  Section RightAction.
    Context (z : C₃)
            (x₁ x₂ : C₁).

    Definition comp_enriched_profunctor_rmap_mor
               (y : C₂)
      : E₁ ⦃ x₁ , x₂ ⦄ ⊗ (P y x₁ ⊗ Q z y)
        -->
        comp_enriched_profunctor_ob z x₂
      := mon_rassociator _ _ _
         · (rmap_e P y x₁ x₂ #⊗ identity _)
         · comp_enriched_profunctor_in z x₂ y.

    Proposition comp_enriched_profunctor_rmap_eq
                (y₁ y₂ : C₂)
      : lmap_e P y₂ y₁ x₁ #⊗ identity _
        · internal_transpose (comp_enriched_profunctor_rmap_mor y₁)
        =
        sym_mon_braiding _ _ _ #⊗ identity _
        · mon_lassociator _ _ _
        · identity _ #⊗ rmap_e Q z y₁ y₂
        · internal_transpose (comp_enriched_profunctor_rmap_mor y₂).
    Proof.
      unfold comp_enriched_profunctor_rmap_mor, internal_transpose.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite lmap_e_rmap_e'.
        rewrite !tensor_comp_id_r.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_comm.
        rewrite !tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        do 5 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- tensor_split'.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      generalize (E₂ ⦃ y₁ , y₂ ⦄).
      generalize (P y₂ x₁).
      generalize (Q z y₁).
      generalize (E₁ ⦃ x₁ , x₂ ⦄).
      intros v₁ v₂ v₃ v₄.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        do 6 apply maponpaths_2.
        pose (maponpaths
                (λ z, identity _ #⊗ mon_lassociator _ _ _ · z)
                (@mon_rassociator_rassociator V v₁ v₄ v₃ v₂)) as p.
        cbn in p.
        rewrite !assoc in p.
        rewrite <- tensor_comp_id_l in p.
        rewrite mon_lassociator_rassociator in p.
        rewrite tensor_id_id in p.
        rewrite id_left in p.
        exact (!p).
      }
      rewrite !assoc'.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        pose (maponpaths
                (λ z, z · identity _ #⊗ mon_rassociator _ _ _)
                (@mon_lassociator_lassociator V v₄ v₁ v₃ v₂)) as p.
        cbn in p.
        rewrite !assoc' in p.
        rewrite <- tensor_comp_id_l in p.
        rewrite mon_lassociator_rassociator in p.
        rewrite tensor_id_id in p.
        rewrite id_right in p.
        exact (!p).
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      refine (!(id_right _) @ _).
      rewrite <- mon_lassociator_rassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_l.
      etrans.
      {
        rewrite !assoc'.
        do 6 apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          rewrite !assoc'.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          rewrite mon_lassociator_lassociator.
          rewrite !assoc.
          rewrite <- tensor_comp_id_r.
          rewrite mon_rassociator_lassociator.
          rewrite tensor_id_id.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          apply sym_mon_hexagon_lassociator.
        }
        rewrite tensor_id_id.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_r.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        apply id_left.
      }
      rewrite <- !tensor_comp_id_l.
      apply maponpaths.
      clear v₁.
      rewrite !assoc.
      rewrite sym_mon_hexagon_lassociator.
      rewrite !assoc'.
      rewrite <- tensor_comp_id_l.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      rewrite id_right.
      apply idpath.
    Qed.

    Definition comp_enriched_profunctor_rmap
      : comp_enriched_profunctor_ob z x₁
        -->
        E₁ ⦃ x₁ , x₂ ⦄ ⊸ comp_enriched_profunctor_ob z x₂.
    Proof.
      use from_comp_enriched_profunctor_ob.
      - exact (λ y, internal_transpose (comp_enriched_profunctor_rmap_mor y)).
      - exact comp_enriched_profunctor_rmap_eq.
    Defined.

    Proposition comp_enriched_profunctor_rmap_comm
                (y : C₂)
      : (comp_enriched_profunctor_in z x₁ y · comp_enriched_profunctor_rmap) #⊗ identity _
        · internal_eval _ _
        =
        sym_mon_braiding _ _ _ · comp_enriched_profunctor_rmap_mor y.
    Proof.
      unfold comp_enriched_profunctor_rmap, internal_transpose.
      rewrite from_comp_enriched_profunctor_ob_comm.
      rewrite internal_beta.
      apply idpath.
    Qed.
  End RightAction.

  (** * 5. The data *)
  Definition comp_enriched_profunctor_data
    : enriched_profunctor_data E₁ E₃.
  Proof.
    use make_enriched_profunctor_data.
    - exact comp_enriched_profunctor_ob.
    - exact (λ z₁ z₂ x,
             (identity _ #⊗ comp_enriched_profunctor_lmap z₁ z₂ x)
             · sym_mon_braiding _ _ _
             · internal_eval _ _).
    - exact (λ z x₁ x₂,
             (identity _ #⊗ comp_enriched_profunctor_rmap z x₁ x₂)
             · sym_mon_braiding _ _ _
             · internal_eval _ _).
  Defined.

  (** * 6. The laws *)
  Proposition comp_enriched_profunctor_laws
    : enriched_profunctor_laws comp_enriched_profunctor_data.
  Proof.
    repeat split.
    - intros z x ; cbn.
      use is_inj_internal_transpose.
      unfold internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite (tensor_split' h).
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        do 3 apply maponpaths_2.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite comp_enriched_profunctor_lmap_comm.
        apply idpath.
      }
      unfold comp_enriched_profunctor_lmap_mor.
      rewrite tensor_lunitor.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_l.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite lmap_e_id.
        apply sym_mon_braiding_lunitor.
      }
      rewrite <- mon_runitor_triangle.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        apply id_left.
      }
      apply sym_mon_braiding_runitor.
    - intros z x ; cbn.
      use is_inj_internal_transpose.
      unfold internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite (tensor_split' h).
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        do 3 apply maponpaths_2.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite comp_enriched_profunctor_rmap_comm.
        apply idpath.
      }
      unfold comp_enriched_profunctor_rmap_mor.
      rewrite tensor_lunitor.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_r.
        rewrite rmap_e_id.
        apply idpath.
      }
      rewrite <- mon_lunitor_triangle.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      apply id_left.
    - intros z₁ z₂ z₃ x ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_transpose.
      rewrite !internal_beta.
      rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _) h).
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_lmap_comm.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        apply id_left.
      }
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_r.
          unfold comp_enriched_profunctor_lmap_mor.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite lmap_e_comp.
        rewrite !assoc'.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        etrans.
        {
          do 3 apply maponpaths_2.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite comp_enriched_profunctor_lmap_comm.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          apply id_left.
        }
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_lmap_mor.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite comp_enriched_profunctor_lmap_comm.
        apply idpath.
      }
      unfold comp_enriched_profunctor_lmap_mor.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        apply maponpaths_2.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        do 2 rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite tensor_comp_id_r.
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      etrans.
      {
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_id_l.
        rewrite !assoc.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        apply maponpaths.
        rewrite sym_mon_tensor_lassociator.
        rewrite !assoc'.
        rewrite mon_rassociator_lassociator.
        rewrite id_right.
        rewrite !assoc.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(id_right _) @ _).
      rewrite <- tensor_id_id.
      rewrite <- sym_mon_braiding_inv.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite <- tensor_comp_id_l.
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_tensor_lassociator.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite mon_lassociator_rassociator.
          rewrite id_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_r.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      refine (_ @ id_right _).
      rewrite <- tensor_id_id.
      rewrite <- mon_lassociator_rassociator.
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite <- mon_lassociator_lassociator.
        apply idpath.
      }
      rewrite <- tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_id_id.
      (** This makes the goal more readable *)
      generalize (P y x ⊗ Q z₁ y) (E₃ ⦃ z₃, z₂ ⦄) (E₃ ⦃ z₂, z₁ ⦄).
      intros v₁ v₂ v₃.
      rewrite (sym_mon_tensor_lassociator V v₁ v₂ v₃).
      refine (_ @ id_left _).
      rewrite <- mon_rassociator_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      refine (_ @ id_left _).
      rewrite <- tensor_id_id.
      rewrite <- sym_mon_braiding_inv.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        apply id_left.
      }
      rewrite !assoc.
      exact (sym_mon_hexagon_lassociator V v₂ v₁ v₃).
    - intros z x₁ x₂ x₃ ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _) h).
      rewrite !assoc'.
      apply maponpaths.
      unfold internal_transpose.
      rewrite !internal_beta.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_rmap_comm.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        apply id_left.
      }
      unfold comp_enriched_profunctor_rmap_mor.
      etrans.
      {
        apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite rmap_e_comp.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        etrans.
        {
          do 3 apply maponpaths_2.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite comp_enriched_profunctor_rmap_comm.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          rewrite id_left.
          apply idpath.
        }
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_rmap_mor.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite comp_enriched_profunctor_rmap_comm.
        unfold comp_enriched_profunctor_rmap_mor.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite <- tensor_comp_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        refine (!(id_right _) @ _).
        rewrite <- tensor_id_id.
        rewrite <- mon_rassociator_lassociator.
        rewrite tensor_comp_id_r.
        rewrite !assoc.
        rewrite <- mon_rassociator_rassociator.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite sym_mon_braiding_inv.
        rewrite id_right.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite mon_lassociator_rassociator.
      apply id_right.
    - intros z₁ z₂ x₁ x₂ ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_transpose.
      rewrite !internal_beta.
      rewrite !(tensor_split (comp_enriched_profunctor_in z₁ x₁ y) h).
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        apply maponpaths_2.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths_2.
        apply maponpaths.
        rewrite !assoc.
        rewrite comp_enriched_profunctor_lmap_comm.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        unfold comp_enriched_profunctor_lmap_mor.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite comp_enriched_profunctor_rmap_comm.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        etrans.
        {
          do 3 apply maponpaths_2.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite comp_enriched_profunctor_rmap_comm.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          rewrite id_left.
          apply idpath.
        }
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc'.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite comp_enriched_profunctor_lmap_comm.
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split'.
        rewrite tensor_comp_l_id_l.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite sym_mon_tensor_lassociator'.
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        apply idpath.
      }
      rewrite tensor_id_id.
      rewrite !assoc.
      apply maponpaths_2.
      refine (_ @ id_right _).
      rewrite <- mon_lassociator_rassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_lassociator_lassociator.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite mon_rassociator_lassociator.
      rewrite tensor_id_id.
      rewrite id_left.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      refine (_ @ id_left _).
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      rewrite <- tensor_comp_id_l.
      rewrite sym_mon_braiding_inv.
      apply tensor_id_id.
  Qed.

  (** * 7. Composition of enriched profunctors *)
  Definition comp_enriched_profunctor
    : E₁ ↛e E₃.
  Proof.
    use make_enriched_profunctor.
    - exact comp_enriched_profunctor_data.
    - exact comp_enriched_profunctor_laws.
  Defined.

  (** * 8. Additional laws for action on morphisms *)
  Proposition comp_enriched_profunctor_lmap_e_arr
              (x : C₁)
              (y : C₂)
              {z₁ z₂ : C₃}
              (g : z₁ --> z₂)
    : comp_enriched_profunctor_in _ x y · lmap_e_arr comp_enriched_profunctor x g
      =
      (identity _ #⊗ lmap_e_arr Q y g) · comp_enriched_profunctor_in z₁ x y.
  Proof.
    etrans.
    {
      unfold lmap_e_arr ; cbn.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite comp_enriched_profunctor_lmap_comm.
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      apply id_left.
    }
    unfold comp_enriched_profunctor_lmap_mor.
    rewrite !assoc.
    apply maponpaths_2.
    unfold lmap_e_arr.
    rewrite !tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_comp_id_l.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_l.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite sym_mon_braiding_linvunitor.
    rewrite <- mon_rinvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      apply id_left.
    }
    rewrite <- tensor_comp_id_l.
    rewrite sym_mon_braiding_rinvunitor.
    apply idpath.
  Qed.

  Proposition comp_enriched_profunctor_rmap_e_arr
              {x₁ x₂ : C₁}
              (f : x₁ --> x₂)
              (y : C₂)
              (z : C₃)
    : comp_enriched_profunctor_in z x₁ y · rmap_e_arr comp_enriched_profunctor f z
      =
      (rmap_e_arr P f y #⊗ identity _) · comp_enriched_profunctor_in z x₂ y.
  Proof.
    etrans.
    {
      unfold rmap_e_arr ; cbn.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite comp_enriched_profunctor_rmap_comm.
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      apply id_left.
    }
    unfold comp_enriched_profunctor_rmap_mor.
    rewrite !assoc.
    apply maponpaths_2.
    unfold rmap_e_arr.
    rewrite !tensor_comp_id_r.
    apply maponpaths_2.
    rewrite <- tensor_id_id.
    rewrite !assoc'.
    rewrite tensor_rassociator.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    apply id_right.
  Qed.
End Composition.
