Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section LeftStrength.
  Context {V : monoidal_cat}.

  Definition left_strength_data
             (F : V ⟶ V)
    : UU
    := ∏ (x y : V), x ⊗ F y --> F(x ⊗ y).

  Definition left_strength_laws
             {F : V ⟶ V}
             (tF : left_strength_data F)
    : UU
    := (∏ (x₁ x₂ y₁ y₂ : V)
          (f : x₁ --> x₂)
          (g : y₁ --> y₂),
        f #⊗ #F g· tF x₂ y₂
        =
        tF x₁ y₁ · #F(f #⊗ g))
       ×
       (∏ (x : V),
        tF I_{V} x · #F(mon_lunitor x)
        =
        mon_lunitor (F x))
       ×
       (∏ (x y z : V),
        tF (x ⊗ y) z · #F(mon_lassociator x y z)
        =
        mon_lassociator x y (F z) · identity x #⊗ tF y z · tF x (y ⊗ z)).

  Proposition isaprop_left_strength_laws
              {F : V ⟶ V}
              (tF : left_strength_data F)
    : isaprop (left_strength_laws tF).
  Proof.
    repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
  Qed.

  Definition left_strength
             (F : V ⟶ V)
    : UU
    := ∑ (tF : left_strength_data F), left_strength_laws tF.

  Definition left_strength_to_data
             {F : V ⟶ V}
             (tF : left_strength F)
             (x y : V)
    : x ⊗ F y --> F(x ⊗ y)
    := pr1 tF x y.

  Coercion left_strength_to_data : left_strength >-> Funclass.

  Section LeftStrengthLaws.
    Context {F : V ⟶ V}
            (tF : left_strength F).

    Proposition left_strength_natural
                {x₁ x₂ y₁ y₂ : V}
                (f : x₁ --> x₂)
                (g : y₁ --> y₂)
      : f #⊗ #F g· tF x₂ y₂
        =
        tF x₁ y₁ · #F(f #⊗ g).
    Proof.
      exact (pr12 tF x₁ x₂ y₁ y₂ f g).
    Qed.

    Proposition left_strength_mon_lunitor
                (x : V)
      : tF I_{V} x · #F(mon_lunitor x)
        =
        mon_lunitor (F x).
    Proof.
      exact (pr122 tF x).
    Qed.

    Proposition left_strength_mon_lassociator
                (x y z : V)
      : tF (x ⊗ y) z · #F(mon_lassociator x y z)
        =
        mon_lassociator x y (F z) · identity x #⊗ tF y z · tF x (y ⊗ z).
    Proof.
      exact (pr222 tF x y z).
    Qed.
  End LeftStrengthLaws.

  Definition left_strong_monad_laws
             {M : Monad V}
             (tM : left_strength M)
    : UU
    := (∏ (x y : V),
        identity x #⊗ η M y · tM x y
        =
        η M (x ⊗ y))
       ×
       (∏ (x y : V),
        identity x #⊗ μ M y · tM x y
        =
        tM x (M y) · #M (tM x y) · μ M (x ⊗ y)).

  Proposition isaprop_left_strong_monad_laws
              {M : Monad V}
              (tM : left_strength M)
    : isaprop (left_strong_monad_laws tM).
  Proof.
    use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
  Qed.

  Definition left_strong_monad
             (M : Monad V)
    : UU
    := ∑ (tM : left_strength M), left_strong_monad_laws tM.

  Coercion left_strong_monad_strength
           {M : Monad V}
           (tM : left_strong_monad M)
    : left_strength M
    := pr1 tM.

  Section LeftStrongMonadLaws.
    Context {M : Monad V}
            (tM : left_strong_monad M).

    Proposition left_strong_monad_unit
                (x y : V)
      : identity x #⊗ η M y · tM x y
        =
        η M (x ⊗ y).
    Proof.
      exact (pr12 tM x y).
    Qed.

    Proposition left_strong_monad_mu
                (x y : V)
      : identity x #⊗ μ M y · tM x y
        =
        tM x (M y) · #M (tM x y) · μ M (x ⊗ y).
    Proof.
      exact (pr22 tM x y).
    Qed.
  End LeftStrongMonadLaws.
End LeftStrength.

Section SelfEnrichment.
  Context (V : sym_mon_closed_cat).

  Definition self_enrichment_data
    : enrichment_data V V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, x ⊸ y).
    - exact internal_id.
    - exact internal_comp.
    - exact (@internal_from_arr V).
    - exact (@internal_to_arr V).
  Defined.

  Proposition self_enrichment_laws
    : enrichment_laws self_enrichment_data.
  Proof.
    repeat split.
    - exact internal_id_left.
    - exact internal_id_right.
    - exact internal_assoc.
    - exact (@internal_to_from_arr V).
    - exact (@internal_from_to_arr V).
    - exact internal_to_arr_id.
    - exact (@internal_to_arr_comp V).
  Qed.

  Definition self_enrichment
    : enrichment V V.
  Proof.
    simple refine (_ ,, _).
    - exact self_enrichment_data.
    - exact self_enrichment_laws.
  Defined.

  Section StrengthToFunctorEnrichment.
    Context {F : V ⟶ V}
            (tF : left_strength F).

    Proposition strength_to_enrichment_laws
      : @is_functor_enrichment
          _ _ _
          F
          self_enrichment self_enrichment
          (λ x y, internal_lam (tF (internal_hom x y) x · # F (internal_eval x y))).
    Proof.
      repeat split.
      - intros x ; cbn.
        use internal_funext.
        intros w h.
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
        refine (!_).
        rewrite tensor_split.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- functor_id.
          rewrite (left_strength_natural tF).
          rewrite !assoc'.
          rewrite <- functor_comp.
          unfold internal_id.
          rewrite internal_beta.
          rewrite left_strength_mon_lunitor.
          apply idpath.
        }
        rewrite tensor_lunitor.
        apply idpath.
      - intros x y z ; cbn.
        use internal_funext.
        intros w h.
        etrans.
        {
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        etrans.
        {
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            rewrite tensor_split.
            rewrite <- functor_id.
            rewrite !assoc'.
            rewrite left_strength_natural.
            apply idpath.
          }
          rewrite !assoc'.
          rewrite <- !functor_comp.
          unfold internal_comp.
          rewrite internal_beta.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          unfold internal_comp.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite !tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- tensor_lassociator.
        rewrite tensor_id_id.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !assoc.
            rewrite left_strength_natural.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- left_strength_mon_lassociator.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite <- !functor_comp.
        apply idpath.
      - intros x y f ; cbn.
        use internal_funext.
        intros w h.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        refine (!_).
        etrans.
        {
          rewrite tensor_split.
          rewrite <- functor_id.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite left_strength_natural.
          rewrite !assoc'.
          rewrite <- functor_comp.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite functor_comp.
          rewrite !assoc.
          rewrite left_strength_mon_lunitor.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lunitor.
        refine (!_).
        etrans.
        {
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        apply idpath.
    Qed.

    Definition strength_to_enrichment
      : functor_enrichment F self_enrichment self_enrichment.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y, internal_lam (tF _ _ · #F (internal_eval x y))).
      - exact strength_to_enrichment_laws.
    Defined.
  End StrengthToFunctorEnrichment.

  Section StrengthToMonadEnrichment.
    Context {M : Monad V}
            (tM : left_strong_monad M).

    Proposition monad_left_strong_to_enrichment_eta
      : nat_trans_enrichment
          (η M)
          (functor_id_enrichment self_enrichment)
          (strength_to_enrichment tM).
    Proof.
      intros x y ; cbn.
      use internal_funext.
      intros w h.
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        unfold internal_from_arr.
        rewrite internal_beta.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- mon_triangle.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite mon_rinvunitor_runitor.
        rewrite id_right.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
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
          rewrite tensor_id_id.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_lunitor_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_linvunitor_lunitor.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      refine (nat_trans_ax (η M) _ _ (internal_eval x y) @ _).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply (left_strong_monad_unit tM).
    Qed.

    Proposition monad_left_strong_to_enrichment_mu
      : nat_trans_enrichment
          (μ M)
          (functor_comp_enrichment
             (strength_to_enrichment tM)
             (strength_to_enrichment tM))
          (strength_to_enrichment tM).
    Proof.
      intros x y ; cbn.
      use internal_funext.
      intros w h.
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
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
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_comp_id_l.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- mon_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_rinvunitor_runitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply left_strong_monad_mu.
      }
      etrans.
      {
        rewrite !assoc'.
        do 3 apply maponpaths.
        exact (!(nat_trans_ax (μ M) _ _ (internal_eval x y))).
      }
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
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
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite tensor_split.
          unfold internal_from_arr.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_lunitor_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_linvunitor_lunitor.
        apply idpath.
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- functor_id.
      rewrite left_strength_natural.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite internal_beta.
      apply idpath.
    Qed.

    Definition monad_left_strong_to_enrichment
      : monad_enrichment self_enrichment M
      := strength_to_enrichment tM
         ,,
         monad_left_strong_to_enrichment_eta
         ,,
         monad_left_strong_to_enrichment_mu.
  End StrengthToMonadEnrichment.
End SelfEnrichment.

(*
  Section MonadEnrichmentToStrength.
    Context {M : Monad V}
            (EM : monad_enrichment self_enrichment M).


    Proposition test
                {x₁ x₂ y₁ y₂ : V}
                (f : x₂ --> x₁)
                (g : y₁ --> y₂)
      : internal_lam (identity _ #⊗ f · internal_eval x₁ y₁ · g) · EM x₂ y₂
        =
        EM x₁ y₁ · internal_lam (identity _ #⊗ #M f · internal_eval (M x₁) (M y₁) · #M g).
    Proof.
      rewrite internal_lam_natural.
      rewrite !assoc.
      rewrite <- tensor_split'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths_2.
        apply (tensor_split (EM x₁ y₁) (#M f)).
      }
      cbn.
      rewrite !assoc'.
      rewrite internal_eval_natural.
      cbn.
    Admitted.

    Proposition monad_enrichment_to_left_strength_laws
      : left_strength_laws
          (λ x y,
           (internal_pair x y · EM y (x ⊗ y)) #⊗ identity _
           · internal_eval _ _).
    Proof.
      repeat split.
      - intros x₁ x₂ y₁ y₂ f g.
        admit.
      - intros x.
        pose (test (identity x) (mon_lunitor x)).
        rewrite !functor_id in p.
        rewrite !tensor_id_id in p.
        rewrite !id_left in p.
        Check internal_eta.
        admit.
      - intros x y z.
        admit.
    Admitted.

    Definition monad_enrichment_to_left_strength
      : left_strength M
      := _ ,, monad_enrichment_to_left_strength_laws.

    Proposition monad_enrichment_to_left_strong_monad_laws
      : left_strong_monad_laws monad_enrichment_to_left_strength.
    Proof.
      split.
      - intros x y ; cbn.
        admit.
      - intros x y ; cbn.
        admit.
    Admitted.

    Definition monad_enrichment_to_left_strong
      : left_strong_monad M
      := monad_enrichment_to_left_strength
         ,,
         monad_enrichment_to_left_strong_monad_laws.
  End MonadEnrichmentToStrength.

  Section StrongMonadEnrichment.
    Context (M : Monad V).

    Proposition monad_enrichment_weq_strength_inv1
                (EM : monad_enrichment self_enrichment M)
      : monad_left_strong_to_enrichment (monad_enrichment_to_left_strong EM)
        =
        EM.
    Proof.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply isaprop_nat_trans_enrichment.
      }
      use subtypePath.
      {
        intro ; apply isaprop_is_functor_enrichment.
      }
      use funextsec ; intro x.
      use funextsec ; intro y ; cbn.
      rewrite !assoc'.
      rewrite <- internal_lam_natural.
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
    Admitted.

    Proposition monad_enrichment_weq_strength_inv2
                (tM : left_strong_monad M)
      : monad_enrichment_to_left_strong (monad_left_strong_to_enrichment tM)
        =
        tM.
    Proof.
      use subtypePath ; [ intro ; apply isaprop_left_strong_monad_laws | ].
      use subtypePath ; [ intro ; apply isaprop_left_strength_laws | ].
      use funextsec ; intro x.
      use funextsec ; intro y ; cbn.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite <- functor_id.
      rewrite !assoc.
      rewrite left_strength_natural.
      rewrite !assoc'.
      rewrite <- functor_comp.
      unfold internal_pair.
      rewrite internal_beta.
      rewrite functor_id.
      apply id_right.
    Qed.

    Definition monad_enrichment_weq_strength
      : monad_enrichment self_enrichment M
        ≃
        left_strong_monad M.
    Proof.
      use weq_iso.
      - exact monad_enrichment_to_left_strong.
      - exact monad_left_strong_to_enrichment.
      - exact monad_enrichment_weq_strength_inv1.
      - exact monad_enrichment_weq_strength_inv2.
    Defined.
  End StrongMonadEnrichment.
End SelfEnrichment.
 *)
