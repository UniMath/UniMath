(***************************************************************************

   Strength to module signature

   In this file, we define a functor from the category of signatures with a
   pointed tensorial strength to module signatures, and prove it maps simple
   examples of signatures with strength to the expected module signatures.
   Finally, we show that models for the obtained module signatures are
   equivalent to Sigma monoids.

 Contents
 1. Definitions
 2. Mapping of trivial and product signatures
 3. Models are Sigma monoids

 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Require Import UniMath.Tactics.EnsureStructuredProofs. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.ModelsOfModuleSignature.

Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.SubstitutionSystems.CategoryOfSignaturesWithStrength.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section StrengthToModuleSignature.
  Context {V : category} (Mon_V : monoidal V).

  Let V_Mon : monoidal_cat := V ,, Mon_V.

  Local Definition PtdV : category := coslice_cat_total V I_{Mon_V}.
  Local Definition Mon_PtdV : monoidal PtdV := monoidal_pointed_objects Mon_V.

  Local Definition Mon_V_swapped : monoidal V := monoidal_swapped Mon_V.

  (** 1. Definitions *)

  Section FixAStrength.
    Context {H : V ⟶ V}.
    Context (θ : pointedtensorialstrength Mon_V_swapped H).

    Local Definition monoid_to_pointed (R : MON Mon_V) : PtdV
      := pr1 R ,, monoid_data_unit _ (pr12 R).

    Section FixAMonoid.
      Context (R : MON Mon_V).

      Let R_ob : V := monoid_carrier _ R.
      Let η : I_{Mon_V} --> R_ob := monoid_data_unit _ (pr12 R).
      Let μ : R_ob ⊗_{Mon_V} R_ob --> R_ob := monoid_data_multiplication _ (pr12 R).

      Let pointed_R : PtdV := monoid_to_pointed R.
      Let pointed_RR : PtdV := pointed_R ⊗_{Mon_PtdV} pointed_R.

      Local Definition pointed_monoid_unit : PtdV ⟦ I_{Mon_PtdV}, pointed_R ⟧
        := η ,, id_left _.

      Local Lemma pointed_multiplication_lemma
        : luinv^{_}_{_} · η ⊗^{Mon_V} η · μ = η.
      Proof.
        etrans.
        { refine (maponpaths (λ x, _ · x · _) _); use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2.
        rewrite assoc, (monoidal_leftunitorinvnat Mon_V), <- id_right, <- assoc, <- assoc.
        refine (maponpaths _ _).
        etrans.
        { refine (maponpaths _ _); use monoid_to_unit_left_law. }
        use (pr2 (monoidal_leftunitorisolaw _ _)).
      Qed.

      Local Definition pointed_multiplication : PtdV ⟦ pointed_RR, pointed_R ⟧
        := μ ,, pointed_multiplication_lemma.

      Let HR_module_subst : H R_ob ⊗_{Mon_V} R_ob --> H R_ob
        := θ pointed_R R_ob · #H μ.

      Local Lemma HR_module_subst_assoc
        : module_laws_assoc (C := V_Mon) (pr1 R) (pr2 R) HR_module_subst.
      Proof.
        unfold module_laws_assoc, HR_module_subst.
        do 2 rewrite assoc; rewrite (bifunctor_rightcomp Mon_V).
        unfold RModules.μ; fold μ R_ob.
        symmetry; etrans.
        { refine (maponpaths (λ x, x · _) _); rewrite <- assoc; refine (maponpaths _ _).
          use (lineator_linnatleft _ _ _ _ θ pointed_R). }
        cbn; rewrite assoc.
        etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use (!monoid_to_assoc_law _ _). }
        do 2 rewrite functor_comp, assoc.
        symmetry; etrans.
        { do 2 rewrite <- assoc; refine (maponpaths _ _).
          rewrite assoc; refine (maponpaths (λ x, x · _) _).
          use (lineator_linnatright _ _ _ _ θ _ _ _ pointed_multiplication). }
        cbn; do 2 rewrite assoc; refine (!maponpaths (λ x, x · _ · _) _).
        symmetry; rewrite <- id_left, assoc, assoc, <- (pr1 (monoidal_associatorisolaw _ _ _ _)); symmetry.
        etrans.
        { refine (maponpaths (λ x, x · _) _); do 2 rewrite <- assoc.
          refine (maponpaths _ _); rewrite assoc.
          symmetry; rewrite <- id_left, assoc, assoc; symmetry.
          etrans; [refine (!maponpaths (λ x, x · _ · _ · _) _); use (tensor_id_id (V := V_Mon)) |].
          rewrite <- tensor_mor_left.
          use (!lineator_preservesactor _ _ _ _ θ pointed_R pointed_R _). }
        cbn; unfold reindexed_actor_data; cbn.
        rewrite <- assoc, <- assoc; use maponpaths.
        rewrite unitorsinv_coincide_on_unit, functor_comp, assoc, assoc.
        etrans.
        { refine (maponpaths (λ x, _ · x · _ · _) _).
          now rewrite (tensor_mor_left (V := V_Mon)), (tensor_id_id (V := V_Mon)), functor_id. }
        rewrite id_right; etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use (pr2 (monoidal_associatorisolaw _ _ _ _)). }
        eassert (_ ⊗^{ tensor_swapped Mon_V} _ = _ ⊗^{Mon_V} _) as hyp
        by use monoidal_swapped_whiskering.
        now rewrite functor_id, id_right, hyp.
      Qed.

      Local Lemma HR_module_subst_unit
        : module_laws_unit (C := V_Mon) (pr1 R) (pr2 R) HR_module_subst.
      Proof.
        unfold module_laws_unit, HR_module_subst, RModules.η; cbn.
        rewrite assoc; etrans.
        { refine (maponpaths (λ x, x · _) _); use (lineator_linnatright _ _ _ _ θ _ _ _ pointed_monoid_unit). }
        cbn; etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use monoid_to_unit_right_law. }
        rewrite <- id_left; etrans.
        2: { refine (maponpaths (λ x, x · _) _); use (tensor_id_id (V := V_Mon)). }
        rewrite <- tensor_mor_left.
        etrans; [|use (lineator_preservesunitor _ _ _ _ θ)].
        cbn; do 2 use maponpaths.
        symmetry; rewrite <- id_left.
        use (maponpaths (λ x, x · _) _); cbn.
        now rewrite (tensor_mor_left (V := V_Mon)), (tensor_id_id (V := V_Mon)).
      Qed.

      Definition strength_to_module
        : module (C := V_Mon) R_ob (monoid_struct _ R) (H R_ob)
        := make_module _ _ _ HR_module_subst_unit HR_module_subst_assoc.
    End FixAMonoid.

    (* Functoriality *)
    Section FixAMonoidMorphism.
      Context (R R' : MON Mon_V) (r : R --> R').

      Let R_ob  : V := monoid_carrier _ R.
      Let R'_ob : V := monoid_carrier _ R'.
      Let r_ob : R_ob --> R'_ob := pr1 r.

      Local Definition r_as_pointed_morphism
        : monoid_to_pointed R --> monoid_to_pointed R'
        := r_ob ,, pr22 r.

      Lemma strength_to_module_morphism
        : is_module_mor _ _ (strength_to_module R)
          (pullback_functor_funct _ (strength_to_module R') _ (pr2 r)) (#H r_ob).
      Proof.
        unfold is_module_mor, pullback_functor_funct; cbn.
        do 2 rewrite assoc.
        etrans.
        2: { rewrite <- assoc, <- functor_comp. refine (maponpaths (λ x, _ · #H x ) (pr12 r)). }
        rewrite functor_comp, assoc; refine (maponpaths (λ x, x · _) _).
        fold R'_ob R_ob r_ob.
        unfold functoronmorphisms1; rewrite functor_comp, assoc.
        etrans.
        { rewrite <- assoc; refine (maponpaths _ (lineator_linnatright _ _ _ _ θ _ _ _ r_as_pointed_morphism)). }
        cbn; rewrite assoc; use (maponpaths (λ x, x · _) _).
        use (lineator_linnatleft _ _ _ _ θ (monoid_to_pointed R)).
      Qed.
    End FixAMonoidMorphism.

    Definition strength_to_module_signature_data
      : @module_signature_data V_Mon.
    Proof.
      use tpair.
      - exact (λ R, _ ,, strength_to_module R).
      - exact (λ R R' r, _ ,, strength_to_module_morphism _ _ r).
    Defined.

    Lemma strength_to_module_signature_axioms
      : module_signature_axioms strength_to_module_signature_data.
    Proof.
      split; intros; apply MOD_mor_eq.
      - use functor_id.
      - use functor_comp.
    Qed.

    Definition strength_to_module_signature
      : module_signature_cat
      := strength_to_module_signature_data ,, strength_to_module_signature_axioms.
  End FixAStrength.

  Section FixAStrengthMorphism.
    Context {H H' : V ⟶ V} {α : H ⟹ H'}.
    Context {θ : pointedtensorialstrength Mon_V_swapped H}.
    Context {θ' : pointedtensorialstrength Mon_V_swapped H'}.
    Context (hyp : is_linear_nat_trans θ θ' α).

    Lemma strength_to_module_signature_morphism_lemma
      (R : MON Mon_V)
      : α (monoid_carrier Mon_V R) ⊗^{ Mon_V}_{r} pr1 R
        · H' (monoid_carrier Mon_V R) ⊗^{ Mon_V}_{l} identity (pr1 R)
        · θ' (monoid_to_pointed R) (monoid_carrier Mon_V R)
        · # H' (monoid_data_multiplication Mon_V (pr12 R))
      = θ (monoid_to_pointed R) (monoid_carrier Mon_V R)
        · # H (monoid_data_multiplication Mon_V (pr12 R))
        · α (monoid_carrier Mon_V R).
    Proof.
      rewrite (bifunctor_leftid Mon_V), id_right.
      etrans.
      2: { rewrite <- assoc; refine (!maponpaths _ _); use nat_trans_ax. }
      cbn; rewrite assoc; use (!maponpaths (λ x, x · _) _).
      use (hyp (monoid_to_pointed R)).
    Qed.

    Definition strength_to_module_signature_morphism
      : strength_to_module_signature θ --> strength_to_module_signature θ'.
    Proof.
      use tpair; cbn.
      - intros R; exists (α _); cbn.
        abstract (
            unfold is_module_mor; cbn;
            do 2 rewrite assoc;
            use strength_to_module_signature_morphism_lemma
          ).
      - intros R R' f; apply MOD_mor_eq.
        abstract (unfold mor_disp; cbn;
             rewrite transportf_total2; cbn;
             rewrite transportf_const; cbn;
             use nat_trans_ax
          ).
    Defined.
  End FixAStrengthMorphism.

  Definition strength_to_module_signature_functor_data
    : functor_data (pointedtensorialstrength_cat Mon_V_swapped) (module_signature_cat (C := V_Mon)).
  Proof.
    use tpair.
    - intros [? θ]; exact (strength_to_module_signature θ).
    - intros ? ? [? hyp]; exact (strength_to_module_signature_morphism hyp).
  Defined.

  Lemma strength_to_module_signature_functor_laws
    : is_functor strength_to_module_signature_functor_data.
  Proof.
    split.
    - intro. apply section_nat_trans_eq; intro.
      apply MOD_mor_eq; easy.
    - intros ? ? ? ? ?. apply section_nat_trans_eq; intro.
      apply MOD_mor_eq. cbn; unfold mor_disp.
      cbn; rewrite transportf_total2.
      cbn; now rewrite transportf_const.
  Qed.

  Definition strength_to_module_signature_functor
    : pointedtensorialstrength_cat Mon_V_swapped ⟶ module_signature_cat (C := V_Mon)
    := make_functor _ strength_to_module_signature_functor_laws.


  (** 2. Mapping of trivial and product signatures *)

  (* The functor maps the "trivial" and "product" signatures with strength to *)
  (* their equivalent as module signatures                                    *)

  Proposition signature_with_strength_to_module_signatures_trivial
    : strength_to_module_signature (trivial_signature_with_strength Mon_V_swapped)
      = trivial_signature.
  Proof.
    use module_signature_equality.
    - intro. use total2_paths_f.
      + use idpath.
      + abstract (
          use subtypePath;
          [use isaprop_module_laws|use id_left]
        ).
    - intros; etrans.
      + refine (maponpaths _ _); use transportf_total2_paths_f.
      + use (transportf_total2_paths_f (λ x, x --> _)).
  Qed.

  Proposition signature_with_strength_to_module_signatures_product
    (H : V ⟶ V) (θ : pointedtensorialstrength Mon_V_swapped H) (D : V)
    : strength_to_module_signature (product_signature_strength Mon_V_swapped H θ D)
      = product_signature (strength_to_module_signature θ) D.
  Proof.
    use module_signature_equality.
    - intro; use total2_paths_f.
      + use idpath.
      + abstract (
        use subtypePath;
        [ use isaprop_module_laws
        | cbn; unfold product_module_subst; cbn; now rewrite (bifunctor_leftcomp Mon_V), assoc ]
          ).
    - intros; etrans.
      + refine (maponpaths _ _); use transportf_total2_paths_f.
      + use (transportf_total2_paths_f (λ x, x --> _)).
  Qed.

  (** 3. Models are Sigma monoids *)
  Section ModelsAreSigmaMonoids.
    Context {H : V ⟶ V}.
    Context (θ : pointedtensorialstrength Mon_V_swapped H).

    Definition sigma_monoid_to_model
      (M : SigmaMonoid θ)
      : models_of_module_signatures_cat (strength_to_module_signature θ).
    Proof.
      use tpair; [|use tpair].
      - use monoid_swapped_to_monoid_functor; exact (SigmaMonoid_to_monoid θ M).
        (* SigmaMonoid_to_monoid gives an element of MON Mon_V_swapped and not MON Mon_V *)
      - exact (SigmaMonoid_τ θ M).
      - exact (!SigmaMonoid_is_compatible θ M).
    Defined.

    Definition model_to_sigma_monoid
      (M : models_of_module_signatures_cat (strength_to_module_signature θ))
      : SigmaMonoid θ.
    Proof.
      induction M as [[M M_mon] [τ hyp]].
      use (_ ,, (_ ,, _) ,, _); cbn.
      - exact M.
      - exact τ.
      - exact (monoid_to_monoid_swapped_monoid _ M_mon).
      - exact (!hyp).
    Defined.

    Definition sigma_monoid_to_model_functor_data
      : functor_data (SigmaMonoid θ) (models_of_module_signatures_cat (strength_to_module_signature θ)).
    Proof.
      exists sigma_monoid_to_model.
      intros M M' f.
      use ((_ ,, _ ,, _) ,, _); cbn.
      - exact (pr1 f).
      - abstract (
            unfold is_monoid_mor_mult; cbn; rewrite <- (monoidal_swapped_whiskering Mon_V); use (pr1 (pr212 f))
          ).
      - exact (pr2 (pr212 f)).
      - exact (pr112 f).
    Defined.

    Lemma sigma_monoid_to_model_functor_laws
      : is_functor sigma_monoid_to_model_functor_data.
    Proof.
      split.
      - intro.
        use subtypePath.
        { intro; use homset_property. }
        apply MON_mor_eq; easy.
      - intros ? ? ? ? ?.
        use subtypePath.
        { intro; use homset_property. }
        apply MON_mor_eq; easy.
    Qed.

    Definition sigma_monoid_to_model_functor
      : SigmaMonoid θ ⟶ models_of_module_signatures_cat (strength_to_module_signature θ)
      := make_functor _ sigma_monoid_to_model_functor_laws.

    Definition model_to_sigma_monoid_functor_data
      : functor_data (models_of_module_signatures_cat (strength_to_module_signature θ)) (SigmaMonoid θ).
    Proof.
      exists model_to_sigma_monoid.
      intros M M' f.
      use (_ ,, (_  ,, _ ,, _) ,, tt); cbn.
      - exact (pr11 f).
      - exact (pr2 f).
      - abstract (unfold is_monoid_mor_mult; rewrite (monoidal_swapped_whiskering Mon_V); exact (pr121 f)).
      - exact (pr221 f).
    Defined.

    Lemma model_to_sigma_monoid_functor_laws
      : is_functor model_to_sigma_monoid_functor_data.
    Proof.
      split.
      - intro.
        apply SigmaMonoid_mor_eq; easy.
      - intros ? ? ? ? ?.
        apply SigmaMonoid_mor_eq; easy.
    Qed.

    Definition model_to_sigma_monoid_functor
      : models_of_module_signatures_cat (strength_to_module_signature θ) ⟶ SigmaMonoid θ
      := make_functor _ model_to_sigma_monoid_functor_laws.

    Local Definition equivalence_models_sigma_monoids_adjuction_unit_data
      : nat_trans_data (functor_identity (SigmaMonoid θ)) (sigma_monoid_to_model_functor ∙ model_to_sigma_monoid_functor).
    Proof.
      intro R.
      exists (identity _).
      use ((_ ,, _ ,, _) ,, tt); cbn.
      - abstract(now rewrite functor_id, id_left, id_right).
      - abstract (
            unfold is_monoid_mor_mult; cbn; unfold functoronmorphisms1;
            now rewrite (bifunctor_leftid (monoidal_swapped Mon_V)),
              (bifunctor_rightid (monoidal_swapped Mon_V)),
              id_left, id_left, id_right
          ).
      - abstract (use id_right).
    Defined.

    Local Lemma equivalence_models_sigma_monoids_adjuction_unit_law
      : is_nat_trans _ _ equivalence_models_sigma_monoids_adjuction_unit_data.
    Proof.
      intros ? ? ?.
      apply SigmaMonoid_mor_eq.
      cbn; now rewrite id_left, id_right.
    Defined.

    Local Definition equivalence_models_sigma_monoids_adjuction_unit
      : functor_identity _ ⟹ sigma_monoid_to_model_functor ∙ model_to_sigma_monoid_functor
      := make_nat_trans _ _ _ equivalence_models_sigma_monoids_adjuction_unit_law.

    Local Definition equivalence_models_sigma_monoids_adjuction_counit_data
      : nat_trans_data (model_to_sigma_monoid_functor ∙ sigma_monoid_to_model_functor) (functor_identity _).
    Proof.
      intro R; use ((_ ,, _ ,, _) ,, _); cbn.
      - exact (identity _).
      - abstract (
            unfold is_monoid_mor_mult, functoronmorphisms1;
            now rewrite (bifunctor_leftid Mon_V), (bifunctor_rightid Mon_V),
              id_left, id_left, id_right
          ).
      - abstract (use id_right).
      - abstract (
          unfold is_model_of_signature_mor; cbn;
          now rewrite functor_id, id_left, id_right
        ).
    Defined.

    Local Lemma equivalence_models_sigma_monoids_adjuction_counit_law
      : is_nat_trans _ _ equivalence_models_sigma_monoids_adjuction_counit_data.
    Proof.
      intros ? ? ?.
      use subtypePath.
      { intro; use homset_property. }
      apply MON_mor_eq.
      cbn; now rewrite id_left, id_right.
    Qed.

    Local Definition equivalence_models_sigma_monoids_adjuction_counit
      : model_to_sigma_monoid_functor ∙ sigma_monoid_to_model_functor ⟹ functor_identity _
      := make_nat_trans _ _ _ equivalence_models_sigma_monoids_adjuction_counit_law.

    Definition equivalence_models_sigma_monoids_adjuction
      : adjunction_data (SigmaMonoid θ) (models_of_module_signatures_cat (strength_to_module_signature θ)).
    Proof.
      use make_adjunction_data.
      - exact sigma_monoid_to_model_functor.
      - exact model_to_sigma_monoid_functor.
      - exact equivalence_models_sigma_monoids_adjuction_unit.
      - exact equivalence_models_sigma_monoids_adjuction_counit.
    Defined.

    Definition equivalence_models_sigma_monoids_forms_equivalence
      : forms_equivalence equivalence_models_sigma_monoids_adjuction.
    Proof.
      split.
      - intro R; use ((_ ,, (_ ,, _ ,, _) ,, tt) ,, _ ,, _); cbn.
        + use identity.
        + abstract (now rewrite functor_id, id_left, id_right).
        + abstract (
              unfold is_monoid_mor_mult, functoronmorphisms1; cbn;
              now rewrite (bifunctor_leftid Mon_V), (bifunctor_rightid Mon_V), id_left, id_left, id_right
            ).
        + abstract (use id_right).
        + apply SigmaMonoid_mor_eq.
          use id_left.
        + apply SigmaMonoid_mor_eq.
          use id_left.
      - intro R; use (((_ ,, _ ,, _) ,, _) ,, _ ,, _); cbn.
        + use identity.
        + abstract (
              unfold is_monoid_mor_mult, functoronmorphisms1;
              now rewrite (bifunctor_leftid Mon_V), (bifunctor_rightid Mon_V),
                id_right, id_right, id_left
            ).
        + abstract (use id_right).
        + abstract (
            unfold is_model_of_signature_mor; cbn;
            now rewrite functor_id, id_left, id_right
          ).
        + use subtypePath.
          { intro; use homset_property. }
          apply MON_mor_eq.
          use id_left.
        + use subtypePath.
          { intro; use homset_property. }
          apply MON_mor_eq.
          use id_left.
    Qed.

    Definition equivalence_models_sigma_monoids
      : equivalence_of_cats (SigmaMonoid θ) (models_of_module_signatures_cat (strength_to_module_signature θ)).
    Proof.
      use make_equivalence_of_cats.
      - exact equivalence_models_sigma_monoids_adjuction.
      - exact equivalence_models_sigma_monoids_forms_equivalence.
    Defined.
  End ModelsAreSigmaMonoids.
End StrengthToModuleSignature.
