Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

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

  Context (H : V ⟶ V).
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
      rewrite <- id_left; etrans; swap 1 2.
      { refine (maponpaths (λ x, x · _) _); use (tensor_id_id (V := V_Mon)). }
      rewrite <- tensor_mor_left.
      etrans; [|use (lineator_preservesunitor _ _ _ _ θ)].
      cbn; do 2 use maponpaths.
      symmetry; rewrite <- id_left.
      use (maponpaths (λ x, x · _) _); cbn.
      now rewrite (tensor_mor_left (V := V_Mon)), (tensor_id_id (V := V_Mon)).
    Qed.

    Definition strength_to_module 
      : module (C := V_Mon) (pr1 R) (pr2 R) (H R_ob)
      := make_module _ _ _ HR_module_subst_unit HR_module_subst_assoc.
  End FixAMonoid.

  (* Functoriality *)
  Section FixAMonoidMorphism.
    Context (R R' : MON Mon_V) (r : R --> R').

    Let R_ob  : V := monoid_carrier _ R.
    Let R'_ob : V := monoid_carrier _ R'.
    Let r_ob : R_ob --> R'_ob := pr1 r.

    Local Definition r_is_pointed_morphism
      : monoid_to_pointed R --> monoid_to_pointed R'
      := r_ob ,, pr22 r.

    Lemma strength_to_module_morphism
      : is_module_mor _ _ (strength_to_module R)
        (pullback_functor_funct _ (strength_to_module R') _ (pr2 r)) (#H r_ob).
    Proof.
      unfold is_module_mor, pullback_functor_funct; cbn.
      do 2 rewrite assoc.
      etrans; swap 1 2.
      { rewrite <- assoc, <- functor_comp. refine (maponpaths (λ x, _ · #H x ) (pr12 r)). }
      rewrite functor_comp, assoc; refine (maponpaths (λ x, x · _) _).
      fold R'_ob R_ob r_ob.
      unfold functoronmorphisms1; rewrite functor_comp, assoc.
      etrans.
      { rewrite <- assoc; refine (maponpaths _ (lineator_linnatright _ _ _ _ θ _ _ _ r_is_pointed_morphism)). }
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
    split; intros; cbn.
    - use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      use functor_id.
    - use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      use functor_comp.
  Qed.

  Definition strength_to_module_signature
    : module_signature_cat
    := strength_to_module_signature_data ,, strength_to_module_signature_axioms.

  Section ModelsAreSigmaMonoids.

    Definition sigma_monoid_to_model 
      (M : SigmaMonoid θ)
      : models_of_module_signatures_cat strength_to_module_signature.
    Proof.
      use tpair; [|use tpair].
      - use monoid_swapped_to_monoid_functor; exact (SigmaMonoid_to_monoid θ M).
        (* SigmaMonoid_to_monoid gives an element of MON Mon_V_swapped and not MON Mon_V *)
      - exact (SigmaMonoid_τ θ M).
      - exact (!SigmaMonoid_is_compatible θ M). 
    Defined.
    
    Definition model_to_sigma_monoid 
      (M : models_of_module_signatures_cat strength_to_module_signature)
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
      : functor_data (SigmaMonoid θ) (models_of_module_signatures_cat strength_to_module_signature).
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
        use invmap; [|use path_sigma_hprop|].
        use homset_property.
        use invmap; [|use path_sigma_hprop|easy].
        use isaprop_is_monoid_mor.
      - intros ? ? ? ? ?. 
        use invmap; [|use path_sigma_hprop|].
        use homset_property.
        use invmap; [|use path_sigma_hprop|easy].
        use isaprop_is_monoid_mor.
    Qed.

    Definition sigma_monoid_to_model_functor
      : SigmaMonoid θ ⟶ models_of_module_signatures_cat strength_to_module_signature
      := make_functor _ sigma_monoid_to_model_functor_laws.

    Definition model_to_sigma_monoid_functor_data
      : functor_data (models_of_module_signatures_cat strength_to_module_signature) (SigmaMonoid θ).
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
        use invmap; [|use path_sigma_hprop|easy].
        do 2 try use isapropdirprod.
        + use homset_property.
        + use isaprop_is_monoid_mor.
        + use isapropunit.
      - intros ? ? ? ? ?. 
        use invmap; [|use path_sigma_hprop|easy].
        do 2 try use isapropdirprod.
        + use homset_property.
        + use isaprop_is_monoid_mor.
        + use isapropunit.
    Qed.

    Definition model_to_sigma_monoid_functor
      : models_of_module_signatures_cat strength_to_module_signature ⟶ SigmaMonoid θ
      := make_functor _ model_to_sigma_monoid_functor_laws.

    Local Definition equivalence_models_sigma_monoids_adjuction_nat1_data
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

    Local Lemma equivalence_models_sigma_monoids_adjuction_nat1_law
      : is_nat_trans _ _ equivalence_models_sigma_monoids_adjuction_nat1_data.
    Proof.
      intros ? ? ?.
      use invmap; [|use path_sigma_hprop|].
      do 2 try use isapropdirprod.
      - use homset_property.
      - use isaprop_is_monoid_mor.
      - use isapropunit.
      - cbn; now rewrite id_left, id_right.
    Defined.

    Local Definition equivalence_models_sigma_monoids_adjuction_nat1
      : functor_identity _ ⟹ sigma_monoid_to_model_functor ∙ model_to_sigma_monoid_functor
      := make_nat_trans _ _ _ equivalence_models_sigma_monoids_adjuction_nat1_law.
    
    Local Definition equivalence_models_sigma_monoids_adjuction_nat2_data
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
      - abstract (now rewrite functor_id, id_left, id_right).
    Defined.

    Local Lemma equivalence_models_sigma_monoids_adjuction_nat2_law
      : is_nat_trans _ _ equivalence_models_sigma_monoids_adjuction_nat2_data.
    Proof.
      intros ? ? ?.
      use invmap; [|use path_sigma_hprop|].
      use homset_property.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_monoid_mor.
      cbn; now rewrite id_left, id_right.
    Qed.

    Local Definition equivalence_models_sigma_monoids_adjuction_nat2
      : model_to_sigma_monoid_functor ∙ sigma_monoid_to_model_functor ⟹ functor_identity _
      := make_nat_trans _ _ _ equivalence_models_sigma_monoids_adjuction_nat2_law.

    Definition equivalence_models_sigma_monoids_adjuction
      : adjunction_data (SigmaMonoid θ) (models_of_module_signatures_cat strength_to_module_signature).
    Proof.
      use make_adjunction_data.
      - exact sigma_monoid_to_model_functor.
      - exact model_to_sigma_monoid_functor.
      - exact equivalence_models_sigma_monoids_adjuction_nat1.
      - exact equivalence_models_sigma_monoids_adjuction_nat2.
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
        + use invmap; [|use path_sigma_hprop|].
          do 2 try use isapropdirprod.
          * use homset_property.
          * use isaprop_is_monoid_mor.
          * use isapropunit.
          * use id_left.
        + use invmap; [|use path_sigma_hprop|].
          do 2 try use isapropdirprod.
          * use homset_property.
          * use isaprop_is_monoid_mor.
          * use isapropunit.
          * use id_left.
      - intro R; use (((_ ,, _ ,, _) ,, _) ,, _ ,, _); cbn.
        + use identity.
        + abstract (
            unfold is_monoid_mor_mult, functoronmorphisms1;
            now rewrite (bifunctor_leftid Mon_V), (bifunctor_rightid Mon_V), 
                        id_right, id_right, id_left
          ).
        + abstract (use id_right).
        + abstract (now rewrite functor_id, id_left, id_right).
        + use invmap; [|use path_sigma_hprop|].
          use homset_property.
          use invmap; [|use path_sigma_hprop|].
          use isaprop_is_monoid_mor.
          use id_left.
        + use invmap; [|use path_sigma_hprop|].
          use homset_property.
          use invmap; [|use path_sigma_hprop|].
          use isaprop_is_monoid_mor.
          use id_left.
    Qed.

    Definition equivalence_models_sigma_monoids
      : equivalence_of_cats (SigmaMonoid θ) (models_of_module_signatures_cat strength_to_module_signature).
    Proof.
      use make_equivalence_of_cats.
      - exact equivalence_models_sigma_monoids_adjuction.
      - exact equivalence_models_sigma_monoids_forms_equivalence.
    Defined.
  End ModelsAreSigmaMonoids.
End StrengthToModuleSignature.

