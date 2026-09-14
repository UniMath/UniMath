(***************************************************************************

 Models of a Module Signature

 In this file, we define models of some given module signature Σ as a monoid R
 and a morphism of right modules Σ(R) --> trivial_module(R).

 Contents
 1. Definitions
 2. Initial models as fixed points of I + Σ(-)
 3. Total category of models and signatures
 4. Modularity

 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Require Import UniMath.Tactics.EnsureStructuredProofs. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.

Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope mor_disp_scope.

Section ModelsOfModuleSignature.
  Context {C : monoidal_cat}.

  Context (Σ : @module_signature_cat C).

  (**
     1. Definitions
   *)

  Definition is_model_of_signature_mor
    {R R' : MON C}
    (r : pr1 (Σ R) --> pr1 R)
    (r' : pr1 (Σ R') --> pr1 R')
    (f : R --> R')
    :=
    r · pr1 f = pr1 (section_disp_on_morphisms (pr1 Σ) f) · r'.

  Definition models_of_module_signatures_disp_cat_ob_mor : disp_cat_ob_mor (MON C).
  Proof.
    use make_disp_cat_ob_mor.
    - intro R; exact (Σ R --> trivial_module (pr1 R) (pr2 R)).
    - intros R R' r r' f; exact (is_model_of_signature_mor (pr1 r) (pr1 r') f).
  Defined.

  Lemma models_of_module_signatures_disp_cat_id_comp
    : disp_cat_id_comp (MON C) models_of_module_signatures_disp_cat_ob_mor.
  Proof.
    split; intros.
    - cbn; unfold is_model_of_signature_mor;
      now rewrite @section_disp_id, id_left, id_right.
    - simpl; unfold is_model_of_signature_mor.
      rewrite @section_disp_comp; simpl.
      rewrite assoc; cbn; etrans.
      + refine (maponpaths (λ x, x · _) X).
      + do 2 rewrite <- assoc; now use maponpaths.
  Qed.

  Definition models_of_module_signatures_disp_cat_data : disp_cat_data (MON C)
    := models_of_module_signatures_disp_cat_ob_mor ,, models_of_module_signatures_disp_cat_id_comp.

  Definition models_of_module_signatures_disp_cat : disp_cat (MON C).
  Proof.
    use (make_disp_cat_locally_prop (D:=models_of_module_signatures_disp_cat_data)).
    red; intros; apply homset_property.
  Defined.

  Definition models_of_module_signatures_cat : category
    := total_category models_of_module_signatures_disp_cat.

  Coercion monoid_of_models_of_module_signatures
    (M : models_of_module_signatures_cat)
    : MON C := pr1 M.

  Definition is_representable := Initial models_of_module_signatures_cat.
End ModelsOfModuleSignature.

(**
   2. Initial models as fixed points of I + Σ(-)
  *)

(* A lemma very similar to Lambek's on initial algebras as fixed points *)
Local Lemma lambek (D : category)
  (F : D ⟶ D)
  (α : F ⟹ functor_identity _)
  (O : Initial D)
  (H : pre_whisker F α = post_whisker α F)
  : isInitial D (F (InitialObject O)).
Proof.
  assert (#F (InitialArrow O _) · α _ = identity _) as H'.
  {
    transitivity (#F (InitialArrow O _) · #F (α (InitialObject O))).
    - use maponpaths; exact (maponpaths (λ f, pr1 f _) H).
    - rewrite <- functor_comp, <- functor_id;
      use maponpaths;
      use InitialArrowEq.
  }

  assert (∏ (d : D) (f : F (InitialObject O) --> d),
      InitialArrow O d = InitialArrow O _ · f
  ) as H'' by (intros; use InitialArrowEq).

  use make_isInitial; intro d.
  exists (α (InitialObject O) · InitialArrow _ _).
  intro f; symmetry;
  rewrite <- id_left, <- H', (H'' _ f), assoc.
  use (maponpaths (λ x, x · f));
  use (!nat_trans_ax α _ _ _).
Qed.

Section InitialModelsAsFixedPoints.
  Context {C : monoidal_cat}.
  Context (Σ : @module_signature_cat C).
  Context (Copr : BinCoproducts C).
  Context (Hpres : ∏ Z, preserves_bincoproduct (rightwhiskering_functor C Z)).

  Let copr (A : C) (B : C) : C := BinCoproductObject (Copr A B).
  Local Notation "A ++ B" := (copr A B) (at level 60).

  Let inl {A B : C} : A --> (A ++ B) := BinCoproductIn1 _.
  Let inr {A B : C} : B --> (A ++ B) := BinCoproductIn2 _.

  Lemma iscopr {X Y : C}
    : isBinCoproduct C X Y (X ++ Y) inl inr.
  Proof.
    use isBinCoproduct_BinCoproduct.
  Qed.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  Local Definition ProdSum {X Y Z : C} : BinCoproduct (X ⊗ Z) (Y ⊗ Z)
    := make_BinCoproduct _ _ _ _ _ _ (Hpres _ _ _ _ _ _ iscopr).

  Local Definition arrow_from_prod_sum {X Y Z : C}
    : (X ++ Y) ⊗ Z --> (X ⊗ Z ++ Y ⊗ Z)
    := BinCoproductArrow ProdSum inl inr.

  Local Lemma arrow_from_prod_sum_inl {X Y Z : C}
    : inl ⊗r Z · @arrow_from_prod_sum X Y Z = inl.
  Proof.
    use (BinCoproductIn1Commutes _ _ _ ProdSum).
  Qed.

  Local Lemma arrow_from_prod_sum_inr {X Y Z : C}
    : inr ⊗r Z · @arrow_from_prod_sum X Y Z = inr.
  Proof.
    use (BinCoproductIn2Commutes _ _ _ ProdSum).
  Qed.

  Local Lemma arrow_from_prod_sum_nat {X Y Z W : C}
    : (X ++ Y) ⊗l inl · @arrow_from_prod_sum X Y (Z ++ W)
    = arrow_from_prod_sum · BinCoproductOfArrows _ _ _ (_ ⊗l inl) (_ ⊗l inl).
  Proof.
    use (BinCoproductArrowsEq _ _ _ ProdSum _); cbn.
    - etrans; etrans; try rewrite assoc; swap 3 4.
      + refine (maponpaths (λ x, x · _) _).
        rewrite tensor_mor_left, tensor_mor_right.
        use tensor_swap.
      + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
        refine (maponpaths _ _).
        use arrow_from_prod_sum_inl.
      + symmetry; refine (maponpaths (λ x, x · _) _).
        use arrow_from_prod_sum_inl.
      + symmetry; use BinCoproductOfArrowsIn1.
    - etrans; etrans; try rewrite assoc; swap 3 4.
      + refine (maponpaths (λ x, x · _) _).
        rewrite tensor_mor_left, tensor_mor_right.
        use tensor_swap.
      + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
        refine (maponpaths _ _).
        use arrow_from_prod_sum_inr.
      + refine (!maponpaths (λ x, x · _) _).
        use arrow_from_prod_sum_inr.
      + symmetry; use BinCoproductOfArrowsIn2.
  Qed.

  Section FixAModel.
    Context (M : models_of_module_signatures_cat Σ).

    Let rM : pr1 (Σ M) --> pr11 M := pr12 M.
    Let ηM : I_{C} --> pr11 M := monoid_data_unit _ (pr121 M).
    Let μM : pr11 M ⊗ pr11 M --> pr11 M := monoid_data_multiplication _ (pr121 M).
    Let pM : pr1 (Σ M) ⊗ pr11 M --> pr1 (Σ M) := pr12 (Σ M).

    Let M' := I_{C} ++ pr1 (Σ M).
    Let η : I_{C} --> M' := inl.

    Local Definition f : M' --> pr11 M
      := BinCoproductArrow _ ηM rM.

    (* Multiplication is defined as the following

                 ≅                       [λ,u]
       M' ⊗ M' -----> I ⊗ M' + Σ(M) ⊗ M' -----> M'
                 μ₁                        μ₂


       where λ is the left unitor and u is defined as the composite of


                  Σ(M) ⊗ f              p            inr
       Σ(M) ⊗ M' ---------> Σ(M) ⊗ M -------> Σ(M) -------> M'

       where p is the module substitution of Σ(M) ∈ MOD M
    *)

    Local Definition μ₁ : M' ⊗ M' --> (I_{C} ⊗ M' ++ pr1 (Σ M) ⊗ M')
      := arrow_from_prod_sum.

    Local Definition μ₂ : (I_{C} ⊗ M' ++ pr1 (Σ M) ⊗ M') --> M'.
    Proof.
      use BinCoproductArrow.
      - use lu_{C}.
      - use (pr1 (Σ M) ⊗l f · pM · inr).
    Defined.

    Local Definition μ : M' ⊗ M' --> M' := μ₁ · μ₂.

    Local Lemma multiplication_inl
      : inl ⊗r M' · μ = lu^{ C }_{ M'}.
    Proof.
      unfold μ, η, μ₁; rewrite assoc.
      etrans.
      - refine (maponpaths (λ x, x · _) arrow_from_prod_sum_inl).
      - use BinCoproductIn1Commutes.
    Qed.

    Local Lemma multiplication_inr
      : inr ⊗r M' · μ = pr1 (Σ M) ⊗l f · pM · inr.
    Proof.
      unfold μ, η, μ₁; rewrite assoc.
      etrans.
      - refine (maponpaths (λ x, x · _) arrow_from_prod_sum_inr).
      - use BinCoproductIn2Commutes.
    Qed.

    Local Lemma f_inl : inl · f = ηM.
    Proof.
      use BinCoproductIn1Commutes.
    Qed.

    Local Lemma f_inr : inr · f = rM.
    Proof.
      use BinCoproductIn2Commutes.
    Qed.


    (* Three laws for M' to be a monoid *)

    Local Lemma μ_lunit : η ⊗r M' · μ = lu^{ C }_{ M'}.
    Proof.
      use multiplication_inl.
    Qed.

    Local Lemma μ_runit : M' ⊗l η · μ = ru^{ C }_{ M'}.
    Proof.
      use (BinCoproductArrowsEq _ _ _ ProdSum _); cbn.
      - etrans; etrans. etrans.
        + rewrite assoc, tensor_mor_left, tensor_mor_right.
          refine (maponpaths (λ x, x · _) _). use tensor_swap.
        + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
          use maponpaths; [|use multiplication_inl].
        + use monoidal_leftunitornat.
        + refine (maponpaths (λ x, x · _) _); use unitors_coincide_on_unit.
        + symmetry; use monoidal_rightunitornat.
      - etrans; (etrans; [etrans|]).
        + rewrite assoc, tensor_mor_left, tensor_mor_right.
          use (maponpaths (λ x, x · _)); [|use tensor_swap].
        + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
          refine (maponpaths _ _); use multiplication_inr.
        + rewrite assoc, assoc.
          refine (!maponpaths (λ x, x · _ · _) _).
          use (bifunctor_leftcomp C).
        + refine (maponpaths (λ x, _ ⊗l x · _ · _) _); use BinCoproductIn1Commutes.
        + refine (maponpaths (λ x, x · _) (pr222 (Σ M))).
        + symmetry; use monoidal_rightunitornat.
    Qed.

    Local Lemma f_respects_multiplication : μ · f = (f #⊗ f) · μM.
    Proof.
      use (BinCoproductArrowsEq _ _ _ ProdSum (pr11 M)).
      - cbn; rewrite assoc; symmetry; etrans; [etrans;etrans|etrans]; symmetry.
        + rewrite assoc; refine (maponpaths (λ x, x · _) _).
          rewrite tensor_split', <- tensor_mor_left, <- tensor_mor_right, assoc.
          use (maponpaths (λ x, x · _)); [|use (bifunctor_rightcomp C)].
        + use (maponpaths (λ x, x ⊗r _ · _ · _)); [|use (!f_inl)].
        + rewrite tensor_mor_left, tensor_mor_right.
          use (maponpaths (λ x, x · _)); [|use tensor_swap'].
        + rewrite <- tensor_mor_right, <- tensor_mor_left, <- assoc.
          refine (!maponpaths _ _); use monoid_to_unit_left_law.
        + symmetry; use monoidal_leftunitornat.
        + refine (maponpaths (λ x, x · _)  multiplication_inl).
      - cbn; rewrite assoc; symmetry; etrans; [etrans;etrans|etrans]; symmetry.
        + rewrite assoc; refine (maponpaths (λ x, x · _) _).
          rewrite tensor_split', <- tensor_mor_left, <- tensor_mor_right, assoc.
          use (maponpaths (λ x, x · _)); [|use (bifunctor_rightcomp C)].
        + use (maponpaths (λ x, x ⊗r _ · _ · _)); [|use (!f_inr)].
        + rewrite tensor_mor_left, tensor_mor_right.
          use (maponpaths (λ x, x · _)); [|use tensor_swap'].
        + rewrite <- tensor_mor_right, <- tensor_mor_left, <- assoc.
          refine (!maponpaths _ (pr22 M)).
        + fold rM; now rewrite assoc.
        + etrans.
          * refine (maponpaths (λ x, x · _) multiplication_inr).
          * do 3 rewrite <- assoc; do 2 use maponpaths; use f_inr.
    Qed.

    Local Definition ProdProdSum {X Y Z W : C}
      : BinCoproduct ((X ⊗ W) ⊗ Z) ((Y ⊗ W) ⊗ Z)
      := make_BinCoproduct _ _ _ _ _ _ (Hpres _ _ _ _ _ _ (Hpres _ _ _ _ _ _ iscopr)).

    Local Lemma μ_assoc : α^{ C }_{ M', M', M'} · M' ⊗l μ · μ = μ ⊗r M' · μ.
    Proof.
      use (BinCoproductArrowsEq _ _ _ ProdProdSum M').
      cbn; repeat rewrite assoc.
      - do 3 etrans; swap 7 8.
        + refine (!maponpaths (λ x, x · _ · _) _); use monoidal_associatornatright.
        + rewrite <- assoc, <- assoc, @tensor_mor_right, @tensor_mor_left.
          refine (maponpaths _ _); rewrite assoc.
          refine (maponpaths (λ x, x · _) _); use tensor_swap.
        + rewrite <- tensor_mor_right, <- tensor_mor_left, <- assoc.
          do 2 (refine (maponpaths _ _)).
          use multiplication_inl.
        + refine (maponpaths _ _); use monoidal_leftunitornat.
        + use assoc.
        + refine (maponpaths (λ x, x · _) _); use right_whisker_with_lunitor.
        + refine (maponpaths (λ x, x · _) _); use (bifunctor_rightcomp C).
        + refine (!maponpaths (λ x, x ⊗r _ · _) _); use multiplication_inl.
      - symmetry; do 3 etrans.
        8: etrans; swap 1 2; symmetry; etrans.
        + cbn. rewrite assoc; etrans.
          * refine (!maponpaths (λ x, x · _) _); use (bifunctor_rightcomp C).
          * refine (maponpaths (λ x, x ⊗r _ · _) _); use multiplication_inr.
        + do 2 rewrite (bifunctor_rightcomp C), <- assoc.
          do 2 (refine (maponpaths _ _)).
          use multiplication_inr.
        + rewrite @tensor_mor_right, @tensor_mor_left, @tensor_mor_right; do 3 rewrite assoc.
          refine (maponpaths (λ x, x · _ · _) _).
          rewrite <- assoc; refine (maponpaths _ _). use tensor_swap.
        + rewrite assoc; refine (maponpaths (λ x, x · _ · _ · _) _). use tensor_swap.
        + repeat rewrite <- tensor_mor_left; repeat rewrite <- tensor_mor_right.
          refine (maponpaths (λ x, x · _) _).
          rewrite <- assoc; refine (!maponpaths _ (pr122 (Σ M))).
        + do 2 rewrite assoc; refine (maponpaths (λ x, x · _ · _ · _) _).
          rewrite <- assoc; refine (!maponpaths _ _).
          use monoidal_associatornatleftright.
        + rewrite assoc; refine (!maponpaths (λ x, x · _ · _ · _ · _) _).
          use monoidal_associatornatleft.
        + do 2 rewrite assoc; refine (!maponpaths (λ x, x · _ · _ ) _).
          use monoidal_associatornatright.
        + rewrite <- assoc, <- assoc, @tensor_mor_left, @tensor_mor_right.
          refine (maponpaths _ _); rewrite assoc.
          refine (maponpaths (λ x, x · _) (tensor_swap _ _)).
        + rewrite <- tensor_mor_left, <- tensor_mor_right.
          refine (maponpaths _ _); rewrite <- assoc.
          refine (maponpaths _ _); use multiplication_inr.
        + do 3 rewrite assoc; use (maponpaths (λ x, x · pM · inr)).
          do 3 rewrite <- assoc; use (maponpaths (λ x, _ · x)).
          etrans; [etrans|].
          * symmetry; use (bifunctor_leftcomp C).
          * refine (maponpaths _ _); use f_respects_multiplication.
          * do 2 rewrite <- (bifunctor_leftcomp C).
            use maponpaths.
            now rewrite assoc, @tensor_split, @tensor_mor_left, @tensor_mor_right.
    Qed.

    Definition iter_model_monoid : monoid C (I_{C} ++ pr1 (Σ M))
      := make_monoid _ μ η μ_lunit μ_runit μ_assoc.

    Local Definition M'_mon : MON C := M' ,, iter_model_monoid.

    Local Definition f_mon : MON C⟦M'_mon, pr1 M⟧
      := f ,, (!f_respects_multiplication ,, f_inl).


    (* To make M' a model, we use the following morphism as model evaluation

                   Σ(f)          inr
           Σ(M') -------> Σ(M) ------> M'
     *)


    Local Definition r : pr1 (Σ M'_mon) --> M'
      := pr1 (section_disp_on_morphisms (pr1 Σ) f_mon) · inr.

    Local Lemma r_is_module_mor
      : is_module_mor _ _ (pr2 (Σ M'_mon)) (pr2 (trivial_module _ _)) r.
    Proof.
      unfold is_module_mor, r; cbn.
      rewrite assoc, (bifunctor_rightcomp C).
      etrans.
      - rewrite <- assoc; refine (maponpaths _ multiplication_inr).
      - rewrite assoc; use (maponpaths (λ x, x · _)).
        exact (pr2 (section_disp_on_morphisms (pr1 Σ) f_mon)).
    Qed.

    Local Definition r_mon
      : (Σ M'_mon) --> trivial_module _ (pr2 M'_mon)
      := r ,, r_is_module_mor.

    Definition iter_model
      : models_of_module_signatures_cat Σ
      := M'_mon ,, r_mon.

    Lemma iter_model_map_is_model_morphism
      : is_model_of_signature_mor Σ r rM f_mon.
    Proof.
      unfold is_model_of_signature_mor, r; rewrite <- assoc.
      use maponpaths.
      use f_inr.
    Qed.


  End FixAModel.


  (* The mapping M ↦ M' is functorial *)

  Section FixAModelMorphism.
    Context (M N : models_of_module_signatures_cat Σ).
    Context (h : M --> N).

    Let M'_mon: MON C := pr1 (iter_model M).
    Let N'_mon: MON C := pr1 (iter_model N).

    Let M' : C := pr1 M'_mon.
    Let N' : C := pr1 N'_mon.

    Let μM' : M' ⊗ M' --> M' := monoid_data_multiplication _ (pr12 M'_mon).
    Let μN' : N' ⊗ N' --> N' := monoid_data_multiplication _ (pr12 N'_mon).

    Let ηM' : I_{C} --> M' := monoid_data_unit _ (pr12 M'_mon).
    Let ηN' : I_{C} --> N' := monoid_data_unit _ (pr12 N'_mon).

    Local Definition h' : M' --> N'
      := BinCoproductOfArrows _ _ _ (identity _)
        (pr1 (section_disp_on_morphisms (pr1 Σ) (pr1 h))).

    Local Lemma f_nat : h' · f N = f M · pr11 h.
    Proof.
      use (BinCoproductArrowsEq _ _ _ _ (pr11 N)); cbn.
      - rewrite assoc, assoc; etrans; etrans; swap 3 4.
        + refine (maponpaths (λ x, x · _) _); use BinCoproductOfArrowsIn1.
        + rewrite id_left; use f_inl.
        + refine (!maponpaths (λ x, x · _) (f_inl _)).
        + refine (!pr221 h).
      - rewrite assoc, assoc; etrans; etrans; swap 3 4.
        + refine (maponpaths (λ x, x · _) _); use BinCoproductOfArrowsIn2.
        + rewrite <- assoc; refine (maponpaths _ _); use f_inr.
        + refine (!maponpaths (λ x, x · _) (f_inr _)).
        + use (!pr2 h).
    Qed.



    Local Lemma h'_respects_multiplication
      : h' #⊗ h' · μN' = μM' · h'.
    Proof.
      use (
        BinCoproductArrowsEq _ _ _
        (make_BinCoproduct _ _ _ _ _ _ (Hpres _ _ _ _ _ _ iscopr))
        N'
      ); cbn.
      - do 2 rewrite assoc; etrans; [etrans; etrans|etrans]; cycle 5.
        + refine (!maponpaths (λ x, x · _) _); use multiplication_inl.
        + rewrite tensor_split', tensor_mor_right, assoc,
            <- tensor_mor_right, <- tensor_mor_right, <- tensor_mor_left.
          use (maponpaths (λ x, x · _ · _)); [|symmetry; use (bifunctor_rightcomp C)].
        + use (maponpaths (λ x, x ⊗r _ · _ · _)); [|use BinCoproductOfArrowsIn1].
        + rewrite id_left, tensor_mor_left, tensor_mor_right.
          use (maponpaths (λ x, x · _ )); [|use tensor_swap].
        + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
          use maponpaths; [|use multiplication_inl].
        + use monoidal_leftunitornat.
      - do 2 rewrite assoc; etrans; etrans; etrans; cycle 6; swap 1 2; swap 7 8.
        + use (maponpaths (λ x, x · _)); [|use (!multiplication_inr _)].
        + rewrite <- assoc; symmetry; use maponpaths; [|use BinCoproductOfArrowsIn2].
        + rewrite tensor_split', tensor_mor_right, assoc,
            <- tensor_mor_right, <- tensor_mor_right, <- tensor_mor_left.
          use (maponpaths (λ x, x · _ · _)); [|symmetry; use (bifunctor_rightcomp C)].
        + use (maponpaths (λ x, x ⊗r _ · _ · _)); [|use BinCoproductOfArrowsIn2].
        + rewrite tensor_mor_left, tensor_mor_right.
          use (maponpaths (λ x, x · _ )); [|use tensor_swap].
        + rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc,
            (bifunctor_rightcomp C), <- assoc.
          do 2 refine (maponpaths _ _).
          use multiplication_inr.
        + rewrite assoc. refine (maponpaths (λ x, x · _) _).
          rewrite <- assoc; refine (maponpaths _ _).
          use (pr2 (section_disp_on_morphisms (pr1 Σ) (pr1 h))).
        + cbn; do 5 rewrite assoc; use (maponpaths (λ x, x · _ · _)).
          etrans; etrans.
          * refine (maponpaths (λ x, x · _) _).
            rewrite tensor_mor_left, tensor_mor_right. use tensor_swap'.
          * rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
            refine (!maponpaths _ _). use (bifunctor_leftcomp C).
          * use (maponpaths (λ x, _ · _ ⊗l x)); [|use f_nat].
          * rewrite (bifunctor_leftcomp C), assoc; use (maponpaths (λ x, x · _)).
            do 2 rewrite @tensor_mor_left, @tensor_mor_right.
            use tensor_swap.
    Qed.


    Local Lemma h'_is_module_mor
      : is_monoid_mor C (pr2 M'_mon) (pr2 N'_mon) h'.
    Proof.
      split.
      - use h'_respects_multiplication.
      - etrans; [use BinCoproductOfArrowsIn1|use id_left].
    Qed.

    Local Definition h'_mon : M'_mon --> N'_mon
      := h' ,, h'_is_module_mor.

    Local Lemma f_nat_mon : f_mon M · pr1 h = h'_mon · f_mon N.
    Proof.
      apply MON_mor_eq.
      use (!f_nat).
    Qed.

    Local Lemma h'_is_model_mor
      : is_model_of_signature_mor Σ (r M) (r N) h'_mon.
    Proof.
      unfold r; etrans; etrans; swap 3 4.
      + rewrite <- assoc; use maponpaths; [|use BinCoproductOfArrowsIn2].
      + rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (!maponpaths pr1 (section_disp_comp Σ _ _ _ _ _)).
      + rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (maponpaths pr1 (section_disp_comp Σ _ _ _ _ _)).
      + eassert _  as H by exact (
          transport_section
          (λ x, pr1 (section_disp_on_morphisms (pr1 Σ) x) · inr (A := I_{C}))
          f_nat_mon
        ); cbn in H.
        rewrite transportf_const in H.
        use H.
    Qed.


    Definition iter_model_morphism
      : iter_model M --> iter_model N
      := h'_mon ,, h'_is_model_mor.
  End FixAModelMorphism.

  (* iter_model_functor is the functor I + Σ(-) : Model(Σ) ⟶ Model(Σ) *)

  Definition iter_model_functor_data
    : functor_data (models_of_module_signatures_cat Σ) (models_of_module_signatures_cat Σ)
    := make_functor_data iter_model iter_model_morphism.

  Lemma iter_model_is_functor : is_functor iter_model_functor_data.
  Proof.
    split.
    - intro M.
      use subtypePath.
      { intro; use homset_property. }
      apply MON_mor_eq.
      symmetry; use BinCoproduct_endo_is_identity.
      + etrans; [use BinCoproductOfArrowsIn1|use id_left].
      + etrans; [use BinCoproductOfArrowsIn2|].
        rewrite <- id_left; use (maponpaths (λ x, x · _)).
        use (maponpaths pr1 (section_disp_id Σ _)).
    - intros M N P h g.
      use subtypePath.
      { intro; use homset_property. }
      apply MON_mor_eq.
      symmetry; use BinCoproductArrowUnique.
      + cbn; rewrite id_left, assoc; etrans; [etrans|].
        * use (maponpaths (λ x, x · _)); [|use BinCoproductOfArrowsIn1].
        * rewrite id_left; use BinCoproductOfArrowsIn1.
        * use id_left.
      + cbn; rewrite assoc; etrans; etrans; swap 3 4.
        * use (maponpaths (λ x, x · _)); [|use BinCoproductOfArrowsIn2].
        * rewrite <- assoc; use maponpaths; [|use BinCoproductOfArrowsIn2].
        * refine (!maponpaths (λ x, x · _) _).
          refine (maponpaths pr1 (section_disp_comp Σ _ _ _ _ _)).
        * use assoc.
  Qed.

  Definition iter_model_functor
    : models_of_module_signatures_cat Σ ⟶ models_of_module_signatures_cat Σ
    := make_functor iter_model_functor_data iter_model_is_functor.


  (* The mapping M' → M forms a natural transformation *)

  Definition iter_model_to_model_nat_trans_data
    : nat_trans_data iter_model_functor (functor_identity _)
    := λ M, f_mon M ,, iter_model_map_is_model_morphism M.

  Lemma iter_model_to_model_nat_is_nat
    : is_nat_trans _ _ iter_model_to_model_nat_trans_data.
  Proof.
    intros M N h.
    use subtypePath.
    { intro; use homset_property. }
    apply MON_mor_eq.
    use f_nat.
  Qed.

  Definition iter_model_to_model_nat_trans
    : iter_model_functor ⟹ functor_identity _
    := make_nat_trans _ _
      iter_model_to_model_nat_trans_data
      iter_model_to_model_nat_is_nat.

  Lemma iter_model_functor_nat_commutes
    : pre_whisker iter_model_functor iter_model_to_model_nat_trans
    = post_whisker iter_model_to_model_nat_trans iter_model_functor.
  Proof.
    apply nat_trans_eq; [use homset_property|]; intro M.
    use subtypePath.
    { intro; use homset_property. }
    apply MON_mor_eq.
    cbn.
    use BinCoproductArrowsEq; cbn.
    - etrans; [etrans|]; swap 2 3.
      + use (f_inl (iter_model M)).
      + symmetry; use BinCoproductOfArrowsIn1.
      + symmetry; use id_left.
    - etrans.
      + use (f_inr (iter_model M)).
      + symmetry; use BinCoproductOfArrowsIn2.
  Qed.


  (* If M is the initial model of Σ then I + Σ(M) is also initial
     (and thus a fixed point by uniqueness of initial objects) *)

  Proposition initial_model_fixed_point (HΣ : is_representable Σ)
    : isInitial _ (iter_model (InitialObject HΣ)).
  Proof.
    use (lambek _ _ _ HΣ iter_model_functor_nat_commutes).
  Qed.
End InitialModelsAsFixedPoints.

(**
   3. Total category of models and signatures

   Objects are pairs (Σ, M) where Σ is a module signature and M is a model of Σ
 *)

Section TotalCategoriesOfModels.
  Context {C : monoidal_cat}.

  (*
     Given h : Σ → Σ', a model (M, r) for Σ' can be transformed into a model
     (M, r') for Σ where r' is the morphism

                    h(M)            r
             Σ(M) -------> Σ'(M) ------> M
  *)

  Definition pullback_functor_data
    {Σ Σ' : @module_signature_cat C} (h : Σ --> Σ')
    : functor_data (models_of_module_signatures_cat Σ') (models_of_module_signatures_cat Σ).
  Proof.
    use make_functor_data.
    - intros (R, r); exists R.
      refine (_ · _).
      + refine (pr1 h R).
      + refine (pr1 r ,, _).
        abstract (
          cbn; unfold pullback_functor_funct, is_module_mor; cbn;
          rewrite @tensor_mor_left, tensor_id_id, id_left;
          use (pr2 r)
        ).
    - intros (R, r) (R', r') (f, H).
      eexists f; cbn.
      abstract (
        etrans;
        [
          rewrite <- assoc; use maponpaths; [| use H]
        | do 2 rewrite assoc; use (maponpaths (λ x, x · _));
          eassert _ as X by exact (maponpaths pr1 (pr2 h R R' f));
          cbn in X; unfold mor_disp in X;
          cbn in X; rewrite transportf_total2 in X;
          cbn in X; rewrite transportf_const in X;
          cbn in X; use (!X)
        ]
      ).
  Defined.

  Lemma pullback_functor_is_functor
    {Σ Σ' : @module_signature_cat C} (h : Σ --> Σ')
    : is_functor (pullback_functor_data h).
  Proof.
    use make_is_functor; unfold functor_idax, functor_compax;
    intros; (use subtypePath; [intro|]);
    now try use homset_property.
  Qed.



  Definition pullback_functor
    {Σ Σ' : @module_signature_cat C} (h : Σ --> Σ')
    : (models_of_module_signatures_cat Σ') ⟶ (models_of_module_signatures_cat Σ)
    := make_functor (pullback_functor_data h) (pullback_functor_is_functor h).

  Definition total_category_of_models_disp_cat_ob_mor : disp_cat_ob_mor (@module_signature_cat C).
  Proof.
    use tpair.
    - use models_of_module_signatures_cat.
    - intros Σ Σ' Rr Rr' h. use (Rr --> pullback_functor h Rr').
  Defined.

  Definition total_category_of_models_disp_cat_id_comp
    : disp_cat_id_comp module_signature_cat total_category_of_models_disp_cat_ob_mor.
  Proof.
    split; intros; use tpair.
    - use identity.
    - cbn; unfold is_model_of_signature_mor; cbn.
      abstract (cbn; now rewrite id_left, id_right, @section_disp_id, id_left).
    - cbn; induction X as [u _]; induction X0 as [v _]; use (u · v).
    - abstract (
        rename x into Σ, y into Σ', z into Σ'', X into u, X0 into v;
        induction xx as [R r]; induction yy as [R' r']; induction zz as [R'' r''];
        simpl; unfold mor_disp, total_category_of_modules_disp_cat_ob_mor;
        simpl; unfold is_model_of_signature_mor;
        simpl; rewrite transportf_total2;
        simpl; rewrite transportf_const;
        simpl; rewrite @section_disp_comp, assoc, assoc, assoc; cbn;
        etrans; [|symmetry; etrans];
        [
          refine (maponpaths (λ x, x · _) (pr2 u))
        | do 3 rewrite <- assoc; refine (maponpaths _ _);
          rewrite assoc; refine (maponpaths (λ x, x · _) _);
          eassert _ by exact (maponpaths pr1 (pr2 f0 R' R'' (pr1 v)));
          simpl in X; unfold mor_disp, total_category_of_modules_disp_cat_ob_mor in X;
          simpl in X; rewrite transportf_total2 in X;
          simpl in X; rewrite transportf_const in X;
          use X
        | cbn; do 3 rewrite <- assoc; do 2 use maponpaths; use (!pr2 v)
        ]
      ).
  Defined.

  Definition total_category_of_models_disp_cat_data : disp_cat_data module_signature_cat
    := total_category_of_models_disp_cat_ob_mor ,, total_category_of_models_disp_cat_id_comp.


  Lemma total_category_of_models_disp_cat_axioms
    : disp_cat_axioms _ total_category_of_models_disp_cat_data.
  Proof.
    repeat split; intros; cycle 3.
    {
      use isaset_total2; [|intros; use isasetaprop]; use homset_property.
    }
    all:
      use subtypePath; [intro; use homset_property|];
      apply MON_mor_eq;
      simpl; unfold transportb, mor_disp, total_category_of_models_disp_cat_ob_mor;
      simpl; rewrite transportf_total2;
      simpl; rewrite transportf_const;
      simpl.
    - use id_left.
    - use id_right.
    - use assoc.
  Qed.

  Definition total_category_of_models_disp_cat : disp_cat module_signature_cat
    := total_category_of_models_disp_cat_data ,, total_category_of_models_disp_cat_axioms.

  Definition total_category_of_models : category
    := total_category total_category_of_models_disp_cat.
End TotalCategoriesOfModels.

(**
   4. Modularity

    A pushout of representable signatures induces a pushout of initial models in total_category_of_models.
 *)

Section Modularity.
  Context {C : monoidal_cat}.
  Context {Σ Σ₁ Σ₂ : @module_signature_cat C}.

  Context {h₁ : Σ --> Σ₁} {h₂ : Σ --> Σ₂}.

  Context (H_pushout : Pushout h₁ h₂).
  Let Σ₁₂ := PushoutObject H_pushout.

  Context (HΣ   : is_representable Σ  ).
  Context (HΣ₁  : is_representable Σ₁ ).
  Context (HΣ₂  : is_representable Σ₂ ).

  Context (HΣ₁₂ : is_representable Σ₁₂).


  (*                                modularity_morphism₁
                        (Σ, M) ---------------------------> (Σ₁, M₁)
                           |                                     |
                           |                                     |
                           |                                     |
                           |                                     |
     modularity_morphism₂  |                                     |  modularity_morphism_in₁
                           |                                     |
                           |                                     |
                           |                                     |
                           |                               ⌜     |
                           |                                     |
                           v                                     v
                        (Σ₂, M₂) -------------------------> (Σ₁₂, M₁₂)
                                  modularity_morphism_in₂
    *)

  Definition modularity_morphism₁
    : total_category_of_models⟦
      (Σ,, InitialObject HΣ) ,
      (Σ₁,, InitialObject HΣ₁)
    ⟧.
  Proof.
    exists h₁; use InitialArrow.
  Defined.

  Definition modularity_morphism₂
    : total_category_of_models⟦
      (Σ,, InitialObject HΣ) ,
      (Σ₂,, InitialObject HΣ₂)
    ⟧.
  Proof.
    exists h₂; use InitialArrow.
  Defined.

  Definition modularity_morphism_in₁
    : total_category_of_models⟦
      (Σ₁,, InitialObject HΣ₁) ,
      (Σ₁₂,, InitialObject HΣ₁₂)
    ⟧.
  Proof.
    exists (PushoutIn1 _); use InitialArrow.
  Defined.

  Definition modularity_morphism_in₂
    : total_category_of_models⟦
      (Σ₂,, InitialObject HΣ₂) ,
      (Σ₁₂,, InitialObject HΣ₁₂)
    ⟧.
  Proof.
    exists (PushoutIn2 _); use InitialArrow.
  Defined.

  Lemma modularity_commutes
    : modularity_morphism₁ · modularity_morphism_in₁
    = modularity_morphism₂ · modularity_morphism_in₂.
  Proof.
    use invmap; [|use total2_paths_equiv|]; use tpair.
    - apply (PushoutSqrCommutes H_pushout).
    - use InitialArrowEq.
  Qed.

  Section ModularityPushoutInducedMorphism.
    Context (Σ' : @module_signature_cat C).
    Context (Rr : models_of_module_signatures_cat Σ').

    Context (f : total_category_of_models⟦(Σ₁,,InitialObject HΣ₁), (Σ',,Rr)⟧).
    Context (g : total_category_of_models⟦(Σ₂,,InitialObject HΣ₂), (Σ',,Rr)⟧).

    Context (H : modularity_morphism₁ · f = modularity_morphism₂ · g).

    Definition modularity_induced_morphism
      : total_category_of_models ⟦ (Σ₁₂,, InitialObject HΣ₁₂), (Σ',,Rr) ⟧
      := PushoutArrow H_pushout _ (pr1 f) (pr1 g) (maponpaths pr1 H) ,,
        InitialArrow HΣ₁₂ _.

    Lemma modularity_morphism_commutes1
      : modularity_morphism_in₁ · modularity_induced_morphism = f.
    Proof.
      use invmap; [|use total2_paths_equiv|]; use tpair.
      - use (PushoutArrow_PushoutIn1 H_pushout).
      - use InitialArrowEq.
    Qed.

    Lemma modularity_morphism_commutes2
      : modularity_morphism_in₂ · modularity_induced_morphism = g.
    Proof.
      use invmap; [|use total2_paths_equiv|]; use tpair.
      - use (PushoutArrow_PushoutIn2 H_pushout).
      - use InitialArrowEq.
    Qed.

    Let triplet
      : ∑(u : total_category_of_models⟦(Σ₁₂,, InitialObject HΣ₁₂), (Σ',,Rr)⟧),
        modularity_morphism_in₁ · u = f
        × modularity_morphism_in₂ · u = g
      := (modularity_induced_morphism ,,
          modularity_morphism_commutes1 ,,
          modularity_morphism_commutes2).

    Context (triplet'
      : ∑(u : total_category_of_models⟦(Σ₁₂,, InitialObject HΣ₁₂), (Σ',,Rr)⟧),
        modularity_morphism_in₁ · u = f
        × modularity_morphism_in₂ · u = g).

    Let u : total_category_of_models⟦(Σ₁₂,, InitialObject HΣ₁₂), (Σ',,Rr)⟧
      := pr1 triplet'.

    Let H' : modularity_morphism_in₁ · u = f
      := pr12 triplet'.

    Let H'' : modularity_morphism_in₂ · u = g
      := pr22 triplet'.

    Lemma modularity_induced_morphism_unique
      : u = modularity_induced_morphism.
    Proof.
      use invmap; [|use total2_paths_equiv|].
      use tpair.
      2: {use subtypePath.
          { intro; use homset_property. }
          simpl; rewrite transportf_total2;
            simpl; rewrite transportf_const;
            simpl; simpl in u.
          use (maponpaths pr1 (InitialArrowUnique HΣ₁₂ (pr1 Rr ,, _) (pr12 u ,, _))).
          simpl; etrans; [use (pr22 u)|].
          refine (maponpaths (λ x, _ (pr1 x · _)) _).
          exact (
              maponpaths (λ x, pr1 x (pr1 Rr))
                (PushoutArrowUnique _ _ _ _ _
                   (isPushout_Pushout H_pushout) _ _ _
                   (maponpaths pr1 H) _
                   (maponpaths pr1 H')
                   (maponpaths pr1 H'')
                )
            ).
      }
      use (PushoutArrowUnique _ _ _ _ _ (isPushout_Pushout H_pushout)).
      + use (maponpaths pr1 H').
      + use (maponpaths pr1 H'').
    Qed.

    Lemma modularity_pushout_uniqueness : triplet' = triplet.
    Proof.
      use subtypePath; [intro; use isapropdirprod|].
      + use (homset_property total_category_of_models _ _ _ f).
      + use (homset_property total_category_of_models _ _ _ g).
      + use modularity_induced_morphism_unique.
    Qed.

  End ModularityPushoutInducedMorphism.

  Definition modularity_is_pushout
    : isPushout
      modularity_morphism₁ modularity_morphism₂
      modularity_morphism_in₁ modularity_morphism_in₂
      modularity_commutes
    := make_isPushout _ _ _ _ modularity_commutes
      (λ Σ' f g H, _ ,, modularity_pushout_uniqueness _ _ _ _ H).

  Definition modularity
    : Pushout modularity_morphism₁ modularity_morphism₂
    := (make_Pushout _ _ _ _ _ _ modularity_is_pushout).
End Modularity.
