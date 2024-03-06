(**********************************************************************

 Enriched adjunctions

 In this file, we define the notion of enriched adjunctions. To do so,
 we first define the notion of an enrichment of an adjunction, which
 is a pair of an enrichment for both functors and for the unit and
 counit. An enriched adjunction is a pair of an adjunction together
 with an enrichment.

 Context
 1. Enrichments of adjunctions
 2. Enriched adjunctions
 3. Isos between the enriched homs

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Enrichments of adjunctions
 *)
Definition adjunction_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (L : adjunction C₁ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (EL : functor_enrichment (left_adjoint L) E₁ E₂)
       (ER : functor_enrichment (right_adjoint L) E₂ E₁),
     (nat_trans_enrichment
        (adjunit L)
        (functor_id_enrichment E₁)
        (functor_comp_enrichment EL ER))
     ×
     (nat_trans_enrichment
        (adjcounit L)
        (functor_comp_enrichment ER EL))
     (functor_id_enrichment E₂).

Definition make_adjunction_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (L : adjunction C₁ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (EL : functor_enrichment (left_adjoint L) E₁ E₂)
           (ER : functor_enrichment (right_adjoint L) E₂ E₁)
           (Eη : nat_trans_enrichment
                   (adjunit L)
                   (functor_id_enrichment E₁)
                   (functor_comp_enrichment EL ER))
           (Eε : nat_trans_enrichment
                   (adjcounit L)
                   (functor_comp_enrichment ER EL)
                   (functor_id_enrichment E₂))
  : adjunction_enrichment L E₁ E₂
  := EL ,, ER ,, Eη ,, Eε.

Section Accessors.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {L : adjunction C₁ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (EL : adjunction_enrichment L E₁ E₂).

  Definition left_adjoint_enrichment
    : functor_enrichment (left_adjoint L) E₁ E₂
    := pr1 EL.

  Definition right_adjoint_enrichment
    : functor_enrichment (right_adjoint L) E₂ E₁
    := pr12 EL.

  Definition adjoint_unit_enrichment
    : nat_trans_enrichment
        (adjunit L)
        (functor_id_enrichment E₁)
        (functor_comp_enrichment
           left_adjoint_enrichment
           right_adjoint_enrichment)
    := pr122 EL.

  Definition adjoint_counit_enrichment
    : nat_trans_enrichment
        (adjcounit L)
        (functor_comp_enrichment
           right_adjoint_enrichment
           left_adjoint_enrichment)
        (functor_id_enrichment E₂)
    := pr222 EL.
End Accessors.

(**
 2. Enriched adjunctions
 *)
Definition enriched_adjunction
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (L : adjunction C₁ C₂), adjunction_enrichment L E₁ E₂.

#[reversible=no] Coercion enriched_adjunction_to_adjunction
         {V : monoidal_cat}
         {C₁ C₂ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         (L : enriched_adjunction E₁ E₂)
  : adjunction C₁ C₂
  := pr1 L.

#[reversible=no] Coercion enriched_adjunction_to_enrichment
         {V : monoidal_cat}
         {C₁ C₂ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         (L : enriched_adjunction E₁ E₂)
  : adjunction_enrichment L E₁ E₂
  := pr2 L.

(**
 3. Isos between the enriched homs
 *)
Section HomEquiv.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {A : adjunction C₁ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (EA : adjunction_enrichment A E₁ E₂).

  Let L : C₁ ⟶ C₂ := left_adjoint A.
  Let EL : functor_enrichment L E₁ E₂
    := left_adjoint_enrichment EA.

  Let R : C₂ ⟶ C₁ := right_adjoint A.
  Let ER : functor_enrichment R E₂ E₁
    := right_adjoint_enrichment EA.

  Let η : functor_identity _ ⟹ L ∙ R := adjunit A.
  Let Eη : nat_trans_enrichment
             η
             (functor_id_enrichment _)
             (functor_comp_enrichment EL ER)
    := adjoint_unit_enrichment EA.

  Let ε : R ∙ L ⟹ functor_identity _ := adjcounit A.
  Let Eε : nat_trans_enrichment
             ε
             (functor_comp_enrichment ER EL)
             (functor_id_enrichment _)
    := adjoint_counit_enrichment EA.

  Definition adjunction_enrichment_left_hom
             (x : C₁)
             (y : C₂)
    : E₂ ⦃ L x , y ⦄ --> E₁ ⦃ x , R y ⦄
    := ER (L x) y · precomp_arr E₁ (R y) (η x).

  Definition adjunction_enrichment_right_hom
             (x : C₁)
             (y : C₂)
    : E₁ ⦃ x , R y ⦄ --> E₂ ⦃ L x , y ⦄
    := EL x (R y) · postcomp_arr E₂ (L x) (ε y).

  Proposition adjunction_enrichment_hom_is_inverse
              (x : C₁)
              (y : C₂)
    : is_inverse_in_precat
        (adjunction_enrichment_left_hom x y)
        (adjunction_enrichment_right_hom x y).
  Proof.
    split ; unfold adjunction_enrichment_left_hom, adjunction_enrichment_right_hom.
    - rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_precomp_arr.
        rewrite !assoc'.
        apply maponpaths.
        apply idpath.
      }
      rewrite precomp_postcomp_arr.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (!(nat_trans_enrichment_to_comp Eε (L x) y)).
      }
      cbn.
      rewrite id_left.
      rewrite <- precomp_arr_comp.
      refine (_ @ precomp_arr_id _ _ _).
      apply maponpaths.
      exact (triangle_1_statement_from_adjunction A x).
    - rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_postcomp_arr.
        rewrite !assoc'.
        apply maponpaths.
        apply idpath.
      }
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_enrichment_to_comp Eη x (R y)).
      }
      cbn.
      rewrite id_left.
      rewrite <- postcomp_arr_comp.
      refine (_ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      exact (triangle_2_statement_from_adjunction A y).
  Qed.

  Definition adjunction_enrichment_hom_iso
             (x : C₁)
             (y : C₂)
    : z_iso (E₂ ⦃ L x , y ⦄) (E₁ ⦃ x , R y ⦄).
  Proof.
    use make_z_iso.
    - exact (adjunction_enrichment_left_hom x y).
    - exact (adjunction_enrichment_right_hom x y).
    - exact (adjunction_enrichment_hom_is_inverse x y).
  Qed.
End HomEquiv.
