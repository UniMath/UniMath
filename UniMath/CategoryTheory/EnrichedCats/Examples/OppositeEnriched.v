(*****************************************************************

 The opposite enriched category

 If we look at categories enriched over a symmetric monoidal
 category, then we can form the opposite. In addition, we
 construct the desired enriched functors and natural
 transformations to show that this gives rise to a duality
 involution on the bicategory of enriched categories

 Contents
 1. Enrichment of the opposite
 2. Pseudofunctoriality
 2.1. Opposite of enriched functors
 2.2. Opposite of enriched transformations
 2.3. Opposite of the identity enriched functors
 2.4. Opposite of the composition of enriched functors
 3. Duality involution
 3.1. The unit and the inverse
 3.2. The naturality of the unit
 3.3. Inverse laws
 3.4. The triangle

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Local Open Scope moncat.

Opaque sym_mon_braiding.

Import MonoidalNotations.

Section OppositeEnriched.
  Context (V : sym_monoidal_cat)
          {C : category}
          (E : enrichment C V).

  (**
   1. Enrichment of the opposite
   *)
  Definition op_enrichment_data
    : enrichment_data (C^opp) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, E ⦃ y , x ⦄).
    - exact (λ x, enriched_id E x).
    - exact (λ x y z, sym_mon_braiding V _ _ · enriched_comp E z y x).
    - exact (λ x y f, enriched_from_arr E f).
    - exact (λ x y f, enriched_to_arr E f).
  Defined.

  Definition op_enrichment_laws
    : enrichment_laws op_enrichment_data.
  Proof.
    repeat split.
    - intros x y ; cbn in *.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      rewrite sym_mon_braiding_runitor.
      apply idpath.
    - intros x y ; cbn in *.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite sym_mon_braiding_lunitor.
      apply idpath.
    - intros w x y z ; cbn in *.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply tensor_sym_mon_braiding.
      }
      rewrite !assoc'.
      rewrite enrichment_assoc'.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite sym_mon_tensor_rassociator.
      rewrite !assoc'.
      rewrite mon_lassociator_rassociator.
      rewrite id_right.
      rewrite !assoc.
      rewrite <- sym_mon_hexagon_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        apply id_left.
      }
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    - intros x y f ; cbn in *.
      apply enriched_to_from_arr.
    - intros x y f ; cbn in *.
      apply enriched_from_to_arr.
    - intros x ; cbn in *.
      apply enriched_to_arr_id.
    - intros x y z f g ; cbn in *.
      refine (enriched_to_arr_comp E g f @ _).
      apply maponpaths.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_sym_mon_braiding.
      rewrite sym_mon_braiding_id.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition op_enrichment
    : enrichment (C^opp) V
    := op_enrichment_data ,, op_enrichment_laws.

  Proposition op_enrichment_precomp
              (w : C)
              {x y : C}
              (f : x --> y)
    : precomp_arr op_enrichment w f
      =
      postcomp_arr E w f.
  Proof.
    unfold precomp_arr, postcomp_arr ; cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    }
    rewrite !assoc.
    rewrite sym_mon_braiding_rinvunitor.
    apply idpath.
  Qed.

  Proposition op_enrichment_postcomp
              {x y : C}
              (f : x --> y)
              (z : C)
    : postcomp_arr op_enrichment z f
      =
      precomp_arr E z f.
  Proof.
    unfold precomp_arr, postcomp_arr ; cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    }
    rewrite !assoc.
    rewrite sym_mon_braiding_linvunitor.
    apply idpath.
  Qed.
End OppositeEnriched.

(**
 2. Pseudofunctoriality
 *)

(**
 2.1. Opposite of enriched functors
 *)
Definition functor_op_enrichment
           (V : sym_monoidal_cat)
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : functor_enrichment
      (functor_op F)
      (op_enrichment V E₁)
      (op_enrichment V E₂).
Proof.
  refine ((λ x y, EF y x) ,, _).
  repeat split.
  - abstract
      (cbn ;
       intro x ;
       exact (functor_enrichment_id EF x)).
  - abstract
      (cbn ;
       intros x y z ;
       rewrite !assoc' ;
       rewrite (functor_enrichment_comp EF z y x) ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       rewrite tensor_sym_mon_braiding ;
       apply idpath).
  - abstract
      (cbn ;
       intros x y f ;
       apply functor_enrichment_from_arr).
Defined.

(**
 2.2. Opposite of enriched transformations
 *)
Definition nat_trans_op_enrichment
           (V : sym_monoidal_cat)
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : F ⟹ G)
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {EF : functor_enrichment F E₁ E₂}
           {EG : functor_enrichment G E₁ E₂}
           (Eτ : nat_trans_enrichment τ EF EG)
  : @nat_trans_enrichment
      V
      (C₁^opp) (C₂^opp)
      _ _
      (op_nt τ)
      _
      _
      (functor_op_enrichment V EG)
      (functor_op_enrichment V EF).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite op_enrichment_precomp, op_enrichment_postcomp.
  exact (!(nat_trans_enrichment_to_comp Eτ y x)).
Qed.

(**
 2.3. Opposite of the identity enriched functors
 *)
Definition functor_identity_op_enrichment
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : nat_trans_enrichment
      (functor_identity_op C)
      (functor_id_enrichment (op_enrichment V E))
      (functor_op_enrichment V (functor_id_enrichment E)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left.
  rewrite op_enrichment_precomp, op_enrichment_postcomp.
  rewrite precomp_arr_id, postcomp_arr_id.
  apply idpath.
Qed.

(**
 2.4. Opposite of the composition of enriched functors
 *)
Definition functor_comp_op_enrichment
           (V : sym_monoidal_cat)
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (EF : functor_enrichment F E₁ E₂)
           (EG : functor_enrichment G E₂ E₃)
  : @nat_trans_enrichment
      V
      (C₁^opp) (C₃^opp)
      _ _
      (functor_comp_op F G)
      _
      _
      (functor_comp_enrichment
         (functor_op_enrichment V EF)
         (functor_op_enrichment V EG))
      (functor_op_enrichment
         V
         (functor_comp_enrichment EF EG)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite op_enrichment_precomp, op_enrichment_postcomp.
  rewrite precomp_arr_id, postcomp_arr_id.
  apply idpath.
Qed.

(**
 3. Duality involution
 *)

(**
 3.1. The unit and the inverse
 *)
Definition op_enriched_unit
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : functor_enrichment
      (functor_identity C)
      E
      (op_enrichment V (op_enrichment V E)).
Proof.
  refine ((λ x y, identity _) ,, _).
  repeat split ; cbn.
  - abstract
      (intro x ;
       apply id_right).
  - abstract
      (intros x y z ;
       rewrite id_right ;
       rewrite tensor_id_id ;
       rewrite id_left ;
       rewrite !assoc ;
       rewrite sym_mon_braiding_inv ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (intros x y f ;
       rewrite id_right ;
       apply idpath).
Defined.

Definition op_enriched_unit_inv
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : functor_enrichment
      (functor_identity _)
      (op_enrichment V (op_enrichment V E))
      E.
Proof.
  refine ((λ x y, identity _) ,, _).
  repeat split.
  - abstract
      (intros x ; cbn ;
       rewrite id_right ;
       apply idpath).
  - abstract
      (intros x y z ; cbn  ;
       rewrite !id_right ;
       rewrite tensor_id_id ;
       rewrite !assoc ;
       rewrite sym_mon_braiding_inv ;
       apply idpath).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_right ;
       apply idpath).
Defined.

(**
 3.2. The naturality of the unit
 *)
Definition op_enriched_unit_naturality
           (V : sym_monoidal_cat)
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (op_unit_nat_trans F)
      (functor_comp_enrichment
         (op_enriched_unit V E₁)
         (functor_op_enrichment V (functor_op_enrichment V EF)))
      (functor_comp_enrichment EF (op_enriched_unit V E₂)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left, !id_right.
  rewrite (precomp_arr_id (op_enrichment V (op_enrichment V E₂))).
  rewrite (postcomp_arr_id (op_enrichment V (op_enrichment V E₂))).
  apply idpath.
Qed.

Definition op_enriched_unit_inv_naturality
           (V : sym_monoidal_cat)
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (op_unit_inv_nat_trans F)
      (functor_comp_enrichment (op_enriched_unit_inv V E₁) EF)
      (functor_comp_enrichment
         (functor_op_enrichment V (functor_op_enrichment V EF))
         (op_enriched_unit_inv V E₂)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left, !id_right.
  rewrite precomp_arr_id, postcomp_arr_id.
  apply idpath.
Qed.

(**
 3.3. Inverse laws
 *)
Definition op_enriched_unit_unit_inv
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : nat_trans_enrichment
      (op_unit_unit_inv_nat_trans C)
      (functor_id_enrichment E)
      (functor_comp_enrichment
         (op_enriched_unit V E)
         (op_enriched_unit_inv V E)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left.
  rewrite precomp_arr_id, postcomp_arr_id.
  apply idpath.
Qed.

Definition op_enriched_unit_inv_unit
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : nat_trans_enrichment
      (op_unit_inv_unit_nat_trans C)
      (functor_comp_enrichment
         (op_enriched_unit_inv V E)
         (op_enriched_unit V E))
      (functor_id_enrichment (op_enrichment V (op_enrichment V E))).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left.
  rewrite (precomp_arr_id (op_enrichment V (op_enrichment V E))).
  rewrite (postcomp_arr_id (op_enrichment V (op_enrichment V E))).
  apply idpath.
Qed.

(**
 3.4. The triangle
 *)
Definition op_enriched_triangle
           (V : sym_monoidal_cat)
           {C : category}
           (E : enrichment C V)
  : nat_trans_enrichment
      (λ _, identity _)
      (op_enriched_unit V (op_enrichment V E))
      (functor_op_enrichment V (op_enriched_unit V E)).
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn in *.
  rewrite !id_left.
  rewrite (precomp_arr_id (op_enrichment V (op_enrichment V (op_enrichment V E)))).
  rewrite (postcomp_arr_id (op_enrichment V (op_enrichment V (op_enrichment V E)))).
  apply idpath.
Qed.
