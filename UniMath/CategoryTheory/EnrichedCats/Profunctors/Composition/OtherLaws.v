(*****************************************************************************************

 Other laws for enriched profunctors

 In this file we establish some miscellaneous related about enriched profunctors.

 Contents
 1. The interchange law
 2. Cylinder laws for the left unitor
 3. Cylinder laws for the right unitor
 4. Cylinder laws for the associator
 5. Composition and whiskering
 6. Saturation of the Verity double bicategory of enriched profunctors

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Invertible.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Coend.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.CompositionProf.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.SquareComp.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Unitors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Associators.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Whiskering.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. The interchange law *)
Proposition enriched_profunctor_interchange
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₉ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {E₇ : enrichment C₇ V}
            {E₈ : enrichment C₈ V}
            {E₉ : enrichment C₉ V}
            {P₁ : E₁ ↛e E₂}
            {P₂ : E₂ ↛e E₃}
            {Q₁ : E₄ ↛e E₅}
            {Q₂ : E₅ ↛e E₆}
            {R₁ : E₇ ↛e E₈}
            {R₂ : E₈ ↛e E₉}
            {F₁ : C₁ ⟶ C₄}
            {EF₁ : functor_enrichment F₁ E₁ E₄}
            {F₂ : C₄ ⟶ C₇}
            {EF₂ : functor_enrichment F₂ E₄ E₇}
            {G₁ : C₂ ⟶ C₅}
            {EG₁ : functor_enrichment G₁ E₂ E₅}
            {G₂ : C₅ ⟶ C₈}
            {EG₂ : functor_enrichment G₂ E₅ E₈}
            {H₁ : C₃ ⟶ C₆}
            {EH₁ : functor_enrichment H₁ E₃ E₆}
            {H₂ : C₆ ⟶ C₉}
            {EH₂ : functor_enrichment H₂ E₆ E₉}
            (τ₁ : enriched_profunctor_square EF₁ EG₁ P₁ Q₁)
            (τ₂ : enriched_profunctor_square EG₁ EH₁ P₂ Q₂)
            (θ₁ : enriched_profunctor_square EF₂ EG₂ Q₁ R₁)
            (θ₂ : enriched_profunctor_square EG₂ EH₂ Q₂ R₂)
  : comp_h_enriched_profunctor_square
      (comp_v_enriched_profunctor_square τ₁ τ₂)
      (comp_v_enriched_profunctor_square θ₁ θ₂)
    =
    comp_v_enriched_profunctor_square
      (comp_h_enriched_profunctor_square τ₁ θ₁)
      (comp_h_enriched_profunctor_square τ₂ θ₂).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros y.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply (comp_v_enriched_profunctor_square_mor_comm θ₁ θ₂).
  }
  refine (!_).
  rewrite !assoc.
  etrans.
  {
    apply (comp_v_enriched_profunctor_square_mor_comm
             (comp_h_enriched_profunctor_square τ₁ θ₁)
             (comp_h_enriched_profunctor_square τ₂ θ₂)).
  }
  cbn.
  rewrite <- tensor_comp_mor.
  apply idpath.
Qed.

(** * 2. Cylinder laws for the left unitor *)
Proposition dwhisker_linvunitor_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            (τ : enriched_profunctor_square EF EG P Q)
            (H₁ : nat_trans_enrichment
                    (nat_trans_id _)
                    EG
                    (functor_comp_enrichment (functor_id_enrichment _) EG))
            (H₂ : nat_trans_enrichment
                    (nat_trans_id _)
                    EF
                    (functor_comp_enrichment (functor_id_enrichment _) EF))
  : dwhisker_enriched_profunctor_square
      H₁
      (comp_h_enriched_profunctor_square (id_h_enriched_profunctor_square P) τ)
    =
    uwhisker_enriched_profunctor_square H₂ τ.
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite id_left.
  rewrite !assoc'.
  rewrite !enriched_from_arr_id.
  rewrite lmap_e_id, rmap_e_id.
  apply idpath.
Qed.

Proposition lwhisker_lunitor_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            (τ : enriched_profunctor_square EF EG P Q)
  : lwhisker_enriched_profunctor_square (lunitor_enriched_profunctor P) τ
    =
    rwhisker_enriched_profunctor_square
      (lunitor_enriched_profunctor Q)
      (comp_v_enriched_profunctor_square
         (id_v_enriched_profunctor_square EF) τ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros y.
  rewrite !assoc.
  rewrite lunitor_enriched_profunctor_mor_comm.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply (lunitor_enriched_profunctor_mor_comm Q).
  }
  cbn.
  rewrite <- (enriched_profunctor_transformation_rmap_e τ).
  cbn.
  rewrite !assoc.
  rewrite <- tensor_split.
  apply idpath.
Qed.

(** * 3. Cylinder laws for the right unitor *)
Proposition dwhisker_rinvunitor_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            (τ : enriched_profunctor_square EF EG P Q)
            (H₁ : nat_trans_enrichment
                    (nat_trans_id _)
                    EG
                    (functor_comp_enrichment EG (functor_id_enrichment _)))
            (H₂ : nat_trans_enrichment
                    (nat_trans_id _)
                    EF
                    (functor_comp_enrichment EF (functor_id_enrichment _)))
  : dwhisker_enriched_profunctor_square
      H₁
      (comp_h_enriched_profunctor_square
         τ
         (id_h_enriched_profunctor_square Q))
    =
    uwhisker_enriched_profunctor_square H₂ τ.
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite id_right.
  rewrite !assoc'.
  rewrite !enriched_from_arr_id.
  rewrite lmap_e_id, rmap_e_id.
  apply idpath.
Qed.

Proposition lwhisker_runitor_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            (τ : enriched_profunctor_square EF EG P Q)
  : lwhisker_enriched_profunctor_square (runitor_enriched_profunctor P) τ
    =
    rwhisker_enriched_profunctor_square
      (runitor_enriched_profunctor Q)
      (comp_v_enriched_profunctor_square
         τ
         (id_v_enriched_profunctor_square EG)).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros y.
  rewrite !assoc.
  rewrite runitor_enriched_profunctor_mor_comm.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply (runitor_enriched_profunctor_mor_comm Q).
  }
  cbn.
  rewrite <- (enriched_profunctor_transformation_lmap_e τ).
  cbn.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite <- tensor_split.
  apply idpath.
Qed.

(** * 4. Cylinder laws for the associator *)
Proposition dwhisker_rassociator_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {E₇ : enrichment C₇ V}
            {E₈ : enrichment C₈ V}
            {F₁ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {F₂ : C₂ ⟶ C₃}
            {EF₂ : functor_enrichment F₂ E₂ E₃}
            {F₃ : C₃ ⟶ C₄}
            {EF₃ : functor_enrichment F₃ E₃ E₄}
            {G₁ : C₅ ⟶ C₆}
            {EG₁ : functor_enrichment G₁ E₅ E₆}
            {G₂ : C₆ ⟶ C₇}
            {EG₂ : functor_enrichment G₂ E₆ E₇}
            {G₃ : C₇ ⟶ C₈}
            {EG₃ : functor_enrichment G₃ E₇ E₈}
            {P₁ : E₁ ↛e E₅}
            {P₂ : E₂ ↛e E₆}
            {P₃ : E₃ ↛e E₇}
            {P₄ : E₄ ↛e E₈}
            (τ₁ : enriched_profunctor_square EF₁ EG₁ P₁ P₂)
            (τ₂ : enriched_profunctor_square EF₂ EG₂ P₂ P₃)
            (τ₃ : enriched_profunctor_square EF₃ EG₃ P₃ P₄)
            (H₁ : nat_trans_enrichment
                    (nat_trans_id _)
                    (functor_comp_enrichment
                       (functor_comp_enrichment EG₁ EG₂)
                       EG₃)
                    (functor_comp_enrichment
                       EG₁
                       (functor_comp_enrichment EG₂ EG₃)))
            (H₂ : nat_trans_enrichment
                    (nat_trans_id _)
                    (functor_comp_enrichment
                       (functor_comp_enrichment EF₁ EF₂)
                       EF₃)
                    (functor_comp_enrichment
                       EF₁
                       (functor_comp_enrichment EF₂ EF₃)))
  : dwhisker_enriched_profunctor_square
      H₁
      (comp_h_enriched_profunctor_square τ₁ (comp_h_enriched_profunctor_square τ₂ τ₃))
    =
    uwhisker_enriched_profunctor_square
      H₂
      (comp_h_enriched_profunctor_square
         (comp_h_enriched_profunctor_square τ₁ τ₂)
         τ₃).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  rewrite !enriched_from_arr_id.
  rewrite lmap_e_id, rmap_e_id.
  apply idpath.
Qed.

Proposition lwhisker_lassociator_enriched_profunctor
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {E₇ : enrichment C₇ V}
            {E₈ : enrichment C₈ V}
            {F₁ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {F₂ : C₃ ⟶ C₄}
            {EF₂ : functor_enrichment F₂ E₃ E₄}
            {F₃ : C₅ ⟶ C₆}
            {EF₃ : functor_enrichment F₃ E₅ E₆}
            {F₄ : C₇ ⟶ C₈}
            {EF₄ : functor_enrichment F₄ E₇ E₈}
            {P₁ : E₁ ↛e E₃}
            {P₂ : E₃ ↛e E₅}
            {P₃ : E₅ ↛e E₇}
            {Q₁ : E₂ ↛e E₄}
            {Q₂ : E₄ ↛e E₆}
            {Q₃ : E₆ ↛e E₈}
            (τ₁ : enriched_profunctor_square EF₁ EF₂ P₁ Q₁)
            (τ₂ : enriched_profunctor_square EF₂ EF₃ P₂ Q₂)
            (τ₃ : enriched_profunctor_square EF₃ EF₄ P₃ Q₃)
  : lwhisker_enriched_profunctor_square
      (lassociator_enriched_profunctor P₁ P₂ P₃)
      (comp_v_enriched_profunctor_square
         (comp_v_enriched_profunctor_square τ₁ τ₂)
         τ₃)
    =
    rwhisker_enriched_profunctor_square
      (lassociator_enriched_profunctor Q₁ Q₂ Q₃)
      (comp_v_enriched_profunctor_square
         τ₁
         (comp_v_enriched_profunctor_square τ₂ τ₃)).
Proof.
  use eq_enriched_profunctor_transformation ; intros x₁ x₂ ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros x₃.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  use is_inj_internal_transpose.
  use from_comp_enriched_profunctor_eq.
  intros x₄.
  use internal_funext.
  intros v h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear v h.
  unfold internal_transpose.
  rewrite !internal_beta.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    do 2 apply maponpaths_2.
    apply maponpaths.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply (lassociator_enriched_profunctor_data_comm Q₁ Q₂ Q₃).
  }
  etrans.
  {
    rewrite tensor_comp_l_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply (lassociator_enriched_profunctor_mor_comm Q₁ Q₂ Q₃).
  }
  cbn.
  etrans.
  {
    apply maponpaths.
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
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
    apply maponpaths_2.
    rewrite <- tensor_comp_id_r.
    apply (lassociator_enriched_profunctor_mor_comm P₁ P₂ P₃).
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    rewrite !assoc'.
    do 2 apply maponpaths.
    apply (comp_v_enriched_profunctor_square_mor_comm
             (comp_v_enriched_profunctor_square τ₁ τ₂)
             τ₃).
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite tensor_comp_r_id_r.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_rassociator.
  apply idpath.
Qed.

(** * 5. Composition and whiskering *)
Proposition enriched_profunctor_square_comp_cylinder_left
            {V : benabou_cosmos}
            {C₁ : category}
            {E₁ : enrichment C₁ V}
            {C₂ : category}
            {E₂ : enrichment C₂ V}
            {C₃ : category}
            {E₃ : enrichment C₃ V}
            {C₄ : category}
            {E₄ : enrichment C₄ V}
            {C₅ : category}
            {E₅ : enrichment C₅ V}
            {C₆ : category}
            {E₆ : enrichment C₆ V}
            {F₁ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {F₂ : C₃ ⟶ C₄}
            {EF₂ : functor_enrichment F₂ E₃ E₄}
            {F₃ : C₅ ⟶ C₆}
            {EF₃ : functor_enrichment F₃ E₅ E₆}
            {P₁ P₂ : enriched_profunctor E₁ E₃}
            {P₁' P₂' : enriched_profunctor E₃ E₅}
            {Q₁ Q₂ : enriched_profunctor E₂ E₄}
            {Q₁' Q₂' : enriched_profunctor E₄ E₆}
            (τ₁ : enriched_profunctor_transformation P₁ P₂)
            (τ₂ : enriched_profunctor_transformation P₁' P₂')
            (θ₁ : enriched_profunctor_transformation Q₁ Q₂)
            (θ₂ : enriched_profunctor_transformation Q₁' Q₂')
            (s₁ : enriched_profunctor_square EF₁ EF₂ P₁ Q₁)
            (s₁' : enriched_profunctor_square EF₁ EF₂ P₂ Q₂)
            (s₂ : enriched_profunctor_square EF₂ EF₃ P₁' Q₁')
            (s₂' : enriched_profunctor_square EF₂ EF₃ P₂' Q₂')
            (p : lwhisker_enriched_profunctor_square τ₁ s₁'
                 =
                 rwhisker_enriched_profunctor_square θ₁ s₁)
            (q : lwhisker_enriched_profunctor_square τ₂ s₂'
                 =
                 rwhisker_enriched_profunctor_square θ₂ s₂)
  : lwhisker_enriched_profunctor_square
      (enriched_profunctor_comp_transformation
         (rwhisker_enriched_profunctor τ₁ P₁')
         (lwhisker_enriched_profunctor P₂ τ₂))
      (comp_v_enriched_profunctor_square s₁' s₂')
    =
    rwhisker_enriched_profunctor_square
      (enriched_profunctor_comp_transformation
         (rwhisker_enriched_profunctor θ₁ Q₁')
         (lwhisker_enriched_profunctor Q₂ θ₂))
      (comp_v_enriched_profunctor_square s₁ s₂).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro y.
  etrans.
  {
    rewrite !assoc.
    do 2 apply maponpaths_2.
    apply rwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    do 2 apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply (rwhisker_enriched_profunctor_mor_comm θ₁).
  }
  etrans.
  {
    rewrite !assoc'.
    do 2 apply maponpaths.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite <- !tensor_comp_mor.
  rewrite !id_left, !id_right.
  pose (from_eq_enriched_profunctor_transformation p y x) as p'.
  pose (from_eq_enriched_profunctor_transformation q z y) as q'.
  cbn in p', q'.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    exact p'.
  }
  apply maponpaths.
  exact q'.
Qed.

Proposition enriched_profunctor_square_comp_cylinder_down
            {V : benabou_cosmos}
            {C₁ : category}
            {E₁ : enrichment C₁ V}
            {C₂ : category}
            {E₂ : enrichment C₂ V}
            {C₃ : category}
            {E₃ : enrichment C₃ V}
            {C₄ : category}
            {E₄ : enrichment C₄ V}
            {C₅ : category}
            {E₅ : enrichment C₅ V}
            {C₆ : category}
            {E₆ : enrichment C₆ V}
            {F₁ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {F₂ : C₁ ⟶ C₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {F₃ : C₂ ⟶ C₃}
            {EF₃ : functor_enrichment F₃ E₂ E₃}
            {F₄ : C₂ ⟶ C₃}
            {EF₄ : functor_enrichment F₄ E₂ E₃}
            {F₅ : C₄ ⟶ C₅}
            {EF₅ : functor_enrichment F₅ E₄ E₅}
            {F₆ : C₄ ⟶ C₅}
            {EF₆ : functor_enrichment F₆ E₄ E₅}
            {F₇ F₈ : C₅ ⟶ C₆}
            {EF₇ : functor_enrichment F₇ E₅ E₆}
            {EF₈ : functor_enrichment F₈ E₅ E₆}
            {P₁ : enriched_profunctor E₁ E₄}
            {P₂ : enriched_profunctor E₂ E₅}
            {P₃ : enriched_profunctor E₃ E₆}
            {τ₁ : F₂ ⟹ F₁}
            {Eτ₁ : nat_trans_enrichment τ₁ EF₂ EF₁}
            {τ₂ : F₄ ⟹ F₃}
            {Eτ₂ : nat_trans_enrichment τ₂ EF₄ EF₃}
            {θ₁ : F₆ ⟹ F₅}
            {Eθ₁ : nat_trans_enrichment θ₁ EF₆ EF₅}
            {θ₂ : F₈ ⟹ pr1 F₇}
            {Eθ₂ : nat_trans_enrichment θ₂ EF₈ EF₇}
            (s₁ : enriched_profunctor_square EF₁ EF₅ P₁ P₂)
            (s₁' : enriched_profunctor_square EF₂ EF₆ P₁ P₂)
            (s₂ : enriched_profunctor_square EF₃ EF₇ P₂ P₃)
            (s₂' : enriched_profunctor_square EF₄ EF₈ P₂ P₃)
            (p : dwhisker_enriched_profunctor_square Eθ₁ s₁
                 =
                 uwhisker_enriched_profunctor_square Eτ₁ s₁')
            (q : dwhisker_enriched_profunctor_square Eθ₂ s₂
                 =
                 uwhisker_enriched_profunctor_square Eτ₂ s₂')
            (H₁ : nat_trans_enrichment
                    (nat_trans_comp
                       (F₆ ∙ F₈) (F₆ ∙ F₇) (F₅ ∙ F₇)
                       (pre_whisker F₆ θ₂)
                       (post_whisker θ₁ F₇))
                    (functor_comp_enrichment EF₆ EF₈)
                    (functor_comp_enrichment EF₅ EF₇))
            (H₂ : nat_trans_enrichment
                    (nat_trans_comp
                       (F₂ ∙ F₄) (F₂ ∙ F₃) (F₁ ∙ F₃)
                       (pre_whisker F₂ τ₂)
                       (post_whisker τ₁ F₃))
                    (functor_comp_enrichment EF₂ EF₄)
                    (functor_comp_enrichment EF₁ EF₃))
  : dwhisker_enriched_profunctor_square
      H₁
      (comp_h_enriched_profunctor_square s₁ s₂)
    =
    uwhisker_enriched_profunctor_square
      H₂
      (comp_h_enriched_profunctor_square s₁' s₂').
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  etrans.
  {
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite enriched_from_arr_comp.
    rewrite !tensor_comp_id_r.
    rewrite !assoc'.
    rewrite lmap_e_comp'.
    rewrite  !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_comp_id_r.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_comp_id_r.
      rewrite sym_mon_braiding_linvunitor.
      apply idpath.
    }
    rewrite !assoc'.
    rewrite tensor_lassociator.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite <- mon_inv_triangle.
    apply idpath.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_l.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply tensor_split'.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      rewrite <- tensor_split.
      apply tensor_split'.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_id_l.
    apply maponpaths.
    rewrite (functor_enrichment_from_arr EF₇).
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_comp_r_id_l.
    rewrite !assoc'.
    apply maponpaths.
    exact (enriched_profunctor_square_lmap_e s₂ (F₅ z) (F₆ z) (F₁ x)).
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    apply idpath.
  }
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_linvunitor.
    rewrite !assoc'.
    do 3 apply maponpaths.
    rewrite !assoc.
    exact (from_eq_enriched_profunctor_transformation q (F₆ z) (F₁ x)).
  }
  cbn.
  etrans.
  {
    rewrite !assoc.
    do 4 apply maponpaths_2.
    exact (from_eq_enriched_profunctor_transformation p z x).
  }
  cbn.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    do 3 apply maponpaths_2.
    exact (!(enriched_profunctor_square_rmap_e s₂' (F₆ z) (F₂ x) (F₁ x))).
  }
  etrans.
  {
    rewrite !assoc.
    do 4 apply maponpaths_2.
    rewrite (tensor_split _ (s₂' _ _)) ; cbn.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc.
    rewrite <- tensor_linvunitor.
    apply idpath.
  }
  rewrite !assoc'.
  do 2 apply maponpaths.
  rewrite enriched_from_arr_comp.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite <- tensor_id_id.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_lassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    exact (!(rmap_e_comp P₃ (F₈(F₆ z)) (F₄(F₂ x)) (F₄(F₁ x)) (F₃(F₁ x)))).
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite <- !tensor_comp_id_r.
  apply maponpaths_2.
  rewrite (functor_enrichment_from_arr EF₃).
  rewrite tensor_comp_r_id_l.
  rewrite !assoc.
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  rewrite <- tensor_rinvunitor.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  refine (_ @ !(Eτ₂ _ _)).
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split.
  apply idpath.
Qed.

(** * 6. Saturation of the Verity double bicategory of enriched profunctors *)
Proposition profunctor_square_to_enriched_nat_trans_left_point
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F G : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            {τ : F ⟹ G}
            (Hτ : nat_trans_enrichment τ EF EG)
            (x : C₁)
  : square_to_enriched_nat_trans_data
      (uwhisker_enriched_profunctor_square
         Hτ
         (id_v_enriched_profunctor_square _)) x
    =
    τ x.
Proof.
  cbn.
  refine (_ @ enriched_to_from_arr E₂ _).
  apply maponpaths.
  rewrite !assoc.
  rewrite functor_enrichment_id.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite <- enrichment_id_right.
    apply idpath.
  }
  rewrite tensor_runitor.
  rewrite !assoc.
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  rewrite mon_rinvunitor_runitor.
  apply id_left.
Qed.

Proposition profunctor_square_to_enriched_nat_trans_left_right_point
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F G : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (τ : enriched_profunctor_square
                   EF EG
                   (identity_enriched_profunctor E₁)
                   (identity_enriched_profunctor E₂))
            (x y : C₁)
  : EG x y
    · mon_linvunitor _
    · enriched_from_arr E₂ (square_to_enriched_nat_trans_data τ y) #⊗ identity _
    · enriched_comp E₂ (G x) (G y) (F y)
    =
    τ x y.
Proof.
  cbn.
  rewrite enriched_from_to_arr.
  rewrite tensor_linvunitor.
  rewrite tensor_comp_id_r.
  rewrite !assoc'.
  pose (enriched_profunctor_square_lmap_e τ y x y) as p.
  cbn in p.
  rewrite !assoc in p.
  rewrite tensor_sym_mon_braiding in p.
  pose (maponpaths (λ z, sym_mon_braiding _ _ _ · z) p) as q.
  cbn in q.
  rewrite !assoc in q.
  rewrite !sym_mon_braiding_inv in q.
  rewrite !id_left in q.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    exact q.
  }
  refine (_ @ id_left _).
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite <- enrichment_id_left.
  apply mon_linvunitor_lunitor.
Qed.
