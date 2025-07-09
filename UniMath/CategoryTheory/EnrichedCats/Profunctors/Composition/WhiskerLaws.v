(*****************************************************************************************

 Whiskering laws for enriched profunctors

 In this file we establish laws related to whisker operations for enriched profunctors.
 These laws are necessary to show that we have a Verity double bicategory of enriched
 profunctors. The proofs boil down to boring calculations.

 Contents
 1. Up whiskering and composition
 2. Down whiskering and composition
 3. Up whiskering and identities
 4. Swapping whiskering
 5. Composition of squares and whiskering

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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

(** * 1. Up whiskering and composition *)
Proposition uwhisker_enriched_profunctor_square_comp
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F₁ F₂ F₃ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {EF₃ : functor_enrichment F₃ E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            {τ₁ : F₁ ⟹ F₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EF₁ EF₂)
            {τ₂ : F₂ ⟹ F₃}
            (Hτ₂ : nat_trans_enrichment τ₂ EF₂ EF₃)
            (θ : enriched_profunctor_square EF₁ EG P Q)
  : uwhisker_enriched_profunctor_square (comp_trans_enrichment Hτ₁ Hτ₂) θ
    =
    uwhisker_enriched_profunctor_square Hτ₂ (uwhisker_enriched_profunctor_square Hτ₁ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  do 2 apply maponpaths.
  rewrite enriched_from_arr_comp.
  etrans.
  {
    do 3 apply maponpaths_2.
    rewrite tensor_split.
    rewrite !assoc.
    rewrite <- tensor_linvunitor.
    apply idpath.
  }
  rewrite !tensor_comp_id_r.
  rewrite !assoc'.
  apply maponpaths.
  rewrite rmap_e_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite <- mon_linvunitor_triangle.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite tensor_lassociator.
  rewrite !assoc'.
  apply maponpaths.
  rewrite tensor_id_id.
  rewrite <- tensor_split.
  rewrite <- tensor_split'.
  apply idpath.
Qed.

(** * 2. Down whiskering and composition *)
Proposition dwhisker_enriched_profunctor_square_comp
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G₁ G₂ G₃ : C₃ ⟶ C₄}
            {EG₁ : functor_enrichment G₁ E₃ E₄}
            {EG₂ : functor_enrichment G₂ E₃ E₄}
            {EG₃ : functor_enrichment G₃ E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            {τ₁ : G₁ ⟹ G₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EG₁ EG₂)
            {τ₂ : G₂ ⟹ G₃}
            (Hτ₂ : nat_trans_enrichment τ₂ EG₂ EG₃)
            (θ : enriched_profunctor_square EF EG₃ P Q)
  : dwhisker_enriched_profunctor_square (comp_trans_enrichment Hτ₁ Hτ₂) θ
    =
    dwhisker_enriched_profunctor_square Hτ₁ (dwhisker_enriched_profunctor_square Hτ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  do 2 apply maponpaths.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite lmap_e_lmap_e.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite enriched_from_arr_comp.
  rewrite tensor_comp_id_r.
  apply maponpaths_2.
  etrans.
  {
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    rewrite <- tensor_comp_id_r.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_r.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    rewrite tensor_split'.
    rewrite !assoc.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    rewrite <- tensor_rinvunitor.
    apply idpath.
  }
  rewrite !tensor_comp_id_r.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite <- mon_linvunitor_triangle.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    apply id_right.
  }
  rewrite <- tensor_comp_id_r.
  rewrite sym_mon_braiding_linvunitor.
  apply idpath.
Qed.

(** * 3. Up whiskering and identities *)
Proposition uwhisker_enriched_profunctor_square_id_square
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {F G : C₁ ⟶ C₂}
            {τ : F ⟹ G}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (Hτ : nat_trans_enrichment τ EF EG)
  : uwhisker_enriched_profunctor_square Hτ (id_v_enriched_profunctor_square EF)
    =
    dwhisker_enriched_profunctor_square Hτ (id_v_enriched_profunctor_square EG).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !tensor_linvunitor.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite <- !tensor_split.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  refine (!(id_left _) @ _).
  rewrite <- mon_lunitor_linvunitor.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    exact (!(Hτ z x)).
  }
  rewrite !assoc.
  do 2 apply maponpaths_2.
  refine (_ @ id_right _).
  rewrite <- mon_runitor_rinvunitor.
  rewrite !assoc.
  rewrite sym_mon_braiding_runitor.
  apply idpath.
Qed.

(** * 4. Swapping whiskering *)
Proposition dwhisker_uwhisker_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F₁ F₂ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {τ₁ : F₁ ⟹ F₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EF₁ EF₂)
            {G₁ G₂ : C₃ ⟶ C₄}
            {EG₁ : functor_enrichment G₁ E₃ E₄}
            {EG₂ : functor_enrichment G₂ E₃ E₄}
            {τ₂ : G₁ ⟹ G₂}
            (Hτ₂ : nat_trans_enrichment τ₂ EG₁ EG₂)
            {P : E₁ ↛e E₃}
            {Q : E₂ ↛e E₄}
            (θ : enriched_profunctor_square EF₁ EG₂ P Q)
  : dwhisker_enriched_profunctor_square
      Hτ₂
      (uwhisker_enriched_profunctor_square Hτ₁ θ)
    =
    uwhisker_enriched_profunctor_square
      Hτ₁
      (dwhisker_enriched_profunctor_square Hτ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  do 2 apply maponpaths.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite rmap_e_lmap_e.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    rewrite <- tensor_id_id.
    rewrite <- tensor_lassociator.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite <- tensor_lassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite mon_lassociator_rassociator.
    apply id_left.
  }
  rewrite <- !tensor_comp_id_r.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split.
  etrans.
  {
    rewrite tensor_sym_mon_braiding.
    apply maponpaths.
    rewrite !assoc.
    rewrite sym_mon_braiding_linvunitor.
    apply idpath.
  }
  rewrite !assoc.
  rewrite tensor_rinvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split'.
  rewrite mon_rinvunitor_I_mon_linvunitor_I.
  apply idpath.
Qed.

Proposition lwhisker_uwhisker_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F₁ F₂ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {τ₁ : F₁ ⟹ F₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EF₁ EF₂)
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P₁ P₂ : E₁ ↛e E₃}
            (τ₂ : enriched_profunctor_transformation P₁ P₂)
            {Q : E₂ ↛e E₄}
            (θ : enriched_profunctor_square EF₁ EG P₂ Q)
  : lwhisker_enriched_profunctor_square
      τ₂
      (uwhisker_enriched_profunctor_square Hτ₁ θ)
    =
    uwhisker_enriched_profunctor_square
      Hτ₁
      (lwhisker_enriched_profunctor_square τ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  apply idpath.
Qed.

Proposition rwhisker_uwhisker_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F₁ F₂ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {τ₁ : F₁ ⟹ F₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EF₁ EF₂)
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {P : E₁ ↛e E₃}
            {Q₁ Q₂ : E₂ ↛e E₄}
            (τ₂ : enriched_profunctor_transformation Q₁ Q₂)
            (θ : enriched_profunctor_square EF₁ EG P Q₁)
  : rwhisker_enriched_profunctor_square
      τ₂
      (uwhisker_enriched_profunctor_square Hτ₁ θ)
    =
    uwhisker_enriched_profunctor_square
      Hτ₁
      (rwhisker_enriched_profunctor_square τ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- enriched_profunctor_transformation_rmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split.
  rewrite <- tensor_split'.
  apply idpath.
Qed.

Proposition lwhisker_dwhisker_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G₁ G₂ : C₃ ⟶ C₄}
            {EG₁ : functor_enrichment G₁ E₃ E₄}
            {EG₂ : functor_enrichment G₂ E₃ E₄}
            {τ₁ : G₁ ⟹ G₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EG₁ EG₂)
            {P₁ P₂ : E₁ ↛e E₃}
            (τ₂ : enriched_profunctor_transformation P₁ P₂)
            {Q : E₂ ↛e E₄}
            (θ : enriched_profunctor_square EF EG₂ P₂ Q)
  : lwhisker_enriched_profunctor_square
      τ₂
      (dwhisker_enriched_profunctor_square Hτ₁ θ)
    =
    dwhisker_enriched_profunctor_square
      Hτ₁
      (lwhisker_enriched_profunctor_square τ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  apply idpath.
Qed.

Proposition rwhisker_dwhisker_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G₁ G₂ : C₃ ⟶ C₄}
            {EG₁ : functor_enrichment G₁ E₃ E₄}
            {EG₂ : functor_enrichment G₂ E₃ E₄}
            {τ₁ : G₁ ⟹ G₂}
            (Hτ₁ : nat_trans_enrichment τ₁ EG₁ EG₂)
            {P : E₁ ↛e E₃}
            {Q₁ Q₂ : E₂ ↛e E₄}
            (τ₂ : enriched_profunctor_transformation Q₁ Q₂)
            (θ : enriched_profunctor_square EF EG₂ P Q₁)
  : rwhisker_enriched_profunctor_square
      τ₂
      (dwhisker_enriched_profunctor_square Hτ₁ θ)
    =
    dwhisker_enriched_profunctor_square
      Hτ₁
      (rwhisker_enriched_profunctor_square τ₂ θ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- enriched_profunctor_transformation_lmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split.
  rewrite <- tensor_split'.
  apply idpath.
Qed.

(** * 5. Composition of squares and whiskering *)
Proposition uwhisker_comp_v_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {F₁ F₂ : C₁ ⟶ C₂}
            {EF₁ : functor_enrichment F₁ E₁ E₂}
            {EF₂ : functor_enrichment F₂ E₁ E₂}
            {τ : F₂ ⟹ F₁}
            (Hτ : nat_trans_enrichment τ EF₂ EF₁)
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {H : C₅ ⟶ C₆}
            {EH : functor_enrichment H E₅ E₆}
            {P₁ : E₁ ↛e E₃}
            {P₂ : E₃ ↛e E₅}
            {Q₁ : E₂ ↛e E₄}
            {Q₂ : E₄ ↛e E₆}
            (θ₁ : enriched_profunctor_square EF₂ EG P₁ Q₁)
            (θ₂ : enriched_profunctor_square EG EH P₂ Q₂)
  : uwhisker_enriched_profunctor_square
      Hτ
      (comp_v_enriched_profunctor_square θ₁ θ₂)
    =
    comp_v_enriched_profunctor_square
      (uwhisker_enriched_profunctor_square Hτ θ₁)
      θ₂.
Proof.
  use eq_enriched_profunctor_transformation ; intros z v ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro x ; cbn.
  etrans.
  {
    rewrite !assoc.
    do 5 apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  refine (!_).
  etrans.
  {
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  cbn.
  rewrite !assoc'.
  rewrite tensor_comp_r_id_r.
  rewrite !assoc'.
  apply maponpaths.
  refine (!_).
  etrans.
  {
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
    apply maponpaths.
    apply comp_enriched_profunctor_rmap_comm.
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    unfold comp_enriched_profunctor_rmap_mor.
    apply id_left.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !tensor_comp_id_r.
  apply maponpaths_2.
  rewrite <- mon_linvunitor_triangle.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- tensor_id_id.
  rewrite tensor_rassociator.
  rewrite !assoc.
  rewrite mon_lassociator_rassociator.
  apply id_left.
Qed.

Proposition dwhisker_comp_v_enriched_profunctor_square
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G : C₃ ⟶ C₄}
            {EG : functor_enrichment G E₃ E₄}
            {H₁ H₂ : C₅ ⟶ C₆}
            {EH₁ : functor_enrichment H₁ E₅ E₆}
            {EH₂ : functor_enrichment H₂ E₅ E₆}
            {τ : H₂ ⟹ H₁}
            (Hτ : nat_trans_enrichment τ EH₂ EH₁)
            {P₁ : E₁ ↛e E₃}
            {P₂ : E₃ ↛e E₅}
            {Q₁ : E₂ ↛e E₄}
            {Q₂ : E₄ ↛e E₆}
            (θ₁ : enriched_profunctor_square EF EG P₁ Q₁)
            (θ₂ : enriched_profunctor_square EG EH₁ P₂ Q₂)
  : dwhisker_enriched_profunctor_square
      Hτ
      (comp_v_enriched_profunctor_square θ₁ θ₂)
    =
    comp_v_enriched_profunctor_square
      θ₁
      (dwhisker_enriched_profunctor_square Hτ θ₂).
Proof.
  use eq_enriched_profunctor_transformation ; intros z v ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro x.
  etrans.
  {
    rewrite !assoc.
    do 5 apply maponpaths_2.
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  refine (!_).
  etrans.
  {
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  cbn.
  rewrite !assoc'.
  rewrite tensor_comp_l_id_r.
  rewrite !assoc'.
  apply maponpaths.
  refine (!_).
  etrans.
  {
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
    apply maponpaths.
    apply comp_enriched_profunctor_lmap_comm.
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    unfold comp_enriched_profunctor_lmap_mor.
    apply id_left.
  }
  rewrite !tensor_comp_id_l.
  rewrite !assoc.
  do 2 apply maponpaths_2.
  rewrite <- mon_linvunitor_triangle.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite <- tensor_lassociator.
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
  }
  rewrite !assoc.
  rewrite <- !tensor_comp_id_r.
  rewrite !assoc'.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc.
  rewrite tensor_comp_id_r.
  rewrite !assoc'.
  rewrite tensor_lassociator.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite sym_mon_braiding_linvunitor.
  rewrite mon_inv_triangle.
  apply idpath.
Qed.

Proposition comp_v_enriched_profunctor_square_uwhisker
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ C₆ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            {E₆ : enrichment C₆ V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {G₁ G₂ : C₃ ⟶ C₄}
            {EG₁ : functor_enrichment G₁ E₃ E₄}
            {EG₂ : functor_enrichment G₂ E₃ E₄}
            {τ : G₂ ⟹ G₁}
            (Hτ : nat_trans_enrichment τ EG₂ EG₁)
            {H : C₅ ⟶ C₆}
            {EH : functor_enrichment H E₅ E₆}
            {P₁ : E₁ ↛e E₃}
            {P₂ : E₃ ↛e E₅}
            {Q₁ : E₂ ↛e E₄}
            {Q₂ : E₄ ↛e E₆}
            (θ₁ : enriched_profunctor_square EF EG₁ P₁ Q₁)
            (θ₂ : enriched_profunctor_square EG₂ EH P₂ Q₂)
  : comp_v_enriched_profunctor_square
      θ₁
      (uwhisker_enriched_profunctor_square Hτ θ₂)
    =
    comp_v_enriched_profunctor_square
      (dwhisker_enriched_profunctor_square Hτ θ₁)
      θ₂.
Proof.
  use eq_enriched_profunctor_transformation ; intros z v ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro x.
  etrans.
  {
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  refine (!_).
  etrans.
  {
    apply comp_v_enriched_profunctor_square_mor_comm.
  }
  cbn.
  rewrite !tensor_comp_r_id_r.
  rewrite !tensor_comp_l_id_r.
  rewrite !assoc'.
  apply maponpaths.
  rewrite comp_enriched_profunctor_comm.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_comp_id_l.
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
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
    rewrite <- tensor_comp_id_l.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_l.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
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
  }
  rewrite !assoc.
  rewrite <- tensor_comp_id_r.
  rewrite sym_mon_braiding_linvunitor.
  rewrite mon_inv_triangle.
  apply idpath.
Qed.
