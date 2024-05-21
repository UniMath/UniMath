(******************************************************************************************

 Squares between enriched profunctors

 Squares of profunctors are one of the ingredients needed to define the double (bi)category
 of (univalent) enriched categories, functors, and profunctors, and in this file, we define
 squares of enriched profunctors. We define squares using transformations between enriched
 profunctors, and we also give several standard operations for squares on profunctors.

 Contents
 1. Squares of enriched profunctors
 2. Accessors/builders for squares of enriched profunctors
 3. Squares and transformations
 4. Examples of squares of enriched profunctors
 4.1. Horizontal identity square
 4.2. Vertical identity square
 4.3. Horizontal composition of squares
 4.4. Up whiskering
 4.5. Down whiskering
 4.6. Left whiskering
 4.7. Right whiskering
 4.8. Companion pairs
 4.9. Conjoints

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Squares of enriched profunctors *)
Definition enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {F : C₁ ⟶ C₂}
           {G : C₁' ⟶ C₂'}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₁' : enrichment C₁' V}
           {E₂' : enrichment C₂' V}
           (EF : functor_enrichment F E₁ E₂)
           (EG : functor_enrichment G E₁' E₂')
           (P : E₁ ↛e E₁')
           (Q : E₂ ↛e E₂')
  : UU
  := enriched_profunctor_transformation
       P
       (precomp_enriched_profunctor EF EG Q).

Identity Coercion enriched_profunctor_square_to_trans
  : enriched_profunctor_square >-> enriched_profunctor_transformation.

(** * 2. Accessors/builders for squares of enriched profunctors *)
Proposition enriched_profunctor_square_lmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {F : C₁ ⟶ C₁'}
            {G : C₂ ⟶ C₂'}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₁' : enrichment C₁' V}
            {E₂' : enrichment C₂' V}
            {EF : functor_enrichment F E₁ E₁'}
            {EG : functor_enrichment G E₂ E₂'}
            {P : E₁ ↛e E₂}
            {Q : E₁' ↛e E₂'}
            (τ : enriched_profunctor_square EF EG P Q)
            (x₁ x₂ : C₂)
            (y : C₁)
  : EG x₂ x₁ #⊗ τ x₁ y · lmap_e Q (G x₁) (G x₂) (F y)
    =
    lmap_e P x₁ x₂ y · τ x₂ y.
Proof.
  rewrite tensor_split.
  rewrite !assoc'.
  exact (enriched_profunctor_transformation_lmap_e τ x₁ x₂ y).
Qed.

Proposition enriched_profunctor_square_rmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {F : C₁ ⟶ C₁'}
            {G : C₂ ⟶ C₂'}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₁' : enrichment C₁' V}
            {E₂' : enrichment C₂' V}
            {EF : functor_enrichment F E₁ E₁'}
            {EG : functor_enrichment G E₂ E₂'}
            {P : E₁ ↛e E₂}
            {Q : E₁' ↛e E₂'}
            (τ : enriched_profunctor_square EF EG P Q)
            (x : C₂)
            (y₁ y₂ : C₁)
  : EF y₁ y₂ #⊗ τ x y₁ · rmap_e Q (G x) (F y₁) (F y₂)
    =
    rmap_e P x y₁ y₂ · τ x y₂.
Proof.
  rewrite tensor_split.
  rewrite !assoc'.
  exact (enriched_profunctor_transformation_rmap_e τ x y₁ y₂).
Qed.

(** * 3. Squares and transformations *)
Definition enriched_profunctor_square_to_transformation_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_square
                  (functor_id_enrichment E₁)
                  (functor_id_enrichment E₂)
                  P Q)
  : enriched_profunctor_transformation_data P Q
  := λ x y, τ x y.

Arguments enriched_profunctor_square_to_transformation_data {V C₁ C₂ E₁ E₂ P Q} τ /.

Proposition enriched_profunctor_square_to_transformation_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_square
                   (functor_id_enrichment E₁)
                   (functor_id_enrichment E₂)
                   P Q)
  : enriched_profunctor_transformation_laws
      (enriched_profunctor_square_to_transformation_data τ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    exact (enriched_profunctor_square_lmap_e τ x₁ x₂ y).
  - intros x y₁ y₂ ; cbn.
    exact (enriched_profunctor_square_rmap_e τ x y₁ y₂).
Qed.

Definition enriched_profunctor_square_to_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_square
                  (functor_id_enrichment E₁)
                  (functor_id_enrichment E₂)
                  P Q)
  : enriched_profunctor_transformation P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (enriched_profunctor_square_to_transformation_data τ).
  - exact (enriched_profunctor_square_to_transformation_laws τ).
Defined.

Definition enriched_profunctor_transformation_to_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor
         (functor_id_enrichment E₁)
         (functor_id_enrichment E₂)
         Q)
  := λ x y, τ x y.

Arguments enriched_profunctor_transformation_to_square_data {V C₁ C₂ E₁ E₂ P Q} τ /.

Proposition enriched_profunctor_transformation_to_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P Q)
  : enriched_profunctor_transformation_laws
      (enriched_profunctor_transformation_to_square_data τ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_id_id.
    rewrite id_left.
    apply enriched_profunctor_transformation_lmap_e.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_id_id.
    rewrite id_left.
    apply enriched_profunctor_transformation_rmap_e.
Qed.

Definition enriched_profunctor_transformation_to_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
  : enriched_profunctor_square
      (functor_id_enrichment E₁)
      (functor_id_enrichment E₂)
      P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (enriched_profunctor_transformation_to_square_data τ).
  - exact (enriched_profunctor_transformation_to_square_laws τ).
Defined.

Definition enriched_profunctor_transformation_square_weq
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : enriched_profunctor_transformation P Q
    ≃
    enriched_profunctor_square
      (functor_id_enrichment E₁)
      (functor_id_enrichment E₂)
      P Q.
Proof.
  use weq_iso.
  - exact enriched_profunctor_transformation_to_square.
  - exact enriched_profunctor_square_to_transformation.
  - abstract
      (intro τ ;
       use eq_enriched_profunctor_transformation ;
       intros x y ;
       apply idpath).
  - abstract
      (intro τ ;
       use eq_enriched_profunctor_transformation ;
       intros x y ;
       apply idpath).
Defined.

Section SquareToTransformation.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {EF : functor_enrichment F E₁ E₂}
          {EG : functor_enrichment G E₁ E₂}
          (τ : enriched_profunctor_square
                 EF EG
                 (identity_enriched_profunctor E₁)
                 (identity_enriched_profunctor E₂)).

  Definition square_to_enriched_nat_trans_data
    : nat_trans_data G F
    := λ x, enriched_to_arr E₂ (enriched_id E₁ x · τ x x).

  Proposition square_to_enriched_nat_trans_enrichment
    : nat_trans_enrichment
        square_to_enriched_nat_trans_data
        EG
        EF.
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y.
    unfold square_to_enriched_nat_trans_data.
    unfold precomp_arr, postcomp_arr.
    rewrite !enriched_from_to_arr.
    rewrite !assoc.
    rewrite tensor_rinvunitor.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_comp_l_id_l.
      rewrite !assoc'.
      apply maponpaths.
      exact (enriched_profunctor_square_rmap_e τ x x y).
    }
    cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_comp_r_id_l.
      rewrite !assoc'.
      apply maponpaths.
      pose (enriched_profunctor_square_lmap_e τ y x y) as p.
      cbn in p.
      rewrite !assoc in p.
      rewrite tensor_sym_mon_braiding in p.
      pose (maponpaths (λ z, sym_mon_braiding _ _ _ · z) p) as q.
      cbn in q.
      rewrite !assoc in q.
      rewrite !sym_mon_braiding_inv in q.
      rewrite !id_left in q.
      exact q.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite <- enrichment_id_left.
    rewrite <- enrichment_id_right.
    rewrite mon_linvunitor_lunitor.
    rewrite mon_rinvunitor_runitor.
    apply idpath.
  Qed.

  Definition square_to_enriched_nat_trans
    : G ⟹ F.
  Proof.
    use make_nat_trans.
    - exact square_to_enriched_nat_trans_data.
    - exact (is_nat_trans_from_enrichment square_to_enriched_nat_trans_enrichment).
  Defined.
End SquareToTransformation.

Arguments square_to_enriched_nat_trans_data {V C₁ C₂ F G E₁ E₂ EF EG} τ /.

(** * 4. Examples of squares of enriched profunctors *)

(** ** 4.1. Horizontal identity square *)
Definition id_h_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor
         (functor_id_enrichment E₁)
         (functor_id_enrichment E₂)
         P)
  := λ _ _, identity _.

Arguments id_h_enriched_profunctor_square_data {V C₁ C₂ E₁ E₂} P /.

Proposition id_h_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
  : enriched_profunctor_transformation_laws
      (id_h_enriched_profunctor_square_data P).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite !tensor_id_id.
    rewrite !id_left, id_right.
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    rewrite !tensor_id_id.
    rewrite !id_left, id_right.
    apply idpath.
Qed.

Definition id_h_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
  : enriched_profunctor_square
      (functor_id_enrichment E₁)
      (functor_id_enrichment E₂)
      P
      P.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (id_h_enriched_profunctor_square_data P).
  - exact (id_h_enriched_profunctor_square_laws P).
Defined.

(** ** 4.2. Vertical identity square *)
Definition id_v_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : enriched_profunctor_transformation_data
      (identity_enriched_profunctor E₁)
      (precomp_enriched_profunctor
         EF EF
         (identity_enriched_profunctor E₂))
  := λ x y, EF x y.

Arguments id_v_enriched_profunctor_square_data {V C₁ C₂ F E₁ E₂} EF /.

Proposition id_v_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (EF : functor_enrichment F E₁ E₂)
  : enriched_profunctor_transformation_laws
      (id_v_enriched_profunctor_square_data EF).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite functor_enrichment_comp.
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite functor_enrichment_comp.
    apply idpath.
Qed.

Definition id_v_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : enriched_profunctor_square
      EF
      EF
      (identity_enriched_profunctor _)
      (identity_enriched_profunctor _).
Proof.
  use make_enriched_profunctor_transformation.
  - exact (id_v_enriched_profunctor_square_data EF).
  - exact (id_v_enriched_profunctor_square_laws EF).
Defined.

(** ** 4.3. Horizontal composition of squares *)
Definition comp_h_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₃ C₁' C₂' C₃' : category}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁' ⟶ C₂'}
           {G₂ : C₂' ⟶ C₃'}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₃ : enrichment C₃ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {EC₃' : enrichment C₃' V}
           {EF₁ : functor_enrichment F₁ EC₁ EC₂}
           {EF₂ : functor_enrichment F₂ EC₂ EC₃}
           {EG₁ : functor_enrichment G₁ EC₁' EC₂'}
           {EG₂ : functor_enrichment G₂ EC₂' EC₃'}
           {P₁ : EC₁ ↛e EC₁'}
           {P₂ : EC₂ ↛e EC₂'}
           {P₃ : EC₃ ↛e EC₃'}
           (τ : enriched_profunctor_square EF₁ EG₁ P₁ P₂)
           (θ : enriched_profunctor_square EF₂ EG₂ P₂ P₃)
  : enriched_profunctor_transformation_data
      P₁
      (precomp_enriched_profunctor
         (functor_comp_enrichment EF₁ EF₂)
         (functor_comp_enrichment EG₁ EG₂)
         P₃)
  := λ x y, τ x y · θ _ _.

Arguments comp_h_enriched_profunctor_square_data
  {V C₁ C₂ C₃ C₁' C₂' C₃'
   F₁ F₂ G₁ G₂
   EC₁ EC₂ EC₃ EC₁' EC₂' EC₃'
   EF₁ EF₂ EG₁ EG₂
   P₁ P₂ P₃}
  τ θ /.

Proposition comp_h_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₃ C₁' C₂' C₃' : category}
            {F₁ : C₁ ⟶ C₂}
            {F₂ : C₂ ⟶ C₃}
            {G₁ : C₁' ⟶ C₂'}
            {G₂ : C₂' ⟶ C₃'}
            {EC₁ : enrichment C₁ V}
            {EC₂ : enrichment C₂ V}
            {EC₃ : enrichment C₃ V}
            {EC₁' : enrichment C₁' V}
            {EC₂' : enrichment C₂' V}
            {EC₃' : enrichment C₃' V}
            {EF₁ : functor_enrichment F₁ EC₁ EC₂}
            {EF₂ : functor_enrichment F₂ EC₂ EC₃}
            {EG₁ : functor_enrichment G₁ EC₁' EC₂'}
            {EG₂ : functor_enrichment G₂ EC₂' EC₃'}
            {P₁ : EC₁ ↛e EC₁'}
            {P₂ : EC₂ ↛e EC₂'}
            {P₃ : EC₃ ↛e EC₃'}
            (τ : enriched_profunctor_square EF₁ EG₁ P₁ P₂)
            (θ : enriched_profunctor_square EF₂ EG₂ P₂ P₃)
  : enriched_profunctor_transformation_laws
      (comp_h_enriched_profunctor_square_data τ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_comp_mor.
    rewrite !assoc'.
    rewrite (enriched_profunctor_square_lmap_e θ).
    rewrite !assoc.
    rewrite (enriched_profunctor_square_lmap_e τ).
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_comp_mor.
    rewrite !assoc'.
    rewrite (enriched_profunctor_square_rmap_e θ).
    rewrite !assoc.
    rewrite (enriched_profunctor_square_rmap_e τ).
    apply idpath.
Qed.

Definition comp_h_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₃ C₁' C₂' C₃' : category}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : C₁' ⟶ C₂'}
           {G₂ : C₂' ⟶ C₃'}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₃ : enrichment C₃ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {EC₃' : enrichment C₃' V}
           {EF₁ : functor_enrichment F₁ EC₁ EC₂}
           {EF₂ : functor_enrichment F₂ EC₂ EC₃}
           {EG₁ : functor_enrichment G₁ EC₁' EC₂'}
           {EG₂ : functor_enrichment G₂ EC₂' EC₃'}
           {P₁ : EC₁ ↛e EC₁'}
           {P₂ : EC₂ ↛e EC₂'}
           {P₃ : EC₃ ↛e EC₃'}
           (τ : enriched_profunctor_square EF₁ EG₁ P₁ P₂)
           (θ : enriched_profunctor_square EF₂ EG₂ P₂ P₃)
  : enriched_profunctor_square
      (functor_comp_enrichment EF₁ EF₂)
      (functor_comp_enrichment EG₁ EG₂)
      P₁
      P₃.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (comp_h_enriched_profunctor_square_data τ θ).
  - exact (comp_h_enriched_profunctor_square_laws τ θ).
Defined.

(** * 4.4. Up whiskering *)
Definition uwhisker_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F F' : C₁ ⟶ C₂}
           {τ : F ⟹ F'}
           {EF : functor_enrichment F EC₁ EC₂}
           {EF' : functor_enrichment F' EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q : EC₂ ↛e EC₂'}
           (Eτ : nat_trans_enrichment τ EF EF')
           (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor EF' EG Q)
  := λ x y,
     θ x y
     · mon_linvunitor _
     · (enriched_from_arr EC₂ (τ y) #⊗ identity _)
     · rmap_e Q (G x) (F y) (F' y).

Arguments uwhisker_enriched_profunctor_square_data
  {V
   C₁ C₂ C₁' C₂'
   EC₁ EC₂ EC₁' EC₂'
   F F'
   τ
   EF EF'
   G EG
   P Q}
  Eτ θ /.

Proposition uwhisker_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {EC₁ : enrichment C₁ V}
            {EC₂ : enrichment C₂ V}
            {EC₁' : enrichment C₁' V}
            {EC₂' : enrichment C₂' V}
            {F F' : C₁ ⟶ C₂}
            {τ : F ⟹ F'}
            {EF : functor_enrichment F EC₁ EC₂}
            {EF' : functor_enrichment F' EC₁ EC₂}
            {G : C₁' ⟶ C₂'}
            {EG : functor_enrichment G EC₁' EC₂'}
            {P : EC₁ ↛e EC₁'}
            {Q : EC₂ ↛e EC₂'}
            (Eτ : nat_trans_enrichment τ EF EF')
            (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_transformation_laws
      (uwhisker_enriched_profunctor_square_data Eτ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite !assoc'.
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    rewrite <- (enriched_profunctor_square_lmap_e θ).
    rewrite (tensor_split (EG x₂ x₁) (θ x₁ y)).
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      rewrite <- tensor_split.
      rewrite tensor_split'.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_linvunitor ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply idpath.
    }
    rewrite lmap_e_rmap_e'.
    rewrite !assoc.
    rewrite tensor_comp_id_l.
    do 2 apply maponpaths_2.
    rewrite !assoc'.
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
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      apply idpath.
    }
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_linvunitor.
    rewrite mon_inv_triangle.
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    etrans.
    {
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite rmap_e_rmap_e.
      apply idpath.
    }
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      apply idpath.
    }
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
      rewrite !assoc.
      rewrite <- tensor_split'.
      apply idpath.
    }
    rewrite tensor_comp_id_l.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_inv_triangle.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      do 2 apply maponpaths_2.
      rewrite !assoc.
      exact (Eτ y₁ y₂).
    }
    rewrite !assoc.
    rewrite <- (enriched_profunctor_square_rmap_e θ).
    etrans.
    {
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite <- tensor_split.
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite tensor_comp_r_id_r.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      apply (rmap_e_rmap_e Q).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_comp_id_r.
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

Definition uwhisker_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F F' : C₁ ⟶ C₂}
           {τ : F ⟹ F'}
           {EF : functor_enrichment F EC₁ EC₂}
           {EF' : functor_enrichment F' EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q : EC₂ ↛e EC₂'}
           (Eτ : nat_trans_enrichment τ EF EF')
           (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_square EF' EG P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (uwhisker_enriched_profunctor_square_data Eτ θ).
  - exact (uwhisker_enriched_profunctor_square_laws Eτ θ).
Defined.

(** * 4.5. Down whiskering *)
Definition dwhisker_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G G' : C₁' ⟶ C₂'}
           {τ : G ⟹ G'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {EG' : functor_enrichment G' EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q : EC₂ ↛e EC₂'}
           (Eτ : nat_trans_enrichment τ EG EG')
           (θ : enriched_profunctor_square EF EG' P Q)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor EF EG Q)
  := λ x y,
     θ x y
     · mon_linvunitor _
     · (enriched_from_arr EC₂' (τ x) #⊗ identity _)
     · lmap_e Q (G' x) (G x) (F y).

Arguments dwhisker_enriched_profunctor_square_data
  {V
   C₁ C₂ C₁' C₂'
   EC₁ EC₂ EC₁' EC₂'
   F EF
   G G'
   τ
   EG EG'
   P Q}
  Eτ θ /.

Proposition dwhisker_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {EC₁ : enrichment C₁ V}
            {EC₂ : enrichment C₂ V}
            {EC₁' : enrichment C₁' V}
            {EC₂' : enrichment C₂' V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F EC₁ EC₂}
            {G G' : C₁' ⟶ C₂'}
            {τ : G ⟹ G'}
            {EG : functor_enrichment G EC₁' EC₂'}
            {EG' : functor_enrichment G' EC₁' EC₂'}
            {P : EC₁ ↛e EC₁'}
            {Q : EC₂ ↛e EC₂'}
            (Eτ : nat_trans_enrichment τ EG EG')
            (θ : enriched_profunctor_square EF EG' P Q)
  : enriched_profunctor_transformation_laws
      (dwhisker_enriched_profunctor_square_data Eτ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    etrans.
    {
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite lmap_e_lmap_e.
      apply idpath.
    }
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_r.
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    }
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
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      do 2 apply maponpaths_2.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    }
    rewrite tensor_comp_id_l.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_inv_triangle.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      do 2 apply maponpaths_2.
      rewrite !assoc.
      rewrite sym_mon_braiding_rinvunitor.
      exact (!(Eτ x₂ x₁)).
    }
    rewrite !assoc.
    rewrite <- (enriched_profunctor_square_lmap_e θ).
    etrans.
    {
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite <- tensor_split.
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_split'.
        rewrite !assoc.
        rewrite <- tensor_rinvunitor.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite tensor_comp_r_id_r.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      apply (lmap_e_lmap_e Q).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_comp_id_r.
    apply maponpaths_2.
    rewrite <- tensor_id_id.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_comp_id_r.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    }
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_linvunitor.
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    rewrite !assoc'.
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    rewrite <- (enriched_profunctor_square_rmap_e θ).
    rewrite (tensor_split (EF y₁ y₂) (θ x y₁)).
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      rewrite <- tensor_split.
      rewrite tensor_split'.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_linvunitor ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply idpath.
    }
    rewrite rmap_e_lmap_e.
    rewrite !assoc.
    rewrite tensor_comp_id_l.
    do 2 apply maponpaths_2.
    rewrite !assoc'.
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
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      apply idpath.
    }
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_linvunitor.
    rewrite mon_inv_triangle.
    apply idpath.
Qed.

Definition dwhisker_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G G' : C₁' ⟶ C₂'}
           {τ : G ⟹ G'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {EG' : functor_enrichment G' EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q : EC₂ ↛e EC₂'}
           (Eτ : nat_trans_enrichment τ EG EG')
           (θ : enriched_profunctor_square EF EG' P Q)
  : enriched_profunctor_square EF EG P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (dwhisker_enriched_profunctor_square_data Eτ θ).
  - exact (dwhisker_enriched_profunctor_square_laws Eτ θ).
Defined.

(** * 4.6. Left whiskering *)
Definition lwhisker_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P P' : EC₁ ↛e EC₁'}
           (τ : enriched_profunctor_transformation P P')
           {Q : EC₂ ↛e EC₂'}
           (θ : enriched_profunctor_square EF EG P' Q)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor EF EG Q)
  := λ x y, τ x y · θ x y.

Arguments lwhisker_enriched_profunctor_square_data
  {V
   C₁ C₂ C₁' C₂'
   EC₁ EC₂ EC₁' EC₂'
   F EF
   G EG
   P P'}
  τ
  {Q}
  θ /.

Proposition lwhisker_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {EC₁ : enrichment C₁ V}
            {EC₂ : enrichment C₂ V}
            {EC₁' : enrichment C₁' V}
            {EC₂' : enrichment C₂' V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F EC₁ EC₂}
            {G : C₁' ⟶ C₂'}
            {EG : functor_enrichment G EC₁' EC₂'}
            {P P' : EC₁ ↛e EC₁'}
            (τ : enriched_profunctor_transformation P P')
            {Q : EC₂ ↛e EC₂'}
            (θ : enriched_profunctor_square EF EG P' Q)
  : enriched_profunctor_transformation_laws
      (lwhisker_enriched_profunctor_square_data τ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite (enriched_profunctor_square_lmap_e θ).
      apply idpath.
    }
    rewrite !assoc.
    rewrite enriched_profunctor_transformation_lmap_e.
    apply idpath.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite (enriched_profunctor_square_rmap_e θ).
      apply idpath.
    }
    rewrite !assoc.
    rewrite enriched_profunctor_transformation_rmap_e.
    apply idpath.
Qed.

Definition lwhisker_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P P' : EC₁ ↛e EC₁'}
           (τ : enriched_profunctor_transformation P P')
           {Q : EC₂ ↛e EC₂'}
           (θ : enriched_profunctor_square EF EG P' Q)
  : enriched_profunctor_square EF EG P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (lwhisker_enriched_profunctor_square_data τ θ).
  - exact (lwhisker_enriched_profunctor_square_laws τ θ).
Defined.

(** * 4.7. Right whiskering *)
Definition rwhisker_enriched_profunctor_square_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q Q' : EC₂ ↛e EC₂'}
           (τ : enriched_profunctor_transformation Q Q')
           (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_transformation_data
      P
      (precomp_enriched_profunctor EF EG Q')
  := λ x y, θ x y · τ (G x) (F y).

Arguments rwhisker_enriched_profunctor_square_data
  {V
   C₁ C₂ C₁' C₂'
   EC₁ EC₂ EC₁' EC₂'
   F EF
   G EG
   P Q Q'}
  τ
  θ /.

Proposition rwhisker_enriched_profunctor_square_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ C₁' C₂' : category}
            {EC₁ : enrichment C₁ V}
            {EC₂ : enrichment C₂ V}
            {EC₁' : enrichment C₁' V}
            {EC₂' : enrichment C₂' V}
            {F : C₁ ⟶ C₂}
            {EF : functor_enrichment F EC₁ EC₂}
            {G : C₁' ⟶ C₂'}
            {EG : functor_enrichment G EC₁' EC₂'}
            {P : EC₁ ↛e EC₁'}
            {Q Q' : EC₂ ↛e EC₂'}
            (τ : enriched_profunctor_transformation Q Q')
            (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_transformation_laws
      (rwhisker_enriched_profunctor_square_data τ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_comp_l_id_r.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_lmap_e.
    rewrite !assoc.
    rewrite (enriched_profunctor_square_lmap_e θ).
    apply idpath.
  - intros x₁ x₂ y ; cbn.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_comp_l_id_r.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_rmap_e.
    rewrite !assoc.
    rewrite (enriched_profunctor_square_rmap_e θ).
    apply idpath.
Qed.

Definition rwhisker_enriched_profunctor_square
           {V : sym_mon_closed_cat}
           {C₁ C₂ C₁' C₂' : category}
           {EC₁ : enrichment C₁ V}
           {EC₂ : enrichment C₂ V}
           {EC₁' : enrichment C₁' V}
           {EC₂' : enrichment C₂' V}
           {F : C₁ ⟶ C₂}
           {EF : functor_enrichment F EC₁ EC₂}
           {G : C₁' ⟶ C₂'}
           {EG : functor_enrichment G EC₁' EC₂'}
           {P : EC₁ ↛e EC₁'}
           {Q Q' : EC₂ ↛e EC₂'}
           (τ : enriched_profunctor_transformation Q Q')
           (θ : enriched_profunctor_square EF EG P Q)
  : enriched_profunctor_square EF EG P Q'.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (rwhisker_enriched_profunctor_square_data τ θ).
  - exact (rwhisker_enriched_profunctor_square_laws τ θ).
Defined.

Section CompanionsAndConjoints.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (EF : functor_enrichment F E₁ E₂).

  (** ** 4.8. Companion pairs *)
  Definition representable_enriched_profunctor_left_unit_data
    : enriched_profunctor_transformation_data
        (representable_enriched_profunctor_left EF)
        (precomp_enriched_profunctor
           EF
           (functor_id_enrichment E₂)
           (identity_enriched_profunctor E₂))
    := λ x y, identity _.

  Arguments representable_enriched_profunctor_left_unit_data /.

  Proposition representable_enriched_profunctor_left_unit_laws
    : enriched_profunctor_transformation_laws
        representable_enriched_profunctor_left_unit_data.
  Proof.
    split.
    - intros x₁ x₂ y ; cbn.
      rewrite !tensor_id_id.
      rewrite !id_left.
      rewrite id_right.
      apply idpath.
    - intros x y₁ y₂ ; cbn.
      rewrite !tensor_id_id.
      rewrite !id_left.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_left_unit
    : enriched_profunctor_square
        EF
        (functor_id_enrichment _)
        (representable_enriched_profunctor_left EF)
        (identity_enriched_profunctor _).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact representable_enriched_profunctor_left_unit_data.
    - exact representable_enriched_profunctor_left_unit_laws.
  Defined.

  Definition representable_enriched_profunctor_left_counit_data
    : enriched_profunctor_transformation_data
        (identity_enriched_profunctor E₁)
        (precomp_enriched_profunctor
           (functor_id_enrichment E₁) EF
           (representable_enriched_profunctor_left EF))
    := λ x y, EF x y.

  Arguments representable_enriched_profunctor_left_counit_data /.

  Proposition representable_enriched_profunctor_left_counit_laws
    : enriched_profunctor_transformation_laws
        representable_enriched_profunctor_left_counit_data.
  Proof.
    split.
    - intros x₁ x₂ y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite functor_enrichment_comp.
      apply idpath.
    - intros x y₁ y₂ ; cbn.
      rewrite tensor_id_id.
      rewrite id_left.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite functor_enrichment_comp.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_left_counit
    : enriched_profunctor_square
        (functor_id_enrichment _)
        EF
        (identity_enriched_profunctor _)
        (representable_enriched_profunctor_left EF).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact representable_enriched_profunctor_left_counit_data.
    - exact representable_enriched_profunctor_left_counit_laws.
  Defined.

  (** ** 4.9. Conjoints *)
  Definition representable_enriched_profunctor_right_unit_data
    : enriched_profunctor_transformation_data
        (identity_enriched_profunctor E₁)
        (precomp_enriched_profunctor
           EF (functor_id_enrichment E₁)
           (representable_enriched_profunctor_right EF))
    := λ x y, EF x y.

  Arguments representable_enriched_profunctor_right_unit_data /.

  Proposition representable_enriched_profunctor_right_unit_laws
    : enriched_profunctor_transformation_laws
        representable_enriched_profunctor_right_unit_data.
  Proof.
    split.
    - intros x₁ x₂ y ; cbn.
      rewrite tensor_id_id.
      rewrite id_left.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite functor_enrichment_comp.
      apply idpath.
    - intros x y₁ y₂ ; cbn.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite functor_enrichment_comp.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_right_unit
    : enriched_profunctor_square
        EF
        (functor_id_enrichment _)
        (identity_enriched_profunctor _)
        (representable_enriched_profunctor_right EF).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact representable_enriched_profunctor_right_unit_data.
    - exact representable_enriched_profunctor_right_unit_laws.
  Defined.

  Definition representable_enriched_profunctor_right_counit_data
    : enriched_profunctor_transformation_data
        (representable_enriched_profunctor_right EF)
        (precomp_enriched_profunctor
           (functor_id_enrichment E₂) EF
           (identity_enriched_profunctor E₂))
    := λ x y, identity _.

  Arguments representable_enriched_profunctor_right_counit_data /.

  Proposition representable_enriched_profunctor_right_counit_laws
    : enriched_profunctor_transformation_laws
        representable_enriched_profunctor_right_counit_data.
  Proof.
    split.
    - intros x₁ x₂ y ; cbn.
      rewrite tensor_id_id.
      rewrite id_left, id_right.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      apply idpath.
    - intros x y₁ y₂ ; cbn.
      rewrite tensor_id_id.
      rewrite !id_left, id_right.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_right_counit
    : enriched_profunctor_square
        (functor_id_enrichment _)
        EF
        (representable_enriched_profunctor_right EF)
        (identity_enriched_profunctor _).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact representable_enriched_profunctor_right_counit_data.
    - exact representable_enriched_profunctor_right_counit_laws.
  Defined.
End CompanionsAndConjoints.

Arguments representable_enriched_profunctor_left_unit_data {V C₁ C₂ F E₁ E₂} EF /.
Arguments representable_enriched_profunctor_left_counit_data {V C₁ C₂ F E₁ E₂} EF /.
Arguments representable_enriched_profunctor_right_unit_data {V C₁ C₂ F E₁ E₂} EF /.
Arguments representable_enriched_profunctor_right_counit_data {V C₁ C₂ F E₁ E₂} EF /.
