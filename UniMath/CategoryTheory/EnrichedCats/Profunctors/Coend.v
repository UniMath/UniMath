(******************************************************************************************

 Coends of enriched profunctor

 Suppose that we have a category `C` together with a `V`-enrichment `E` where `V` is a Benaou
 cosmos, and suppose that we have an enriched profunctor `P : E ↛e E`. Then `P` gives rise
 to a coend. In this file, we construct this coend explicitly, and we give accessors for
 this coend.

 Content
 1. Construction of the coend of an enriched profunctor
 2. Accessors

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section Coend.
  Context {V : benabou_cosmos}
          {C : category}
          {E : enrichment C V}
          (P : E ↛e E).

  (** * 1. Construction of the coend of an enriched profunctor *)
  Local Definition ob_coprod
    : Coproduct _ _ _
    := benabou_cosmos_coproducts V C (λ x, P x x).

  Local Definition mor_coprod
    : Coproduct _ _ _
    := benabou_cosmos_coproducts
         V
         (C × C)
         (λ xy, E ⦃ pr1 xy , pr2 xy ⦄ ⊗ P (pr2 xy) (pr1 xy)).

  Local Definition left_mor
    : mor_coprod --> ob_coprod.
  Proof.
    use CoproductArrow.
    exact (λ xy,
           lmap_e P (pr2 xy) (pr1 xy) (pr1 xy)
           · CoproductIn _ _ ob_coprod (pr1 xy)).
  Defined.

  Local Definition right_mor
    : mor_coprod --> ob_coprod.
  Proof.
    use CoproductArrow.
    exact (λ xy,
           rmap_e P (pr2 xy) (pr1 xy) (pr2 xy)
           · CoproductIn _ _ ob_coprod (pr2 xy)).
  Defined.

  Local Definition enriched_profunctor_coend_coequalizer
    : Coequalizer left_mor right_mor
    := benabou_cosmos_coequalizers _ _ _ left_mor right_mor.

  Definition enriched_profunctor_coend
    : V
    := enriched_profunctor_coend_coequalizer.

  (** * 2. Accessors *)
  Definition enriched_profunctor_coend_in
             (x : C)
    : P x x --> enriched_profunctor_coend
    := CoproductIn _ _ ob_coprod x
       · CoequalizerArrow enriched_profunctor_coend_coequalizer.

  Proposition enriched_profunctor_coend_comm
              (x y : C)
    : lmap_e P y x x · enriched_profunctor_coend_in x
      =
      rmap_e P y x y · enriched_profunctor_coend_in y.
  Proof.
    pose (maponpaths
            (λ z, CoproductIn _ _ mor_coprod (x ,, y) · z)
            (CoequalizerEqAr enriched_profunctor_coend_coequalizer)) as p.
    cbn in p.
    unfold left_mor, right_mor in p.
    rewrite !assoc in p.
    refine (_ @ p @ _).
    - refine (!_).
      rewrite (CoproductInCommutes _ _ _ mor_coprod _ _ (x ,, y)).
      rewrite !assoc'.
      apply idpath.
    - rewrite (CoproductInCommutes _ _ _ mor_coprod _ _ (x ,, y)).
      rewrite !assoc'.
      apply idpath.
  Qed.

  Proposition enriched_profunctor_coend_comm_arr
              {y₁ y₂ : C}
              (g : y₁ --> y₂)
    : lmap_e_arr P y₁ g · enriched_profunctor_coend_in y₁
      =
      rmap_e_arr P g y₂ · enriched_profunctor_coend_in y₂.
  Proof.
    unfold lmap_e_arr, rmap_e_arr.
    rewrite !assoc'.
    rewrite enriched_profunctor_coend_comm.
    apply idpath.
  Qed.

  Definition from_enriched_profunctor_coend
             (v : V)
             (fs : ∏ (x : C), P x x --> v)
             (ps : ∏ (x y : C),
                   lmap_e P y x x · fs x
                   =
                   rmap_e P y x y · fs y)
    : enriched_profunctor_coend --> v.
  Proof.
    use CoequalizerOut.
    - use CoproductArrow.
      exact fs.
    - abstract
        (use CoproductArrow_eq ;
         intros xy ;
         induction xy as [ x y ] ; cbn ;
         rewrite !assoc ;
         unfold left_mor, right_mor ;
         rewrite !(CoproductInCommutes _ _ _ mor_coprod _ _ (x ,, y)) ;
         cbn ;
         rewrite !assoc' ;
         rewrite !(CoproductInCommutes _ _ _ ob_coprod) ;
         exact (ps x y)).
  Defined.

  Proposition from_enriched_profunctor_coend_comm
              (v : V)
              (fs : ∏ (x : C), P x x --> v)
              (ps : ∏ (x y : C),
                    lmap_e P y x x · fs x
                    =
                    rmap_e P y x y · fs y)
              (x : C)
    : enriched_profunctor_coend_in x · from_enriched_profunctor_coend v fs ps
      =
      fs x.
  Proof.
    unfold enriched_profunctor_coend_in, from_enriched_profunctor_coend.
    rewrite !assoc'.
    rewrite CoequalizerCommutes.
    apply (CoproductInCommutes _ _ _ ob_coprod).
  Qed.

  Definition enriched_profunctor_coend_eq_mor
             {v : V}
             {f g : enriched_profunctor_coend --> v}
             (ps : ∏ (x : C),
                   enriched_profunctor_coend_in x · f
                   =
                   enriched_profunctor_coend_in x · g)
    : f = g.
  Proof.
    use CoequalizerOutsEq.
    use CoproductArrow_eq.
    intro x.
    rewrite !assoc.
    exact (ps x).
  Qed.
End Coend.

#[global] Opaque enriched_profunctor_coend.
#[global] Opaque enriched_profunctor_coend_in.
#[global] Opaque from_enriched_profunctor_coend.
