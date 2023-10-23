(*****************************************************************

 Change of base for enriched categories

 In this file, we define the change of base for enriched
 categories. In textbooks, this construction works as follows: if
 we have two monoidal categories `V₁` and `V₂` and a lax monoidal
 functor `F : V₁ ⟶ V₂`, then every category enriched over `V₁`
 gives rise to a category enriched over `V₂`. The objects stay the
 same and for the enriched morphisms, we use the functor `F`.

 However, in a univalent setting, we would like to restrict this
 construction. Let `V₁` be any monoidal category (for example,
 `Set`) and let `V₂` be the terminal monoidal category (only one
 object and only one morphism). Then we have a functor `V₁ ⟶ V₂`
 and as such, every category enriched over `V₁` is also enriched
 over the terminal monoidal category. However, between any two
 objects in a category enriched over the terminal monoidal
 category, there is at most one isomorphism. As such, if we leave
 the objects the same in this construction, this does not in
 general give rise to a univalent category.

 To guarantee that the change of base actually gives rise to a
 univalent category, we define a notion of preserving the
 underlying category (`preserve_underlying`), and this is
 sufficient to construct the desired assumptions. As such,
 univalence of the change of base follows directly from the
 univalence of the original category.

 We also show that functors that satisfy the following two
 conditions preserve the underlying category:
 - The functor is fully faithful on morphisms from the unit
 - The functor is a strong monoidal functor

 We also discuss the action of the change of base on functors
 and natural transformations.

 Contents
 1. Functors that preserve the underlying category
 1.1. The definition of such functors
 1.2. Conditions that imply preservation of the underlying category
 2. Change of base: enrichment for categories
 3. Change of base: enrichment for functors
 4. Change of base: enrichment for natural transformations
 5. Change of base on the identity
 6. Change of base on composition

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Functors that preserve the underlying category
 *)

(**
 1.1. The definition of such functors
 *)
Definition preserve_underlying_data
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
  : UU
  := ∏ (v : V₁), I_{V₂} --> F v → I_{V₁} --> v.

Definition preserves_underlying_laws
           {V₁ V₂ : monoidal_cat}
           {F : lax_monoidal_functor V₁ V₂}
           (Fv : preserve_underlying_data F)
  : UU
  := (∏ (v : V₁)
        (f : I_{V₂} --> F v),
      mon_functor_unit F · #F (Fv v f) = f)
     ×
     (∏ (v : V₁)
        (f : I_{V₁} --> v),
      Fv v (mon_functor_unit F · #F f) = f).

Definition preserve_underlying
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
  : UU
  := ∑ (Fv : preserve_underlying_data F), preserves_underlying_laws Fv.

Definition make_preserve_underlying
           {V₁ V₂ : monoidal_cat}
           {F : lax_monoidal_functor V₁ V₂}
           (Fv : preserve_underlying_data F)
           (HFv : preserves_underlying_laws Fv)
  : preserve_underlying F
  := Fv ,, HFv.

Definition preserve_underlying_to_data
           {V₁ V₂ : monoidal_cat}
           {F : lax_monoidal_functor V₁ V₂}
           (Fv : preserve_underlying F)
           (v : V₁)
  : I_{V₂} --> F v → I_{V₁} --> v
  := pr1 Fv v.

Coercion preserve_underlying_to_data : preserve_underlying >-> Funclass.

Section Laws.
  Context {V₁ V₂ : monoidal_cat}
          {F : lax_monoidal_functor V₁ V₂}
          (Fv : preserve_underlying F).

  Proposition preserve_underlying_right_inv
              {v : V₁}
              (f : I_{V₂} --> F v)
    : mon_functor_unit F · #F (Fv v f) = f.
  Proof.
    exact (pr12 Fv v f).
  Qed.

  Proposition preserve_underlying_left_inv
              {v : V₁}
              (f : I_{V₁} --> v)
    : Fv v (mon_functor_unit F · #F f) = f.
  Proof.
    exact (pr22 Fv v f).
  Qed.
End Laws.

(**
 1.2. Conditions that imply preservation of the underlying category
 *)
Definition strong_fully_faithful_on_points_to_preserve_underlying
           {V₁ V₂ : monoidal_cat}
           {F : strong_monoidal_functor V₁ V₂}
           (HF : ∏ (x : V₁), isweq (λ (f : I_{V₁} --> x), #F f))
  : preserve_underlying F.
Proof.
  use make_preserve_underlying.
  - exact (λ v f, invmap (make_weq _ (HF v)) (strong_functor_unit_inv F · f)).
  - split.
    + abstract
        (intros v f ;
         refine (maponpaths (λ z, _ · z) (homotweqinvweq (make_weq _ (HF v)) _) @ _) ;
         rewrite !assoc ;
         rewrite strong_functor_unit_unit_inv ;
         apply id_left).
    + abstract
        (intros v f ;
         rewrite !assoc ;
         rewrite strong_functor_unit_inv_unit ;
         rewrite id_left ;
         apply (homotinvweqweq (make_weq _ (HF v)) _)).
Defined.

Definition strong_fully_faithful_to_preserve_underlying
           {V₁ V₂ : monoidal_cat}
           {F : strong_monoidal_functor V₁ V₂}
           (HF : fully_faithful F)
  : preserve_underlying F.
Proof.
  use strong_fully_faithful_on_points_to_preserve_underlying.
  intro v.
  apply HF.
Defined.

Section ChangeOfBase.
  Context {V₁ V₂ : monoidal_cat}
          (F : lax_monoidal_functor V₁ V₂)
          (Fv : preserve_underlying F).

  (**
   2. Change of base: enrichment for categories
   *)
  Section Enrichment.
    Context {C : category}
            (E : enrichment C V₁).

    Definition change_of_base_enrichment_data
      : enrichment_data C V₂.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - exact (λ x y, F (E ⦃ x , y ⦄)).
      - exact (λ x, mon_functor_unit F · #F (enriched_id E x)).
      - exact (λ x y z, mon_functor_tensor F _ _ · #F (enriched_comp E x y z)).
      - exact (λ x y f, mon_functor_unit F · #F (enriched_from_arr E f)).
      - exact (λ x y f,
               enriched_to_arr
                 E
                 (Fv _ f)).
    Defined.

    Definition change_of_base_enrichment_laws
      : enrichment_laws change_of_base_enrichment_data.
    Proof.
      repeat split.
      - intros x y ; cbn.
        refine (mon_functor_lunitor F (E ⦃ x, y ⦄) @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          exact (enrichment_id_left E x y).
        }
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_mon_functor_tensor.
        }
        apply maponpaths_2.
        apply maponpaths.
        apply functor_id.
      - intros x y ; cbn.
        refine (mon_functor_runitor F (E ⦃ x, y ⦄) @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          exact (enrichment_id_right E x y).
        }
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_mon_functor_tensor.
        }
        do 2 apply maponpaths_2.
        apply functor_id.
      - intros w x y z ; cbn.
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply tensor_comp_id_l.
          }
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply functor_id.
          }
          apply (tensor_mon_functor_tensor F).
        }
        etrans.
        {
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (!_).
          apply (mon_functor_lassociator F).
        }
        etrans.
        {
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite <- !functor_comp.
          apply maponpaths.
          rewrite !assoc.
          refine (!_).
          apply enrichment_assoc.
        }
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            apply tensor_comp_id_r.
          }
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              refine (!_).
              apply functor_id.
            }
            apply (tensor_mon_functor_tensor F).
          }
          rewrite !assoc'.
          rewrite <- functor_comp.
          apply idpath.
        }
        apply idpath.
      - intros x y f ; cbn.
        refine (_ @ enriched_to_from_arr E f).
        apply maponpaths.
        apply preserve_underlying_left_inv.
      - intros x y f ; cbn.
        rewrite enriched_from_to_arr.
        apply preserve_underlying_right_inv.
      - intros x ; cbn.
        refine (_ @ enriched_to_arr_id E _).
        apply maponpaths.
        apply preserve_underlying_left_inv.
      - intros x y z f g ; cbn.
        refine (enriched_to_arr_comp E f g @ _).
        apply maponpaths.
        refine (!_).
        rewrite tensor_comp_l_id_l.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite tensor_comp_r_id_l.
          rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !assoc.
            rewrite tensor_mon_functor_tensor.
            rewrite !assoc'.
            rewrite <- functor_comp.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- mon_functor_linvunitor.
          rewrite <- functor_comp.
          apply idpath.
        }
        rewrite preserve_underlying_left_inv.
        apply idpath.
    Qed.

    Definition change_of_base_enrichment
      : enrichment C V₂.
    Proof.
      simple refine (_ ,, _).
      - exact change_of_base_enrichment_data.
      - exact change_of_base_enrichment_laws.
    Defined.

    Proposition change_of_base_precomp
                {x y : C}
                (w : C)
                (f : x --> y)
      : precomp_arr change_of_base_enrichment w f
        =
        #F (precomp_arr E w f).
    Proof.
      unfold precomp_arr ; cbn.
      rewrite !functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite mon_functor_rinvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_mon_functor_tensor.
      rewrite functor_id.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      apply idpath.
    Qed.

    Proposition change_of_base_postcomp
                {x y : C}
                (w : C)
                (f : x --> y)
      : postcomp_arr change_of_base_enrichment w f
        =
        #F (postcomp_arr E w f).
    Proof.
      unfold postcomp_arr ; cbn.
      rewrite !functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite mon_functor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_mon_functor_tensor.
      rewrite functor_id.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      apply idpath.
    Qed.
  End Enrichment.

  (**
   3. Change of base: enrichment for functors
   *)
  Section EnrichmentFunctor.
    Context {C₁ C₂ : category}
            {H : C₁ ⟶ C₂}
            {E₁ : enrichment C₁ V₁}
            {E₂ : enrichment C₂ V₁}
            (HE : functor_enrichment H E₁ E₂).

    Definition change_of_base_functor_enrichment_laws
      : @is_functor_enrichment
          _ _ _
          H
          (change_of_base_enrichment E₁)
          (change_of_base_enrichment E₂)
          (λ x y : C₁, # F (HE x y)).
    Proof.
      repeat split.
      - intros x ; cbn.
        rewrite !assoc'.
        rewrite <- functor_comp.
        do 2 apply maponpaths.
        apply functor_enrichment_id.
      - intros x y z ; cbn.
        rewrite !assoc.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply (tensor_mon_functor_tensor F).
        }
        rewrite !assoc'.
        rewrite <- !functor_comp.
        do 2 apply maponpaths.
        refine (!_).
        apply functor_enrichment_comp.
      - intros x y f ; cbn.
        rewrite !assoc'.
        rewrite <- (functor_comp F).
        do 2 apply maponpaths.
        apply functor_enrichment_from_arr.
    Qed.

    Definition change_of_base_functor_enrichment
      : functor_enrichment
          H
          (change_of_base_enrichment E₁)
          (change_of_base_enrichment E₂).
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y, #F (HE x y)).
      - exact change_of_base_functor_enrichment_laws.
    Defined.
  End EnrichmentFunctor.

  (**
   4. Change of base: enrichment for natural transformations
   *)
  Definition change_of_base_nat_trans_enrichment
             {C₁ C₂ : category}
             {H₁ H₂ : C₁ ⟶ C₂}
             {τ : H₁ ⟹ H₂}
             {E₁ : enrichment C₁ V₁}
             {E₂ : enrichment C₂ V₁}
             {HE₁ : functor_enrichment H₁ E₁ E₂}
             {HE₂ : functor_enrichment H₂ E₁ E₂}
             (Hτ : nat_trans_enrichment τ HE₁ HE₂)
    : nat_trans_enrichment
        τ
        (change_of_base_functor_enrichment HE₁)
        (change_of_base_functor_enrichment HE₂).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite change_of_base_precomp, change_of_base_postcomp.
    rewrite <- !functor_comp.
    apply maponpaths.
    exact (nat_trans_enrichment_to_comp Hτ x y).
  Qed.

  (**
   5. Change of base on the identity
   *)
  Definition change_of_base_enrichment_identity
             {C : univalent_category}
             (E : enrichment C V₁)
    : nat_trans_enrichment
        (λ _, identity _)
        (functor_id_enrichment (change_of_base_enrichment E))
        (change_of_base_functor_enrichment (functor_id_enrichment E)).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite precomp_arr_id, postcomp_arr_id.
    rewrite functor_id.
    apply idpath.
  Qed.

  (**
   6. Change of base on composition
   *)
  Definition change_of_base_enrichment_comp
             {C₁ C₂ C₃ : univalent_category}
             {G₁ : C₁ ⟶ C₂}
             {G₂ : C₂ ⟶ C₃}
             {E₁ : enrichment C₁ V₁}
             {E₂ : enrichment C₂ V₁}
             {E₃ : enrichment C₃ V₁}
             (EG₁ : functor_enrichment G₁ E₁ E₂)
             (EG₂ : functor_enrichment G₂ E₂ E₃)
    : nat_trans_enrichment
        (λ c, identity _)
        (functor_comp_enrichment
           (change_of_base_functor_enrichment EG₁)
           (change_of_base_functor_enrichment EG₂))
        (change_of_base_functor_enrichment (functor_comp_enrichment EG₁ EG₂)).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite precomp_arr_id, postcomp_arr_id.
    rewrite !id_right.
    rewrite functor_comp.
    apply idpath.
  Qed.
End ChangeOfBase.
