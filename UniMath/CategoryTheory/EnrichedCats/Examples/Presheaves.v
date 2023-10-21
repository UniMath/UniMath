(**********************************************************************

 Presheaves of enriched categories

 In this file, we define an enrichment for the category of presheaves.

 In the file `FunctorCategory.v`, we showed that the category of
 V-enriched functors between two V-enriched categories forms a V-enriched
 category as well. However, this does not capture all examples that
 one might want to have, such as the category of V-valued presheaves. If we were
 to use the category of V-enriched functors, then we only get V-valued presheaves
 on categories `C` enriched over `V`. As such, we do not naturally get
 all the examples that one might want to consider, such as presheaves
 over partial orders.

 If we assume that `V` is a complete symmetric monoidal closed category,
 then we can define an enrichment for the presheaves on `C` valued in
 `V` for all sufficiently small categories `C`. To define this
 enrichment, we need to define an object in `V` that represents the
 natural transformations between two functors `F, G : C ⟶ V`. This
 object is defined in two steps.
 1. We take the product of `F x ⊸ G x` for all `x : C`
    ([presheaf_enrichment_hom_prod]). This represents the data of the
    natural transformation.
 2. We take an equalizer ([presheaf_enrichment_hom]). The two maps of
    this equalizer represent the left hand side and the right hand side
    of the usual naturality condition. The natural condition is
    expressed in the language of `V`.
 The statement [presheaf_enrichment_naturality] shows how we can apply
 the naturality condition of natural transformations.

 We also need to define the identity and the composition for our
 enrichment. The approach is similar to how we define natural
 transformations. For example, for the identity, we first define the
 data of our transformation ([presheaf_enrichment_id_data]). In this
 definition, we express that the identity transformation is pointwise
 the identity morphism. Afterwards, we prove the naturality condition
 ([presheaf_enrichment_id_laws]), which, in this case, concretely means
 that our morphism actually maps to the equalizer. The idea is the same
 for the map that shows that global elements are the same as natural
 transformations ([presheaf_enrichment_from_arr]).

 To prove the laws for the enrichment, our argument is again similar to
 how we prove the laws for the presheaf category. To prove equations of
 natural transformations, we compare them pointwise. By using the
 universal property of the equalizer and the product, we can compare
 morphisms into the hom object 'pointwise' as well. The uniqueness for
 morphisms into an equalizer, allows us to compare the transformations
 as morphisms into a product, and by the uniqueness of morphisms into
 the product, we compare them for every projection. Since these
 projections represent the components of our natural transformation,
 the argument proceeds by considering the natural transformations
 pointwise.

 Content
 1. Hom objects of presheaves
 2. The identity for the enrichment
 3. Composition for the enrichment
 4. Global elements versus natural transformations
 5. Laws of the enrichment
 6. Enrichment for the presheaf category

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.HomFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section PresheafEnrichment.
  Context (V : sym_mon_closed_cat)
          (C : category)
          (EqV : Equalizers V)
          (PV : Products C V)
          (PV' : Products (∑ (x y : C), x --> y) V).

  (** * 1. Hom objects of presheaves *)
  Definition presheaf_enrichment_hom_prod
             (F G : C ⟶ V)
    : V
    := PV (λ x, F x ⊸ G x).

  Definition presheaf_enrichment_hom_eq_type
             (F G : C ⟶ V)
    : V
    := PV' (λ xyf, F (pr1 xyf) ⊸ G (pr12 xyf)).

  Definition presheaf_enrichment_hom_eq_left
             (F G : C ⟶ V)
    : presheaf_enrichment_hom_prod F G
      -->
      presheaf_enrichment_hom_eq_type F G.
  Proof.
    use ProductArrow.
    intros xyf.
    pose (x := pr1 xyf).
    pose (f := pr22 xyf).
    unfold presheaf_enrichment_hom_prod ; cbn.
    exact (ProductPr _ _ _ x
           · mon_linvunitor _
           · internal_from_arr (#G f) #⊗ identity _
           · internal_comp _ _ _).
  Defined.

  Definition presheaf_enrichment_hom_eq_right
             (F G : C ⟶ V)
    : presheaf_enrichment_hom_prod F G
      -->
      presheaf_enrichment_hom_eq_type F G.
  Proof.
    use ProductArrow.
    intros xyf.
    pose (y := pr12 xyf).
    pose (f := pr22 xyf).
    unfold presheaf_enrichment_hom_prod ; cbn.
    exact (ProductPr _ _ _ y
           · mon_rinvunitor _
           · identity _ #⊗ internal_from_arr (#F f)
           · internal_comp _ _ _).
  Defined.

  Definition presheaf_enrichment_hom
             (F G : C ⟶ V)
    : Equalizer _ _
    := EqV
         _ _
         (presheaf_enrichment_hom_eq_left F G)
         (presheaf_enrichment_hom_eq_right F G).

  Proposition presheaf_enrichment_naturality_help
              (F G : C ⟶ V)
              {x y : C}
              (f : x --> y)
    : (EqualizerArrow (presheaf_enrichment_hom F G)
       · presheaf_enrichment_hom_eq_left F G
       · ProductPr _ _ _ (x ,, y ,, f)) #⊗ identity _
      · internal_eval _ _
      =
      (EqualizerArrow (presheaf_enrichment_hom F G)
       · presheaf_enrichment_hom_eq_right F G
       · ProductPr _ _ _ (x ,, y ,, f)) #⊗ identity _
      · internal_eval _ _.
  Proof.
    do 3 apply maponpaths_2.
    apply EqualizerEqAr.
  Qed.

  Proposition presheaf_enrichment_naturality
              (F G : C ⟶ V)
              {x y : C}
              (f : x --> y)
    : (EqualizerArrow (presheaf_enrichment_hom F G) · ProductPr _ _ _ x) #⊗ identity _
      · internal_eval (F x) (G x)
      · # G f
      =
      (EqualizerArrow (presheaf_enrichment_hom F G) · ProductPr _ _ _ y) #⊗ identity _
      · identity _ #⊗ # F f
      · internal_eval (F y) (G y).
  Proof.
    refine (_ @ presheaf_enrichment_naturality_help F G f @ _).
    - refine (!_).
      etrans.
      {
        etrans.
        {
          do 2 apply maponpaths_2.
          unfold presheaf_enrichment_hom_eq_left.
          rewrite !assoc'.
          apply maponpaths.
          exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ (x ,, y ,, f)).
        }
        cbn.
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite tensor_id_id.
          rewrite !assoc.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        rewrite mon_lunitor_triangle.
        rewrite <- tensor_comp_id_r.
        rewrite mon_linvunitor_lunitor.
        apply tensor_id_id.
      }
      rewrite id_left.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      apply idpath.
    - etrans.
      {
        etrans.
        {
          do 2 apply maponpaths_2.
          unfold presheaf_enrichment_hom_eq_right.
          rewrite !assoc'.
          apply maponpaths.
          exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ (x ,, y ,, f)).
        }
        cbn.
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite tensor_comp_id_l.
          apply idpath.
        }
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- mon_triangle.
        rewrite <- tensor_comp_id_r.
        rewrite mon_rinvunitor_runitor.
        apply tensor_id_id.
      }
      rewrite id_left.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      apply idpath.
  Qed.

  (** * 2. The identity for the enrichment *)
  Definition presheaf_enrichment_id_data
             (F : C ⟶ V)
    : I_{V} --> presheaf_enrichment_hom_prod F F.
  Proof.
    use ProductArrow ; cbn.
    intro i.
    apply internal_id.
  Defined.

  Proposition presheaf_enrichment_id_laws
              (F : C ⟶ V)
    : presheaf_enrichment_id_data F · presheaf_enrichment_hom_eq_left F F
      =
      presheaf_enrichment_id_data F · presheaf_enrichment_hom_eq_right F F.
  Proof.
    use ProductArrow_eq.
    intros xyf.
    induction xyf as [ x [ y f ]].
    unfold presheaf_enrichment_hom_eq_left, presheaf_enrichment_hom_eq_right.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    cbn.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite !internal_beta.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_l.
      unfold internal_from_arr.
      rewrite internal_beta.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- mon_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_rinvunitor_runitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_id.
      rewrite internal_beta.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lunitor.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_lunitor_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_linvunitor_lunitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    rewrite !assoc.
    rewrite tensor_split.
    unfold internal_id.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite <- tensor_lunitor.
    rewrite !assoc.
    rewrite <- tensor_comp_id_l.
    apply idpath.
  Qed.

  Definition presheaf_enrichment_id
             (F : C ⟶ V)
    :  I_{V} --> presheaf_enrichment_hom F F.
  Proof.
    use EqualizerIn.
    - exact (presheaf_enrichment_id_data F).
    - exact (presheaf_enrichment_id_laws F).
  Defined.

  (** * 3. Composition for the enrichment *)
  Definition presheaf_enrichment_comp_data
             (F G H : C ⟶ V)
    : presheaf_enrichment_hom G H ⊗ presheaf_enrichment_hom F G
      -->
      presheaf_enrichment_hom_prod F H.
  Proof.
    use ProductArrow.
    intro x ; cbn.
    exact ((EqualizerArrow _ · ProductPr _ _ _ x) #⊗ (EqualizerArrow _ · ProductPr _ _ _ x)
           · internal_comp _ _ _).
  Defined.

  Proposition presheaf_enrichment_comp_laws
              (F G H : C ⟶ V)
    : presheaf_enrichment_comp_data F G H · presheaf_enrichment_hom_eq_left F H
      =
      presheaf_enrichment_comp_data F G H · presheaf_enrichment_hom_eq_right F H.
  Proof.
    use ProductArrow_eq.
    intros xyf.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    cbn.
    etrans.
    {
      rewrite !assoc.
      unfold presheaf_enrichment_comp_data.
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    cbn.
    etrans.
    {
      rewrite !assoc.
      unfold presheaf_enrichment_comp_data.
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    refine (!_).
    use internal_funext.
    intros a h.
    induction xyf as [ x [ y f ]] ; cbn.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    etrans.
    {
      do 5 apply maponpaths.
      apply internal_beta.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lunitor.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_lunitor_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_linvunitor_lunitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply internal_beta.
    }
    etrans.
    {
      rewrite !assoc.
      do 3 apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 5 apply maponpaths.
      apply internal_beta.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_l.
      unfold internal_from_arr.
      rewrite internal_beta.
      rewrite tensor_comp_id_l.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- mon_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_rinvunitor_runitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      apply internal_beta.
    }
    etrans.
    {
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      exact (presheaf_enrichment_naturality G H f).
    }
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      apply maponpaths_2.
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      exact (presheaf_enrichment_naturality F G f).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_split.
    rewrite <- !tensor_split'.
    rewrite <- !tensor_comp_mor.
    rewrite !id_right.
    apply idpath.
  Qed.

  Definition presheaf_enrichment_comp
             (F G H : C ⟶ V)
    : presheaf_enrichment_hom G H ⊗ presheaf_enrichment_hom F G
      -->
      presheaf_enrichment_hom F H.
  Proof.
    use EqualizerIn.
    - exact (presheaf_enrichment_comp_data F G H).
    - exact (presheaf_enrichment_comp_laws F G H).
  Defined.

  (** * 4. Global elements versus natural transformations *)
  Definition presheaf_enrichment_from_arr_data
             {F G : C ⟶ V}
             (τ : F ⟹ G)
    : I_{V} --> presheaf_enrichment_hom_prod F G.
  Proof.
    use ProductArrow.
    exact (λ x, internal_from_arr (τ x)).
  Defined.

  Proposition presheaf_enrichment_from_arr_laws
              {F G : C ⟶ V}
              (τ : F ⟹ G)
    : presheaf_enrichment_from_arr_data τ · presheaf_enrichment_hom_eq_left F G
      =
      presheaf_enrichment_from_arr_data τ · presheaf_enrichment_hom_eq_right F G.
  Proof.
    use ProductArrow_eq.
    intros xyf.
    induction xyf as [ x [ y f ]].
    unfold presheaf_enrichment_hom_eq_left, presheaf_enrichment_hom_eq_right.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (ProductPrCommutes (∑ (x y : C), x --> y) V _ _ _ _ _).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (ProductPrCommutes C V _ _ _ _ _).
    }
    cbn.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite !internal_beta.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_l.
      unfold internal_from_arr.
      rewrite internal_beta.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- mon_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_rinvunitor_runitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite internal_beta.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lunitor.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_lunitor_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_linvunitor_lunitor.
      apply tensor_id_id.
    }
    rewrite id_left.
    rewrite !assoc.
    rewrite tensor_split.
    unfold internal_id.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      unfold internal_from_arr.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !assoc'.
    rewrite <- !tensor_lunitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_id_l.
    rewrite !assoc'.
    do 2 apply maponpaths.
    exact (!(nat_trans_ax τ _ _ f)).
  Qed.

  Definition presheaf_enrichment_from_arr
             {F G : C ⟶ V}
             (τ : F ⟹ G)
    : I_{V} --> presheaf_enrichment_hom F G.
  Proof.
    use EqualizerIn.
    - exact (presheaf_enrichment_from_arr_data τ).
    - exact (presheaf_enrichment_from_arr_laws τ).
  Defined.

  Section ToArr.
    Context {F G : C ⟶ V}
            (τ : I_{ V} --> presheaf_enrichment_hom F G).

    Definition presheaf_enrichment_to_arr_data
      : nat_trans_data F G
      := λ x, internal_to_arr (τ · EqualizerArrow _ · ProductPr _ _ _ x).

    Arguments presheaf_enrichment_to_arr_data /.

    Proposition presheaf_enrichment_to_arr_laws
      : is_nat_trans F G presheaf_enrichment_to_arr_data.
    Proof.
      intros x y f ; cbn.
      unfold internal_to_arr.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        exact (presheaf_enrichment_naturality F G f).
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite <- !tensor_comp_id_r.
      rewrite !assoc.
      apply idpath.
    Qed.

    Definition presheaf_enrichment_to_arr
      : F ⟹ G.
    Proof.
      use make_nat_trans.
      - exact presheaf_enrichment_to_arr_data.
      - exact presheaf_enrichment_to_arr_laws.
    Defined.
  End ToArr.

  Definition presheaf_enrichment_data
    : enrichment_data [C , V] V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact presheaf_enrichment_hom.
    - exact presheaf_enrichment_id.
    - exact presheaf_enrichment_comp.
    - exact (λ F G τ, presheaf_enrichment_from_arr τ).
    - exact (λ F G τ, presheaf_enrichment_to_arr τ).
  Defined.

  (** * 5. Laws of the enrichment *)
  Proposition presheaf_enrichment_laws
    : enrichment_laws presheaf_enrichment_data.
  Proof.
    repeat split.
    - intros F G ; cbn.
      use EqualizerInsEq.
      unfold presheaf_enrichment_comp.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply EqualizerCommutes.
      }
      use ProductArrow_eq.
      intro x.
      unfold presheaf_enrichment_comp_data.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        do 2 apply maponpaths_2.
        unfold presheaf_enrichment_id.
        rewrite !assoc.
        rewrite EqualizerCommutes.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_id.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite tensor_lunitor.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite mon_lunitor_triangle.
      rewrite <- !tensor_comp_mor.
      rewrite id_left, !id_right.
      rewrite !assoc'.
      apply idpath.
    - intros F G ; cbn.
      use EqualizerInsEq.
      unfold presheaf_enrichment_comp.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply EqualizerCommutes.
      }
      use ProductArrow_eq.
      intro x.
      unfold presheaf_enrichment_comp_data.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        unfold presheaf_enrichment_id.
        rewrite !assoc.
        rewrite EqualizerCommutes.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      use internal_funext.
      intros a h.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_r_id_r.
      }
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        apply maponpaths_2.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_id.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite tensor_lunitor.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_l_id_l.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply tensor_comp_r_id_l.
      }
      rewrite !assoc.
      apply maponpaths_2.
      apply mon_triangle.
    - intros F₁ F₂ F₃ F₄ ; cbn.
      use EqualizerInsEq.
      unfold presheaf_enrichment_comp.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply EqualizerCommutes.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply EqualizerCommutes.
      }
      refine (!_).
      use ProductArrow_eq.
      intro x.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite !assoc.
      rewrite <- !tensor_comp_mor.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_mor.
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply EqualizerCommutes.
        }
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite id_left.

      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply EqualizerCommutes.
        }
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite id_left.
      refine (!_).
      etrans.
      {
        rewrite !tensor_comp_mor.
        rewrite !tensor_comp_l_id_r.
        rewrite !assoc.
        rewrite <- tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        rewrite !tensor_comp_mor.
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        apply idpath.
      }
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split.
          apply idpath.
        }
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite <- tensor_comp_mor.
        rewrite id_right, id_left.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split'.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_mor.
        rewrite id_right, id_left.
        rewrite <- tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite internal_assoc.
      rewrite !assoc.
      apply idpath.
    - intros F G τ ; cbn.
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      unfold presheaf_enrichment_to_arr_data, presheaf_enrichment_from_arr.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply EqualizerCommutes.
      }
      unfold presheaf_enrichment_from_arr_data.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      apply internal_to_from_arr.
    - intros F G τ ; cbn.
      unfold presheaf_enrichment_from_arr, presheaf_enrichment_to_arr.
      use EqualizerInsEq.
      rewrite EqualizerCommutes.
      unfold presheaf_enrichment_from_arr_data.
      use ProductArrow_eq.
      intros x.
      etrans.
      {
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      cbn.
      unfold presheaf_enrichment_to_arr_data.
      apply internal_from_to_arr.
    - intros F.
      use nat_trans_eq ; [ apply homset_property | ].
      intros x ; cbn.
      unfold presheaf_enrichment_to_arr_data, presheaf_enrichment_id.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply EqualizerCommutes.
      }
      unfold presheaf_enrichment_from_arr_data.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      apply internal_to_arr_id.
    - intros F G H τ θ.
      use nat_trans_eq ; [ apply homset_property | ].
      intros x ; cbn.
      unfold presheaf_enrichment_to_arr_data, presheaf_enrichment_from_arr.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply EqualizerCommutes.
        }
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_comp_mor.
        rewrite !assoc.
        rewrite !EqualizerCommutes.
        etrans.
        {
          apply maponpaths.
          exact (ProductPrCommutes C V _ _ _ _ _).
        }
        apply maponpaths_2.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      unfold internal_to_arr.
      rewrite !assoc.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        unfold internal_from_arr.
        rewrite internal_beta.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_lunitor.
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      refine (_ @ mon_linvunitor_lunitor _).
      apply maponpaths_2.
      refine (_ @ id_right _).
      rewrite !assoc'.
      apply maponpaths.
      rewrite mon_lunitor_triangle.
      rewrite <- tensor_comp_id_r.
      rewrite mon_linvunitor_lunitor.
      apply tensor_id_id.
  Qed.

  (** * 6. Enrichment for the presheaf category *)
  Definition presheaf_enrichment
    : enrichment [C , V] V.
  Proof.
    simple refine (_ ,, _).
    - exact presheaf_enrichment_data.
    - exact presheaf_enrichment_laws.
  Defined.
End PresheafEnrichment.
