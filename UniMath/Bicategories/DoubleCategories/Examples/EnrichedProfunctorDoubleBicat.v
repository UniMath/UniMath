(*****************************************************************************************

 The Verity double bicategory of enriched profunctors

 In this file, we construct the Verity double bicategory of enriched profunctors. Suppose
 that `V` is a univalent Benabou cosmos (i.e., a univalent symmetric monoidal closed category
 that is both complete and cocomplete). Then we define the following Verity double bicategory:
 - Objects: univalent categories together with a `V`-enrichment
 - Horizontal morphisms: functors together with `V`-enrichment
 - Vertical morphisms: `V`-enriched profunctors
 - Horizontal 2-cells: enriched natural transformations of functors
 - Vertical 2-cells: enriched natural transformations of profunctors

 The first interesting aspect of this construction is that essentially, it closely follows
 the development of the Verity double bicategory of univalent categories and profunctors.
 Enriched profunctors and operations on them are defined similarly compared to profunctors
 of categories. In addition, the proofs of the many laws follow the same steps. The only
 difference is that we need to take many extra steps due to the fact that we are enriching
 over an arbitrary symmetric monoidal category rather than just sets.

 From a technical point of view, it has to be noted that this construction is very much
 split across multiple files. In the file `ProfunctorDoubleBicat.v`, all laws for Verity
 double bicategories are proven. However, in the enriched case, most of these laws are
 actually proven in various files in the directory `Profunctors/Composition`. The reason for
 that is purely technical and not conceptual at all: this increased the speed of type
 checking. If these proofs were to be moved to this file in their corresponding statement,
 then the `Qeds` would be significantly slower.

 Finally, we show that this double bicategory is gregarious univalent. This follows from
 the fact that the bicategory of univalent enriched categories is univalent.

 Contents
 1. The 2-sided displayed category of the Verity bicategory of enriched profunctors
 2. The vertical bicategory of enriched profunctors
 3. The whiskering operations
 4. More laws
 5. The Verity double bicategory of enriched categories and profunctors

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
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
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.RepresentableLaws.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.Core.

Local Open Scope cat.
Local Open Scope double_bicat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section Enriched.
  Context {V : benabou_cosmos}
          (HV : is_univalent V).

  Local Notation "∁" := (op2_bicat (bicat_of_enriched_cats V)).

  (** * 1. The 2-sided displayed category of the Verity bicategory of enriched profunctors *)
  Definition enriched_profunctor_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor ∁ ∁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (C₁ C₂ : enriched_cat V), C₁ ↛e C₂).
    - exact (λ (C₁ C₂ D₁ D₂ : enriched_cat V)
               (P : C₁ ↛e D₁)
               (Q : C₂ ↛e D₂)
               (F : enriched_functor C₁ C₂)
               (G : enriched_functor D₁ D₂),
             enriched_profunctor_square
               (enriched_functor_enrichment F)
               (enriched_functor_enrichment G)
               P
               Q).
  Defined.

  Proposition enriched_profunctor_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp enriched_profunctor_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ C D P,
             id_h_enriched_profunctor_square P).
    - exact (λ C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ F₁ F₂ G₁ G₂ τ₁ τ₂,
             comp_h_enriched_profunctor_square τ₁ τ₂).
  Defined.

  Definition enriched_profunctor_twosided_disp_cat_data
    : twosided_disp_cat_data ∁ ∁.
  Proof.
    simple refine (_ ,, _).
    - exact enriched_profunctor_twosided_disp_cat_ob_mor.
    - exact enriched_profunctor_twosided_disp_cat_id_comp.
  Defined.

  Definition enriched_profunctor_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact ∁.
    - exact enriched_profunctor_twosided_disp_cat_data.
  Defined.

  (** * 2. The vertical bicategory of enriched profunctors *)
  Definition enriched_profunctor_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp enriched_profunctor_ver_sq_bicat.
  Proof.
    split.
    - split.
      + exact (λ (C : enriched_cat V), identity_enriched_profunctor C).
      + exact (λ (C₁ C₂ C₃ : enriched_cat V)
                 (P : C₁ ↛e C₂)
                 (Q : C₂ ↛e C₃),
               comp_enriched_profunctor P Q).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P Q : C₁ ↛e C₂),
             enriched_profunctor_transformation P Q).
  Defined.

  Definition enriched_profunctor_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells enriched_profunctor_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P : C₁ ↛e C₂),
             enriched_profunctor_id_transformation P).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P : C₁ ↛e C₂),
             lunitor_enriched_profunctor P).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P : C₁ ↛e C₂),
             runitor_enriched_profunctor P).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P : C₁ ↛e C₂),
             linvunitor_enriched_profunctor P).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P : C₁ ↛e C₂),
             rinvunitor_enriched_profunctor P).
    - exact (λ (C₁ C₂ C₃ C₄ : enriched_cat V)
               (P : C₁ ↛e C₂)
               (Q : C₂ ↛e C₃)
               (R : C₃ ↛e C₄),
             rassociator_enriched_profunctor P Q R).
    - exact (λ (C₁ C₂ C₃ C₄ : enriched_cat V)
               (P : C₁ ↛e C₂)
               (Q : C₂ ↛e C₃)
               (R : C₃ ↛e C₄),
             lassociator_enriched_profunctor P Q R).
    - exact (λ (C₁ C₂ : enriched_cat V)
               (P Q R : C₁ ↛e C₂)
               (τ : enriched_profunctor_transformation P Q)
               (θ : enriched_profunctor_transformation Q R),
             enriched_profunctor_comp_transformation τ θ).
    - exact (λ (C₁ C₂ C₃ : enriched_cat V)
               (P : C₁ ↛e C₂)
               (Q₁ Q₂ : C₂ ↛e C₃)
               (τ : enriched_profunctor_transformation Q₁ Q₂),
             lwhisker_enriched_profunctor P τ).
    - exact (λ (C₁ C₂ C₃ : enriched_cat V)
               (P₁ P₂ : C₁ ↛e C₂)
               (Q : C₂ ↛e C₃)
               (τ : enriched_profunctor_transformation P₁ P₂),
             rwhisker_enriched_profunctor τ Q).
  Defined.

  Proposition enriched_profunctor_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws enriched_profunctor_ver_sq_bicat_id_comp_cells.
  Proof.
    repeat split.
    - intros C₁ C₂ P Q τ.
      use eq_enriched_profunctor_transformation ; intros y x ; cbn.
      apply id_left.
    - intros C₁ C₂ P Q τ.
      use eq_enriched_profunctor_transformation ; intros y x ; cbn.
      apply id_right.
    - intros C₁ C₂ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
      use eq_enriched_profunctor_transformation ; intros y x ; cbn.
      apply assoc.
    - intros C₁ C₂ C₃ P Q.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intros y.
      refine (lwhisker_enriched_profunctor_mor_comm _ _ _ _ _ @ _) ; cbn.
      rewrite tensor_id_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros C₁ C₂ C₃ P Q.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intros y.
      refine (rwhisker_enriched_profunctor_mor_comm _ _ _ _ _ @ _) ; cbn.
      rewrite tensor_id_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros C₁ C₂ C₃ P Q₁ Q₂ Q₃ τ₁ τ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intros y.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      cbn.
      rewrite <- tensor_comp_id_l.
      apply idpath.
    - intros C₁ C₂ C₃ P₁ P₂ P₃ Q τ₁ τ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intro y.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      cbn.
      rewrite <- tensor_comp_id_r.
      apply idpath.
    - intros C₁ C₂ P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intro y.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply lunitor_enriched_profunctor_mor_comm.
      }
      refine (enriched_profunctor_transformation_rmap_e _ _ _ _ @ _).
      refine (!_).
      rewrite !assoc.
      apply maponpaths_2.
      apply lunitor_enriched_profunctor_mor_comm.
    - intros C₁ C₂ P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intro y.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply runitor_enriched_profunctor_mor_comm.
      }
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply enriched_profunctor_transformation_lmap_e.
      }
      refine (!_).
      rewrite !assoc.
      apply maponpaths_2.
      apply runitor_enriched_profunctor_mor_comm.
    - intros C₁ C₂ C₃ C₄ P Q R₁ R₂ τ.
      apply enriched_lwhisker_lwhisker.
    - intros C₁ C₂ C₃ C₄ P Q₁ Q₂ R τ.
      apply enriched_rwhisker_lwhisker.
    - intros C₁ C₂ C₃ C₄ P₁ P₂ Q R τ.
      apply enriched_rwhisker_rwhisker.
    - intros C₁ C₂ C₃ P₁ P₂ Q₁ Q₂ τ₁ τ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intros y.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply lwhisker_enriched_profunctor_mor_comm.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        apply rwhisker_enriched_profunctor_mor_comm.
      }
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite <- tensor_split'.
      apply idpath.
    - intros C₁ C₂ P.
      exact (inv_enriched_profunctor_transformation_right
               _
               (is_iso_lunitor_enriched_profunctor P)).
    - intros C₁ C₂ P.
      exact (inv_enriched_profunctor_transformation_left
               _
               (is_iso_lunitor_enriched_profunctor P)).
    - intros C₁ C₂ P.
      exact (inv_enriched_profunctor_transformation_right
               _
               (is_iso_runitor_enriched_profunctor P)).
    - intros C₁ C₂ P.
      exact (inv_enriched_profunctor_transformation_left
               _
               (is_iso_runitor_enriched_profunctor P)).
    - intros C₁ C₂ C₃ C₄ P Q R.
      exact (inv_enriched_profunctor_transformation_right
               _
               (is_iso_lassociator_enriched_profunctor P Q R)).
    - intros C₁ C₂ C₃ C₄ P Q R.
      exact (inv_enriched_profunctor_transformation_left
               _
               (is_iso_lassociator_enriched_profunctor P Q R)).
    - intros C₁ C₂ C₃ P Q.
      apply enriched_triangle_law.
    - intros C₁ C₂ C₃ C₄ C₅ P₁ P₂ P₃ P₄.
      apply enriched_pentagon_law.
  Qed.

  Definition enriched_profunctor_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact enriched_profunctor_ver_sq_bicat.
    - exact enriched_profunctor_ver_sq_bicat_ver_id_comp.
    - exact enriched_profunctor_ver_sq_bicat_id_comp_cells.
    - exact enriched_profunctor_ver_sq_bicat_prebicat_laws.
    - abstract
        (intros C₁ C₂ P Q ;
         apply isaset_enriched_profunctor_transformation).
  Defined.

  Definition enriched_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq enriched_profunctor_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ C₁ C₂ F,
             id_v_enriched_profunctor_square _).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ τ θ,
             comp_v_enriched_profunctor_square τ θ).
  Defined.

  Definition enriched_profunctor_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact enriched_profunctor_ver_bicat_sq_bicat.
    - exact enriched_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  (** * 3. The whiskering operations *)
  Definition enriched_profunctor_double_bicat_whiskering
    : double_bicat_whiskering enriched_profunctor_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ _ _ _ _ _ _ _ _ _ τ s,
             lwhisker_enriched_profunctor_square τ s).
    - exact (λ _ _ _ _ _ _ _ _ _ τ s,
             rwhisker_enriched_profunctor_square τ s).
    - exact (λ _ _ _ _ _ _ _ _ _ (τ : enriched_nat_trans _ _) s,
             uwhisker_enriched_profunctor_square τ s).
    - exact (λ _ _ _ _ _ _ _ _ _ (τ : enriched_nat_trans _ _) s,
             dwhisker_enriched_profunctor_square τ s).
  Defined.

  Definition enriched_profunctor_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact enriched_profunctor_ver_bicat_sq_bicat_ver_id_comp.
    - exact enriched_profunctor_double_bicat_whiskering.
  Defined.

  (** * 4. More laws *)
  Proposition enriched_profunctor_lwhisker_square_id_comp_law
    : lwhisker_square_id_comp_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x.
      apply id_left.
    - intros C₁ C₂ C₃ C₄ F G P₁ P₂ P₃ Q τ₁ τ₂ θ.
      use eq_enriched_profunctor_transformation ; intros z x.
      apply assoc'.
  Qed.

  Proposition enriched_profunctor_rwhisker_square_id_comp_law
    : rwhisker_square_id_comp_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply id_right.
    - intros C₁ C₂ C₃ C₄ F G P₁ P₂ P₃ Q τ₁ τ₂ θ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply assoc.
  Qed.

  Proposition enriched_profunctor_uwhisker_square_id_comp_law
    : uwhisker_square_id_comp_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      rewrite enriched_from_arr_id.
      rewrite !assoc'.
      rewrite rmap_e_id.
      rewrite mon_linvunitor_lunitor.
      apply id_right.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ G P Q τ₁ τ₂ θ.
      refine (_ @ uwhisker_enriched_profunctor_square_comp _ _ _).
      cbn.
      apply maponpaths_2.
      apply isaprop_nat_trans_enrichment.
  Qed.

  Proposition enriched_profunctor_dwhisker_square_id_comp_law
    : dwhisker_square_id_comp_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      rewrite enriched_from_arr_id.
      rewrite !assoc'.
      rewrite lmap_e_id.
      rewrite mon_linvunitor_lunitor.
      apply id_right.
    - intros C₁ C₂ C₃ C₄ F G₁ G₂ G₃ P Q τ₁ τ₂ θ.
      refine (_ @ dwhisker_enriched_profunctor_square_comp _ _ _).
      cbn.
      apply maponpaths_2.
      apply isaprop_nat_trans_enrichment.
  Qed.

  Proposition enriched_profunctor_whisker_square_compatible
    : whisker_square_compatible
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_whisker_square_compatible.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ G₁ G₂ P Q τ₁ τ₂ θ.
      apply dwhisker_uwhisker_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ G P₁ P₂ Q τ₁ τ₂ θ.
      apply lwhisker_uwhisker_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ G P Q₁ Q₂ τ₁ τ₂ θ.
      apply rwhisker_uwhisker_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ F G₁ G₂ P₁ P₂ Q τ₁ τ₂ θ.
      apply lwhisker_dwhisker_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ F G₁ G₂ P Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
      apply rwhisker_dwhisker_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ F G P₁ P₂ Q₁ Q₂ τ₁ τ₂ θ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply assoc'.
  Qed.

  Proposition enriched_profunctor_whisker_square_id_square
    : whisker_square_id_square
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ P Q τ.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros C₁ C₂ F G τ.
      apply uwhisker_enriched_profunctor_square_id_square.
  Qed.

  Proposition enriched_profunctor_whisker_square_comp_square
    : whisker_square_comp_square
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_whisker_square_comp_square.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂.
      apply uwhisker_comp_v_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F G H₁ H₂ P₁ P₂ Q₁ Q₂ τ θ₁ θ₂.
      apply dwhisker_comp_v_enriched_profunctor_square.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F G₁ G₂ H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂.
      apply comp_v_enriched_profunctor_square_uwhisker.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P₁ P₂ Q R τ θ₁ θ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply assoc.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q₁ Q₂ R τ θ₁ θ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply assoc'.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q R₁ R₂ τ θ₁ θ₂.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply assoc.
  Qed.

  Proposition enriched_profunctor_whisker_square_bicat_law
    : whisker_square_bicat_law enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact enriched_profunctor_lwhisker_square_id_comp_law.
    - exact enriched_profunctor_rwhisker_square_id_comp_law.
    - exact enriched_profunctor_uwhisker_square_id_comp_law.
    - exact enriched_profunctor_dwhisker_square_id_comp_law.
    - exact enriched_profunctor_whisker_square_compatible.
    - exact enriched_profunctor_whisker_square_id_square.
    - exact enriched_profunctor_whisker_square_comp_square.
  Qed.

  Proposition enriched_profunctor_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₉ P₁ P₂ Q₁ Q₂ R₁ R₂ F₁ F₂ G₁ G₂ H₁ H₂ τ₁ τ₂ θ₁ θ₂.
      apply enriched_profunctor_interchange.
    - intro C.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply idpath.
    - intros C₁ C₂ C₃ P Q.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      use from_comp_enriched_profunctor_eq.
      intros y.
      rewrite id_right.
      rewrite (comp_v_enriched_profunctor_square_mor_comm
                 (id_h_enriched_profunctor_square P)
                 (id_h_enriched_profunctor_square Q)).
      cbn.
      rewrite tensor_id_id.
      apply id_left.
    - intros C₁ C₂ C₃ P Q.
      use eq_enriched_profunctor_transformation ; intros z x ; cbn.
      apply idpath.
  Qed.

  Proposition enriched_profunctor_associator_cylinder_law
    : associator_cylinder_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ F₁ F₂ F₃ G₁ G₂ G₃ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
      pose (dwhisker_rassociator_enriched_profunctor
              τ₁ τ₂ τ₃
              (disp_rassociator (pr2 G₁) (pr2 G₂) (pr2 G₃))
              (disp_rassociator (pr2 F₁) (pr2 F₂) (pr2 F₃)))
        as p.
      refine (_ @ p @ _).
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ F₁ F₂ F₃ F₄ P₁ P₂ P₃ Q₁ Q₂ Q₃ τ₁ τ₂ τ₃.
      apply lwhisker_lassociator_enriched_profunctor.
  Qed.

  Proposition enriched_profunctor_lunitor_cylinder_law
    : lunitor_cylinder_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      apply dwhisker_linvunitor_enriched_profunctor.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      apply lwhisker_lunitor_enriched_profunctor.
  Qed.

  Proposition enriched_profunctor_runitor_cylinder_law
    : runitor_cylinder_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      pose (dwhisker_rinvunitor_enriched_profunctor
              τ
              (disp_rinvunitor (pr2 G)) (disp_rinvunitor (pr2 F)))
        as p.
      refine (_ @ p @ _).
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
    - intros C₁ C₂ C₃ C₄ F G P Q τ.
      apply lwhisker_runitor_enriched_profunctor.
  Qed.

  Proposition enriched_profunctor_comp_cylinder_law
    : comp_cylinder_law
        enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    split.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ F₃ P₁ P₂ P₁' P₂' Q₁ Q₂ Q₁' Q₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂'.
      apply enriched_profunctor_square_comp_cylinder_left.
    - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ F₃ F₄ F₅ F₆ F₇ F₈ P₁ P₂ P₃ τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂'.
      intros p q.
      pose (H₁ := disp_vcomp2
                    (disp_lwhisker (pr2 F₆) (pr2 θ₂))
                    (disp_rwhisker (pr2 F₇) (pr2 θ₁))).
      pose (H₂ := disp_vcomp2
                    (disp_lwhisker (pr2 F₂) (pr2 τ₂))
                    (disp_rwhisker (pr2 F₃) (pr2 τ₁))).
      refine (_ @ enriched_profunctor_square_comp_cylinder_down _ _ _ _ p q H₁ H₂ @ _).
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
      + use eq_enriched_profunctor_transformation.
        intros x y.
        apply idpath.
  Qed.

  Proposition enriched_profunctor_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    refine (_ ,, _ ,, _ ,, _).
    - exact enriched_profunctor_associator_cylinder_law.
    - exact enriched_profunctor_lunitor_cylinder_law.
    - exact enriched_profunctor_runitor_cylinder_law.
    - exact enriched_profunctor_comp_cylinder_law.
  Qed.

  Proposition enriched_profunctor_double_bicat_laws
    : double_bicat_laws enriched_profunctor_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact enriched_profunctor_whisker_square_bicat_law.
    - exact enriched_profunctor_double_bicat_id_comp_square_laws.
    - exact enriched_profunctor_double_bicat_cylinder_laws.
    - intro ; intros.
      apply isaset_enriched_profunctor_transformation.
  Qed.

  (** * 5. The Verity double bicategory of enriched categories and profunctors *)
  Definition enriched_profunctor_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact enriched_profunctor_ver_bicat_sq_id_comp_whisker.
    - exact enriched_profunctor_double_bicat_laws.
  Defined.

  (** * 6. 2-cells versus squares *)
  Definition enriched_profunctor_vertically_saturated
    : vertically_saturated
        enriched_profunctor_verity_double_bicat.
  Proof.
    intros C₁ C₂ P Q ; cbn in *.
    use isweq_iso.
    - exact enriched_profunctor_square_to_transformation.
    - abstract
        (intros τ ;
         use eq_enriched_profunctor_transformation ;
         intros y x ; cbn ;
         rewrite id_right ;
         apply idpath).
    - abstract
        (intros τ ;
         use eq_enriched_profunctor_transformation ;
         intros y x ; cbn ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition profunctor_square_to_enriched_nat_trans
             {C₁ C₂ : enriched_profunctor_verity_double_bicat}
             {F G : C₁ --> C₂}
             (τ : square_double_bicat F G (id_h _) (id_h _))
    : F ==> G.
  Proof.
    use make_enriched_nat_trans.
    - exact (square_to_enriched_nat_trans τ).
    - exact (square_to_enriched_nat_trans_enrichment τ).
  Defined.

  Proposition profunctor_square_to_enriched_nat_trans_left
              {C₁ C₂ : enriched_profunctor_verity_double_bicat}
              {F G : C₁ --> C₂}
              (τ : F ==> G)
    : profunctor_square_to_enriched_nat_trans (horizontal_cell_to_square τ) = τ.
  Proof.
    use eq_enriched_nat_trans.
    apply profunctor_square_to_enriched_nat_trans_left_point.
  Qed.

  Proposition profunctor_square_to_enriched_nat_trans_left_right
              {C₁ C₂ : enriched_profunctor_verity_double_bicat}
              {F G : C₁ --> C₂}
              (τ : square_double_bicat F G (id_h _) (id_h _))
    : horizontal_cell_to_square (profunctor_square_to_enriched_nat_trans τ) = τ.
  Proof.
    use eq_enriched_profunctor_transformation.
    apply profunctor_square_to_enriched_nat_trans_left_right_point.
  Qed.

  Definition enriched_profunctor_horizontally_saturated
    : horizontally_saturated
        enriched_profunctor_verity_double_bicat.
  Proof.
    intros C₁ C₂ F G.
    use isweq_iso.
    - exact profunctor_square_to_enriched_nat_trans.
    - exact profunctor_square_to_enriched_nat_trans_left.
    - exact profunctor_square_to_enriched_nat_trans_left_right.
  Defined.

  Definition enriched_profunctor_is_weak_double_cat
    : is_weak_double_cat enriched_profunctor_verity_double_bicat.
  Proof.
    split.
    - exact enriched_profunctor_vertically_saturated.
    - exact enriched_profunctor_horizontally_saturated.
  Defined.

  (** * 7. Companion pairs of profunctors *)
  Definition all_companions_enriched_profunctor_verity_double_bicat
    : all_companions enriched_profunctor_verity_double_bicat.
  Proof.
    refine (λ C₁ C₂ F,
            representable_enriched_profunctor_left (enriched_functor_enrichment F)
            ,,
            _).
    use make_are_companions ; cbn.
    - apply representable_enriched_profunctor_left_unit.
    - apply representable_enriched_profunctor_left_counit.
    - apply representable_enriched_profunctor_left_left_eq.
    - abstract
        (refine (_ @ representable_enriched_profunctor_left_right_eq _) ;
         use eq_enriched_profunctor_transformation ; intros z x ;
         apply idpath).
  Defined.

  Definition all_conjoints_enriched_cat_profunctor_verity_double_bicat
    : all_conjoints enriched_profunctor_verity_double_bicat.
  Proof.
    refine (λ C₁ C₂ F,
            representable_enriched_profunctor_right (enriched_functor_enrichment F)
            ,,
            _).
    use make_are_conjoints ; cbn.
    - apply representable_enriched_profunctor_right_unit.
    - apply representable_enriched_profunctor_right_counit.
    - apply representable_enriched_profunctor_right_left_eq.
    - abstract
        (refine (_ @ representable_enriched_profunctor_right_right_eq _) ;
         use eq_enriched_profunctor_transformation ; intros z x ;
         apply idpath).
  Defined.

  (** * 8. Vertical invertible 2-cells of enriched profunctors *)
  Definition enriched_profunctor_nat_iso_weq_vertible_invertible_2cell
             {C₁ C₂ : enriched_profunctor_verity_double_bicat}
             {P Q : C₁ -|-> C₂}
             (τ : P =|=> Q)
    : is_iso_enriched_profunctor_transformation τ
      ≃
      is_invertible_2cell τ.
  Proof.
    use weqimplimpl.
    - intros Hτ.
      use make_is_invertible_2cell.
      + exact (inv_enriched_profunctor_transformation _ Hτ).
      + apply inv_enriched_profunctor_transformation_right.
      + apply inv_enriched_profunctor_transformation_left.
    - intros Hτ y x.
      use make_is_z_isomorphism.
      + exact (pr1 (Hτ^-1) y x).
      + split.
        * abstract
            (exact (from_eq_enriched_profunctor_transformation (vcomp_rinv Hτ) y x)).
        * abstract
            (exact (from_eq_enriched_profunctor_transformation (vcomp_linv Hτ) y x)).
    - apply isaprop_is_iso_enriched_profunctor_transformation.
    - apply isaprop_is_invertible_2cell.
  Defined.

  (** * 9. The local univalence of the Verity double bicategory of squares *)
  Definition ver_locally_enriched_profunctor_verity_double_bicat
    : ver_locally_univalent enriched_profunctor_verity_double_bicat.
  Proof.
    intros C₁ C₂ P Q.
    use weqhomot.
    - refine (weqfibtototal _ _ enriched_profunctor_nat_iso_weq_vertible_invertible_2cell
              ∘ _)%weq.
      apply enriched_profunctor_univalent_cat.
      exact HV.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_invertible_2cell.
      }
      use eq_enriched_profunctor_transformation.
      intros x y ; cbn.
      apply idpath.
  Qed.

  Definition locally_univalent_enriched_profunctor_verity_double_bicat
    : locally_univalent_verity_double_bicat enriched_profunctor_verity_double_bicat.
  Proof.
    split.
    - use op2_bicat_is_univalent_2_1.
      apply is_univalent_2_1_bicat_of_enriched_cats.
    - exact ver_locally_enriched_profunctor_verity_double_bicat.
  Defined.

  (** * 10. The global univalence of the Verity double bicategory of squares *)
  Definition hor_globally_univalent_enriched_profunctor_verity_double_bicat
    : hor_globally_univalent enriched_profunctor_verity_double_bicat.
  Proof.
    use op2_bicat_is_univalent_2_0.
    - apply is_univalent_2_1_bicat_of_enriched_cats.
    - use is_univalent_2_0_bicat_of_enriched_cats.
      exact HV.
  Defined.

  Definition gregarious_univalent_enriched_profunctor_verity_double_bicat
    : gregarious_univalent enriched_profunctor_verity_double_bicat.
  Proof.
    use hor_globally_univalent_to_gregarious_univalent.
    - exact locally_univalent_enriched_profunctor_verity_double_bicat.
    - exact hor_globally_univalent_enriched_profunctor_verity_double_bicat.
    - exact enriched_profunctor_vertically_saturated.
  Defined.

  Definition univalent_enriched_profunctor_verity_double_bicat
    : univalent_verity_double_bicat enriched_profunctor_verity_double_bicat.
  Proof.
    split.
    - exact gregarious_univalent_enriched_profunctor_verity_double_bicat.
    - exact locally_univalent_enriched_profunctor_verity_double_bicat.
  Defined.
End Enriched.
