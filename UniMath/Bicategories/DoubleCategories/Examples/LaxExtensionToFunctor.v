(******************************************************************************************

 Lax extensions and lax double functors

 We show that the type of functors together with a lax extension is equivalent to the type
 of lax double functors. The notion of lax extension is fundamental in the study of
 bisimulation. To define bisimulations for coalgebras for an endofunctors, one needs to be
 able to lift relations along that functor. There are various notions to define such liftings,
 and one of them is given by lax extensions. Lax extensions are closely related to lax double
 functors, and we prove their equivalence (see Section 1.13 in "Monoidal Topology: A Categorical
 Approach to Order, Metric and Topology"). We also give a specialized builder for lax double
 endofunctors on the double category of quantale-enriched relations.

 References
 - Section 1.13 in "Monoidal Topology: A Categorical Approach to Order, Metric and Topology",
   editors Dirk Hofmann, Gavin Seal, Walter Tholen.

 Content
 1. Every lax extension gives rise to a lax double functor
 2. Every lax double functor gives rise to a lax extension
 3. Equivalence between lax double functors and functors with a lax extension

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.EnrichedRels.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Examples.EnrichedRelDoubleCat.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichedRelation.
Require Import UniMath.CategoryTheory.EnrichedCats.LaxExtension.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Every lax extension gives rise to a lax double functor *)
Section LaxDoubleFunctorRel.
  Context {V : quantale_cosmos}
          {F : SET ⟶ SET}
          (L : lax_extension V F)
          (FR : ∏ (X Y : hSet),
                enriched_relation V X Y
                →
                enriched_relation V (F X) (F Y))
          (FS : ∏ (X₁ X₂ Y₁ Y₂ : hSet)
                  (R₁ : enriched_relation V X₁ Y₁)
                  (R₂ : enriched_relation V X₂ Y₂)
                  (f : X₁ → X₂)
                  (g : Y₁ → Y₂)
                  (p : enriched_relation_square f g R₁ R₂),
                enriched_relation_square
                  (#F f) (#F g)
                  (FR X₁ Y₁ R₁) (FR X₂ Y₂ R₂))
          (FI : ∏ (X : hSet),
                enriched_relation_square
                  (idfun _) (idfun _)
                  (id_enriched_relation (F X))
                  (FR X X (id_enriched_relation X)))
          (FC : ∏ (X Y Z : hSet)
                  (R : enriched_relation V X Y)
                  (S : enriched_relation V Y Z),
                enriched_relation_square
                  (idfun _) (idfun _)
                  (FR X Y R ·e FR Y Z S) (FR X Z (R ·e S))).

  Definition make_enriched_relation_twosided_disp_functor_data
    : twosided_disp_functor_data
        F F
        (enriched_relation_twosided_disp_cat V)
        (enriched_relation_twosided_disp_cat V).
  Proof.
    simple refine (_ ,, _).
    - exact FR.
    - exact FS.
  Defined.

  Definition make_enriched_relation_twosided_disp_functor
    : twosided_disp_functor
        F F
        (enriched_relation_twosided_disp_cat V)
        (enriched_relation_twosided_disp_cat V).
  Proof.
    simple refine (_ ,, _).
    - exact make_enriched_relation_twosided_disp_functor_data.
    - abstract
        (split ; intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  Definition make_enriched_relation_double_functor_hor_id
    : double_functor_hor_id
        make_enriched_relation_twosided_disp_functor
        (enriched_rel_double_cat_hor_id V)
        (enriched_rel_double_cat_hor_id V).
  Proof.
    use make_double_functor_hor_id.
    - exact FI.
    - abstract
        (intro ; intros ;
         apply isaprop_enriched_relation_square).
  Defined.

  Definition make_enriched_relation_double_functor_hor_comp
    : double_functor_hor_comp
        make_enriched_relation_twosided_disp_functor
        (enriched_rel_double_cat_hor_comp V)
        (enriched_rel_double_cat_hor_comp V).
  Proof.
    use make_double_functor_hor_comp.
    - exact FC.
    - abstract
        (intro ; intros ;
         apply isaprop_enriched_relation_square).
  Defined.

  Definition make_enriched_relation_lax_double_functor
    : lax_double_functor
        (enriched_rel_univalent_double_cat V)
        (enriched_rel_univalent_double_cat V).
  Proof.
    use make_lax_double_functor.
    - exact F.
    - exact make_enriched_relation_twosided_disp_functor.
    - exact make_enriched_relation_double_functor_hor_id.
    - exact make_enriched_relation_double_functor_hor_comp.
    - abstract
        (intro ; intros ;
         apply isaprop_enriched_relation_square).
    - abstract
        (intro ; intros ;
         apply isaprop_enriched_relation_square).
    - abstract
        (intro ; intros ;
         apply isaprop_enriched_relation_square).
  Defined.
End LaxDoubleFunctorRel.

Definition lax_extension_to_lax_double_functor
           {V : quantale_cosmos}
           {F : SET ⟶ SET}
           (L : lax_extension V F)
  : lax_double_functor
      (enriched_rel_univalent_double_cat V)
      (enriched_rel_univalent_double_cat V).
Proof.
  use make_enriched_relation_lax_double_functor.
  - exact F.
  - exact (λ X Y R, L X Y R).
  - exact (λ X₁ X₂ Y₁ Y₂ R S f g p, lax_extension_enriched_relation_square L p).
  - exact (lax_extension_id_enriched_relation L).
  - exact (λ X Y Z R S, lax_extension_enriched_rel_comp L R S).
Defined.

(** * 2. Every lax double functor gives rise to a lax extension *)
Section FunctorToExtension.
  Context {V : quantale_cosmos}
          (F : lax_double_functor
                 (enriched_rel_univalent_double_cat V)
                 (enriched_rel_univalent_double_cat V)).

  Definition lax_double_functor_to_extension_data
    : lax_extension_data V F
    := λ X Y R, #h F R.

  Arguments lax_double_functor_to_extension_data /.

  Proposition lax_double_functor_to_extension_laws
    : lax_extension_laws lax_double_functor_to_extension_data.
  Proof.
    repeat split.
    - intros X Y R S p.
      pose (enriched_relation_square_to_le
              (#s F (enriched_relation_le_to_square p)))
        as e.
      unfold lax_double_functor_to_extension_data.
      refine (enriched_relation_le_trans e _).
      rewrite <- enriched_relation_comp_conj.
      rewrite !(lax_double_functor_id_v F).
      rewrite companion_enriched_relation_id.
      rewrite conjoint_enriched_relation_id.
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_square_to_le.
        apply enriched_relation_lunitor.
      }
      use enriched_relation_square_to_le.
      apply enriched_relation_runitor.
    - intros.
      apply (lax_double_functor_comp_h F).
    - intros X Y f ; cbn.
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_eq_to_le.
        apply maponpaths.
        refine (!(id_left (#F f)) @ _).
        apply idpath.
      }
      refine (enriched_relation_le_trans _ _).
      {
        exact (companion_enriched_relation_comp (identity (F X)) (#F f)).
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
        rewrite companion_enriched_relation_id.
        exact (enriched_relation_square_to_le (lax_double_functor_id_h F X)).
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
        exact (#s F (companion_enriched_relation_right f)).
      }
      rewrite <- enriched_relation_comp_conj.
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_eq_to_le.
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply (lax_double_functor_id_v F X).
        }
        rewrite companion_enriched_relation_id.
        apply idpath.
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
        use enriched_relation_square_to_le.
        apply enriched_relation_lunitor.
      }
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_square_to_le.
        apply enriched_relation_lassociator.
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
        use enriched_relation_square_to_le.
        apply comp_conjoint_companion_enriched_relation.
      }
      use enriched_relation_square_to_le.
      apply enriched_relation_runitor.
    - intros X Y f ; cbn.
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_eq_to_le.
        apply maponpaths.
        refine (!(id_left (#F f)) @ _).
        apply idpath.
      }
      refine (enriched_relation_le_trans _ _).
      {
        exact (conjoint_enriched_relation_comp (identity (F X)) (#F f)).
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
        rewrite conjoint_enriched_relation_id.
        exact (enriched_relation_square_to_le (lax_double_functor_id_h F X)).
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
        exact (enriched_relation_square_to_le (#s F (conjoint_enriched_relation_left f))).
      }
      rewrite <- enriched_relation_comp_conj.
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_eq_to_le.
        do 2 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          apply (lax_double_functor_id_v F X).
        }
        rewrite conjoint_enriched_relation_id.
        apply idpath.
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
        refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
        use enriched_relation_square_to_le.
        apply enriched_relation_runitor.
      }
      refine (enriched_relation_le_trans _ _).
      {
        use enriched_relation_square_to_le.
        apply enriched_relation_rassociator.
      }
      refine (enriched_relation_le_trans _ _).
      {
        refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
        use enriched_relation_square_to_le.
        apply comp_conjoint_companion_enriched_relation.
      }
      use enriched_relation_square_to_le.
      apply enriched_relation_lunitor.
  Qed.

  Definition lax_double_functor_to_lax_extension
    : lax_extension V F.
  Proof.
    use make_lax_extension.
    - exact lax_double_functor_to_extension_data.
    - exact lax_double_functor_to_extension_laws.
  Defined.

  Definition lax_double_functor_to_functor_with_lax_extension
    : functor_with_lax_extension V
    := _ ,, lax_double_functor_to_lax_extension.
End FunctorToExtension.

(** * 3. Equivalence between lax double functors and functors with a lax extension *)
Proposition lax_double_functor_weq_functor_with_lax_extension_left
             {V : quantale_cosmos}
             (F : lax_double_functor
                    (enriched_rel_univalent_double_cat V)
                    (enriched_rel_univalent_double_cat V))
  : lax_extension_to_lax_double_functor (lax_double_functor_to_lax_extension F) = F.
Proof.
  use subtypePath.

  {
    intro.
    apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    repeat (use isapropdirprod) ;
    repeat (use impred ; intro) ;
    apply isasetaprop ;
    apply isaprop_enriched_relation_square.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod.
    - use isaproptotal2.
      {
        intro.
        apply isaprop_double_functor_hor_id_laws.
      }
      intros.
      repeat (use funextsec ; intro).
      apply (is_poset_category_quantale_cosmos V).
    - use isaproptotal2.
      {
        intro.
        apply isaprop_double_functor_hor_comp_laws.
      }
      intros.
      repeat (use funextsec ; intro).
      apply (is_poset_category_quantale_cosmos V).
  }
  use total2_paths_f.
  - apply idpath.
  - use subtypePath.
    {
      intro.
      apply isaprop_twosided_disp_functor_laws.
    }
    cbn.
    use subtypePath.
    {
      intro.
      repeat (use impred ; intro).
      apply V.
    }
    apply idpath.
Qed.

Proposition lax_double_functor_weq_functor_with_lax_extension_right
            {V : quantale_cosmos}
            (F : functor_with_lax_extension V)
  : lax_double_functor_to_functor_with_lax_extension
      (lax_extension_to_lax_double_functor (lax_extension_of_functor F))
    =
    F.
Proof.
  refine (maponpaths (λ z, _ ,, z) _).
  use eq_lax_extension.
  intros.
  apply idpath.
Qed.

Definition lax_double_functor_weq_functor_with_lax_extension
           (V : quantale_cosmos)
  : lax_double_functor
      (enriched_rel_univalent_double_cat V)
      (enriched_rel_univalent_double_cat V)
    ≃
    functor_with_lax_extension V.
Proof.
  use weq_iso.
  - exact lax_double_functor_to_functor_with_lax_extension.
  - exact (λ F, lax_extension_to_lax_double_functor
                  (lax_extension_of_functor F)).
  - exact lax_double_functor_weq_functor_with_lax_extension_left.
  - exact lax_double_functor_weq_functor_with_lax_extension_right.
Defined.
