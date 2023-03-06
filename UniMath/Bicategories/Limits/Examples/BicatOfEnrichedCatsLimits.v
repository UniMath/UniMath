(*********************************************************************************

 Limits of enriched categories

 In this file we construct several limits of enriched categories.

 Contents:
 1. Final object
 2. Inserters
 3. Equifiers
 4. Eilenberg-Moore objects

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnitEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.DialgebraEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.EilenbergMooreEnriched.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfEnrichedCats.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor.

Section LimitsEnrichedCats.
  Context (V : monoidal_cat).

  (**
   1. Final object
   *)

  (**
   Note that to construct the final object, we assume that the
   monoidal category `V` is semi-cartesian, which means that
   the unit is a terminal object. We use this to construct the
   univalent enriched unit category.
   *)
  Section FinalObject.
    Context (HV : isTerminal V 𝟙).

    Let enriched_bifinal : bicat_of_enriched_cats V
      := unit_category ,, unit_enrichment V HV.

    Definition is_bifinal_enriched_cats
      : is_bifinal enriched_bifinal.
    Proof.
      use make_is_bifinal.
      - exact (λ E,
               functor_to_unit _
               ,,
               functor_to_unit_enrichment V HV (pr2 E)).
      - exact (λ C F G,
               unit_category_nat_trans (pr1 F) (pr1 G)
               ,,
               nat_trans_to_unit_enrichment _ _ _ (pr2 F) (pr2 G)).
      - abstract
          (intros C f g α β ;
           use subtypePath ;
           [ intro ; apply isaprop_nat_trans_enrichment
           | ] ;
           apply nat_trans_to_unit_eq).
    Defined.

    Definition bifinal_enriched_cats
      : bifinal_obj (bicat_of_enriched_cats V)
      := enriched_bifinal ,, is_bifinal_enriched_cats.
  End FinalObject.

  (**
   2. Inserters
   *)
  Section Inserters.
    Context (HV : Equalizers V)
            {E₁ E₂ : bicat_of_enriched_cats V}
            (F G : E₁ --> E₂).

    Definition enriched_inserter_cat
      : bicat_of_enriched_cats V
      := univalent_dialgebra (pr1 F) (pr1 G)
         ,,
         dialgebra_enrichment _ HV (pr2 F) (pr2 G).

    Definition enriched_inserter_pr1
      : enriched_inserter_cat --> E₁
      := dialgebra_pr1 (pr1 F) (pr1 G)
         ,,
         dialgebra_pr1_enrichment _ HV (pr2 F) (pr2 G).

    Definition enriched_inserter_cell
      : enriched_inserter_pr1 · F ==> enriched_inserter_pr1 · G
      := dialgebra_nat_trans (pr1 F) (pr1 G)
         ,,
         dialgebra_nat_trans_enrichment _ HV (pr2 F) (pr2 G).

    Definition enriched_inserter_cone
      : inserter_cone F G.
    Proof.
      use make_inserter_cone.
      - exact enriched_inserter_cat.
      - exact enriched_inserter_pr1.
      - exact enriched_inserter_cell.
    Defined.

    Definition enriched_inserter_ump_1
      : has_inserter_ump_1 enriched_inserter_cone.
    Proof.
      intros q.
      use make_inserter_1cell.
      - simple refine (_ ,, _).
        + exact (nat_trans_to_dialgebra
                   (pr1 (inserter_cone_pr1 q))
                   (pr1 (inserter_cone_cell q))).
        + exact (nat_trans_to_dialgebra_enrichment
                   _
                   HV
                   (pr2 F) (pr2 G)
                   (pr1 (inserter_cone_cell q))
                   (pr2 (inserter_cone_cell q))).
      - use make_invertible_2cell.
        + simple refine (_ ,, _).
          * exact (nat_trans_to_dialgebra_pr1
                     (pr1 (inserter_cone_pr1 q))
                     (pr1 (inserter_cone_cell q))).
          * exact (nat_trans_to_dialgebra_pr1_enrichment
                     _
                     HV
                     (pr2 F) (pr2 G)
                     (pr1 (inserter_cone_cell q))
                     (pr2 (inserter_cone_cell q))).
        + use make_is_invertible_2cell.
          * simple refine (_ ,, _).
            ** cbn.
               exact (nat_z_iso_inv
                        (nat_trans_to_dialgebra_pr1_nat_z_iso
                           (pr1 (inserter_cone_pr1 q))
                           (pr1 (inserter_cone_cell q)))).
            ** exact (nat_trans_to_dialgebra_pr1_enrichment_inv
                        _
                        HV
                        (pr2 F) (pr2 G)
                        (pr1 (inserter_cone_cell q))
                        (pr2 (inserter_cone_cell q))).
          * abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro x ; cbn ;
               apply id_left).
          * abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro x ; cbn ;
               apply id_left).
      - abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           rewrite !(functor_id (pr1 F)), !(functor_id (pr1 G)) ;
           rewrite !id_left, !id_right ;
           apply idpath).
    Defined.

    Definition enriched_inserter_ump_2
      : has_inserter_ump_2 enriched_inserter_cone.
    Proof.
      intros E₀ K₁ K₂ α p.
      simple refine (_ ,, _).
      - simple refine (_ ,, _).
        + apply (build_nat_trans_to_dialgebra (pr1 K₁) (pr1 K₂) (pr1 α)).
          abstract
            (intro x ;
             pose (maponpaths (λ z, pr11 z x) p) as p' ;
             cbn in p' ;
             rewrite !id_left, !id_right in p' ;
             exact p').
        + apply build_nat_trans_to_dialgebra_enrichment.
          exact (pr2 α).
      - abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           apply idpath).
    Defined.

    Definition enriched_inserter_ump_eq
      : has_inserter_ump_eq enriched_inserter_cone.
    Proof.
      intros E₀ K₁ K₂ α p n₁ n₂ q₁ q₂.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use eq_dialgebra.
      exact (maponpaths (λ z, pr11 z x) (q₁ @ !q₂)).
    Qed.
  End Inserters.

  Definition has_inserters_bicat_of_enriched_cats
             (HV : Equalizers V)
    : has_inserters (bicat_of_enriched_cats V).
  Proof.
    intros E₁ E₂ F G.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (enriched_inserter_cat HV F G).
    - exact (enriched_inserter_pr1 HV F G).
    - exact (enriched_inserter_cell HV F G).
    - simple refine (_ ,, _ ,, _).
      + exact (enriched_inserter_ump_1 HV F G).
      + exact (enriched_inserter_ump_2 HV F G).
      + exact (enriched_inserter_ump_eq HV F G).
  Defined.

  (**
   3. Equifiers
   *)
  Section EquifierEnrichedCat.
    Context {E₁ E₂ : bicat_of_enriched_cats V}
            {F G : E₁ --> E₂}
            (τ θ : F ==> G).

    Definition equifier_bicat_of_enriched_cats
      : bicat_of_enriched_cats V.
    Proof.
      simple refine (_ ,, _).
      - use (subcategory_univalent (pr1 E₁)).
        intro x.
        use make_hProp.
        + exact (pr11 τ x = pr11 θ x).
        + apply homset_property.
      - apply (fullsub_enrichment _ (pr2 E₁)).
    Defined.

    Definition equifier_bicat_of_enriched_cats_pr1
      : equifier_bicat_of_enriched_cats --> E₁
      := sub_precategory_inclusion _ _ ,, fullsub_inclusion_enrichment _ _ _.

    Definition equifier_bicat_of_enriched_cats_eq
      : equifier_bicat_of_enriched_cats_pr1 ◃ τ
        =
        equifier_bicat_of_enriched_cats_pr1 ◃ θ.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      exact (pr2 x).
    Qed.

    Definition equifier_bicat_of_enriched_cats_cone
      : equifier_cone F G τ θ
      := make_equifier_cone
           equifier_bicat_of_enriched_cats
           equifier_bicat_of_enriched_cats_pr1
           equifier_bicat_of_enriched_cats_eq.

    Section EquifierUMP1.
      Context (E₀ : bicat_of_enriched_cats V)
              (H : E₀ --> E₁)
              (q : H ◃ τ = H ◃ θ).

      Definition equifier_bicat_of_enriched_cats_ump_1_functor_data
        : functor_data
            (pr11 E₀)
            (pr11 equifier_bicat_of_enriched_cats).
      Proof.
        use make_functor_data.
        - refine (λ x, pr11 H x ,, _).
          exact (maponpaths (λ z, pr11 z x) q).
        - exact (λ x y f, # (pr11 H) f ,, tt).
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_functor_laws
        : is_functor equifier_bicat_of_enriched_cats_ump_1_functor_data.
      Proof.
        split ; intro ; intros.
        - use subtypePath ; [ intro ; apply isapropunit | ] ; cbn.
          apply functor_id.
        - use subtypePath ; [ intro ; apply isapropunit | ] ; cbn.
          apply functor_comp.
      Qed.

      Definition equifier_bicat_of_enriched_cats_ump_1_functor
        : pr11 E₀ ⟶ pr11 equifier_bicat_of_enriched_cats.
      Proof.
        use make_functor.
        - exact equifier_bicat_of_enriched_cats_ump_1_functor_data.
        - exact equifier_bicat_of_enriched_cats_ump_1_functor_laws.
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_enrichment
        : functor_enrichment
            equifier_bicat_of_enriched_cats_ump_1_functor
            (pr2 E₀)
            (fullsub_enrichment V (pr2 E₁) _).
      Proof.
        simple refine (_ ,, _).
        - exact (λ x y, pr12 H x y).
        - repeat split.
          + abstract
              (intros x ; cbn ;
               exact (functor_enrichment_id (pr2 H) x)).
          + abstract
              (intros x y z ; cbn ;
               exact (functor_enrichment_comp (pr2 H) x y z)).
          + abstract
              (intros x y f ; cbn ;
               exact (functor_enrichment_from_arr (pr2 H) f)).
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_mor
        : E₀ --> equifier_bicat_of_enriched_cats_cone.
      Proof.
        simple refine (_ ,, _).
        - exact equifier_bicat_of_enriched_cats_ump_1_functor.
        - exact equifier_bicat_of_enriched_cats_ump_1_enrichment.
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_cell
        : equifier_bicat_of_enriched_cats_ump_1_mor
          · equifier_bicat_of_enriched_cats_pr1
          ==>
          H.
      Proof.
        simple refine (_ ,, _).
        - use make_nat_trans.
          + exact (λ _, identity _).
          + abstract
              (intros x y f ; cbn ;
               rewrite id_left, id_right ;
               apply idpath).
        - abstract
            (intros x y ; cbn ;
             rewrite id_right ;
             rewrite !enriched_from_arr_id ;
             rewrite tensor_split' ;
             rewrite !assoc' ;
             rewrite <- enrichment_id_right ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               refine (!_) ;
               apply tensor_rinvunitor
             | ] ;
             rewrite !assoc' ;
             rewrite mon_rinvunitor_runitor ;
             rewrite id_right ;
             rewrite tensor_split ;
             rewrite !assoc' ;
             rewrite <- enrichment_id_left ;
             rewrite !assoc ;
             refine (!_) ;
             etrans ;
             [ apply maponpaths_2 ;
               refine (!_) ;
               apply tensor_linvunitor
             | ] ;
             rewrite !assoc' ;
             rewrite mon_linvunitor_lunitor ;
             apply id_right).
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_inv
        : H
          ==>
          equifier_bicat_of_enriched_cats_ump_1_mor
          · equifier_bicat_of_enriched_cats_pr1.
      Proof.
        simple refine (_ ,, _).
        - use make_nat_trans.
          + exact (λ _, identity _).
          + abstract
              (intros x y f ; cbn ;
               rewrite id_left, id_right ;
               apply idpath).
        - abstract
            (intros x y ; cbn ;
             rewrite id_right ;
             rewrite !enriched_from_arr_id ;
             rewrite tensor_split' ;
             rewrite !assoc' ;
             rewrite <- enrichment_id_right ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               refine (!_) ;
               apply tensor_rinvunitor
             | ] ;
             rewrite !assoc' ;
             rewrite mon_rinvunitor_runitor ;
             rewrite id_right ;
             rewrite tensor_split ;
             rewrite !assoc' ;
             rewrite <- enrichment_id_left ;
             rewrite !assoc ;
             refine (!_) ;
             etrans ;
             [ apply maponpaths_2 ;
               refine (!_) ;
               apply tensor_linvunitor
             | ] ;
             rewrite !assoc' ;
             rewrite mon_linvunitor_lunitor ;
             apply id_right).
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_1_inv2cell
        : invertible_2cell
            (equifier_bicat_of_enriched_cats_ump_1_mor
             · equifier_bicat_of_enriched_cats_pr1)
            H.
      Proof.
        use make_invertible_2cell.
        - exact equifier_bicat_of_enriched_cats_ump_1_cell.
        - use make_is_invertible_2cell.
          + exact equifier_bicat_of_enriched_cats_ump_1_inv.
          + abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro ;
               apply id_right).
          + abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro ;
               apply id_right).
      Defined.
    End EquifierUMP1.

    Definition equifier_bicat_of_enriched_cats_ump_1
      : has_equifier_ump_1 equifier_bicat_of_enriched_cats_cone.
    Proof.
      intros q.
      use make_equifier_1cell.
      - exact (equifier_bicat_of_enriched_cats_ump_1_mor (pr1 q) (pr12 q) (pr22 q)).
      - exact (equifier_bicat_of_enriched_cats_ump_1_inv2cell (pr1 q) (pr12 q) (pr22 q)).
    Defined.

    Section EquifierUMP2.
      Context {D : bicat_of_enriched_cats V}
              {H₁ H₂ : D --> equifier_bicat_of_enriched_cats_cone}
              (α : H₁ · equifier_cone_pr1 equifier_bicat_of_enriched_cats_cone
                   ==>
                   H₂ · equifier_cone_pr1 equifier_bicat_of_enriched_cats_cone).

      Definition equifier_bicat_of_univ_cats_ump_2_nat_trans
        : pr1 H₁ ==> pr1 H₂.
      Proof.
        use make_nat_trans.
        - exact (λ x, pr11 α x ,, tt).
        - abstract
            (intros x y f ;
             use subtypePath ; [ intro ; apply isapropunit | ] ;
             cbn ;
             exact (nat_trans_ax (pr1 α) _ _ f)).
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_2_enrichment
        : nat_trans_enrichment
            (pr1 equifier_bicat_of_univ_cats_ump_2_nat_trans)
            (pr2 H₁)
            (pr2 H₂).
      Proof.
        intros x y ; cbn.
        pose (pr2 α x y) as p.
        cbn in p.
        rewrite !id_right in p.
        exact p.
      Qed.

      Definition equifier_bicat_of_enriched_cats_ump_2_cell
        : H₁ ==> H₂.
      Proof.
        simple refine (_ ,, _).
        - exact equifier_bicat_of_univ_cats_ump_2_nat_trans.
        - exact equifier_bicat_of_enriched_cats_ump_2_enrichment.
      Defined.

      Definition equifier_bicat_of_enriched_cats_ump_2_eq
        : equifier_bicat_of_enriched_cats_ump_2_cell ▹ _  = α.
      Proof.
        use subtypePath.
        {
          intro.
          apply isaprop_nat_trans_enrichment.
        }
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        apply idpath.
      Qed.
    End EquifierUMP2.

    Definition equifier_bicat_of_enriched_cats_ump_2
      : has_equifier_ump_2 equifier_bicat_of_enriched_cats_cone.
    Proof.
      intros D H₁ H₂ α.
      exact (equifier_bicat_of_enriched_cats_ump_2_cell α
             ,,
             equifier_bicat_of_enriched_cats_ump_2_eq α).
    Defined.

    Definition equifier_bicat_of_enriched_cats_ump_eq
      : has_equifier_ump_eq equifier_bicat_of_enriched_cats_cone.
    Proof.
      intros D H₁ H₂ α φ₁ φ₂ p q.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      exact (maponpaths (λ z, pr11 z x) (p @ !q)).
    Qed.
  End EquifierEnrichedCat.

  Definition has_equifiers_bicat_of_enriched_cats
    : has_equifiers (bicat_of_enriched_cats V).
  Proof.
    intros E₁ E₂ F G τ θ.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (equifier_bicat_of_enriched_cats τ θ).
    - exact (equifier_bicat_of_enriched_cats_pr1 τ θ).
    - exact (equifier_bicat_of_enriched_cats_eq τ θ).
    - simple refine (_ ,, _ ,, _).
      + exact (equifier_bicat_of_enriched_cats_ump_1 τ θ).
      + exact (equifier_bicat_of_enriched_cats_ump_2 τ θ).
      + exact (equifier_bicat_of_enriched_cats_ump_eq τ θ).
  Defined.

  (**
   4. Eilenberg-Moore objects
   *)
  Section EilenbergMooreEnrichedCat.
    Context (HV : Equalizers V)
            (EM : mnd (bicat_of_enriched_cats V)).

    Let C : univalent_category := pr1 (ob_of_mnd EM).
    Let E : enrichment C V := pr2 (ob_of_mnd EM).
    Let M : Monad C := Monad_from_mnd_enriched_cats _ EM.
    Let EM' : monad_enrichment E M
      := Monad_enrichment_from_mnd_enriched_cats _ EM.

    Definition em_enriched_cat_cone
      : em_cone EM.
    Proof.
      use make_em_cone.
      - exact (eilenberg_moore_univalent_cat C M
               ,,
               eilenberg_moore_enrichment HV EM').
      - exact (eilenberg_moore_pr M
               ,,
               eilenberg_moore_pr_enrichment HV EM').
      - exact (eilenberg_moore_nat_trans M
               ,,
               eilenberg_moore_nat_trans_enrichment HV EM').
      - abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           rewrite id_left ;
           exact (!(pr12 x))).
      - abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           rewrite (functor_id (pr1 (endo_of_mnd EM))) ;
           rewrite id_left, id_right ;
           exact (!(pr22 x))).
    Defined.

    Section EilenbergMooreUMP1.
      Context (q : em_cone EM).

      Let C' : univalent_category := pr11 q.

      Definition em_enriched_cat_ump_1_functor
        : C' ⟶ eilenberg_moore_cat M.
      Proof.
        use functor_to_eilenberg_moore_cat.
        - exact (pr1 (mor_of_mnd_mor (mor_of_em_cone _ q))).
        - exact (pr1 (mnd_mor_endo (mor_of_em_cone _ q))).
        - abstract
            (intro x ;
             refine (!(mnd_mor_unit_enriched _ (mor_of_em_cone _ q) x) @ _) ;
             apply (functor_id
                      (pr1 (mor_of_mnd_mor (mor_of_em_cone EM q))))).
        - abstract
            (intro x ;
             refine (_ @ (mnd_mor_mu_enriched _ (mor_of_em_cone _ q) x) @ _) ;
             [ refine (!(id_right _) @ _) ;
               apply maponpaths ;
               refine (!_) ;
               apply (functor_id
                        (pr1 (mor_of_mnd_mor (mor_of_em_cone EM q))))
             | cbn ;
               apply idpath ]).
      Defined.

      Definition em_enriched_cat_ump_1_enrichment
        : functor_enrichment
            em_enriched_cat_ump_1_functor
            (pr21 q)
            (eilenberg_moore_enrichment HV EM').
      Proof.
        use functor_to_eilenberg_moore_cat_enrichment.
        - exact (pr2 (mor_of_mnd_mor (mor_of_em_cone _ q))).
        - exact (pr2 (mnd_mor_endo (mor_of_em_cone _ q))).
      Defined.

      Definition em_enriched_cat_ump_1_mor
        : q --> em_enriched_cat_cone.
      Proof.
        simple refine (_ ,, _).
        - exact em_enriched_cat_ump_1_functor.
        - exact em_enriched_cat_ump_1_enrichment.
      Defined.

      Definition em_enriched_cat_ump_1_inv2cell_cell
        : # (mnd_incl (bicat_of_enriched_cats V))
            em_enriched_cat_ump_1_mor
          · mor_of_em_cone EM em_enriched_cat_cone
          ==>
          mor_of_em_cone EM q.
      Proof.
        use make_mnd_cell.
        - simple refine (_ ,, _).
          + apply functor_to_eilenberg_moore_cat_pr.
          + apply (functor_to_eilenberg_moore_cat_pr_enrichment
                     HV
                     EM').
        - abstract
            (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
             use nat_trans_eq ; [ apply homset_property | ] ;
             intro x ;
             do 2 refine (id_right _ @ _) ;
             do 2 refine (assoc' _ _ _ @ _) ;
             refine (id_left _ @ _) ;
             do 2 refine (assoc _ _ _ @ _) ;
             do 3 refine (id_right _ @ _) ;
             refine (!_) ;
             refine (_ @ id_left _) ;
             refine (maponpaths (λ z, z · _) _) ;
             apply (functor_id M)).
      Defined.

      Definition em_enriched_cat_ump_1_inv2cell_inv
        : mor_of_mnd_mor (mor_of_em_cone EM q)
          ==>
          mor_of_mnd_mor
          (# (mnd_incl (bicat_of_enriched_cats V))
             em_enriched_cat_ump_1_mor
           · mor_of_em_cone EM em_enriched_cat_cone).
      Proof.
        simple refine (_ ,, _).
        - exact (nat_z_iso_to_trans_inv
                   (functor_to_eilenberg_moore_cat_pr_nat_z_iso
                      M
                      (pr1 (mor_of_mnd_mor (mor_of_em_cone _ q)))
                      (pr1 (mnd_mor_endo (mor_of_em_cone _ q)))
                      _ _)).
        - apply functor_to_eilenberg_moore_cat_pr_enrichment_inv.
      Defined.

      Definition em_enriched_cat_ump_1_inv2cell
        : invertible_2cell
            (# (mnd_incl (bicat_of_enriched_cats V))
               em_enriched_cat_ump_1_mor
             · mor_of_em_cone EM em_enriched_cat_cone)
            (mor_of_em_cone EM q).
      Proof.
        use make_invertible_2cell.
        - exact em_enriched_cat_ump_1_inv2cell_cell.
        - use is_invertible_mnd_2cell.
          use make_is_invertible_2cell.
          + exact em_enriched_cat_ump_1_inv2cell_inv.
          + abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro x ;
               apply id_left).
          + abstract
              (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
               use nat_trans_eq ; [ apply homset_property | ] ;
               intro x ;
               apply id_left).
      Defined.
    End EilenbergMooreUMP1.

    Definition em_enriched_cat_ump_1
      : em_ump_1 EM em_enriched_cat_cone.
    Proof.
      intro q.
      use make_em_cone_mor.
      - exact (em_enriched_cat_ump_1_mor q).
      - exact (em_enriched_cat_ump_1_inv2cell q).
    Defined.

    Section EilenbergMooreUMP2.
      Context {E' : bicat_of_enriched_cats V}
              (FE₁ FE₂ : E' --> em_enriched_cat_cone)
              (Eτ : # (mnd_incl (bicat_of_enriched_cats V)) FE₁
                    · mor_of_em_cone EM em_enriched_cat_cone
                    ==>
                    # (mnd_incl (bicat_of_enriched_cats V)) FE₂
                    · mor_of_em_cone EM em_enriched_cat_cone).

      Let C' : univalent_category := pr1 E'.
      Let F₁ : C' ⟶ eilenberg_moore_cat M := pr1 FE₁.
      Let F₂ : C' ⟶ eilenberg_moore_cat M := pr1 FE₂.
      Let τ : F₁ ∙ eilenberg_moore_pr M ⟹ F₂ ∙ eilenberg_moore_pr M := pr11 Eτ.

      Definition em_enriched_cat_ump_2_eq
                 (x : C')
        : mor_of_eilenberg_moore_ob (F₁ x) · τ x
          =
          # M (τ x) · mor_of_eilenberg_moore_ob (F₂ x).
      Proof.
        refine (!_ @ mnd_cell_endo_enriched _ Eτ x @ _).
        - do 4 refine (assoc' _ _ _ @ _).
          refine (id_left _ @ _).
          apply maponpaths.
          refine (id_left _ @ _).
          refine (assoc _ _ _ @ _).
          refine (_ @ id_left _).
          simpl.
          apply maponpaths_2.
          refine (id_right _ @ _).
          apply id_left.
        - apply maponpaths.
          do 3 refine (assoc' _ _ _ @ _).
          refine (id_left _ @ _).
          refine (_ @ id_right _).
          simpl.
          apply maponpaths.
          refine (id_left _ @ _).
          refine (id_right _ @ _).
          apply id_left.
      Qed.

      Definition em_enriched_cat_ump_2_nat_trans
        : F₁ ⟹ F₂
        := nat_trans_to_eilenberg_moore_cat M F₁ F₂ τ em_enriched_cat_ump_2_eq.

      Definition em_enriched_cat_ump_2_cell
        : FE₁ ==> FE₂.
      Proof.
        simple refine (_ ,, _).
        - exact em_enriched_cat_ump_2_nat_trans.
        - use nat_trans_to_eilenberg_moore_cat_enrichment.
          apply (pr21 Eτ).
      Defined.
    End EilenbergMooreUMP2.

    Definition em_enriched_cat_ump_2
      : em_ump_2 EM em_enriched_cat_cone.
    Proof.
      intros E' FE₁ FE₂ Eτ.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply cellset_property | ] ;
           use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ;
           pose (maponpaths (λ z, pr111 z x) (pr2 φ₁)) as p₁ ;
           pose (maponpaths (λ z, pr111 z x) (pr2 φ₂)) as p₂ ;
           use eq_mor_eilenberg_moore ;
           exact (p₁ @ (!p₂))).
      - simple refine (_ ,, _).
        + exact (em_enriched_cat_ump_2_cell FE₁ FE₂ Eτ).
        + abstract
            (use eq_mnd_cell ;
             use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
             use nat_trans_eq ; [ apply homset_property | ] ;
             intro x ;
             apply idpath).
    Defined.

    Definition em_enriched_cat_ump
      : has_em_ump EM em_enriched_cat_cone.
    Proof.
      split.
      - exact em_enriched_cat_ump_1.
      - exact em_enriched_cat_ump_2.
    Defined.
  End EilenbergMooreEnrichedCat.

  Definition has_em_bicat_of_enriched_cats
             (HV : Equalizers V)
    : bicat_has_em (bicat_of_enriched_cats V)
    := λ EM, em_enriched_cat_cone HV EM ,, em_enriched_cat_ump HV EM.
End LimitsEnrichedCats.
