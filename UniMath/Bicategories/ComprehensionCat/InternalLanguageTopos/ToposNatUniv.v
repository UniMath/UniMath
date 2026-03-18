(**

 The internal language of elementary toposes with a NNO and a universe

 We have established biequivalences between bicategories of univalent categories with finite
 limits and various kinds of structure, and univalent DFL full comprehension categories with
 the corresponding structure. We used these biequivalence to give an internal language
 theorem for univalent elementary toposes with a natural numbers object. In this file, we
 give an internal language theorem for elementary toposes with a NNO and a universe. The
 universe is required to satisfy the following closure conditions.
 - The natural numbers object must be contained in the universe.
 - The subobject classifier must be contained in the universe.
 - The universe must contain every proposition. This corresponds to propositional resizing.
 - The universe must be closed under ∑-types and ∏-types.
 This notion of universe is based on "Universes in toposes" by Streicher, and these closure
 conditions have various implications. For instance, since the universe contains every
 proposition, we can directly conclude that the unit type and tne empty type are in the
 universe. In addition, since the universe contains the subobject classifier, one can show
 that the universe also is closed under sums and quotients.

 References
 - "Universes in toposes" by Streicher

 Contents
 1. The bicategory of elementary toposes with a NNO and universe
 2. Accessors for elementary toposes with a NNO and universe
 3. The bicategory of elementary topos comprehension categories with a NNO and universe
 4. Accessors for elementary toposes comprehension categories with a NNO and universe
 5. The biequivalence
 6. Type formers in a topos with a universe
 6.1. Parameterized NNO
 6.2. Subobject classifier
 6.3. Propositional resizing
 6.4. ∑-types
 6.5. ∏-types
 6.6. Universes for toposes
 7. Accessors for topos universes
 8. The biequivalence for topos universes

                                                                                          *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Reindex.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.ProductDispBiequiv.
Require Import UniMath.Bicategories.DisplayedBicats.ReindexBiequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.BiequivalenceCoherent.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.CatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.Pretopos.
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.PiPretopos.
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.ToposNat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.UniverseBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Resizing.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.PiTypes.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The bicategory of elementary toposes with a NNO and universe *)
Definition disp_bicat_of_univ_topos_with_NNO_univ
  : disp_bicat bicat_of_univ_cat_with_finlim
  := disp_dirprod_bicat
       disp_bicat_of_univ_topos_with_NNO
       disp_bicat_finlim_universe.

Proposition disp_2cells_isaprop_disp_bicat_of_univ_topos_with_NNO_univ
  : disp_2cells_isaprop disp_bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_2cells_isaprop_prod.
  - exact disp_2cells_isaprop_disp_bicat_of_univ_topos_with_NNO.
  - exact disp_2cells_isaprop_disp_bicat_finlim_universe.
Defined.

Proposition disp_locally_groupoid_disp_bicat_of_univ_topos_with_NNO_univ
  : disp_locally_groupoid disp_bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_locally_groupoid_prod.
  - exact disp_locally_groupoid_disp_bicat_of_univ_topos_with_NNO.
  - exact disp_locally_groupoid_disp_bicat_finlim_universe.
Defined.

Proposition disp_univalent_2_disp_bicat_of_univ_topos_with_NNO_univ
  : disp_univalent_2 disp_bicat_of_univ_topos_with_NNO_univ.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
  - exact disp_univalent_2_disp_bicat_of_univ_topos_with_NNO.
  - exact disp_univalent_2_disp_bicat_finlim_universe.
Qed.

Proposition disp_univalent_2_0_disp_bicat_of_univ_topos_with_NNO_univ
  : disp_univalent_2_0 disp_bicat_of_univ_topos_with_NNO_univ.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_topos_with_NNO_univ.
Qed.

Proposition disp_univalent_2_1_disp_bicat_of_univ_topos_with_NNO_univ
  : disp_univalent_2_1 disp_bicat_of_univ_topos_with_NNO_univ.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_topos_with_NNO_univ.
Qed.

Definition bicat_of_univ_topos_with_NNO_univ
  : bicat
  := total_bicat disp_bicat_of_univ_topos_with_NNO_univ.

Proposition is_univalent_2_bicat_of_univ_topos_with_NNO_univ
  : is_univalent_2 bicat_of_univ_topos_with_NNO_univ.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_of_univ_topos_with_NNO_univ.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_0_bicat_of_univ_topos_with_NNO_univ
  : is_univalent_2_0 bicat_of_univ_topos_with_NNO_univ.
Proof.
  apply is_univalent_2_bicat_of_univ_topos_with_NNO_univ.
Defined.

Proposition is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ
  : is_univalent_2_1 bicat_of_univ_topos_with_NNO_univ.
Proof.
  apply is_univalent_2_bicat_of_univ_topos_with_NNO_univ.
Defined.

(** * 2. Accessors for elementary toposes with a NNO and universe *)
Definition univ_topos_with_NNO_univ
  : UU
  := bicat_of_univ_topos_with_NNO_univ.

Coercion univ_topos_with_NNO_to_univ_pretopos
         (E : univ_topos_with_NNO_univ)
  : univ_pretopos.
Proof.
  use make_univ_pretopos.
  - exact (pr1 E).
  - exact (pr111 (pr111 (pr112 E))).
  - exact (pr1 (pr211 (pr111 (pr112 E)))).
  - exact (pr2 (pr211 (pr111 (pr112 E)))).
  - exact (pr21 (pr111 (pr112 E))).
  - exact (pr112 (pr111 (pr112 E))).
  - exact (pr212 (pr111 (pr112 E))).
  - exact (pr22 (pr111 (pr112 E))).
Defined.

Definition univ_topos_with_NNO_univ_subobject_classifier
           (E : univ_topos_with_NNO_univ)
  : subobject_classifier (terminal_univ_cat_with_finlim E)
  := pr211 (pr112 E).

Definition univ_topos_with_NNO_univ_NNO
           (E : univ_topos_with_NNO_univ)
  : parameterized_NNO
      (terminal_univ_cat_with_finlim E)
      (binproducts_univ_cat_with_finlim E)
  := pr21 (pr112 E).

Definition is_locally_cartesian_closed_univ_topos_with_NNO_univ
           (E : univ_topos_with_NNO_univ)
  : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim E)
  := pr1 (pr212 E).

Coercion cat_with_ob_univ_topos_with_NNO_universe
           (E : univ_topos_with_NNO_univ)
  : univ_cat_with_finlim_universe.
Proof.
  use make_univ_cat_with_finlim_universe.
  - exact E.
  - exact (pr122 E).
  - exact (pr222 E).
Defined.

Definition make_univ_topos_with_NNO
           (E : univ_pi_pretopos)
           (Ω : subobject_classifier (terminal_univ_cat_with_finlim E))
           (N : parameterized_NNO
                  (terminal_univ_cat_with_finlim E)
                  (binproducts_univ_cat_with_finlim E))
           (u : E)
           (el : cat_stable_el_map (pretopos_to_finlim E ,, u))
           (H : is_coherent_cat_stable_el_map el)
  : univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, (((((((_ ,, (_ ,, _)) ,, _)
                   ,, ((_ ,, _) ,, _)) ,, _) ,, _) ,, tt) ,, (_ ,, tt))
                   ,, (_ ,, _ ,, _)) ; cbn.
  - exact (pretopos_to_finlim E).
  - exact (strict_initial_univ_pretopos E).
  - exact (bincoproducts_univ_pretopos E).
  - exact (stable_bincoproducts_univ_pretopos E).
  - exact (disjoint_bincoproducts_univ_pretopos E).
  - exact (is_regular_category_coeqs_of_kernel_pair
             (is_regular_category_univ_pretopos E)).
  - exact (is_regular_category_regular_epi_pb_stable
             (is_regular_category_univ_pretopos E)).
  - exact (all_internal_eqrel_effective_univ_pretopos E).
  - exact Ω.
  - exact N.
  - exact (univ_pi_pretopos_lccc E).
  - exact u.
  - exact el.
  - exact H.
Defined.

Definition functor_topos_with_NNO_univ
           (E₁ E₂ : univ_topos_with_NNO_univ)
  : UU
  := E₁ --> E₂.

Coercion functor_topos_with_NNO_univ_to_functor_pretopos
         {E₁ E₂ : univ_topos_with_NNO_univ}
         (F : functor_topos_with_NNO_univ E₁ E₂)
  : functor_pretopos E₁ E₂.
Proof.
  use make_functor_pretopos.
  - exact (pr1 F).
  - exact (pr11 (pr112 (pr112 F))).
  - exact (pr21 (pr112 (pr112 F))).
  - exact (pr12 (pr112 (pr112 F))).
Defined.

Definition preserves_subobject_classifier_functor_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F : functor_topos_with_NNO_univ E₁ E₂)
  : preserves_subobject_classifier
      F
      (terminal_univ_cat_with_finlim E₁)
      (terminal_univ_cat_with_finlim E₂)
      (functor_finlim_preserves_terminal F)
  := pr212 (pr112 F).

Definition preserves_NNO_functor_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F : functor_topos_with_NNO_univ E₁ E₂)
  : preserves_parameterized_NNO
      (univ_topos_with_NNO_univ_NNO E₁)
      (univ_topos_with_NNO_univ_NNO E₂)
      F
      (functor_finlim_preserves_terminal F)
  := pr22 (pr112 F).

Definition preserves_locally_cartesian_closed_functor_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F : functor_topos_with_NNO_univ E₁ E₂)
  : preserves_locally_cartesian_closed
      (functor_finlim_preserves_pullback F)
      (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₁)
      (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₂)
  := pr2 (pr212 F).

Definition functor_topos_with_NNO_universe
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F : functor_topos_with_NNO_univ E₁ E₂)
  : functor_finlim_universe
      (cat_with_ob_univ_topos_with_NNO_universe E₁)
      (cat_with_ob_univ_topos_with_NNO_universe E₂).
Proof.
  use make_functor_finlim_universe.
  - exact F.
  - exact (pr122 F).
  - exact (pr222 F).
Defined.

Definition make_functor_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F : functor_pretopos E₁ E₂)
           (HF : preserves_subobject_classifier
                   F
                   (terminal_univ_cat_with_finlim E₁)
                   (terminal_univ_cat_with_finlim E₂)
                   (functor_finlim_preserves_terminal F))
           (HF' : preserves_locally_cartesian_closed
                    (functor_finlim_preserves_pullback F)
                    (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₁)
                    (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₂))
           (HF'' : preserves_parameterized_NNO
                     (univ_topos_with_NNO_univ_NNO E₁)
                     (univ_topos_with_NNO_univ_NNO E₂)
                     F
                     (functor_finlim_preserves_terminal F))
           (Fu : z_iso
                   (F (univ_cat_universe E₁))
                   (univ_cat_universe E₂))
           (Fel : functor_preserves_el
                    (univ_cat_cat_stable_el_map E₁)
                    (univ_cat_cat_stable_el_map E₂)
                    (pr1 F ,, Fu))
  : functor_topos_with_NNO_univ E₁ E₂.
Proof.
  simple refine (_ ,, (((tt ,, ((((_ ,, _) ,, (_ ,, tt)) ,, _) ,, _))
                   ,, (tt ,, _)) ,, (_ ,, _))).
  - exact (functor_pretopos_to_functor_finlim F).
  - exact (preserves_initial_functor_pretopos F).
  - exact (preserves_bincoproduct_functor_pretopos F).
  - exact (preserves_regular_epi_functor_pretopos F).
  - exact HF.
  - exact HF''.
  - exact HF'.
  - exact Fu.
  - exact Fel.
Defined.

Definition nat_trans_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           (F G : functor_topos_with_NNO_univ E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_topos_with_NNO_univ_to_nat_trans_finlim
         {E₁ E₂ : univ_topos_with_NNO_univ}
         {F G : functor_topos_with_NNO_univ E₁ E₂}
         (τ : nat_trans_topos_with_NNO_univ F G)
  : nat_trans_finlim F G
  := pr1 τ.

Coercion nat_trans_topos_with_NNO_univ_to_nat_trans_finlim_universe
         {E₁ E₂ : univ_topos_with_NNO_univ}
         {F G : functor_topos_with_NNO_univ E₁ E₂}
         (τ : nat_trans_topos_with_NNO_univ F G)
  : nat_trans_finlim_universe
      (functor_topos_with_NNO_universe F)
      (functor_topos_with_NNO_universe G).
Proof.
  simple refine (pr1 τ ,, _ ,, _).
  - exact (pr122 τ).
  - exact (pr222 τ).
Defined.

Definition make_nat_trans_topos_with_NNO_univ
           {E₁ E₂ : univ_topos_with_NNO_univ}
           {F G : functor_topos_with_NNO_univ E₁ E₂}
           (τ : F ⟹ G)
           (p : τ (univ_cat_universe E₁)
                · functor_on_universe (functor_topos_with_NNO_universe G)
                =
                functor_on_universe (functor_topos_with_NNO_universe F))
           (q : nat_trans_preserves_el
                  (make_nat_trans_finlim τ ,, p
                    : nat_trans_finlim_ob
                        (functor_topos_with_NNO_universe F)
                        (functor_topos_with_NNO_universe G))
                  (functor_finlim_universe_preserves_el
                     (functor_topos_with_NNO_universe F))
                  (functor_finlim_universe_preserves_el
                     (functor_topos_with_NNO_universe G)))
  : nat_trans_topos_with_NNO_univ F G
  := make_nat_trans_finlim τ ,, (((tt ,, tt) ,, (tt ,, tt)) ,, p ,, q).

Proposition nat_trans_topos_with_NNO_eq
            {E₁ E₂ : univ_topos_with_NNO_univ}
            {F G : functor_topos_with_NNO_univ E₁ E₂}
            {τ₁ τ₂ : nat_trans_topos_with_NNO_univ F G}
            (p : ∏ (x : E₁), τ₁ x = τ₂ x)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isaproptotal2.
    - intro.
      use isaproptotal2.
      + intro.
        apply isaprop_nat_trans_preserves_el.
      + intros.
        apply homset_property.
    - intros.
      use pathsdirprod ; use pathsdirprod ; apply isapropunit.
  }
  use nat_trans_finlim_eq.
  exact p.
Qed.

(** * 3. The bicategory of elementary topos comprehension categories with a NNO and universe *)
Definition disp_bicat_univ_topos_with_NNO_univ_language
  : disp_bicat bicat_of_dfl_full_comp_cat
  := disp_dirprod_bicat
       disp_bicat_univ_topos_with_NNO_language
       disp_bicat_dfl_full_comp_cat_with_univ.

Proposition disp_2cells_isaprop_disp_bicat_univ_topos_with_NNO_univ_language
  : disp_2cells_isaprop disp_bicat_univ_topos_with_NNO_univ_language.
Proof.
  use disp_2cells_isaprop_prod.
  - exact disp_2cells_isaprop_disp_bicat_univ_topos_with_NNO_language.
  - exact disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ.
Defined.

Proposition disp_locally_groupoid_disp_bicat_univ_topos_with_NNO_univ_language
  : disp_locally_groupoid disp_bicat_univ_topos_with_NNO_univ_language.
Proof.
  use disp_locally_groupoid_prod.
  - exact disp_locally_groupoid_disp_bicat_univ_topos_with_NNO_language.
  - exact disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ.
Defined.

Proposition disp_univalent_2_disp_bicat_univ_topos_with_NNO_univ_language
  : disp_univalent_2 disp_bicat_univ_topos_with_NNO_univ_language.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_dfl_full_comp_cat.
  - exact disp_univalent_2_disp_bicat_univ_topos_with_NNO_language.
  - exact disp_univalent_2_disp_bicat_dfl_full_comp_cat_with_univ.
Qed.

Proposition disp_univalent_2_0_disp_bicat_univ_topos_with_NNO_univ_language
  : disp_univalent_2_0 disp_bicat_univ_topos_with_NNO_univ_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_with_NNO_univ_language.
Qed.

Proposition disp_univalent_2_1_disp_bicat_univ_topos_with_NNO_univ_language
  : disp_univalent_2_1 disp_bicat_univ_topos_with_NNO_univ_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_with_NNO_univ_language.
Qed.

Definition univ_topos_with_NNO_univ_language
  : bicat
  := total_bicat disp_bicat_univ_topos_with_NNO_univ_language.

Proposition is_univalent_2_univ_topos_with_NNO_univ_language
  : is_univalent_2 univ_topos_with_NNO_univ_language.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_univ_topos_with_NNO_univ_language.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_univ_topos_with_NNO_univ_language
  : is_univalent_2_0 univ_topos_with_NNO_univ_language.
Proof.
  apply is_univalent_2_univ_topos_with_NNO_univ_language.
Qed.

Proposition is_univalent_2_1_univ_topos_with_NNO_univ_language
  : is_univalent_2_1 univ_topos_with_NNO_univ_language.
Proof.
  apply is_univalent_2_univ_topos_with_NNO_univ_language.
Qed.

(** * 4. Accessors for elementary toposes comprehension categories with a NNO and universe *)
Definition topos_NNO_univ_comp_cat
  : UU
  := univ_topos_with_NNO_univ_language.

Coercion topos_NNO_comp_cat_univ_to_dfl_comp_cat
         (C : topos_NNO_univ_comp_cat)
  : dfl_full_comp_cat
  := pr1 C.

Definition fiberwise_strict_initial_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      strict_initial_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (local_property_conj_left
                   (pr1 (pr112 C)))))).

Definition fiberwise_bincoproduct_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      stable_bincoproducts_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (local_property_conj_left
                   (pr1 (pr112 C)))))).

Definition fiberwise_regular_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      regular_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_conj_right
          (local_property_conj_left
             (local_property_conj_left (pr1 (pr112 C))))).

Definition fiberwise_effective_eqrel_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      all_eqrel_effective_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_conj_right
          (local_property_conj_left
             (local_property_conj_left (pr1 (pr112 C))))).

Definition fiberwise_subobject_classifier_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      subobject_classifier_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_conj_left (pr1 (pr112 C))).

Definition fiberwise_nno_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : fiberwise_cat_property
      parameterized_NNO_local_property
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C)
  := local_property_conj_right (pr1 (pr112 C)).

Definition comp_cat_dependent_prod_topos_NNO_comp_cat
           (C : topos_NNO_univ_comp_cat)
  : comp_cat_dependent_prod C
  := pr1 (pr212 C).

Definition topos_NNO_comp_cat_universe
           (C : topos_NNO_univ_comp_cat)
  : dfl_full_comp_cat_with_univ.
Proof.
  use make_dfl_full_comp_cat_with_univ.
  - exact (topos_NNO_comp_cat_univ_to_dfl_comp_cat C).
  - exact (pr122 C).
  - exact (pr222 C).
Defined.

Definition topos_NNO_univ_comp_cat_functor
           (C₁ C₂ : topos_NNO_univ_comp_cat)
  : UU
  := C₁ --> C₂.

Coercion topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor
         {C₁ C₂ : topos_NNO_univ_comp_cat}
         (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C₁)
      (topos_NNO_comp_cat_univ_to_dfl_comp_cat C₂)
  := pr1 F.

Definition fiberwise_strict_initial_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_strict_initial_topos_NNO_comp_cat C₁)
      (fiberwise_strict_initial_topos_NNO_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left
                (local_property_functor_conj_left (pr2 (pr112 F)))))).

Definition fiberwise_bincoproduct_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_bincoproduct_topos_NNO_comp_cat C₁)
      (fiberwise_bincoproduct_topos_NNO_comp_cat C₂)
  := local_property_functor_conj_right
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left
                (local_property_functor_conj_left (pr2 (pr112 F)))))).

Definition fiberwise_regular_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_regular_topos_NNO_comp_cat C₁)
      (fiberwise_regular_topos_NNO_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_conj_right
          (local_property_functor_conj_left
             (local_property_functor_conj_left (pr2 (pr112 F))))).

Definition fiberwise_subobject_classifier_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_subobject_classifier_topos_NNO_comp_cat C₁)
      (fiberwise_subobject_classifier_topos_NNO_comp_cat C₂)
  := local_property_functor_conj_right
       (local_property_functor_conj_left (pr2 (pr112 F))).

Definition fiberwise_nno_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_nno_topos_NNO_comp_cat C₁)
      (fiberwise_nno_topos_NNO_comp_cat C₂)
  := local_property_functor_conj_right (pr2 (pr112 F)).

Definition preserves_comp_cat_dependent_prod_topos_NNO_comp_cat_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : preserves_comp_cat_dependent_prod
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (comp_cat_dependent_prod_topos_NNO_comp_cat C₁)
      (comp_cat_dependent_prod_topos_NNO_comp_cat C₂)
  := pr2 (pr212 F).

Definition topos_NNO_univ_comp_cat_with_functor
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : dfl_full_comp_cat_with_univ_functor
      (topos_NNO_comp_cat_universe C₁)
      (topos_NNO_comp_cat_universe C₂).
Proof.
  use make_dfl_full_comp_cat_with_univ_functor.
  - exact F.
  - exact (pr122 F).
  - exact (pr222 F).
Defined.

Definition topos_NNO_univ_comp_cat_nat_trans
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           (F G : topos_NNO_univ_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion topos_NNO_univ_comp_cat_nat_trans_to_dfl_full_comp_cat_nat_trans
         {C₁ C₂ : topos_NNO_univ_comp_cat}
         {F G : topos_NNO_univ_comp_cat_functor C₁ C₂}
         (τ : topos_NNO_univ_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor F)
      (topos_NNO_univ_comp_cat_functor_to_dfl_comp_cat_functor G)
  := pr1 τ.

Definition topos_NNO_univ_dfl_comp_cat_nat_trans_univ
           {C₁ C₂ : topos_NNO_univ_comp_cat}
           {F G : topos_NNO_univ_comp_cat_functor C₁ C₂}
           (τ : topos_NNO_univ_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_with_univ_nat_trans
      (topos_NNO_univ_comp_cat_with_functor F)
      (topos_NNO_univ_comp_cat_with_functor G).
Proof.
  use make_dfl_full_comp_cat_with_univ_nat_trans.
  - simple refine (_ ,, _).
    + exact (pr111 τ).
    + exact (pr122 τ).
  - exact (pr222 τ).
Defined.

(** * 5. The biequivalence *)
Definition disp_psfunctor_lang_univ_topos_with_NNO_univ
  : disp_psfunctor
      disp_bicat_of_univ_topos_with_NNO_univ
      disp_bicat_univ_topos_with_NNO_univ_language
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  refine (prod_disp_psfunctor
            _ _ _ _
            disp_psfunctor_lang_univ_topos_with_NNO
            finlim_to_dfl_comp_cat_disp_psfunctor_universe).
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
    + exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - use disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ.
Defined.

Definition lang_univ_topos_with_NNO_univ
  : psfunctor
      bicat_of_univ_topos_with_NNO_univ
      univ_topos_with_NNO_univ_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_univ_topos_with_NNO_univ.

Definition internal_language_univ_topos_with_NNO_univ
  : is_biequivalence lang_univ_topos_with_NNO_univ.
Proof.
  refine (total_is_biequivalence
            _ _ _
            (prod_disp_is_biequivalence_data
               _ _ _ _
               _ _ _ _
               _ _ _ _
               _ _ _ _
               (prod_disp_is_biequivalence_data
                  _ _ _ _
                  _ _ _ _
                  _ _ _ _
                  _ _ _ _
                  (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
                     topos_with_NNO_local_property)
                  finlim_biequiv_dfl_comp_cat_psfunctor_pi_types)
               finlim_biequiv_dfl_comp_cat_psfunctor_universe)).
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
    + exact disp_2cells_isaprop_univ_lccc.
  - use disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    + exact disp_locally_groupoid_univ_lccc.
  - exact disp_2cells_isaprop_disp_bicat_finlim_universe.
  - exact disp_locally_groupoid_disp_bicat_finlim_universe.
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
Defined.

Definition mod_univ_topos_with_NNO_univ
  : psfunctor
      univ_topos_with_NNO_univ_language
      bicat_of_univ_topos_with_NNO_univ
  := inv_psfunctor_of_is_biequivalence
       internal_language_univ_topos_with_NNO_univ.

Definition internal_language_univ_topos_with_NNO_univ_unit
  : pstrans
      (comp_psfunctor
         mod_univ_topos_with_NNO_univ
         lang_univ_topos_with_NNO_univ)
      (id_psfunctor _)
  := unit_of_is_biequivalence internal_language_univ_topos_with_NNO_univ.

Definition internal_language_univ_topos_with_NNO_univ_counit
  : pstrans
      (id_psfunctor _)
      (comp_psfunctor
         lang_univ_topos_with_NNO_univ
         mod_univ_topos_with_NNO_univ)
  := invcounit_of_is_biequivalence internal_language_univ_topos_with_NNO_univ.

Definition internal_language_univ_topos_with_NNO_univ_counit_pt
           (C : topos_NNO_univ_comp_cat)
  : C --> lang_univ_topos_with_NNO_univ (mod_univ_topos_with_NNO_univ C)
  := internal_language_univ_topos_with_NNO_univ_counit C.

(** * 6. Type formers in a topos with a universe *)

(** ** 6.1. Parameterized NNO *)
Definition disp_cat_ob_mor_topos_with_NNO_univ_nno_type
  : disp_cat_ob_mor bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact (λ (E : univ_topos_with_NNO_univ),
           pnno_in_cat_univ
             (C := E)
             (univ_topos_with_NNO_univ_NNO E)).
  - exact (λ (E₁ E₂ : univ_topos_with_NNO_univ)
             (c₁ : pnno_in_cat_univ
                     (C := E₁)
                     (univ_topos_with_NNO_univ_NNO E₁))
             (c₂ : pnno_in_cat_univ
                     (C := E₂)
                     (univ_topos_with_NNO_univ_NNO E₂))
             (F : functor_topos_with_NNO_univ E₁ E₂),
           functor_preserves_pnno_in_cat_univ
             c₁ c₂
             (functor_topos_with_NNO_universe F)
             (preserves_NNO_functor_topos_with_NNO_univ F)).
Defined.

Proposition disp_cat_id_comp_topos_with_NNO_univ_nno_type
  : disp_cat_id_comp
      bicat_of_univ_topos_with_NNO_univ
      disp_cat_ob_mor_topos_with_NNO_univ_nno_type.
Proof.
  split.
  - intros E c.
    refine (transportf
              (functor_preserves_pnno_in_cat_univ _ _ _)
              _
              (id_functor_preserves_pnno_in_cat_univ c)).
    apply isaprop_preserves_parameterized_NNO.
  - intros E₁ E₂ E₃ F G c₁ c₂ c₃ Fc Gc.
    refine (transportf
              (functor_preserves_pnno_in_cat_univ _ _ _)
              _
              (comp_functor_preserves_pnno_in_cat_univ Fc Gc)).
    apply isaprop_preserves_parameterized_NNO.
Defined.

Definition disp_cat_data_topos_with_NNO_univ_nno_type
  : disp_cat_data bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_topos_with_NNO_univ_nno_type.
  - exact disp_cat_id_comp_topos_with_NNO_univ_nno_type.
Defined.

Definition disp_bicat_topos_with_NNO_univ_nno_type
  : disp_bicat bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_topos_with_NNO_univ_nno_type.
Defined.

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_nno_type
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_nno_type.
Proof.
  use disp_cell_unit_bicat_univalent_2.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - intros.
    apply isaprop_functor_preserves_type_in_cat_univ.
  - intros.
    apply isaset_type_in_cat_univ.
  - intros E c₁ c₂ F.
    apply pnno_in_cat_univ_univalence_lemma.
    refine (transportf
              (functor_preserves_pnno_in_cat_univ _ _ _)
              _
              (pr1 F)).
    apply isaprop_preserves_parameterized_NNO.
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_nno_type
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_nno_type.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_nno_type.
Qed.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_nno_type
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_nno_type.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_nno_type.
Qed.

(** ** 6.2. Subobject classifier *)
Definition disp_cat_ob_mor_topos_with_NNO_univ_subobj_classifier
  : disp_cat_ob_mor bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact (λ (E : univ_topos_with_NNO_univ),
           subobject_classifier_in_cat_univ
             (C := E)
             (univ_topos_with_NNO_univ_subobject_classifier E)).
  - exact (λ (E₁ E₂ : univ_topos_with_NNO_univ)
             (c₁ : subobject_classifier_in_cat_univ
                     (C := E₁)
                     (univ_topos_with_NNO_univ_subobject_classifier E₁))
             (c₂ : subobject_classifier_in_cat_univ
                     (C := E₂)
                     (univ_topos_with_NNO_univ_subobject_classifier E₂))
             (F : functor_topos_with_NNO_univ E₁ E₂),
           functor_preserves_subobject_classifier_in_cat_univ
             c₁ c₂
             (functor_topos_with_NNO_universe F)
             (preserves_subobject_classifier_functor_topos_with_NNO_univ F)).
Defined.

Proposition disp_cat_id_comp_topos_with_NNO_univ_subobj_classifier
  : disp_cat_id_comp
      bicat_of_univ_topos_with_NNO_univ
      disp_cat_ob_mor_topos_with_NNO_univ_subobj_classifier.
Proof.
  split.
  - intros E c.
    refine (transportf
              (functor_preserves_subobject_classifier_in_cat_univ _ _ _)
              _
              (id_functor_preserves_subobject_classifier_in_cat_univ c)).
    apply isaprop_preserves_subobject_classifier.
  - intros E₁ E₂ E₃ F G c₁ c₂ c₃ Fc Gc.
    refine (transportf
              (functor_preserves_subobject_classifier_in_cat_univ _ _ _)
              _
              (comp_functor_preserves_subobject_classifier_in_cat_univ Fc Gc)).
    apply isaprop_preserves_subobject_classifier.
Defined.

Definition disp_cat_data_topos_with_NNO_univ_subobj_classifier
  : disp_cat_data bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_topos_with_NNO_univ_subobj_classifier.
  - exact disp_cat_id_comp_topos_with_NNO_univ_subobj_classifier.
Defined.

Definition disp_bicat_topos_with_NNO_univ_subobj_classifier
  : disp_bicat bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_topos_with_NNO_univ_subobj_classifier.
Defined.

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_subobj_classifier
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_subobj_classifier.
Proof.
  use disp_cell_unit_bicat_univalent_2.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - intros.
    apply isaprop_functor_preserves_type_in_cat_univ.
  - intros.
    apply isaset_type_in_cat_univ.
  - intros E c₁ c₂ F.
    apply subobject_classifier_in_cat_univ_univalence_lemma.
    refine (transportf
              (functor_preserves_subobject_classifier_in_cat_univ _ _ _)
              _
              (pr1 F)).
    apply isaprop_preserves_subobject_classifier.
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_subobj_classifier
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_subobj_classifier.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_subobj_classifier.
Qed.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_subobj_classifier
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_subobj_classifier.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_subobj_classifier.
Qed.

(** ** 6.3. Propositional resizing *)
Definition disp_cat_ob_mor_topos_with_NNO_univ_resizing
  : disp_cat_ob_mor bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact (λ (E : univ_topos_with_NNO_univ),
           cat_univ_stable_codes_resizing E).
  - exact (λ (E₁ E₂ : univ_topos_with_NNO_univ)
             (c₁ : cat_univ_stable_codes_resizing E₁)
             (c₂ : cat_univ_stable_codes_resizing E₂)
             (F : functor_topos_with_NNO_univ E₁ E₂),
           functor_preserves_stable_resizing_codes
             c₁ c₂
             (functor_topos_with_NNO_universe F)).
Defined.

Proposition disp_cat_id_comp_topos_with_NNO_univ_resizing
  : disp_cat_id_comp
      bicat_of_univ_topos_with_NNO_univ
      disp_cat_ob_mor_topos_with_NNO_univ_resizing.
Proof.
  split.
  - intros E c.
    exact (identity_preserves_resizing_codes c).
  - intros E₁ E₂ E₃ F G c₁ c₂ c₃ Fc Gc.
    exact (comp_preserves_resizing_codes Fc Gc).
Defined.

Definition disp_cat_data_topos_with_NNO_univ_resizing
  : disp_cat_data bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_topos_with_NNO_univ_resizing.
  - exact disp_cat_id_comp_topos_with_NNO_univ_resizing.
Defined.

Definition disp_bicat_topos_with_NNO_univ_resizing
  : disp_bicat bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_topos_with_NNO_univ_resizing.
Defined.

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_resizing
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_resizing.
Proof.
  use disp_cell_unit_bicat_univalent_2.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - intros.
    apply isaprop_functor_preserves_stable_resizing_codes.
  - intros.
    apply isaset_cat_univ_stable_codes_resizing.
  - intros E c₁ c₂ F.
    apply cat_univ_stable_codes_resizing_univalence_lemma.
    exact (pr1 F).
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_resizing
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_resizing.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_resizing.
Qed.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_resizing
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_resizing.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_resizing.
Qed.

(** ** 6.4. ∑-types *)
Definition disp_cat_ob_mor_topos_with_NNO_univ_sigma
  : disp_cat_ob_mor bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact (λ (E : univ_topos_with_NNO_univ),
           cat_univ_stable_codes_sigma E).
  - exact (λ (E₁ E₂ : univ_topos_with_NNO_univ)
             (c₁ : cat_univ_stable_codes_sigma E₁)
             (c₂ : cat_univ_stable_codes_sigma E₂)
             (F : functor_topos_with_NNO_univ E₁ E₂),
           functor_preserves_stable_codes_sigma
             c₁ c₂
             (functor_topos_with_NNO_universe F)).
Defined.

Proposition disp_cat_id_comp_topos_with_NNO_univ_sigma
  : disp_cat_id_comp
      bicat_of_univ_topos_with_NNO_univ
      disp_cat_ob_mor_topos_with_NNO_univ_sigma.
Proof.
  split.
  - intros E c.
    exact (identity_preserves_stable_codes_sigma c).
  - intros E₁ E₂ E₃ F G c₁ c₂ c₃ Fc Gc.
    exact (comp_preserves_stable_codes_sigma Fc Gc).
Defined.

Definition disp_cat_data_topos_with_NNO_univ_sigma
  : disp_cat_data bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_topos_with_NNO_univ_sigma.
  - exact disp_cat_id_comp_topos_with_NNO_univ_sigma.
Defined.

Definition disp_bicat_topos_with_NNO_univ_sigma
  : disp_bicat bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_topos_with_NNO_univ_sigma.
Defined.

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_sigma
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_sigma.
Proof.
  use disp_cell_unit_bicat_univalent_2.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - intros.
    apply isaprop_functor_preserves_stable_codes_sigma.
  - intros.
    apply isaset_cat_univ_stable_codes_sigma.
  - intros E c₁ c₂ F.
    apply sigma_univ_univalence_lemma.
    exact (pr1 F).
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_sigma
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_sigma.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_sigma.
Qed.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_sigma
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_sigma.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_sigma.
Qed.

(** ** 6.5. ∏-types *)
Definition disp_cat_ob_mor_topos_with_NNO_univ_pi
  : disp_cat_ob_mor bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact (λ (E : univ_topos_with_NNO_univ),
           cat_univ_stable_codes_pi
             (C := E)
             (is_locally_cartesian_closed_univ_topos_with_NNO_univ E)).
  - exact (λ (E₁ E₂ : univ_topos_with_NNO_univ)
             (c₁ : cat_univ_stable_codes_pi
                     (C := E₁)
                     (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₁))
             (c₂ : cat_univ_stable_codes_pi
                     (C := E₂)
                     (is_locally_cartesian_closed_univ_topos_with_NNO_univ E₂))
             (F : functor_topos_with_NNO_univ E₁ E₂),
           functor_preserves_stable_codes_pi
             c₁ c₂
             (functor_topos_with_NNO_universe F)
             (preserves_locally_cartesian_closed_functor_topos_with_NNO_univ F)).
Defined.

Proposition disp_cat_id_comp_topos_with_NNO_univ_pi
  : disp_cat_id_comp
      bicat_of_univ_topos_with_NNO_univ
      disp_cat_ob_mor_topos_with_NNO_univ_pi.
Proof.
  split.
  - intros E c.
    exact (identity_preserves_stable_codes_pi c).
  - intros E₁ E₂ E₃ F G c₁ c₂ c₃ Fc Gc.
    exact (comp_preserves_stable_codes_pi Fc Gc).
Defined.

Definition disp_cat_data_topos_with_NNO_univ_pi
  : disp_cat_data bicat_of_univ_topos_with_NNO_univ.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_topos_with_NNO_univ_pi.
  - exact disp_cat_id_comp_topos_with_NNO_univ_pi.
Defined.

Definition disp_bicat_topos_with_NNO_univ_pi
  : disp_bicat bicat_of_univ_topos_with_NNO_univ.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_topos_with_NNO_univ_pi.
Defined.

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_pi
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_pi.
Proof.
  use disp_cell_unit_bicat_univalent_2.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - intros.
    apply isaprop_functor_preserves_stable_codes_pi.
  - intros.
    apply isaset_cat_univ_stable_codes_pi.
  - intros E c₁ c₂ F.
    apply pi_univ_univalence_lemma.
    exact (pr1 F).
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_pi
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_pi.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_pi.
Qed.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_pi
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_pi.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_pi.
Qed.

(** ** 6.6. Universes for toposes *)
Definition disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_bicat bicat_of_univ_topos_with_NNO_univ
  := disp_dirprod_bicat
       disp_bicat_topos_with_NNO_univ_nno_type
       (disp_dirprod_bicat
          disp_bicat_topos_with_NNO_univ_subobj_classifier
          (disp_dirprod_bicat
             disp_bicat_topos_with_NNO_univ_resizing
             (disp_dirprod_bicat
                disp_bicat_topos_with_NNO_univ_sigma
                disp_bicat_topos_with_NNO_univ_pi))).

Proposition disp_univalent_2_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_univalent_2 disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  repeat (use is_univalent_2_dirprod_bicat).
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - exact disp_univalent_2_disp_bicat_topos_with_NNO_univ_nno_type.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - exact disp_univalent_2_disp_bicat_topos_with_NNO_univ_subobj_classifier.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - exact disp_univalent_2_disp_bicat_topos_with_NNO_univ_resizing.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - exact disp_univalent_2_disp_bicat_topos_with_NNO_univ_sigma.
  - exact disp_univalent_2_disp_bicat_topos_with_NNO_univ_pi.
Qed.

Proposition disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_univalent_2_0 disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_topos_univ.
Defined.

Proposition disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_univalent_2_1 disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  apply disp_univalent_2_disp_bicat_topos_with_NNO_univ_topos_univ.
Defined.

Proposition disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_2cells_iscontr disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  repeat (use disp_2cells_of_dirprod_iscontr) ; apply disp_2cells_iscontr_disp_bicat_cells_unit.
Qed.

Proposition disp_2cells_isaprop_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_2cells_isaprop disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  use disp_2cells_isaprop_from_disp_2cells_iscontr.
  exact disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.
Defined.

Proposition disp_locally_groupoid_disp_bicat_topos_with_NNO_univ_topos_univ
  : disp_locally_groupoid disp_bicat_topos_with_NNO_univ_topos_univ.
Proof.
  use disp_2cells_isgroupoid_from_disp_2cells_iscontr.
  exact disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.
Defined.

Definition disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_bicat univ_topos_with_NNO_univ_language
  := reindex_disp_bicat_univ
       is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ
       mod_univ_topos_with_NNO_univ
       disp_bicat_topos_with_NNO_univ_topos_univ
       disp_2cells_isaprop_disp_bicat_topos_with_NNO_univ_topos_univ.

Proposition disp_univalent_2_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_univalent_2 disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  use disp_univalent_2_reindex_disp_bicat.
  - exact disp_locally_groupoid_disp_bicat_topos_with_NNO_univ_topos_univ.
  - exact is_univalent_2_1_univ_topos_with_NNO_univ_language.
  - exact is_univalent_2_1_bicat_of_univ_topos_with_NNO_univ.
  - exact disp_univalent_2_0_disp_bicat_topos_with_NNO_univ_topos_univ.
  - exact disp_univalent_2_1_disp_bicat_topos_with_NNO_univ_topos_univ.
Qed.

Proposition disp_univalent_2_0_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_univalent_2_0 disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_with_NNO_topos_univ_language.
Defined.

Proposition disp_univalent_2_1_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_univalent_2_1 disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_with_NNO_topos_univ_language.
Defined.

Proposition disp_2cells_iscontr_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_2cells_iscontr disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  refine (disp_2cells_iscontr_reindex_disp_bicat _ _ _ _ _).
  apply disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.
Qed.

Proposition disp_2cells_isaprop_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_2cells_isaprop disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  use disp_2cells_isaprop_from_disp_2cells_iscontr.
  exact disp_2cells_iscontr_disp_bicat_univ_topos_with_NNO_topos_univ_language.
Defined.

Proposition disp_locally_groupoid_disp_bicat_univ_topos_with_NNO_topos_univ_language
  : disp_locally_groupoid disp_bicat_univ_topos_with_NNO_topos_univ_language.
Proof.
  use disp_2cells_isgroupoid_from_disp_2cells_iscontr.
  exact disp_2cells_iscontr_disp_bicat_univ_topos_with_NNO_topos_univ_language.
Defined.

(** * 7. Accessors for topos universes *)
Definition bicat_topos_with_NNO_univ_topos_univ
  : bicat
  := total_bicat disp_bicat_topos_with_NNO_univ_topos_univ.

Definition topos_with_NNO_univ_topos_univ
  : UU
  := bicat_topos_with_NNO_univ_topos_univ.

Coercion to_topos_with_NNO_univ
         (E : topos_with_NNO_univ_topos_univ)
  : univ_topos_with_NNO_univ
  := pr1 E.

Section UnivAccessors.
  Context (E : topos_with_NNO_univ_topos_univ).

  Definition topos_with_NNO_univ_topos_univ_pnno
    : pnno_in_cat_univ
        (C := E)
        (univ_topos_with_NNO_univ_NNO E)
    := pr12 E.

  Definition topos_with_NNO_univ_topos_univ_subobject_classifier
    : subobject_classifier_in_cat_univ
        (C := E)
        (univ_topos_with_NNO_univ_subobject_classifier E)
    := pr122 E.

  Definition topos_with_NNO_univ_topos_univ_resizing
    : cat_univ_stable_codes_resizing E
    := pr1 (pr222 E).

  Definition topos_with_NNO_univ_topos_univ_sigma
    : cat_univ_stable_codes_sigma E
    := pr12 (pr222 E).

  Definition topos_with_NNO_univ_topos_univ_pi
    : cat_univ_stable_codes_pi
        (C := E)
        (is_locally_cartesian_closed_univ_topos_with_NNO_univ E)
    := pr22 (pr222 E).
End UnivAccessors.

Definition make_topos_with_NNO_univ_topos_univ
           (E : univ_topos_with_NNO_univ)
           (nc : pnno_in_cat_univ
                   (C := E)
                   (univ_topos_with_NNO_univ_NNO E))
           (Ωc : subobject_classifier_in_cat_univ
                   (C := E)
                   (univ_topos_with_NNO_univ_subobject_classifier E))
           (rc : cat_univ_stable_codes_resizing E)
           (Σc : cat_univ_stable_codes_sigma E)
           (Πc : cat_univ_stable_codes_pi
                   (C := E)
                   (is_locally_cartesian_closed_univ_topos_with_NNO_univ E))
  : topos_with_NNO_univ_topos_univ
  := E ,, nc ,, Ωc ,, rc ,, Σc ,, Πc.

Definition functor_topos_with_NNO_univ_topos_univ
           (E₁ E₂ : topos_with_NNO_univ_topos_univ)
  : UU
  := E₁ --> E₂.

Coercion functor_topos_with_NNO_univ_topos_univ_to_functor_topos_with_NNO_univ
         {E₁ E₂ : topos_with_NNO_univ_topos_univ}
         (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_topos_with_NNO_univ E₁ E₂
  := pr1 F.

Definition functor_topos_with_NNO_univ_topos_univ_pnno
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_preserves_pnno_in_cat_univ
      (topos_with_NNO_univ_topos_univ_pnno E₁)
      (topos_with_NNO_univ_topos_univ_pnno E₂)
      (functor_topos_with_NNO_universe F)
      (preserves_NNO_functor_topos_with_NNO_univ F)
  := pr12 F.

Definition functor_topos_with_NNO_univ_topos_univ_subobject_classifier
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_preserves_subobject_classifier_in_cat_univ
      (topos_with_NNO_univ_topos_univ_subobject_classifier E₁)
      (topos_with_NNO_univ_topos_univ_subobject_classifier E₂)
      (functor_topos_with_NNO_universe F)
      (preserves_subobject_classifier_functor_topos_with_NNO_univ F)
  := pr122 F.

Definition functor_topos_with_NNO_univ_topos_univ_resizing
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_preserves_stable_resizing_codes
      (topos_with_NNO_univ_topos_univ_resizing E₁)
      (topos_with_NNO_univ_topos_univ_resizing E₂)
      (functor_topos_with_NNO_universe F)
  := pr1 (pr222 F).

Definition functor_topos_with_NNO_univ_topos_univ_sigma
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_preserves_stable_codes_sigma
      (topos_with_NNO_univ_topos_univ_sigma E₁)
      (topos_with_NNO_univ_topos_univ_sigma E₂)
      (functor_topos_with_NNO_universe F)
  := pr12 (pr222 F).

Definition functor_topos_with_NNO_univ_topos_univ_pi
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : functor_preserves_stable_codes_pi
      (topos_with_NNO_univ_topos_univ_pi E₁)
      (topos_with_NNO_univ_topos_univ_pi E₂)
      (functor_topos_with_NNO_universe F)
      (preserves_locally_cartesian_closed_functor_topos_with_NNO_univ F)
  := pr22 (pr222 F).

Definition make_functor_topos_with_NNO_univ_topos_univ
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F : functor_topos_with_NNO_univ E₁ E₂)
           (Fn : functor_preserves_pnno_in_cat_univ
                   (topos_with_NNO_univ_topos_univ_pnno E₁)
                   (topos_with_NNO_univ_topos_univ_pnno E₂)
                   (functor_topos_with_NNO_universe F)
                   (preserves_NNO_functor_topos_with_NNO_univ F))
           (FΩ : functor_preserves_subobject_classifier_in_cat_univ
                   (topos_with_NNO_univ_topos_univ_subobject_classifier E₁)
                   (topos_with_NNO_univ_topos_univ_subobject_classifier E₂)
                   (functor_topos_with_NNO_universe F)
                   (preserves_subobject_classifier_functor_topos_with_NNO_univ F))
           (Fr : functor_preserves_stable_resizing_codes
                   (topos_with_NNO_univ_topos_univ_resizing E₁)
                   (topos_with_NNO_univ_topos_univ_resizing E₂)
                   (functor_topos_with_NNO_universe F))
           (FΣ : functor_preserves_stable_codes_sigma
                   (topos_with_NNO_univ_topos_univ_sigma E₁)
                   (topos_with_NNO_univ_topos_univ_sigma E₂)
                   (functor_topos_with_NNO_universe F))
           (FΠ : functor_preserves_stable_codes_pi
                   (topos_with_NNO_univ_topos_univ_pi E₁)
                   (topos_with_NNO_univ_topos_univ_pi E₂)
                   (functor_topos_with_NNO_universe F)
                   (preserves_locally_cartesian_closed_functor_topos_with_NNO_univ F))
  : functor_topos_with_NNO_univ_topos_univ E₁ E₂
  := F ,, Fn ,, FΩ ,, Fr ,, FΣ ,, FΠ.

Definition nat_trans_topos_with_NNO_univ_topos_univ
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           (F G : functor_topos_with_NNO_univ_topos_univ E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_topos_with_NNO_univ_topos_univ_to_nat_trans_topos_NNO_univ
         {E₁ E₂ : topos_with_NNO_univ_topos_univ}
         {F G : functor_topos_with_NNO_univ_topos_univ E₁ E₂}
         (τ : nat_trans_topos_with_NNO_univ_topos_univ F G)
  : nat_trans_topos_with_NNO_univ F G
  := pr1 τ.

Definition make_nat_trans_topos_with_NNO_univ_topos_univ
           {E₁ E₂ : topos_with_NNO_univ_topos_univ}
           {F G : functor_topos_with_NNO_univ_topos_univ E₁ E₂}
           (τ : nat_trans_topos_with_NNO_univ F G)
  : nat_trans_topos_with_NNO_univ_topos_univ F G
  := τ ,, tt ,, tt ,, tt ,, tt ,, tt.

Proposition nat_trans_topos_with_NNO_univ_topos_univ_eq
            {E₁ E₂ : topos_with_NNO_univ_topos_univ}
            {F G : functor_topos_with_NNO_univ_topos_univ E₁ E₂}
            {τ₁ τ₂ : nat_trans_topos_with_NNO_univ_topos_univ F G}
            (p : (τ₁ : nat_trans_topos_with_NNO_univ F G) = τ₂)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro ; intros.
    apply disp_2cells_isaprop_disp_bicat_topos_with_NNO_univ_topos_univ.
  }
  exact p.
Qed.

Definition bicat_univ_topos_with_NNO_topos_univ_language
  : bicat
  := total_bicat disp_bicat_univ_topos_with_NNO_topos_univ_language.

Definition univ_topos_with_NNO_topos_univ_language
  : UU
  := bicat_univ_topos_with_NNO_topos_univ_language.

Definition univ_topos_with_NNO_topos_univ_language_to_comp_cat
           (C : univ_topos_with_NNO_topos_univ_language)
  : topos_NNO_univ_comp_cat
  := pr1 C.

Definition univ_topos_with_NNO_topos_univ_language_functor
           (C₁ C₂ : univ_topos_with_NNO_topos_univ_language)
  : UU
  := C₁ --> C₂.

Definition univ_topos_with_NNO_topos_univ_language_comp_cat_functor
           {C₁ C₂ : univ_topos_with_NNO_topos_univ_language}
           (F : univ_topos_with_NNO_topos_univ_language_functor C₁ C₂)
  : topos_NNO_univ_comp_cat_functor
      (univ_topos_with_NNO_topos_univ_language_to_comp_cat C₁)
      (univ_topos_with_NNO_topos_univ_language_to_comp_cat C₂)
  := pr1 F.

Definition univ_topos_with_NNO_topos_univ_language_nat_trans
           {C₁ C₂ : univ_topos_with_NNO_topos_univ_language}
           (F G : univ_topos_with_NNO_topos_univ_language_functor C₁ C₂)
  : UU
  := F ==> G.

Definition univ_topos_with_NNO_topos_univ_language_nat_comp_cat_trans
           {C₁ C₂ : univ_topos_with_NNO_topos_univ_language}
           {F G : univ_topos_with_NNO_topos_univ_language_functor C₁ C₂}
           (τ : univ_topos_with_NNO_topos_univ_language_nat_trans F G)
  : topos_NNO_univ_comp_cat_nat_trans
      (univ_topos_with_NNO_topos_univ_language_comp_cat_functor F)
      (univ_topos_with_NNO_topos_univ_language_comp_cat_functor G)
  := pr1 τ.

(** * 8. The biequivalence for topos universes *)
Definition disp_psfunctor_lang_univ_topos_with_NNO_topos_univ
  : disp_psfunctor
      disp_bicat_topos_with_NNO_univ_topos_univ
      disp_bicat_univ_topos_with_NNO_topos_univ_language
      lang_univ_topos_with_NNO_univ
  := reindex_disp_psfunctor_inv_univ
       is_univalent_2_bicat_of_univ_topos_with_NNO_univ
       internal_language_univ_topos_with_NNO_univ
       disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.

Definition disp_psfunctor_mod_univ_topos_with_NNO_topos_univ
  : disp_psfunctor
      disp_bicat_univ_topos_with_NNO_topos_univ_language
      disp_bicat_topos_with_NNO_univ_topos_univ
      mod_univ_topos_with_NNO_univ
  := reindex_disp_psfunctor_univ
       is_univalent_2_bicat_of_univ_topos_with_NNO_univ
       mod_univ_topos_with_NNO_univ
       disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.

Definition lang_univ_topos_with_NNO_topos_univ
  : psfunctor
      bicat_topos_with_NNO_univ_topos_univ
      bicat_univ_topos_with_NNO_topos_univ_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_univ_topos_with_NNO_topos_univ.

Definition mod_univ_topos_with_NNO_topos_univ
  : psfunctor
      bicat_univ_topos_with_NNO_topos_univ_language
      bicat_topos_with_NNO_univ_topos_univ
  := total_psfunctor
       _ _ _
       disp_psfunctor_mod_univ_topos_with_NNO_topos_univ.

Definition disp_biequivalence_unit_counit_topos_with_NNO_topos_univ
  : is_disp_biequivalence_unit_counit
      disp_bicat_topos_with_NNO_univ_topos_univ
      disp_bicat_univ_topos_with_NNO_topos_univ_language
      (coherent_is_biequivalence_adjoints
         is_univalent_2_univ_topos_with_NNO_univ_language
         internal_language_univ_topos_with_NNO_univ)
      disp_psfunctor_lang_univ_topos_with_NNO_topos_univ
      disp_psfunctor_mod_univ_topos_with_NNO_topos_univ
  := reindex_is_disp_biequivalence_unit_counit_univ_coh
       is_univalent_2_univ_topos_with_NNO_univ_language
       is_univalent_2_bicat_of_univ_topos_with_NNO_univ
       internal_language_univ_topos_with_NNO_univ
       disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.

Definition disp_biequivalence_data_topos_with_NNO_topos_univ
  : disp_is_biequivalence_data
      disp_bicat_topos_with_NNO_univ_topos_univ
      disp_bicat_univ_topos_with_NNO_topos_univ_language
      (coherent_is_biequivalence_adjoints
         is_univalent_2_univ_topos_with_NNO_univ_language
         internal_language_univ_topos_with_NNO_univ)
      disp_biequivalence_unit_counit_topos_with_NNO_topos_univ
  := reindex_disp_is_biequivalence_univ_coh
       is_univalent_2_univ_topos_with_NNO_univ_language
       is_univalent_2_bicat_of_univ_topos_with_NNO_univ
       internal_language_univ_topos_with_NNO_univ
       disp_2cells_iscontr_disp_bicat_topos_with_NNO_univ_topos_univ.

Definition internal_language_univ_topos_with_NNO_topos_univ
  : is_biequivalence lang_univ_topos_with_NNO_topos_univ
  := total_is_biequivalence
       _ _ _
       disp_biequivalence_data_topos_with_NNO_topos_univ.
