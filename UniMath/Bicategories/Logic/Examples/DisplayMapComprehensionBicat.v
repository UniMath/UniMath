(*******************************************************************

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Logic.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.DisplayMapBicatCleaving.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

(**
 6. The comprehension bicategory of a display map bicategory
 *)
Section DispMapBicatToCompBicat.
  Context {B : bicat}
          (D : disp_map_bicat B)
          (HB : is_univalent_2 B).

  Let DD : disp_bicat B := disp_map_bicat_to_disp_bicat D.

  Definition disp_map_bicat_comprehension_data
    : disp_psfunctor_data DD (cod_disp_bicat B) (id_psfunctor B).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x hx, pr1 hx ,, pr12 hx).
    - exact (λ x y f hx hy hf, pr1 hf ,, pr22 hf).
    - exact (λ x y f g α hx hy hf hg hα, hα).
    - simple refine (λ x hx, _ ,, _).
      + use make_disp_2cell_cod.
        * exact (id₂ _).
        * abstract
            (unfold coherent_homot ; cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             apply idpath).
      + use is_disp_invertible_2cell_cod ; simpl.
        is_iso.
    - simple refine (λ x y z f g hx hy hz hf hg, _ ,, _).
      + use make_disp_2cell_cod.
        * exact (id₂ _).
        * abstract
            (unfold coherent_homot ; cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             apply idpath).
      + use is_disp_invertible_2cell_cod ; simpl.
        is_iso.
  Defined.

  Definition disp_map_bicat_comprehension_is_disp_psfunctor
    : is_disp_psfunctor _ _ _ disp_map_bicat_comprehension_data.
  Proof.
    repeat split ; intro ; intros ;
      (use subtypePath ; [ intro ; apply cellset_property | ]).
    - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)) ; cbn.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)) ; cbn.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)) ; cbn.
      rewrite id2_rwhisker, lwhisker_id2.
      rewrite !id2_left, !id2_right.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)) ; cbn.
      rewrite !id2_left, id2_right.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)) ; cbn.
      rewrite !id2_left, id2_right.
      apply idpath.
  Qed.

  Definition disp_map_bicat_comprehension
    : disp_psfunctor DD (cod_disp_bicat B) (id_psfunctor B)
    := disp_map_bicat_comprehension_data
       ,,
       disp_map_bicat_comprehension_is_disp_psfunctor.

  Definition global_cartesian_disp_map_bicat_comprehension
    : global_cartesian_disp_psfunctor disp_map_bicat_comprehension.
  Proof.
    use preserves_global_lifts_to_cartesian.
    - exact HB.
    - exact (cod_disp_univalent_2 _ HB).
    - exact (global_cleaving_of_disp_map_bicat D).
    - intros x y f hy.
      use is_pb_to_cartesian_1cell.
      exact (mirror_has_pb_ump
               (pb_of_pred_ob_has_pb_ump D (pr12 hy) f (pr22 hy))).
  Defined.

  Definition disp_map_bicat_to_comp_bicat
    : comprehension_bicat_structure B.
  Proof.
    use make_comprehension_bicat_structure.
    - exact DD.
    - exact disp_map_bicat_comprehension.
    - exact (global_cleaving_of_disp_map_bicat D).
    - exact global_cartesian_disp_map_bicat_comprehension.
  Defined.

  Definition disp_map_bicat_to_comp_bicat_local_opcartesian
             (HD : is_covariant_disp_map_bicat D)
    : local_opcartesian_disp_psfunctor
        (comp_of disp_map_bicat_to_comp_bicat).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? H.
    apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
    cbn.
    apply (disp_map_is_opcartesian_2cell_to_is_opcartesian_2cell_sopfib _ HD).
    exact H.
  Defined.

  Definition is_covariant_disp_map_bicat_to_comp_bicat
             (HD : is_covariant_disp_map_bicat D)
    : is_covariant disp_map_bicat_to_comp_bicat.
  Proof.
    repeat split.
    - exact (local_opcleaving_of_disp_map_bicat _ HD).
    - exact (lwhisker_opcartesian_disp_map_bicat _ HD).
    - exact (rwhisker_opcartesian_disp_map_bicat _ HD).
    - exact (disp_map_bicat_to_comp_bicat_local_opcartesian HD).
  Defined.

  Definition disp_map_bicat_to_comp_bicat_local_cartesian
             (HD : is_contravariant_disp_map_bicat D)
    : local_cartesian_disp_psfunctor
        (comp_of disp_map_bicat_to_comp_bicat).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? H.
    apply is_cartesian_2cell_sfib_to_is_cartesian_2cell.
    cbn.
    apply (disp_map_is_cartesian_2cell_to_is_cartesian_2cell_sfib _ HD).
    exact H.
  Defined.

  Definition is_contravariant_disp_map_bicat_to_comp_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : is_contravariant disp_map_bicat_to_comp_bicat.
  Proof.
    repeat split.
    - exact (local_cleaving_of_disp_map_bicat _ HD).
    - exact (lwhisker_cartesian_disp_map_bicat _ HD).
    - exact (rwhisker_cartesian_disp_map_bicat _ HD).
    - exact (disp_map_bicat_to_comp_bicat_local_cartesian HD).
  Defined.

  Definition disp_map_bicat_comprehension_bicat
             (HD : is_covariant_disp_map_bicat D)
    : comprehension_bicat
    := _ ,, _ ,, is_covariant_disp_map_bicat_to_comp_bicat HD.

  Definition disp_map_bicat_contravariant_comprehension_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : contravariant_comprehension_bicat
    := _ ,, _ ,, is_contravariant_disp_map_bicat_to_comp_bicat HD.
End DispMapBicatToCompBicat.

(**
 7. Internal Street fibrations and opfibrations
 *)
Definition internal_sfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat_structure B
  := disp_map_bicat_to_comp_bicat (sfib_disp_map_bicat B) HB.

Definition is_contravariant_internal_sfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : is_contravariant (internal_sfib_comprehension_bicat_structure B HB).
Proof.
  use is_contravariant_disp_map_bicat_to_comp_bicat.
  apply sfib_disp_map_bicat_is_contravariant.
Defined.

Definition internal_sfib_contravariant_comprehension_bicat
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : contravariant_comprehension_bicat
  := _ ,, _ ,, is_contravariant_internal_sfib_comprehension_bicat_structure B HB.

Definition internal_sopfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat_structure B
  := disp_map_bicat_to_comp_bicat (sopfib_disp_map_bicat B) HB.

Definition is_covariant_internal_sopfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : is_covariant (internal_sopfib_comprehension_bicat_structure B HB).
Proof.
  use is_covariant_disp_map_bicat_to_comp_bicat.
  apply sopfib_disp_map_bicat_is_covariant.
Defined.

Definition internal_sopfib_comprehension_bicat
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat
  := _ ,, _ ,, is_covariant_internal_sopfib_comprehension_bicat_structure B HB.
