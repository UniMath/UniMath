(******************************************************************************************

 The domain displayed bicategory has a cleaving

 Contents
 1. Lax slices
 1.1. Characterization of opcartesian 2-cells
 1.2. Local opcleaving and isocleaving
 1.3. Characterizations of cartesian 1-cells
 1.4. Global cleaving
 2. Oplax slices
 2.1. Characterization of cartesian 2-cells
 2.2. Local cleaving and isocleaving
 2.3. Characterizations of cartesian 1-cells
 2.4. Global cleaving
 3. Slice bicatgories
 3.1. Local isocleaving
 3.2. Characterizations of cartesian 1-cells
 3.3. Global cleaving

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LaxSlice.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.

Local Open Scope cat.

(**
 1. Lax slices
 *)
Section LaxSliceCleaving.
  Context {B : bicat}
          (a : B).

  (**
   1.1. Characterization of opcartesian 2-cells
   *)
  Definition lax_slice_is_opcartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : lax_slice_disp_bicat B a c₁}
             {t₂ : lax_slice_disp_bicat B a c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
    : is_opcartesian_2cell (lax_slice_disp_bicat B a) αα.
  Proof.
    intros s₃ ss₃ γ γα.
    use iscontraprop1.
    - use isaproptotal2.
      + intro ; apply (lax_slice_disp_bicat B a).
      + intros.
        apply cellset_property.
    - simple refine (_ ,, _).
      + cbn in *.
        rewrite <- γα, <- αα.
        rewrite !vassocl.
        apply maponpaths.
        rewrite rwhisker_vcomp.
        apply idpath.
      + apply cellset_property.
  Qed.

  (**
   1.2. Local opcleaving and isocleaving
   *)
  Definition lax_slice_local_opcleaving
    : local_opcleaving (lax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _) ; cbn.
    - exact (α • (β ▹ t₂)).
    - simple refine (idpath _ ,, _).
      apply lax_slice_is_opcartesian_2cell.
  Defined.

  Definition lax_slice_local_iso_cleaving
    : local_iso_cleaving (lax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (α • (β^-1 ▹ s₂) ,, _ ,, _).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite rwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite id2_rwhisker ;
         apply id2_right).
    - apply lax_slice_disp_locally_groupoid.
  Defined.

  (**
   1.3. Characterizations of cartesian 1-cells
   *)
  Definition lax_slice_invertible_2cell_is_cartesian_1cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : lax_slice_disp_bicat B a c₁}
             {t₂ : lax_slice_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : is_invertible_2cell ss)
    : cartesian_1cell (lax_slice_disp_bicat B a) ss.
  Proof.
    split.
    - intros c₃ t₃ s' ss'.
      simple refine (_ ,, _).
      + exact (ss' • rassociator _ _ _ • (s' ◃ Hss^-1)).
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite !vassocl ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite lwhisker_id2 ;
             rewrite id2_left ;
             apply rassociator_lassociator).
        * apply lax_slice_disp_locally_groupoid.
    - cbn.
      intros c₃ t₃ s₁ s₂ α αα β ββ Lh Lh' ; cbn in *.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply (lax_slice_disp_bicat B a) | ] ;
           apply cellset_property).
      + cbn.
        simple  refine (_ ,, _).
        * abstract
            (pose (pr12 Lh') as p ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             use (vcomp_rcancel (s₂ ◃ ss)) ; [ is_iso ; apply Hss | ] ;
             use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
             refine (_ @ !p) ; clear p ;
             rewrite !vassocl ;
             pose (pr12 Lh) as p ;
             refine (_ @ ββ) ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             refine (_ @ maponpaths (λ z, z • _) p) ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             rewrite vcomp_whisker ;
             rewrite !vassocl ;
             rewrite rwhisker_rwhisker ;
             apply idpath).
        * apply cellset_property.
  Defined.

  Definition lax_slice_cartesian_1cell_is_invertible_2cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : lax_slice_disp_bicat B a c₁}
             {t₂ : lax_slice_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : cartesian_1cell (lax_slice_disp_bicat B a) ss)
    : is_invertible_2cell ss.
  Proof.
    cbn in *.
    pose (pr1 Hss c₁ (s · t₂) (id₁ _) (linvunitor _ • lassociator _ _ _)) as p.
    unfold lift_1cell_factor in p.
    cbn in p.
    pose (maponpaths (λ z, z • rassociator _ _ _) (pr12 p)) as d.
    cbn in d.
    rewrite id2_rwhisker in d.
    rewrite id2_right in d.
    rewrite !vassocl in d.
    rewrite !lassociator_rassociator in d.
    rewrite !id2_right in d.
    use make_is_invertible_2cell.
    - exact (pr1 p • lunitor _).
    - pose (@cartesian_1cell_lift_2cell
              _ _ _ _ _ _ _ _ Hss
              c₁
              t₁
              (id₁ _) (id₁ _)
              (ss • linvunitor _ • lassociator _ _ _)
              (ss • linvunitor _ • lassociator _ _ _)
              (id2 _)) as lift2.
      cbn in lift2.
      rewrite !id2_rwhisker, !id2_right in lift2.
      pose (lift2 (idpath _)) as l'.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left.
      refine (!(id2_right _) @ _).
      use (l' (ss • pr1 p ,, _) (linvunitor _ ,, _)) ; cbn.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_right.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite d.
          apply idpath.
        * apply lax_slice_disp_locally_groupoid.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_right.
          apply maponpaths_2.
          rewrite linvunitor_natural.
          rewrite <- lwhisker_hcomp.
          apply idpath.
        * apply lax_slice_disp_locally_groupoid.
    - rewrite !vassocl.
      rewrite <- vcomp_lunitor.
      rewrite !vassocr.
      rewrite d.
      apply linvunitor_lunitor.
  Qed.

  (**
   1.4. Global cleaving
   *)
  Definition lax_slice_global_cleaving
    : global_cleaving (lax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ s.
    simple refine (s · t₁ ,, id₂ _ ,, _) ; cbn.
    apply lax_slice_invertible_2cell_is_cartesian_1cell.
    is_iso.
  Defined.
End LaxSliceCleaving.

(**
 2. Oplax slices
 *)
Section OplaxSliceCleaving.
  Context {B : bicat}
          (a : B).

  (**
   2.1. Characterization of cartesian 2-cells
   *)
  Definition oplax_slice_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : oplax_slice_disp_bicat B a c₁}
             {t₂ : oplax_slice_disp_bicat B a c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
    : is_cartesian_2cell (oplax_slice_disp_bicat B a) αα.
  Proof.
    intros s₃ ss₃ γ γα.
    use iscontraprop1.
    - use isaproptotal2.
      + intro ; apply (oplax_slice_disp_bicat B a).
      + intros.
        apply cellset_property.
    - simple refine (_ ,, _).
      + cbn in *.
        rewrite <- αα, <- γα.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_vcomp.
        apply idpath.
      + apply cellset_property.
  Qed.

  (**
   2.2. Local cleaving and isocleaving
   *)
  Definition oplax_slice_local_cleaving
    : local_cleaving (oplax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _) ; cbn.
    - exact ((β ▹ t₂) • α).
    - simple refine (idpath _ ,, _).
      apply oplax_slice_is_cartesian_2cell.
  Defined.

  Definition oplax_slice_local_iso_cleaving
    : local_iso_cleaving (oplax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _ ,, _).
    - exact ((β ▹ s₂) • α).
    - abstract
        (cbn ;
         apply idpath).
    - apply oplax_slice_disp_locally_groupoid.
  Defined.

  (**
   2.3. Characterizations of cartesian 1-cells
   *)
  Definition oplax_slice_invertible_2cell_is_cartesian_1cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : oplax_slice_disp_bicat B a c₁}
             {t₂ : oplax_slice_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : is_invertible_2cell ss)
    : cartesian_1cell (oplax_slice_disp_bicat B a) ss.
  Proof.
    split.
    - intros c₃ t₃ s' ss'.
      simple refine (_ ,, _).
      + exact ((s' ◃ Hss^-1) • lassociator _ _ _ • ss').
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             rewrite id2_rwhisker, id2_left ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_rinv ;
             rewrite lwhisker_id2 ;
             rewrite id2_left ;
             rewrite !vassocr ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             apply idpath).
        * apply oplax_slice_disp_locally_groupoid.
    - cbn.
      intros c₃ t₃ s₁ s₂ α αα β ββ Lh Lh' ; cbn in *.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply (oplax_slice_disp_bicat B a) | ] ;
           apply cellset_property).
      + cbn.
        simple  refine (_ ,, _).
        * abstract
            (pose (pr12 Lh) as p ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_left in p ;
             pose (pr12 Lh') as p' ;
             cbn in p' ;
             rewrite id2_rwhisker in p' ;
             rewrite id2_left in p' ;
             cbn ;
             use (vcomp_lcancel (s₁ ◃ ss)) ; [ is_iso ; apply Hss | ] ;
             use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ] ;
             rewrite !vassocr ;
             refine (_ @ p) ;
             refine (_ @ ββ) ;
             refine (_ @ maponpaths (λ z, _ • z) (!p')) ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite rwhisker_rwhisker_alt ;
             rewrite !vassocl ;
             rewrite vcomp_whisker ;
             apply idpath).
        * apply cellset_property.
  Defined.

  Definition oplax_slice_cartesian_1cell_is_invertible_2cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : oplax_slice_disp_bicat B a c₁}
             {t₂ : oplax_slice_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : cartesian_1cell (oplax_slice_disp_bicat B a) ss)
    : is_invertible_2cell ss.
  Proof.
    cbn in *.
    pose (pr1 Hss c₁ (s · t₂) (id₁ _) (rassociator _ _ _ • lunitor _)) as p.
    unfold lift_1cell_factor in p.
    pose (pr12 p) as d.
    cbn in d.
    rewrite id2_rwhisker in d.
    rewrite id2_left in d.
    use make_is_invertible_2cell.
    - exact (linvunitor _ • pr1 p).
    - rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      rewrite <- d.
      rewrite id2_right.

      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    - pose (@cartesian_1cell_lift_2cell
              _ _ _ _ _ _ _ _ Hss
              c₁
              t₁
              (id₁ _) (id₁ _)
              (rassociator _ _ _ • lunitor _ • ss)
              (rassociator _ _ _ • lunitor _ • ss)
              (id2 _)) as lift2.
      cbn in lift2.
      rewrite !id2_rwhisker, !id2_left in lift2.
      pose (lift2 (idpath _)) as l'.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (!(id2_left _) @ _).
      use (l' (lunitor _ ,, _) (pr1 p • ss ,, _)) ; cbn.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_left.
          rewrite !vassocl.
          apply maponpaths.
          rewrite vcomp_lunitor.
          apply idpath.
        * apply oplax_slice_disp_locally_groupoid.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_left.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite d.
          rewrite !vassocl.
          apply idpath.
        * apply oplax_slice_disp_locally_groupoid.
  Qed.

  (**
   2.4. Global cleaving
   *)
  Definition oplax_slice_global_cleaving
    : global_cleaving (oplax_slice_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ s.
    simple refine (s · t₁ ,, id₂ _ ,, _) ; cbn.
    apply oplax_slice_invertible_2cell_is_cartesian_1cell.
    is_iso.
  Defined.
End OplaxSliceCleaving.


(**
 3. Slice bicatgories
 *)
Section SliceCleaving.
  Context {B : bicat}
          (a : B).

  (**
   3.1. Local isocleaving
   *)
  Definition slice_local_iso_cleaving
    : local_iso_cleaving (slice_disp_bicat a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _ ,, _).
    - exact (comp_of_invertible_2cell
               α
               (rwhisker_of_invertible_2cell
                  _
                  (inv_of_invertible_2cell β))).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite rwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite id2_rwhisker ;
         apply id2_right).
    - apply disp_locally_groupoid_slice_disp_bicat.
  Defined.

  (**
   3.2. Characterizations of cartesian 1-cells
   *)
  Definition slice_is_cartesian_1cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : slice_disp_bicat a c₁}
             {t₂ : slice_disp_bicat a c₂}
             (ss : t₁ -->[ s ] t₂)
    : cartesian_1cell (slice_disp_bicat a) ss.
  Proof.
    split.
    - intros c₃ t₃ s' ss'.
      simple refine (_ ,, _).
      + exact (comp_of_invertible_2cell
                 ss'
                 (comp_of_invertible_2cell
                    (rassociator_invertible_2cell _ _ _)
                    (lwhisker_of_invertible_2cell
                       _
                       (inv_of_invertible_2cell ss)))).
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite !vassocl ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite lwhisker_id2 ;
             rewrite id2_left ;
             apply rassociator_lassociator).
        * apply disp_locally_groupoid_slice_disp_bicat.
    - cbn.
      intros c₃ t₃ s₁ s₂ α αα β ββ Lh Lh' ; cbn in *.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply (slice_disp_bicat a) | ] ;
           apply cellset_property).
      + cbn.
        simple  refine (_ ,, _).
        * abstract
            (pose (pr12 Lh') as p ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             use (vcomp_rcancel (s₂ ◃ ss)) ; [ is_iso ; apply ss | ] ;
             use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
             rewrite !vassocl ;
             refine (_ @ !p) ; clear p ;
             pose (pr12 Lh) as p ;
             refine (_ @ ββ) ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             refine (_ @ maponpaths (λ z, z • _) p) ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             rewrite vcomp_whisker ;
             rewrite !vassocl ;
             rewrite rwhisker_rwhisker ;
             apply idpath).
        * apply cellset_property.
  Defined.

  (**
   3.3. Global cleaving
   *)
  Definition slice_global_cleaving
    : global_cleaving (slice_disp_bicat a).
  Proof.
    intros c₁ c₂ t₁ s.
    cbn in *.
    simple refine (s · t₁ ,, id2_invertible_2cell _ ,, _) ; cbn.
    apply slice_is_cartesian_1cell.
  Defined.
End SliceCleaving.
