(*****************************************************************************

 The cleaving associated to a display map bicategories

 Every display map bicategory gives rise to a cleaving. If the display map
 bicategory is covariant, then the associated cleaving has a local opcleaving.
 If the display map bicategory is contravariant, then so is the associated
 cleaving has a local cleaving.

 1. Pullback squares are cartesian 1-cells
 2. Global cleaving
 3. Characterization of cartesian cells
 4. Characterization of opcartesian cells
 5. Local cleaving
 6. Local opcleaving

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.InternalStreetOpFibration.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

Section DispMapBicatCleaving.
  Context {B : bicat}
          (D : disp_map_bicat B).

  Let DD : disp_bicat B := disp_map_bicat_to_disp_bicat D.

  (**
   1. Pullback squares are cartesian 1-cells
   *)
  Section PullbackToCartesian.
    Context {pb x y z : B}
            {f : y --> z}
            {g : x --> z}
            (p₁ : pb --> x)
            (p₂ : pb --> y)
            (Hp₂ : pred_ob D p₂)
            (Hg : pred_ob D g)
            (Hp₁ : pred_mor D p₂ g p₁)
            (γ : invertible_2cell (p₁ · g) (p₂ · f) )
            (cone := make_pb_cone pb p₁ p₂  γ)
            (Hpb : has_pb_ump cone).

    Let hy : DD y.
    Proof.
      use make_disp_map_bicat_ob.
      - exact pb.
      - exact p₂.
      - exact Hp₂.
    Defined.

    Let hz : DD z.
    Proof.
      use make_disp_map_bicat_ob.
      - exact x.
      - exact g.
      - exact Hg.
    Defined.

    Let hf : hy -->[ f ] hz.
    Proof.
      use make_disp_map_bicat_mor.
      - exact p₁.
      - exact Hp₁.
      - exact (inv_of_invertible_2cell γ).
    Defined.

    Section LiftOneCellFactor.
      Context {c : B}
              {cc : DD c}
              {k : B ⟦ c, y ⟧}
              (gg : cc -->[ k · f ] hz).

      Let other_cone : pb_cone g f
        := make_pb_cone
             (pr1 cc)
             (pr1 gg)
             (pr12 cc · k)
             (comp_of_invertible_2cell
                (inv_of_invertible_2cell (pr22 gg))
                (lassociator_invertible_2cell _ _ _)).

      Let φ : pb_1cell other_cone cone
        := has_pb_ump_1 Hpb other_cone.

      Definition pb_lift_1cell_factor
        : lift_1cell_factor DD hf gg.
      Proof.
        simple refine (_ ,, (_ ,, _) ,, _).
        - use make_disp_map_bicat_mor.
          + exact (pb_1cell_1cell φ).
          + exact (pred_mor_closed_under_pb_ump_mor
                     D
                     _ _ _ _ _ _ _ _ _
                     Hpb
                     other_cone
                     _ _ _ _ _
                     Hg
                     Hp₁
                     (pr12 gg)).
          + exact (inv_of_invertible_2cell (pb_1cell_pr2 φ)).
        - exact (pb_1cell_pr1 φ).
        - abstract
            (cbn ;
             pose (pb_1cell_eq φ) as q ;
             cbn in q ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             do 4 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn) ;
             rewrite q ;
             rewrite !vassocl ;
             apply maponpaths ;
             refine (!_) ;
             etrans ;
             [ do 4 apply maponpaths ;
               rewrite !vassocr ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               rewrite !vassocl ;
               apply idpath
             | ] ;
             etrans ;
             [ do 3 apply maponpaths ;
               rewrite !vassocr ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker, id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ do 2 apply maponpaths ;
               rewrite !vassocr ;
               rewrite lassociator_rassociator, id2_left ;
               apply idpath
             | ] ;
             rewrite vcomp_linv ;
             apply id2_right).
        - apply is_invertible_to_is_disp_invertible.
          apply property_from_invertible_2cell.
      Defined.
    End LiftOneCellFactor.

    Section LiftTwoCellFactor.
      Context {c : B}
              {cc : DD c}
              {h h' : c --> y}
              {gg : cc -->[ h · f ] hz}
              {gg' : cc -->[ h' · f ] hz}
              {δ : h ==> h'}
              (σσ : disp_2cells (δ ▹ f) gg gg')
              (Lh : lift_1cell_factor DD hf gg)
              (Lh' : lift_1cell_factor DD hf gg').

      Let ℓ : pr1 cc --> pr1 hy := pr11 Lh.
      Let ℓp₂ : invertible_2cell (pr12 cc · h) (ℓ · p₂)  := pr221 Lh.
      Let ℓp₁
        : invertible_2cell (ℓ · p₁) (pr1 gg).
      Proof.
        use make_invertible_2cell.
        - exact (pr112 Lh).
        - apply (is_disp_invertible_to_is_invertible _ _ _ (pr22 Lh)).
      Defined.

      Let ℓ' : pr1 cc --> pb := pr11 Lh'.
      Let ℓ'p₂ : invertible_2cell (pr12 cc · h') (ℓ' · p₂) := pr221 Lh'.
      Let ℓ'p₁
        : invertible_2cell (ℓ' · p₁) (pr1 gg').
      Proof.
        use make_invertible_2cell.
        - exact (pr112 Lh').
        - apply (is_disp_invertible_to_is_invertible _ _ _ (pr22 Lh')).
      Defined.

      Definition pb_lift_2cell_factor_cell_eq
        : (ℓ ◃ γ)
          • lassociator ℓ p₂ f
          • ((ℓp₂ ^-1 • (pr12 cc ◃ δ) • ℓ'p₂) ▹ f)
          • rassociator ℓ' p₂ f
          =
          lassociator ℓ p₁ g
          • ((ℓp₁ • pr1 σσ • ℓ'p₁ ^-1) ▹ g)
          • rassociator ℓ' p₁ g
          • (ℓ' ◃ γ).
      Proof.
        pose (pr212 Lh) as d.
        pose (pr212 Lh') as d'.
        pose (pr2 σσ) as d''.
        cbn in d, d', d''.
        rewrite lwhisker_id2, id2_left in d.
        rewrite lwhisker_id2, id2_left in d'.
        refine (!_).
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        use vcomp_move_L_pM.
        {
          is_iso.
          apply property_from_invertible_2cell.
        }
        cbn.
        do 2 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn).
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        rewrite !vassocr.
        rewrite !vassocr in d.
        etrans.
        {
          do 4 apply maponpaths_2.
          exact d.
        }
        clear d.
        rewrite d'' ; clear d''.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        rewrite <- d' ; clear d'.
        use vcomp_move_R_Mp.
        {
          is_iso ;
            [ apply (is_invertible_2cell_inv (pr2 ℓ'p₁))
            | apply property_from_invertible_2cell ].
        }
        cbn.
        rewrite !vassocl.
        apply idpath.
      Qed.

      Definition pb_lift_2cell_factor_cell
        : ℓ ==> ℓ'.
      Proof.
        use (pb_ump_cell Hpb) ; cbn.
        - exact (ℓp₁ • pr1 σσ • (ℓ'p₁)^-1).
        - exact (ℓp₂^-1 • (_ ◃ δ) • ℓ'p₂).
        - exact pb_lift_2cell_factor_cell_eq.
      Defined.

      Definition pb_lift_2cell_factor_unique
        : isaprop (lift_2cell_factor_type DD hf σσ Lh Lh').
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply disp_cellset_property.
        }
        use subtypePath.
        {
          intro ; apply cellset_property.
        }
        use (pb_ump_eq Hpb).
        - exact (ℓp₁ • pr1 σσ • (ℓ'p₁)^-1).
        - exact (ℓp₂^-1 • (_ ◃ δ) • ℓ'p₂).
        - apply pb_lift_2cell_factor_cell_eq.
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (!(transportf_disp_map_bicat_cell _ _ _) @ maponpaths pr1 (pr2 φ₁)).
        - rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          exact (pr21 φ₁).
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (!(transportf_disp_map_bicat_cell _ _ _) @ maponpaths pr1 (pr2 φ₂)).
        - rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          exact (pr21 φ₂).
      Qed.

      Definition pb_lift_2cell_factor
        : lift_2cell_factor DD hf σσ Lh Lh'.
      Proof.
        use iscontraprop1.
        - exact pb_lift_2cell_factor_unique.
        - simple refine (_ ,, _).
          + use make_disp_map_bicat_cell.
            * exact pb_lift_2cell_factor_cell.
            * abstract
                (etrans ;
                 [ apply maponpaths ;
                   apply (pb_ump_cell_pr2 Hpb)
                 | ] ;
                 rewrite !vassocr ;
                 rewrite vcomp_rinv, id2_left ;
                 apply idpath).
          + abstract
              (use subtypePath ; [ intro ; apply cellset_property | ] ;
               refine (transportf_disp_map_bicat_cell _ _ _ @ _) ;
               cbn ;
               etrans ; [ apply maponpaths_2 ; apply (pb_ump_cell_pr1 Hpb) | ] ;
               do 2 refine (vassocl _ _ _ @ _) ;
               apply maponpaths ;
               refine (_ @ id2_right _) ;
               apply maponpaths ;
               apply vcomp_linv).
      Defined.
    End LiftTwoCellFactor.

    Definition pb_to_cartesian_1cell
      : cartesian_1cell DD hf.
    Proof.
      split.
      - exact @pb_lift_1cell_factor.
      - exact @pb_lift_2cell_factor.
    Defined.
  End PullbackToCartesian.

  (**
   2. Global cleaving
   *)
  Definition global_cleaving_of_disp_map_bicat
    : global_cleaving DD.
  Proof.
    intros x y yy f.
    pose (pb := pb_ob_of_pred_ob D (pr12 yy) f (pr22 yy)).
    pose (p₁ := pb_pr1_of_pred_ob D (pr12 yy) f (pr22 yy)).
    pose (p₂ := pb_pr2_of_pred_ob D (pr12 yy) f (pr22 yy)).
    pose (γ := pb_cell_of_pred_ob D (pr12 yy) f (pr22 yy)).
    pose (ump := pb_of_pred_ob_has_pb_ump D (pr12 yy) f (pr22 yy)).
    pose (Hp₁ := mor_of_pb_preserves_pred_ob D (pr22 yy) ump).
    pose (Hp₂ := pb_preserves_pred_ob D (pr22 yy) ump).
    simple refine (_ ,, _ ,, _).
    - use make_disp_map_bicat_ob.
      + exact pb.
      + exact p₂.
      + exact Hp₂.
    - use make_disp_map_bicat_mor ; cbn.
      + exact p₁.
      + exact Hp₁.
      + exact (inv_of_invertible_2cell γ).
    - apply pb_to_cartesian_1cell.
      apply ump.
  Defined.

  (**
   3. Characterization of cartesian cells
   *)
  Section CartesianOfSFibToCartesian.
    Context {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : DD c₁}
            {t₂ : DD c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_cartesian_2cell_sfib (pr12 t₂) (pr1 αα)).

    Section FixSome.
      Context {h : c₁ --> c₂}
              {hh : t₁ -->[ h] t₂}
              {γ : h ==> s₁}
              (γα : hh ==>[ γ • α] ss₂).

      Definition disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_unique
        : isaprop (∑ γγ : hh ==>[ γ] ss₁, γγ •• αα = γα).
      Proof.
        cbn in *.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply disp_map_bicat_to_disp_bicat | ].
        use subtypePath ; [ intro ; apply cellset_property | ].
        use (is_cartesian_2cell_sfib_factor_unique _ Hαα).
        - exact (pr1 γα).
        - exact ((pr22 hh)^-1 • (_ ◃ γ) • pr22 ss₁).
        - abstract
            (rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             refine (pr2 γα @ _) ;
             rewrite <- lwhisker_vcomp ;
             rewrite !vassocl ;
             apply maponpaths ;
             exact (!(pr2 αα))).
        - abstract
            (rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             exact (pr21 φ₁)).
        - abstract
            (rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             exact (pr21 φ₂)).
        - exact (maponpaths pr1 (pr2 φ₁)).
        - exact (maponpaths pr1 (pr2 φ₂)).
      Qed.

      Definition disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell
        : hh ==>[ γ ] ss₁.
      Proof.
        use make_disp_map_bicat_cell.
        - use (is_cartesian_2cell_sfib_factor _ Hαα (pr1 γα)).
          + exact ((pr22 hh)^-1 • (_ ◃ γ) • pr22 ss₁).
          + abstract
              (rewrite !vassocl ;
               use vcomp_move_L_pM ; [ is_iso | ] ;
               refine (pr2 γα @ _) ;
               rewrite <- lwhisker_vcomp ;
               rewrite !vassocl ;
               apply maponpaths ;
               exact (!(pr2 αα))).
        - abstract
            (rewrite is_cartesian_2cell_sfib_factor_over ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             rewrite id2_left ;
             apply idpath).
      Defined.

      Definition disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_comm
        : disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell •• αα = γα.
      Proof.
        cbn.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        apply is_cartesian_2cell_sfib_factor_comm.
      Qed.
    End FixSome.

    Definition disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell
      : is_cartesian_2cell DD αα.
    Proof.
      intros h hh γ γα.
      use iscontraprop1.
      - exact (disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_unique γα).
      - simple refine (_ ,, _).
        + exact (disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell γα).
        + exact (disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell_comm γα).
    Defined.
  End CartesianOfSFibToCartesian.

  Section CartesianOfSFibToCartesian.
    Context (HD : is_contravariant_disp_map_bicat D)
            {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : DD c₁}
            {t₂ : DD c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_cartesian_2cell DD αα).

    Let Ht₂ : internal_sfib (pr12 t₂).
    Proof.
      apply HD.
      exact (pr22 t₂).
    Defined.

    Let f : pr1 t₁ --> pr1 t₂
      := internal_sfib_cleaving_lift_mor _ Ht₂ ((_ ◃ α) • pr22 ss₂).

    Let β : f ==> pr1 ss₂
      := internal_sfib_cleaving_lift_cell _ Ht₂ ((_ ◃ α) • pr22 ss₂).

    Let γ : invertible_2cell (f · pr12 t₂) (pr12 t₁ · s₁)
      := internal_sfib_cleaving_com _ Ht₂ ((_ ◃ α) • pr22 ss₂).

    Let Hss₂ : mor_preserves_cartesian (pr12 t₁) (pr12 t₂) (pr1 ss₂)
      := pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 ss₂).

    Local Definition disp_map_cartesian_2cell_sfib_src : t₁ -->[ s₁] t₂.
    Proof.
      use make_disp_map_bicat_mor.
      - exact f.
      - apply HD.
        unfold f.
        intros z h₁ h₂ δ Hδ.
        assert (H₁ : is_cartesian_2cell_sfib (pr12 t₂) (h₂ ◃ β)).
        {
          apply (pr2 Ht₂).
          apply internal_sfib_cleaving_is_cartesian.
        }
        assert (H₂ : is_cartesian_2cell_sfib (pr12 t₂) (h₁ ◃ β)).
        {
          apply (pr2 Ht₂).
          apply internal_sfib_cleaving_is_cartesian.
        }
        assert (H₃ : is_cartesian_2cell_sfib (pr12 t₂) (δ ▹ pr1 ss₂)).
        {
          apply Hss₂.
          exact Hδ.
        }
        use (is_cartesian_2cell_sfib_postcomp
               _ _
               H₁
               (vcomp_is_cartesian_2cell_sfib _ H₂ H₃)).
        abstract
          (rewrite vcomp_whisker ;
           apply idpath).
      - exact (inv_of_invertible_2cell γ).
    Defined.

    Local Definition disp_map_cartesian_2cell_sfib_src_cell
      : disp_map_cartesian_2cell_sfib_src ==>[ α ] ss₂.
    Proof.
      use make_disp_map_bicat_cell.
      - exact β.
      - abstract
          (cbn ;
           etrans ;
           [ apply maponpaths ;
             apply internal_sfib_cleaving_over
           | ] ;
           rewrite !vassocr ;
           rewrite vcomp_linv ;
           rewrite id2_left ;
           apply idpath).
    Defined.

    Let Hβ : is_cartesian_2cell_sfib
               (pr12 t₂)
               (pr1 disp_map_cartesian_2cell_sfib_src_cell)
      := internal_sfib_cleaving_is_cartesian _ Ht₂ ((_ ◃ α) • pr22 ss₂).

    Definition disp_map_is_cartesian_2cell_to_is_cartesian_2cell_sfib
      : is_cartesian_2cell_sfib (pr12 t₂) (pr1 αα).
    Proof.
      pose (disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell _ Hβ)
        as Hβ'.
      rewrite (is_cartesian_2cell_unique_iso_com Hαα Hβ').
      refine (transportf
                (is_cartesian_2cell_sfib (pr12 t₂))
                _
                _).
      - refine (!_).
        apply transportf_disp_map_bicat_cell.
      - use vcomp_is_cartesian_2cell_sfib.
        + use invertible_is_cartesian_2cell_sfib.
          exact (is_disp_invertible_to_is_invertible
                   _ _ _
                   (pr2 (is_cartesian_2cell_unique_iso Hαα Hβ'))).
        + apply Hβ.
    Qed.
  End CartesianOfSFibToCartesian.

  (**
   4. Characterization of opcartesian cells
   *)
  Section OpCartesianOfSOpFibToOpCartesian.
    Context {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : DD c₁}
            {t₂ : DD c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_opcartesian_2cell_sopfib (pr12 t₂) (pr1 αα)).

    Section FixSome.
      Context {h : c₁ --> c₂}
              {hh : t₁ -->[ h ] t₂}
              {γ : s₂ ==> h}
              (γα : ss₁ ==>[ α • γ ] hh).

      Definition disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_unique
        : isaprop (∑ γγ : ss₂ ==>[ γ ] hh, αα •• γγ = γα).
      Proof.
        cbn in *.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply DD | ].
        use subtypePath ; [ intro ; apply cellset_property | ].
        use (is_opcartesian_2cell_sopfib_factor_unique _ Hαα).
        - exact (pr1 γα).
        - exact ((pr22 ss₂)^-1 • (_ ◃ γ) • pr22 hh).
        - abstract
            (use (vcomp_lcancel (pr22 ss₁)) ; [ apply (pr22 ss₁) | ] ;
            rewrite !vassocr ;
            refine (pr2 γα @ _) ;
            apply maponpaths_2 ;
            rewrite <- lwhisker_vcomp ;
            apply maponpaths_2 ;
            refine (!_) ;
            refine (maponpaths (λ z, z • _) (pr2 αα) @ _) ;
            rewrite !vassocl ;
            rewrite vcomp_rinv ;
            rewrite id2_right ;
            apply idpath).
        - abstract
            (rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             exact (pr21 φ₁)).
        - abstract
            (rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             exact (pr21 φ₂)).
        - exact (maponpaths pr1 (pr2 φ₁)).
        - exact (maponpaths pr1 (pr2 φ₂)).
      Qed.

      Definition disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell
        : ss₂ ==>[ γ ] hh.
      Proof.
        use make_disp_map_bicat_cell.
        - use (is_opcartesian_2cell_sopfib_factor _ Hαα (pr1 γα)).
          + exact ((pr22 ss₂)^-1 • (_ ◃ γ) • pr22 hh).
          + abstract
              (use (vcomp_lcancel (pr22 ss₁)) ; [ apply (pr22 ss₁) | ] ;
               rewrite !vassocr ;
               refine (pr2 γα @ _) ;
               apply maponpaths_2 ;
               rewrite <- lwhisker_vcomp ;
               apply maponpaths_2 ;
               refine (!_) ;
               refine (maponpaths (λ z, z • _) (pr2 αα) @ _) ;
               rewrite !vassocl ;
               rewrite vcomp_rinv ;
               rewrite id2_right ;
               apply idpath).
        - abstract
            (rewrite is_opcartesian_2cell_sopfib_factor_over ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             rewrite id2_left ;
             apply idpath).
      Defined.

      Definition disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_comm
        : αα •• disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell
          =
          γα.
      Proof.
        cbn.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        apply is_opcartesian_2cell_sopfib_factor_comm.
      Qed.
    End FixSome.

    Definition disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell
      : is_opcartesian_2cell DD αα.
    Proof.
      intros h hh γ γα.
      use iscontraprop1.
      - exact (disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_unique γα).
      - simple refine (_ ,, _).
        + exact (disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell γα).
        + exact (disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_comm γα).
    Defined.
  End OpCartesianOfSOpFibToOpCartesian.

  Section OpCartesianOfSOpFibToOpCartesian.
    Context (HD : is_covariant_disp_map_bicat D)
            {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : DD c₁}
            {t₂ : DD c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_opcartesian_2cell DD αα).

    Let Ht₂ : internal_sopfib (pr12 t₂).
    Proof.
      apply HD.
      exact (pr22 t₂).
    Defined.

    Let f : pr1 t₁ --> pr1 t₂
      := internal_sopfib_opcleaving_lift_mor _ Ht₂ ((pr22 ss₁)^-1 • (_ ◃ α)).

    Let β : pr1 ss₁ ==> f
      := internal_sopfib_opcleaving_lift_cell _ Ht₂ ((pr22 ss₁)^-1 • (_ ◃ α)).

    Let γ : invertible_2cell (pr12 t₁ · s₂) (f · pr12 t₂)
      := internal_sopfib_opcleaving_com _ Ht₂ ((pr22 ss₁)^-1 • (_ ◃ α)).

    Let Hss₁ : mor_preserves_opcartesian (pr12 t₁) (pr12 t₂) (pr1 ss₁)
      := pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 ss₁).

    Local Definition disp_map_opcartesian_2cell_sopfib_src : t₁ -->[ s₂ ] t₂.
    Proof.
      use make_disp_map_bicat_mor.
      - exact f.
      - apply HD.
        unfold f.
        intros z h₁ h₂ δ Hδ.
        assert (H₁ : is_opcartesian_2cell_sopfib (pr12 t₂) (h₂ ◃ β)).
        {
          apply (pr2 Ht₂).
          apply internal_sopfib_opcleaving_is_opcartesian.
        }
        assert (H₂ : is_opcartesian_2cell_sopfib (pr12 t₂) (h₁ ◃ β)).
        {
          apply (pr2 Ht₂).
          apply internal_sopfib_opcleaving_is_opcartesian.
        }
        assert (H₃ : is_opcartesian_2cell_sopfib (pr12 t₂) (δ ▹ pr1 ss₁)).
        {
          apply Hss₁.
          exact Hδ.
        }
        use (is_opcartesian_2cell_sopfib_precomp
               _ _
               H₂
               (vcomp_is_opcartesian_2cell_sopfib _ H₃ H₁)).
        abstract
          (rewrite vcomp_whisker ;
           apply idpath).
      - exact γ.
    Defined.

    Local Definition disp_map_opcartesian_2cell_sopfib_src_cell
      : ss₁ ==>[ α ] disp_map_opcartesian_2cell_sopfib_src.
    Proof.
      use make_disp_map_bicat_cell.
      - exact β.
      - abstract
          (cbn ;
           etrans ;
           [ apply maponpaths ;
             apply internal_sopfib_opcleaving_over
           | ] ;
           rewrite !vassocr ;
           rewrite vcomp_rinv ;
           rewrite id2_left ;
           apply idpath).
    Defined.

    Let Hβ : is_opcartesian_2cell_sopfib
               (pr12 t₂)
               (pr1 disp_map_opcartesian_2cell_sopfib_src_cell)
      := internal_sopfib_opcleaving_is_opcartesian _ Ht₂ ((pr22 ss₁)^-1 • (_ ◃ α)).

    Definition disp_map_is_opcartesian_2cell_to_is_opcartesian_2cell_sopfib
      : is_opcartesian_2cell_sopfib (pr12 t₂) (pr1 αα).
    Proof.
      pose (disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell _ Hβ)
        as Hβ'.
      rewrite (is_opcartesian_2cell_unique_iso_com Hαα Hβ').
      refine (transportf
                (is_opcartesian_2cell_sopfib (pr12 t₂))
                _
                _).
      - refine (!_).
        apply transportf_disp_map_bicat_cell.
      - use vcomp_is_opcartesian_2cell_sopfib.
        + apply Hβ.
        + use invertible_is_opcartesian_2cell_sopfib.
          exact (is_disp_invertible_to_is_invertible
                   _ _ _
                   (pr2 (is_opcartesian_2cell_unique_iso Hαα Hβ'))).
    Qed.
  End OpCartesianOfSOpFibToOpCartesian.

  (**
   5. Local cleaving
   *)
  Section LocalCleaving.
    Context (HD : is_contravariant_disp_map_bicat D).

    Section LocalLift.
      Context {x y : B}
              {xx : DD x}
              {yy : DD y}
              {f g : x --> y}
              (gg : xx -->[ g ] yy)
              (α : f ==> g).

      Let H : internal_sfib (pr12 yy) := pr1 HD _ _ _ (pr22 yy).

      Let ff : pr1 xx --> pr1 yy
        := internal_sfib_cleaving_lift_mor _ H ((pr12 xx ◃ α) • pr22 gg).

      Let β : ff ==> pr1 gg
        := internal_sfib_cleaving_lift_cell (pr12 yy) H ((pr12 xx ◃ α) • pr22 gg).

      Let γ : invertible_2cell (ff · pr12 yy) (pr12 xx · f)
        := internal_sfib_cleaving_com
                 (pr12 yy)
                 H
                 ((pr12 xx ◃ α) • pr22 gg).

      Let Hgg : mor_preserves_cartesian (pr12 xx) (pr12 yy) (pr1 gg)
        := pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 gg).

      Definition local_cleaving_of_disp_map_bicat_cartesian
        : pred_mor D (pr12 xx) (pr12 yy) ff.
      Proof.
        apply HD.
        intros z h₁ h₂ δ Hδ.
        assert (H₁ : is_cartesian_2cell_sfib (pr12 yy) (h₂ ◃ β)).
        {
          apply (pr2 H).
          apply internal_sfib_cleaving_is_cartesian.
        }
        assert (H₂ : is_cartesian_2cell_sfib (pr12 yy) (h₁ ◃ β)).
        {
          apply (pr2 H).
          apply internal_sfib_cleaving_is_cartesian.
        }
        assert (H₃ : is_cartesian_2cell_sfib (pr12 yy) (δ ▹ pr1 gg)).
        {
          apply Hgg.
          exact Hδ.
        }
        use (is_cartesian_2cell_sfib_postcomp
               _
               _
               H₁
               (vcomp_is_cartesian_2cell_sfib _ H₂ H₃)).
        abstract
          (rewrite vcomp_whisker ;
           apply idpath).
      Defined.

      Definition local_cleaving_of_disp_map_bicat_lift
        : xx -->[ f ] yy.
      Proof.
        use make_disp_map_bicat_mor.
        - exact ff.
        - exact local_cleaving_of_disp_map_bicat_cartesian.
        - exact (inv_of_invertible_2cell γ).
      Defined.

      Definition local_cleaving_of_disp_map_bicat_cell
        : local_cleaving_of_disp_map_bicat_lift ==>[ α ] gg.
      Proof.
        use make_disp_map_bicat_cell.
        - exact (internal_sfib_cleaving_lift_cell _ H ((pr12 xx ◃ α) • pr22 gg)).
        - abstract
            (cbn ;
             etrans ;
             [ apply maponpaths ;
               apply internal_sfib_cleaving_over
             | ] ;
             rewrite !vassocr ;
             rewrite vcomp_linv ;
             rewrite id2_left ;
             apply idpath).
      Defined.
    End LocalLift.

    Definition local_cleaving_of_disp_map_bicat
      : local_cleaving DD.
    Proof.
      intros x y xx yy f g gg α.
      simple refine (_ ,, _ ,, _).
      - exact (local_cleaving_of_disp_map_bicat_lift gg α).
      - exact (local_cleaving_of_disp_map_bicat_cell gg α).
      - apply disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell.
        apply internal_sfib_cleaving_is_cartesian.
    Defined.
  End LocalCleaving.

  Definition lwhisker_cartesian_disp_map_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : lwhisker_cartesian DD.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? H.
    apply disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell.
    apply (pr1 HD _ _ _ (pr22 yy)).
    apply disp_map_is_cartesian_2cell_to_is_cartesian_2cell_sfib.
    - exact HD.
    - exact H.
  Defined.

  Definition rwhisker_cartesian_disp_map_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : rwhisker_cartesian DD.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? H.
    apply disp_map_is_cartesian_2cell_sfib_to_is_cartesian_2cell.
    apply (pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 hh)).
    apply disp_map_is_cartesian_2cell_to_is_cartesian_2cell_sfib.
    - apply HD.
    - exact H.
  Qed.

  (**
   6. Local opcleaving
   *)
  Section LocalOpCleaving.
    Context (HD : is_covariant_disp_map_bicat D).

    Section LocalLift.
      Context {x y : B}
              {xx : DD x}
              {yy : DD y}
              {f g : x --> y}
              (ff : xx -->[ f ] yy)
              (α : f ==> g).

      Let H : internal_sopfib (pr12 yy) := pr1 HD _ _ _ (pr22 yy).

      Let gg : pr1 xx --> pr1 yy
        := internal_sopfib_opcleaving_lift_mor _ H ((pr22 ff)^-1 • (pr12 xx ◃ α)).

      Let β : pr1 ff ==> gg
        := internal_sopfib_opcleaving_lift_cell _ H ((pr22 ff)^-1 • (pr12 xx ◃ α)).

      Let γ : invertible_2cell
                (pr12 xx · g)
                (gg · pr12 yy)
        := internal_sopfib_opcleaving_com _ H ((pr22 ff)^-1 • (pr12 xx ◃ α)).

      Let Hff : mor_preserves_opcartesian (pr12 xx) (pr12 yy) (pr1 ff)
        := pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 ff).

      Definition local_opcleaving_of_disp_map_bicat_opcartesian
        : pred_mor D (pr12 xx) (pr12 yy) gg.
      Proof.
        apply HD.
        intros z h₁ h₂ δ Hδ.
        assert (H₁ : is_opcartesian_2cell_sopfib (pr12 yy) (h₂ ◃ β)).
        {
          apply (pr2 H).
          apply internal_sopfib_opcleaving_is_opcartesian.
        }
        assert (H₂ : is_opcartesian_2cell_sopfib (pr12 yy) (h₁ ◃ β)).
        {
          apply (pr2 H).
          apply internal_sopfib_opcleaving_is_opcartesian.
        }
        assert (H₃ : is_opcartesian_2cell_sopfib (pr12 yy) (δ ▹ pr1 ff)).
        {
          apply Hff.
          exact Hδ.
        }
        use (is_opcartesian_2cell_sopfib_precomp
               _
               _
               H₂
               (vcomp_is_opcartesian_2cell_sopfib _ H₃ H₁)).
        abstract
          (rewrite vcomp_whisker ;
           apply idpath).
      Defined.

      Definition local_opcleaving_of_disp_map_bicat_lift
        : xx -->[ g ] yy.
      Proof.
        use make_disp_map_bicat_mor.
        - exact gg.
        - exact local_opcleaving_of_disp_map_bicat_opcartesian.
        - exact γ.
      Defined.

      Definition local_opcleaving_of_disp_map_bicat_cell
        : ff ==>[ α ] local_opcleaving_of_disp_map_bicat_lift.
      Proof.
        use make_disp_map_bicat_cell.
        - exact (internal_sopfib_opcleaving_lift_cell _ H ((pr22 ff)^-1 • (pr12 xx ◃ α))).
        - abstract
            (cbn ;
             etrans ;
             [ apply maponpaths ;
               apply internal_sopfib_opcleaving_over
             | ] ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             rewrite id2_left ;
             apply idpath).
      Defined.
    End LocalLift.

    Definition local_opcleaving_of_disp_map_bicat
      : local_opcleaving DD.
    Proof.
      intros x y xx yy f g ff α.
      simple refine (_ ,, _ ,, _).
      - exact (local_opcleaving_of_disp_map_bicat_lift ff α).
      - exact (local_opcleaving_of_disp_map_bicat_cell ff α).
      - apply disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
        apply internal_sopfib_opcleaving_is_opcartesian.
    Defined.
  End LocalOpCleaving.

  Definition lwhisker_opcartesian_disp_map_bicat
             (HD : is_covariant_disp_map_bicat D)
    : lwhisker_opcartesian DD.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? H.
    apply disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
    apply (pr1 HD _ _ _ (pr22 yy)).
    apply disp_map_is_opcartesian_2cell_to_is_opcartesian_2cell_sopfib.
    - exact HD.
    - exact H.
  Defined.

  Definition rwhisker_opcartesian_disp_map_bicat
             (HD : is_covariant_disp_map_bicat D)
    : rwhisker_opcartesian DD.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? H.
    apply disp_map_is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
    apply (pr1 (pr2 HD _ _ _ _ _ _ _) (pr12 hh)).
    apply disp_map_is_opcartesian_2cell_to_is_opcartesian_2cell_sopfib.
    - apply HD.
    - exact H.
  Qed.
End DispMapBicatCleaving.
