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
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

(**
The codomain displayed bicategory has a cleaving
Here we assume that every 2-cell is invertible
 *)
Section CodomainCleaving.
  Context (B : bicat).

  Section CartesianOfSFibToCartesian.
    Context {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : cod_disp_bicat B c₁}
            {t₂ : cod_disp_bicat B c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_cartesian_2cell_sfib (pr2 t₂) (pr1 αα)).

    Section FixSome.
      Context {h : c₁ --> c₂}
              {hh : t₁ -->[ h] t₂}
              {γ : h ==> s₁}
              (γα : hh ==>[ γ • α] ss₂).

      Definition is_cartesian_2cell_sfib_to_is_cartesian_2cell_unique
        : isaprop (∑ γγ : hh ==>[ γ] ss₁, γγ •• αα = γα).
      Proof.
        cbn in *.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply cod_disp_bicat | ].
        use subtypePath ; [ intro ; apply cellset_property | ].
        use (is_cartesian_2cell_sfib_factor_unique _ Hαα).
        - exact (pr1 γα).
        - exact ((pr2 hh)^-1 • (_ ◃ γ) • pr2 ss₁).
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

      Definition is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell
        : hh ==>[ γ ] ss₁.
      Proof.
        cbn in *.
        use make_disp_2cell_cod.
        - use (is_cartesian_2cell_sfib_factor _ Hαα (pr1 γα)).
          + exact ((pr2 hh)^-1 • (_ ◃ γ) • pr2 ss₁).
          + abstract
              (rewrite !vassocl ;
               use vcomp_move_L_pM ; [ is_iso | ] ;
               refine (pr2 γα @ _) ;
               rewrite <- lwhisker_vcomp ;
               rewrite !vassocl ;
               apply maponpaths ;
               exact (!(pr2 αα))).
        - abstract
            (unfold coherent_homot ;
             rewrite is_cartesian_2cell_sfib_factor_over ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             rewrite id2_left ;
             apply idpath).
      Defined.

      Definition is_cartesian_2cell_sfib_to_is_cartesian_2cell_comm
        : is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell •• αα = γα.
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

    Definition is_cartesian_2cell_sfib_to_is_cartesian_2cell
      : is_cartesian_2cell (cod_disp_bicat B) αα.
    Proof.
      intros h hh γ γα.
      use iscontraprop1.
      - exact (is_cartesian_2cell_sfib_to_is_cartesian_2cell_unique γα).
      - simple refine (_ ,, _).
        + exact (is_cartesian_2cell_sfib_to_is_cartesian_2cell_cell γα).
        + exact (is_cartesian_2cell_sfib_to_is_cartesian_2cell_comm γα).
    Defined.
  End CartesianOfSFibToCartesian.

  Definition cod_invertible_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : cod_disp_bicat B c₁}
             {t₂ : cod_disp_bicat B c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
             (Hαα : is_invertible_2cell (pr1 αα))
    : is_cartesian_2cell (cod_disp_bicat B) αα.
  Proof.
    apply is_cartesian_2cell_sfib_to_is_cartesian_2cell.
    apply invertible_is_cartesian_2cell_sfib.
    exact Hαα.
  Defined.

  Section OpCartesianOfSOpFibToOpCartesian.
    Context {c₁ c₂ : B}
            {s₁ s₂ : c₁ --> c₂}
            {α : s₁ ==> s₂}
            {t₁ : cod_disp_bicat B c₁}
            {t₂ : cod_disp_bicat B c₂}
            {ss₁ : t₁ -->[ s₁ ] t₂}
            {ss₂ : t₁ -->[ s₂ ] t₂}
            (αα : ss₁ ==>[ α ] ss₂)
            (Hαα : is_opcartesian_2cell_sopfib (pr2 t₂) (pr1 αα)).

    Section FixSome.
      Context {h : c₁ --> c₂}
              {hh : t₁ -->[ h ] t₂}
              {γ : s₂ ==> h}
              (γα : ss₁ ==>[ α • γ ] hh).

      Definition is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_unique
        : isaprop (∑ γγ : ss₂ ==>[ γ ] hh, αα •• γγ = γα).
      Proof.
        cbn in *.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply cod_disp_bicat | ].
        use subtypePath ; [ intro ; apply cellset_property | ].
        use (is_opcartesian_2cell_sopfib_factor_unique _ Hαα).
        - exact (pr1 γα).
        - exact ((pr2 ss₂)^-1 • (_ ◃ γ) • pr2 hh).
        - abstract
              (use (vcomp_lcancel (pr12 ss₁)) ; [ apply (pr2 ss₁) | ] ;
               rewrite !vassocr ;
               rewrite !(pr2 γα) ;
               apply maponpaths_2 ;
               rewrite <- lwhisker_vcomp ;
               apply maponpaths_2 ;
               rewrite (pr2 αα) ;
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

      Definition is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell
        : ss₂ ==>[ γ ] hh.
      Proof.
        cbn in *.
        use make_disp_2cell_cod.
        - use (is_opcartesian_2cell_sopfib_factor _ Hαα (pr1 γα)).
          + exact ((pr2 ss₂)^-1 • (_ ◃ γ) • pr2 hh).
          + abstract
              (use (vcomp_lcancel (pr12 ss₁)) ; [ apply (pr2 ss₁) | ] ;
               rewrite !vassocr ;
               rewrite !(pr2 γα) ;
               apply maponpaths_2 ;
               rewrite <- lwhisker_vcomp ;
               apply maponpaths_2 ;
               rewrite (pr2 αα) ;
               rewrite !vassocl ;
               rewrite vcomp_rinv ;
               rewrite id2_right ;
               apply idpath).
        - abstract
            (unfold coherent_homot ;
             rewrite is_opcartesian_2cell_sopfib_factor_over ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             rewrite id2_left ;
             apply idpath).
      Defined.

      Definition is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_comm
        : αα •• is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell = γα.
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

    Definition is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell
      : is_opcartesian_2cell (cod_disp_bicat B) αα.
    Proof.
      intros h hh γ γα.
      use iscontraprop1.
      - exact (is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_unique γα).
      - simple refine (_ ,, _).
        + exact (is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_cell γα).
        + exact (is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell_comm γα).
    Defined.
  End OpCartesianOfSOpFibToOpCartesian.

  Definition cod_invertible_is_opcartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : cod_disp_bicat B c₁}
             {t₂ : cod_disp_bicat B c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
             (Hαα : is_invertible_2cell (pr1 αα))
    : is_opcartesian_2cell (cod_disp_bicat B) αα.
  Proof.
    apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
    apply invertible_is_opcartesian_2cell_sopfib.
    exact Hαα.
  Defined.

  (** Characterization of cartesian 1-cells *)
  Section PullbackToCartesian.
    Context {x y : B}
            {f : x --> y}
            {hx : cod_disp_bicat B x}
            {hy : cod_disp_bicat B y}
            (π : pr1 hx --> pr1 hy)
            (p : invertible_2cell (pr2 hx · f) (π · pr2 hy))
            (pb := make_pb_cone (pr1 hx) (pr2 hx) π p)
            (pb_sqr : has_pb_ump pb).

    Section Lift1CellConeMor.
      Context {z : B}
              {hz : cod_disp_bicat B z}
              {g : z --> x}
              (hg : hz -->[ g · f] hy).

      Let other_cone : pb_cone f (pr2 hy)
        := make_pb_cone
             (pr1 hz)
             (pr2 hz · g)
             (pr1 hg)
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                (pr2 hg)).

      Definition lift_1cell_to_pb_1cell
                 (Hg : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg)
        : pb_1cell other_cone pb.
      Proof.
        use make_pb_1cell.
        - exact (pr11 Hg).
        - use inv_of_invertible_2cell.
          exact (pr21 Hg).
        - use make_invertible_2cell.
          + exact (pr112 Hg).
          + exact (pr21 (cod_disp_invertible_invertible_2_cell _ (pr2 Hg))).
        - abstract
            (pose (pr212 Hg) as q ;
             cbn ; cbn in q ;
             rewrite lwhisker_id2 in q ;
             rewrite id2_left in q ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn) ;
             refine (_ @ maponpaths (λ z, z • _) q) ; clear q ;
             rewrite !vassocl ;
             do 3 apply maponpaths ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite rwhisker_vcomp ;
             pose (maponpaths pr1 (disp_vcomp_rinv (pr2 Hg))) as q ;
             unfold transportb in q ;
             cbn in q ;
             rewrite pr1_transportf, transportf_const in q ;
             cbn in q ;
             refine (!_) ;
             etrans ;
             [ do 2 apply maponpaths ;
               apply maponpaths_2 ;
               apply maponpaths ;
               exact q
             | ] ;
             rewrite id2_rwhisker, id2_left ;
             rewrite lassociator_rassociator ;
             apply id2_right).
      Defined.

      Definition pb_1cell_to_lift_1cell
                 (Hg : pb_1cell other_cone pb)
        : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg.
      Proof.
        simple refine ((_ ,, _) ,, ((_ ,, _) ,, _)).
        - exact (pb_1cell_1cell Hg).
        - exact (inv_of_invertible_2cell (pb_1cell_pr1 Hg)).
        - exact (pr1 (pb_1cell_pr2 Hg)).
        - abstract
            (cbn ;
             pose (pb_1cell_eq Hg) as q ;
             cbn in q ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn) ;
             refine (maponpaths (λ z, z • _) q @ _) ; clear q ;
             rewrite !vassocl ;
             do 3 apply maponpaths ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
             rewrite !vassocr ;
             rewrite rassociator_lassociator ;
             rewrite id2_left, id2_right ;
             apply idpath).
        - use is_disp_invertible_2cell_cod.
          exact (pr2 (pb_1cell_pr2 Hg)).
      Defined.
    End Lift1CellConeMor.

    Definition is_pb_to_cartesian_lift_1cell
               {z : B}
               {hz : cod_disp_bicat B z}
               {g : B ⟦ z, x ⟧}
               (hg : hz -->[ g · f] hy)
      : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg.
    Proof.
      apply pb_1cell_to_lift_1cell.
      apply (has_pb_ump_1 pb_sqr).
    Defined.

    Section Lift2CellConeCell.
      Context {c : B}
              {cc : cod_disp_bicat B c}
              {h h' : c --> x}
              {gg : cc -->[ h · f] hy}
              {gg' : cc -->[ h' · f] hy}
              {δ : h ==> h'}
              (σσ : gg ==>[ δ ▹ f] gg')
              (Lh : lift_1cell_factor (cod_disp_bicat B) (π,, p) gg)
              (Lh' : lift_1cell_factor (cod_disp_bicat B) (π,, p) gg').

      Let ℓ : pr1 cc --> pr1 hx := pr11 Lh.
      Let ℓhx : invertible_2cell (pr2 cc · h) (ℓ · pr2 hx) := pr21 Lh.
      Let ℓπ
        : invertible_2cell (ℓ · π) (pr1 gg)
        := pr1 (cod_disp_invertible_invertible_2_cell _ (pr2 Lh)).
      Let ℓ' : pr1 cc --> pr1 hx := pr11 Lh'.
      Let ℓhx' : invertible_2cell (pr2 cc · h') (ℓ' · pr2 hx) := pr21 Lh'.
      Let ℓπ'
        : invertible_2cell (ℓ' · π) (pr1 gg')
        := pr1 (cod_disp_invertible_invertible_2_cell _ (pr2 Lh')).

      Definition is_pb_to_cartesian_lift_2cell_cell_eq
        : (ℓ ◃ p)
          • lassociator ℓ π (pr2 hy)
          • ((pr112 Lh • pr1 σσ • pr1 (disp_inv_cell (pr2 Lh'))) ▹ pr2 hy)
          • rassociator ℓ' π (pr2 hy)
          =
          lassociator ℓ (pr2 hx) f
          • ((ℓhx ^-1 • (pr2 cc ◃ δ) • ℓhx') ▹ f)
          • rassociator ℓ' (pr2 hx) f
          • (ℓ' ◃ p).
      Proof.
        pose (pr212 Lh) as d.
        pose (pr212 Lh') as d'.
        cbn in d, d'.
        rewrite lwhisker_id2, id2_left in d.
        rewrite lwhisker_id2, id2_left in d'.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        rewrite !vassocr.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact d.
        }
        clear d.
        rewrite <- rwhisker_lwhisker.
        use vcomp_move_R_Mp ; [ is_iso | ].
        cbn.
        use vcomp_move_R_Mp.
        {
          is_iso.
          apply (is_invertible_2cell_inv (pr2 ℓπ')).
        }
        cbn.
        rewrite !vassocl.
        rewrite !vassocl in d'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact d'.
        }
        refine (!_).
        exact (pr2 σσ).
      Qed.

      Definition is_pb_to_cartesian_lift_2cell_cell
        : ℓ ==> ℓ'.
      Proof.
        use (pb_ump_cell pb_sqr) ; cbn.
        - exact (ℓhx^-1 • (_ ◃ δ) • ℓhx').
        - exact (ℓπ • pr1 σσ • (ℓπ')^-1).
        - exact is_pb_to_cartesian_lift_2cell_cell_eq.
      Defined.

      Definition is_pb_to_cartesian_lift_2cell_cell_homot
        : coherent_homot δ is_pb_to_cartesian_lift_2cell_cell.
      Proof.
        unfold coherent_homot.
        etrans.
        {
          apply maponpaths.
          apply (pb_ump_cell_pr1 pb_sqr).
        }
        rewrite !vassocr.
        rewrite vcomp_rinv, id2_left.
        apply idpath.
      Qed.

      Definition is_pb_to_cartesian_lift_2cell_disp_cell
        : Lh ==>[ δ ] Lh'.
      Proof.
        use make_disp_2cell_cod.
        - exact is_pb_to_cartesian_lift_2cell_cell.
        - exact is_pb_to_cartesian_lift_2cell_cell_homot.
      Defined.

      Definition is_pb_to_cartesian_lift_2cell_unique
        : isaprop (lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh').
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
        use (pb_ump_eq pb_sqr).
        - exact (ℓhx^-1 • (_ ◃ δ) • ℓhx').
        - exact (ℓπ • pr1 σσ • (ℓπ')^-1).
        - apply is_pb_to_cartesian_lift_2cell_cell_eq.
        - rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          exact (pr21 φ₁).
        - pose (!(transportf_cell_of_cod_over (id2_right (δ ▹ f) @ ! id2_left (δ ▹ f)) _)
                @ maponpaths pr1 (pr2 φ₁)) as d.
          use vcomp_move_L_Mp ; [ is_iso | ].
          exact d.
        - rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          exact (pr21 φ₂).
        - pose (!(transportf_cell_of_cod_over (id2_right (δ ▹ f) @ ! id2_left (δ ▹ f)) _)
                @ maponpaths pr1 (pr2 φ₂)) as d.
          use vcomp_move_L_Mp ; [ is_iso | ].
          exact d.
      Qed.

      Definition is_pb_to_cartesian_lift_2cell
        : lift_2cell_factor (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        use iscontraprop1.
        - exact is_pb_to_cartesian_lift_2cell_unique.
        - simple refine (_ ,, _).
          + exact is_pb_to_cartesian_lift_2cell_disp_cell.
          + abstract
              (use subtypePath ; [ intro ; apply cellset_property | ] ;
               etrans ; [ exact (transportf_cell_of_cod_over _ _) | ] ;
               simpl ;
               etrans ; [ apply maponpaths_2 ; apply (pb_ump_cell_pr2 pb_sqr) | ] ;
               do 2 refine (vassocl _ _ _ @ _) ;
               apply maponpaths ;
               refine (_ @ id2_right _) ;
               apply maponpaths ;
               apply (pr2 ℓπ')).
      Defined.
    End Lift2CellConeCell.

    Definition is_pb_to_cartesian_1cell
      : cartesian_1cell (cod_disp_bicat B) (π ,, p).
    Proof.
      split.
      - exact @is_pb_to_cartesian_lift_1cell.
      - exact @is_pb_to_cartesian_lift_2cell.
    Defined.
  End PullbackToCartesian.

  Context (inv_B : locally_groupoid B).

  Section CartesianToPullback.
    Context {x y : B}
            {f : x --> y}
            {hx : cod_disp_bicat B x}
            {hy : cod_disp_bicat B y}
            (π : pr1 hx --> pr1 hy)
            (p : invertible_2cell (pr2 hx · f) (π · pr2 hy))
            (Hp : cartesian_1cell (cod_disp_bicat B) (π,, p)).

    Let pb := make_pb_cone (pr1 hx) (pr2 hx) π p.

    Definition cartesian_1cell_pb_ump_1
      : pb_ump_1 pb.
    Proof.
      intro q.
      pose (pr1 Hp x (make_ar (pb_cone_pr1 q)) (id₁ _)
                (pb_cone_pr2 q ,, comp_of_invertible_2cell
                             (lwhisker_of_invertible_2cell
                                _
                                (lunitor_invertible_2cell _))
                             (pb_cone_cell q))) as w.
      pose (lift_1cell_to_pb_1cell π p _ w) as r.
      use make_pb_1cell.
      - exact r.
      - exact (comp_of_invertible_2cell
                  (pb_1cell_pr1 r)
                  (runitor_invertible_2cell _)).
      - exact (pb_1cell_pr2 r).
      - abstract
          (refine (pb_1cell_eq r @ _) ; cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           do 3 apply maponpaths_2 ;
           apply lunitor_lwhisker).
    Defined.

    Section PullbackUMP2.
      Context {q : B}
              {φ ψ : q --> pb}
              {α : φ · pb_cone_pr1 pb ==> ψ · pb_cone_pr1 pb}
              {β : φ · pb_cone_pr2 pb ==> ψ · pb_cone_pr2 pb}
              (r : (φ ◃ pb_cone_cell pb)
                   • lassociator φ (pb_cone_pr2 pb) (pr2 hy)
                   • (β ▹ pr2 hy)
                   • rassociator ψ (pb_cone_pr2 pb) (pr2 hy)
                   =
                   lassociator φ (pb_cone_pr1 pb) f
                   • (α ▹ f)
                   • rassociator ψ (pb_cone_pr1 pb) f
                   • (ψ ◃ pb_cone_cell pb)).

      Let φ_disp
        : make_ar φ -->[ pr2 hx · f] hy.
      Proof.
        use make_disp_1cell_cod.
        - exact (φ · π).
        - exact (comp_of_invertible_2cell
                   (lwhisker_of_invertible_2cell φ p)
                   (lassociator_invertible_2cell _ _ _)).
      Defined.

      Let φ_cone : pb_cone f (pr2 hy)
        := make_pb_cone
             q
             (φ · pr2 hx)
             (φ · π)
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                (pr2 φ_disp)).

      Let φ_cell : pb_1cell φ_cone pb.
      Proof.
        use make_pb_1cell.
        - exact φ.
        - apply id2_invertible_2cell.
        - apply id2_invertible_2cell.
        - abstract
            (cbn ;
             rewrite !id2_rwhisker, !id2_right ;
             rewrite !vassocr ;
             rewrite lassociator_rassociator ;
             rewrite id2_left ;
             rewrite !vassocl ;
             rewrite lassociator_rassociator ;
             rewrite id2_right ;
             apply idpath).
      Defined.

      Let ψ_disp
        : make_ar φ -->[ pr2 hx · f] hy.
      Proof.
        use make_disp_1cell_cod.
        - exact (ψ · π).
        - use make_invertible_2cell.
          + exact (lassociator _ _ _
                   • (α ▹ f)
                   • rassociator _ _ _
                   • (ψ ◃ p)
                   • lassociator _ _ _).
          + is_iso.
            * apply inv_B.
            * apply property_from_invertible_2cell.
      Defined.

      Let σσ : φ_disp ==>[ id₂ (pr2 hx) ▹ f] ψ_disp.
      Proof.
        use make_disp_2cell_cod.
        - exact β.
        - abstract
            (unfold coherent_homot ;
             cbn ;
             rewrite id2_rwhisker, lwhisker_id2, id2_left ;
             use vcomp_move_L_Mp ; [ is_iso | ] ;
             exact r).
      Defined.

      Let ψ_cone : pb_cone f (pr2 hy)
        := make_pb_cone
             q
             (φ · pr2 hx)
             (ψ · π)
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell φ (pr2 hx) f)
                (pr2 ψ_disp)).

      Let ψ_cell : pb_1cell ψ_cone pb.
      Proof.
        use make_pb_1cell.
        - exact ψ.
        - refine (inv_of_invertible_2cell _).
          use make_invertible_2cell.
          + exact α.
          + apply inv_B.
        - apply id2_invertible_2cell.
        - abstract
            (cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite !vassocl ;
             rewrite lassociator_rassociator ;
             rewrite id2_right ;
             do 3 (use vcomp_move_L_pM ; [ is_iso | ]) ;
             cbn ;
             rewrite !vassocr ;
             apply idpath).
      Defined.

      Let φ_lift : lift_1cell_factor (cod_disp_bicat B) (π,, p) φ_disp
        := pb_1cell_to_lift_1cell π p φ_disp φ_cell.

      Let ψ_lift : lift_1cell_factor (cod_disp_bicat B) (π,, p) ψ_disp
        := pb_1cell_to_lift_1cell π p ψ_disp ψ_cell.

      Definition cartesian_1cell_pb_2cell
        : φ ==> ψ
        := pr1 (cartesian_1cell_lift_2cell _ _ Hp σσ φ_lift ψ_lift).

      Definition cartesian_1cell_pb_2cell_pr1
        : cartesian_1cell_pb_2cell ▹ pb_cone_pr1 pb = α.
      Proof.
        pose (pr2 (cartesian_1cell_lift_2cell _ _ Hp σσ φ_lift ψ_lift)) as d.
        cbn in d.
        rewrite lwhisker_id2, !id2_left in d.
        exact d.
      Qed.

      Definition cartesian_1cell_pb_2cell_pr2
        : cartesian_1cell_pb_2cell ▹ pb_cone_pr2 pb = β.
      Proof.
        pose (maponpaths
                pr1
                (cartesian_1cell_lift_2cell_commutes
                   _ _
                   Hp σσ
                   φ_lift ψ_lift))
          as d.
        cbn in d.
        rewrite pr1_transportf, transportf_const in d.
        cbn in d.
        rewrite id2_right, id2_left in d.
        exact d.
      Qed.

      Section Uniqueness.
        Context (τ₁ τ₂ : φ ==> ψ)
                (pr1τ₁ : τ₁ ▹ pb_cone_pr1 pb = α)
                (pr2τ₁ : τ₁ ▹ pb_cone_pr2 pb = β)
                (pr1τ₂ : τ₂ ▹ pb_cone_pr1 pb = α)
                (pr2τ₂ : τ₂ ▹ pb_cone_pr2 pb = β).

        Let lift_τ₁ : φ_lift ==>[ id₂ (pr2 hx)] ψ_lift.
        Proof.
          use make_disp_2cell_cod.
          - exact τ₁.
          - abstract
              (unfold coherent_homot ;
               cbn ;
               rewrite lwhisker_id2, !id2_left ;
               exact pr1τ₁).
        Defined.

        Let lift_τ₂ : φ_lift ==>[ id₂ (pr2 hx)] ψ_lift.
        Proof.
          use make_disp_2cell_cod.
          - exact τ₂.
          - abstract
              (unfold coherent_homot ;
               cbn ;
               rewrite lwhisker_id2, !id2_left ;
               exact pr1τ₂).
        Defined.

        Definition cartesian_1cell_pb_2cell_unique
          : τ₁ = τ₂.
        Proof.
          refine (maponpaths
                    pr1
                    (isaprop_lift_of_lift_2cell
                       _ _
                       (pr2 Hp _ _ _ _ _ _ _ σσ φ_lift ψ_lift)
                       lift_τ₁ lift_τ₂
                       _
                       _)) ;
            (use subtypePath ; [ intro ; apply cellset_property | ]) ;
            cbn ;
            rewrite pr1_transportf, transportf_const ;
            cbn.
          - rewrite id2_left, id2_right.
            exact pr2τ₁.
          - rewrite id2_left, id2_right.
            exact pr2τ₂.
        Qed.
      End Uniqueness.
    End PullbackUMP2.

    Definition cartesian_1cell_pb_ump_2
      : pb_ump_2 pb.
    Proof.
      intros q φ ψ α β r.
      apply iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros τ₁ τ₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           exact (cartesian_1cell_pb_2cell_unique
                    r
                    _ _
                    (pr12 τ₁) (pr22 τ₁)
                    (pr12 τ₂) (pr22 τ₂))).
      - exact (cartesian_1cell_pb_2cell r
               ,,
               cartesian_1cell_pb_2cell_pr1 r
               ,,
               cartesian_1cell_pb_2cell_pr2 r).
    Defined.

    Definition cartesian_1cell_to_is_pb
      : has_pb_ump pb.
    Proof.
      split.
      - exact cartesian_1cell_pb_ump_1.
      - exact cartesian_1cell_pb_ump_2.
    Defined.
  End CartesianToPullback.

  Context (pb_B : has_pb B).

  Definition cod_global_cleaving
    : global_cleaving (cod_disp_bicat B).
  Proof.
    intros x y hx f ; cbn in *.
    pose (pb_B _ _ _ f (pr2 hx)) as pb.
    pose (pr1 pb) as pb₁.
    pose (pr2 pb) as pb₂.
    simple refine ((_ ,, _) ,, (_ ,, _) ,, _) ; cbn.
    - exact pb₁.
    - exact (pb_cone_pr1 pb₁).
    - exact (pb_cone_pr2 pb₁).
    - exact (pb_cone_cell pb₁).
    - apply is_pb_to_cartesian_1cell.
      exact pb₂.
  Defined.

  Definition cod_local_cleaving
    : local_cleaving (cod_disp_bicat B).
  Proof.
    intros x y hx hy f g hf hg.
    simple refine (_ ,, _).
    - simple refine (pr1 hf ,, pr2 hx ◃ hg • pr12 hf ,, _).
      cbn.
      is_iso.
      + apply inv_B.
      + apply (pr22 hf).
    - simple refine (_ ,, _).
      + simple refine (id2 _ ,, _).
        abstract
          (cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_right ;
           apply idpath).
      + simpl.
        apply cod_invertible_is_cartesian_2cell ; cbn.
        is_iso.
  Defined.

  Definition cod_local_opcleaving
    : local_opcleaving (cod_disp_bicat B).
  Proof.
    intros x y hx hy f g hf hg.
    simple refine (_ ,, _).
    - cbn.
      simple refine (pr1 hf ,, (pr2 hx ◃ _^-1) • pr12 hf ,, _) ; cbn.
      + exact hg.
      + apply inv_B.
      + is_iso.
        apply (pr22 hf).
    - simple refine (_ ,, _).
      + simple refine (id2 _ ,, _).
        abstract
          (cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_right ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           apply idpath).
      + simpl.
        apply cod_invertible_is_opcartesian_2cell ; cbn.
        is_iso.
  Defined.

  Definition cod_cleaving_lwhisker_cartesian
    : lwhisker_cartesian (cod_disp_bicat B).
  Proof.
    intro ; intros.
    apply cod_invertible_is_cartesian_2cell.
    apply inv_B.
  Defined.

  Definition cod_cleaving_rwhisker_cartesian
    : rwhisker_cartesian (cod_disp_bicat B).
  Proof.
    intro ; intros.
    apply cod_invertible_is_cartesian_2cell.
    apply inv_B.
  Defined.

  Definition cod_cleaving_lwhisker_opcartesian
    : lwhisker_opcartesian (cod_disp_bicat B).
  Proof.
    intro ; intros.
    apply cod_invertible_is_opcartesian_2cell ; apply inv_B.
  Defined.

  Definition cod_cleaving_rwhisker_opcartesian
    : rwhisker_opcartesian (cod_disp_bicat B).
  Proof.
    intro ; intros.
    apply cod_invertible_is_opcartesian_2cell ; apply inv_B.
  Defined.

  Definition cod_cleaving_of_bicats
    : cleaving_of_bicats (cod_disp_bicat B).
  Proof.
    repeat split.
    - exact cod_local_cleaving.
    - exact cod_global_cleaving.
    - exact cod_cleaving_lwhisker_cartesian.
    - exact cod_cleaving_rwhisker_cartesian.
  Defined.
End CodomainCleaving.

Definition cod_fibration_one_types
  : cleaving_of_bicats (cod_disp_bicat one_types).
Proof.
  use cod_cleaving_of_bicats.
  - exact one_type_2cell_iso.
  - exact one_types_has_pb.
Defined.
