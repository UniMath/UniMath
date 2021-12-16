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
    intros h hh γ γα.
    cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply (cod_disp_bicat B) | ] ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         pose (maponpaths pr1 (pr2 φ₁)) as p₁ ;
         cbn in p₁ ;
         pose (maponpaths pr1 (pr2 φ₂)) as p₂ ;
         cbn in p₂ ;
         pose (r := p₁ @ !p₂) ;
         use (vcomp_rcancel _ Hαα) ;
         exact r).
    - simple refine ((_ ,, _) ,, _).
      + exact (pr1 γα • Hαα^-1).
      + abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite (pr2 γα) ;
           rewrite <- lwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- (pr2 αα) ;
           rewrite !vassocl ;
           rewrite rwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           apply id2_right).
      + abstract
          (use subtypePath ; [ intro ; apply cellset_property | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite vcomp_linv ;
           apply id2_right).
  Defined.

  Context (inv_B : locally_groupoid B)
          (pb_B : has_pb B).

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
          + apply inv_B.
        - abstract
            (pose (pr212 Hg) as q ;
             cbn ; cbn in q ;
             rewrite lwhisker_id2 in q ;
             rewrite id2_left in q ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn) ;
             rewrite !vassocr ;
             do 2 (use vcomp_move_L_Mp ; [ is_iso | ] ; cbn) ;
             exact q).
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
      exact (has_pb_ump_1 pb_sqr _).
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

      Definition lift_2cell_cone
        : UU
        := ∑ (α : pr11 Lh ==> pr11 Lh'),
           (pr121 Lh • (α ▹ pr2 hx) = (pr2 cc ◃ δ) • pr121 Lh')
           ×
           ((α ▹ π) • pr112 Lh' = pr112 Lh • pr1 σσ).

      Definition cone_cell_to_lift_2cell
                 (α : pr11 Lh ==> pr11 Lh')
                 (α_pr1 : pr121 Lh • (α ▹ pr2 hx) = (pr2 cc ◃ δ) • pr121 Lh')
                 (α_pr2 : (α ▹ π) • pr112 Lh' = pr112 Lh • pr1 σσ)
        : lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        simple refine ((α ,, α_pr1) ,, _).
        use subtypePath ; [ intro ; apply cellset_property | ].
        simpl.
        rewrite pr1_transportf.
        rewrite transportf_const.
        cbn.
        exact α_pr2.
      Defined.

      Definition lift_2cell_to_cone_cell
                 (α : lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh')
        : lift_2cell_cone.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact (pr11 α).
        - exact (pr21 α).
        - abstract
            (pose (maponpaths pr1 (pr2 α)) as q ;
             cbn ;
             simpl in q ;
             rewrite pr1_transportf in q ;
             rewrite transportf_const in q ;
             exact q).
      Defined.

      Definition cone_cell_weq_lift_2cell
        : lift_2cell_cone
          ≃
          lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        use make_weq.
        - exact (λ z, cone_cell_to_lift_2cell (pr1 z) (pr12 z) (pr22 z)).
        - use gradth.
          + exact lift_2cell_to_cone_cell.
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply (cod_disp_bicat B) | ] ;
               use subtypePath ;
               [ intro ; apply cellset_property | ] ;
               apply idpath).
      Defined.

      Let cone : pb_cone f (pr2 hy)
        := make_pb_cone
             (pr1 cc) (pr2 cc · h') (pr1 gg')
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell (pr2 cc) h' f)
                (pr2 gg')).

      Let cell₂ : pb_1cell cone pb := lift_1cell_to_pb_1cell _ Lh'.

      Local Definition cell₁ : pb_1cell cone pb.
      Proof.
        pose (lift_1cell_to_pb_1cell _ Lh) as lift.
        use make_pb_1cell.
        - exact lift.
        - exact (comp_of_invertible_2cell
                   (pb_1cell_pr1 lift)
                   (lwhisker_of_invertible_2cell
                      _
                      (δ ,, inv_B _ _ _ _ _))).
        - exact (comp_of_invertible_2cell
                   (pb_1cell_pr2 lift)
                   (pr1 σσ ,, inv_B _ _ _ _ _)).
        - abstract
            (cbn ;
             pose (pb_1cell_eq lift) as q ;
             cbn in q ;
             rewrite q ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- rwhisker_lwhisker_rassociator ;
             do 2 apply maponpaths_2 ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             use vcomp_move_L_Mp ; [ is_iso | ] ; cbn ;
             exact (pr2 σσ)).
      Defined.

      Definition pb_2cell_to_cone_cell
                 (α : pb_2cell cell₁ cell₂)
        : lift_2cell_cone.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact α.
        - abstract
            (pose (pb_2cell_pr1 α) as q ;
             cbn in q ;
             refine (!(id2_right _) @ _) ;
             etrans ;
               [ apply maponpaths ;
                 refine (!_) ;
                 exact (vcomp_linv (pr221 Lh'))
               | ] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             refine (maponpaths (λ z, _ • z) q @ _) ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             apply id2_left).
        - exact (pb_2cell_pr2 α).
      Defined.

      Definition cone_cell_to_pb_2cell
                 (α : lift_2cell_cone)
        : pb_2cell cell₁ cell₂.
      Proof.
        use make_pb_2cell.
        - exact (pr1 α).
        - abstract
            (pose (pr12 α) as q ;
             cbn ;
             use vcomp_move_R_Mp ; [ is_iso | ] ;
             rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             cbn ;
             exact q).
        - exact (pr22 α).
      Defined.

      Definition pb_2cell_weq_cone_cell
        : pb_2cell cell₁ cell₂ ≃ lift_2cell_cone.
      Proof.
        use make_weq.
        - exact pb_2cell_to_cone_cell.
        - use gradth.
          + exact cone_cell_to_pb_2cell.
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
      Defined.

      Local Lemma is_pb_to_cartesian_lift_2cell_equality
        : (cell₁ ◃ pb_cone_cell pb)
          • lassociator _ _ _
          • ((pb_1cell_pr2 cell₁ • (pb_1cell_pr2 cell₂) ^-1) ▹ pr2 hy)
          • rassociator _ _ _
          =
          lassociator _ _ _
          • ((pb_1cell_pr1 cell₁ • (pb_1cell_pr1 cell₂) ^-1) ▹ f)
          • rassociator _ _ _
          • (cell₂ ◃ pb_cone_cell pb).
      Proof.
        cbn.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocr.
        do 2 (use vcomp_move_R_Mp ; [ is_iso | ]).
        cbn.
        rewrite !vassocl.
        do 2 (use vcomp_move_L_pM ; [ is_iso | ]).
        cbn.
        pose (pr212 Lh) as m.
        cbn in m.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact m.
        }
        clear m.
        rewrite !vassocl.
        rewrite lwhisker_id2, id2_left.
        etrans.
        {
          exact (pr2 σσ).
        }
        cbn.
        pose (pr212 Lh') as m.
        cbn in m.
        rewrite !vassocr.
        rewrite lwhisker_id2, id2_left in m.
        etrans.
        {
          apply maponpaths.
          exact (!m).
        }
        clear m.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        apply idpath.
      Qed.

      Definition is_pb_to_cartesian_lift_2cell_unique
        : isaprop (pb_2cell cell₁ cell₂).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
        use (pb_ump_eq pb_sqr).
        - exact (pb_1cell_pr1 cell₁ • (pb_1cell_pr1 cell₂)^-1).
        - exact (pb_1cell_pr2 cell₁ • (pb_1cell_pr2 cell₂)^-1).
        - exact is_pb_to_cartesian_lift_2cell_equality.
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (pb_2cell_pr1 φ₁).
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (pb_2cell_pr2 φ₁).
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (pb_2cell_pr1 φ₂).
        - use vcomp_move_L_Mp ; [ is_iso | ].
          exact (pb_2cell_pr2 φ₂).
      Qed.

      Definition is_pb_to_cartesian_lift_2cell
        : lift_2cell_factor (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        use (iscontrweqf cone_cell_weq_lift_2cell).
        use (iscontrweqf pb_2cell_weq_cone_cell).
        use iscontraprop1.
        - exact is_pb_to_cartesian_lift_2cell_unique.
        - use make_pb_2cell.
          + use (pb_ump_cell
                   pb_sqr
                   _ _
                   (pb_1cell_pr1 cell₁ • (pb_1cell_pr1 cell₂)^-1)
                   (pb_1cell_pr2 cell₁ • (pb_1cell_pr2 cell₂)^-1)).
            exact is_pb_to_cartesian_lift_2cell_equality.
          + abstract
              (refine (maponpaths (λ z, z • _) (pb_ump_cell_pr1 _ _ _ _ _ _) @ _) ;
               rewrite !vassocl ;
               rewrite vcomp_linv ;
               apply id2_right).
          + abstract
              (refine (maponpaths (λ z, z • _) (pb_ump_cell_pr2 _ _ _ _ _ _) @ _) ;
               rewrite !vassocl ;
               rewrite vcomp_linv ;
               apply id2_right).
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
           do 2 apply maponpaths ;
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
          + apply inv_B.
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

  Definition cod_cleaving_of_bicats
    : cleaving_of_bicats (cod_disp_bicat B).
  Proof.
    repeat split.
    - exact cod_local_cleaving.
    - exact cod_global_cleaving.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
  Defined.
End CodomainCleaving.

Definition cod_fibration_one_types
  : cleaving_of_bicats (cod_disp_bicat one_types).
Proof.
  use cod_cleaving_of_bicats.
  - exact one_type_2cell_iso.
  - exact one_types_has_pb.
Defined.
