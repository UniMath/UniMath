(****************************************************************************

 Eilenberg-Moore objects in the opposite bicategory

 We show that Eilenberg-Moore objects in the opposite bicategory can be
 constructed from Kleisli objects in the original bicategory.

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Colimits.KleisliObjects.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInOp1Bicat.

Local Open Scope cat.

Section EilenbergMooreOpposite.
  Context {B : bicat}.

  Section Op1Cone.
    Context (m : mnd (op1_bicat B)).

    Let x : B := ob_of_mnd m.
    Let f : x --> x := endo_of_mnd m.
    Let η : id₁ x ==> f := unit_of_mnd m.
    Let μ : f · f ==> f := mult_of_mnd m.

    Section ToKleisliCocone.
      Context (e : em_cone m).

      Let h : B ⟦ ob_of_mnd m , e ⟧ := mor_of_mnd_mor (mor_of_em_cone _ e).
      Let γ : f · h ==> h · id₁ _ := mnd_mor_endo (mor_of_em_cone _ e).
      Let p₁ : rinvunitor h • (_ ◃ id₂ _) = linvunitor h • (η ▹ _) • γ
        := mnd_mor_unit (mor_of_em_cone _ e).
      Let p₂ : rassociator _ _ _
               • (f ◃ γ)
               • lassociator _ _ _
               • (γ ▹ _)
               • rassociator _ _ _
               • (h ◃ runitor _)
               =
               (μ ▹ h) • γ
          := mnd_mor_mu (mor_of_em_cone _ e).

      Definition from_op1_em_cone
        : kleisli_cocone m.
      Proof.
        use make_kleisli_cocone.
        - exact e.
        - exact h.
        - exact (γ • runitor _).
        - abstract
            (cbn ;
             rewrite lwhisker_id2 in p₁ ;
             rewrite id2_right in p₁ ;
             rewrite !vassocr ;
             use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
             use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
             rewrite !vassocr ;
             exact (!p₁)).
        - abstract
            (rewrite !vassocr ;
             refine (_ @ maponpaths (λ z, z • _) p₂) ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite <- !lwhisker_vcomp ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite runitor_triangle ;
             rewrite vcomp_runitor ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite <- runitor_triangle ;
             rewrite !vassocr ;
             rewrite lassociator_rassociator ;
             rewrite id2_left ;
             apply idpath).
      Defined.
    End ToKleisliCocone.

    Definition to_op1_em_cone
               (k : kleisli_cocone m)
      : em_cone m.
    Proof.
      use make_em_cone.
      - exact k.
      - exact (mor_of_kleisli_cocone _ k).
      - exact (cell_of_kleisli_cocone _ k • rinvunitor _).
      - abstract
          (cbn ;
           rewrite !vassocr ;
           refine (!(id2_left _) @ _) ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           rewrite kleisli_cocone_unit ;
           apply idpath).
      - abstract
          (cbn ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite lwhisker_vcomp ;
           rewrite rinvunitor_runitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite kleisli_cocone_mult ;
           apply idpath).
    Defined.

    Section ToEMMore.
      Context (e : em_cone m)
              {k : kleisli_cocone m}
              (g : kleisli_cocone_mor m k (from_op1_em_cone e)).

      Let h : B ⟦ ob_of_mnd m , e ⟧
        := mor_of_mnd_mor (mor_of_em_cone m e).

      Let γ : f · h ==> h · id₁ _
        := mnd_mor_endo (mor_of_em_cone m e).

      Definition to_op1_em_cone_mor_mnd_cell_eq
        : lassociator _ _ _
          • ((cell_of_kleisli_cocone m k • rinvunitor _) ▹ g)
          • rassociator _ _ _
          • (mor_of_kleisli_cocone m k ◃ (lunitor g • rinvunitor g))
          • lassociator _ _ _
          • (cell_of_kleisli_cocone_mor _ g ▹ _)
          =
          (_ ◃ cell_of_kleisli_cocone_mor _ g)
          • γ.
      Proof.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite !rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp.
        rewrite lwhisker_vcomp.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite rinvunitor_triangle.
        rewrite !rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact (!(kleisli_cocone_mor_endo _ g)).
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          refine (vassocl _ _ _ @ _).
          apply maponpaths.
          cbn.
          apply runitor_rinvunitor.
        }
        rewrite id2_right.
        apply idpath.
      Qed.

      Definition to_op1_em_cone_mor_mnd_cell
        : # (mnd_incl (op1_bicat B)) g · mor_of_em_cone m (to_op1_em_cone k)
          ==>
          mor_of_em_cone m e.
      Proof.
        use make_mnd_cell.
        - exact (cell_of_kleisli_cocone_mor _ g).
        - exact to_op1_em_cone_mor_mnd_cell_eq.
      Defined.

      Definition to_op1_em_cone_mor
        : em_cone_mor
            _
            e
            (to_op1_em_cone k).
      Proof.
        use make_em_cone_mor.
        - exact g.
        - use make_invertible_2cell.
          + exact to_op1_em_cone_mor_mnd_cell.
          + use is_invertible_mnd_2cell.
            exact (cell_of_kleisli_cocone_mor_is_invertible _ g).
      Defined.
    End ToEMMore.

    Definition op1_has_em_ump_1
               (k : kleisli_cocone m)
               (Hk : has_kleisli_ump_1 _ k)
      : em_ump_1 m (to_op1_em_cone k).
    Proof.
      intro e.
      use to_op1_em_cone_mor.
      exact (Hk (from_op1_em_cone e)).
    Defined.

    Section UMP2.
      Context (k : kleisli_cocone m)
              (Hk : has_kleisli_ump_2 _ k)
              {z : B}
              {g₁ g₂ : k --> z}
              (α : # (mnd_incl (op1_bicat B)) g₁ · mor_of_em_cone m (to_op1_em_cone k)
                   ==>
                   # (mnd_incl (op1_bicat B)) g₂ · mor_of_em_cone m (to_op1_em_cone k)).

      Let αcell : mor_of_kleisli_cocone m k · g₁ ==> mor_of_kleisli_cocone m k · g₂
          := cell_of_mnd_cell α.

      Let p : lassociator _ _ _
              • ((cell_of_kleisli_cocone m k • rinvunitor _) ▹ g₁)
              • rassociator _ _ _
              • (_ ◃ (lunitor _ • rinvunitor _))
              • lassociator _ _ _
              • (αcell ▹ _)
              =
              (_ ◃ αcell)
              • (lassociator _ _ _
                 • ((cell_of_kleisli_cocone m k • rinvunitor _) ▹ _)
                 • rassociator _ _ _
                 • (_ ◃ (lunitor _ • rinvunitor _))
                 • lassociator _ _ _)
          := mnd_cell_endo α.

      Local Lemma op1_has_em_ump_2_help_eq
        : lassociator _ _ _ • (cell_of_kleisli_cocone m k ▹ g₁) • αcell
          =
          (_ ◃ αcell) • lassociator _ _ _ • (cell_of_kleisli_cocone m k ▹ g₂).
      Proof.
        rewrite <- !lwhisker_vcomp in p.
        rewrite <- !rwhisker_vcomp in p.
        rewrite !vassocl in p.
        rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)) in p.
        rewrite lunitor_lwhisker in p.
        rewrite !vassocl in p.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) in p.
        rewrite rwhisker_vcomp in p.
        rewrite rinvunitor_runitor in p.
        rewrite id2_rwhisker in p.
        rewrite id2_left in p.
        rewrite !vassocl in p.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) in p.
        rewrite rinvunitor_triangle in p.
        rewrite !vassocl in p.
        rewrite !rwhisker_hcomp in p.
        rewrite <- rinvunitor_natural in p.
        rewrite <- !rwhisker_hcomp in p.
        rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)) in p.
        rewrite !rwhisker_hcomp in p.
        rewrite <- triangle_l_inv in p.
        rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp in p.
        rewrite !vassocl in p.
        rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • z)))) (vassocr _ _ _)) in p.
        rewrite lassociator_rassociator in p.
        rewrite id2_left in p.
        rewrite !vassocl in p.
        rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)) in p.
        rewrite lwhisker_vcomp in p.
        rewrite linvunitor_lunitor in p.
        rewrite lwhisker_id2 in p.
        rewrite id2_left in p.
        rewrite rinvunitor_triangle in p.
        use (vcomp_rcancel (rinvunitor _)) ; [ is_iso | ].
        rewrite !vassocl.
        exact p.
      Qed.

      Definition op1_has_em_ump_2_unique
        : isaprop
            (∑ (β : g₁ ==> g₂), ## (mnd_incl (op1_bicat B)) β ▹ _ = α).
      Proof.
        use invproofirrelevance.
        intros β₁ β₂.
        use subtypePath ; [ intro ; apply cellset_property | ].
        use (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (Hk z g₁ g₂ αcell _))
                  (pr1 β₁ ,, _)
                  (pr1 β₂ ,, _))).
        - exact op1_has_em_ump_2_help_eq.
        - exact (maponpaths pr1 (pr2 β₁)).
        - exact (maponpaths pr1 (pr2 β₂)).
      Qed.

      Definition op1_has_em_ump_2_cell
        : g₁ ==> g₂
        := pr11 (Hk z g₁ g₂ αcell op1_has_em_ump_2_help_eq).

      Definition op1_has_em_ump_2_eq
        : ## (mnd_incl (op1_bicat B)) op1_has_em_ump_2_cell ▹ _ = α.
      Proof.
        use eq_mnd_cell.
        exact (pr21 (Hk z g₁ g₂ αcell op1_has_em_ump_2_help_eq)).
      Qed.
    End UMP2.

    Definition op1_has_em_ump_2
               (k : kleisli_cocone m)
               (Hk : has_kleisli_ump_2 _ k)
      : em_ump_2 m (to_op1_em_cone k).
    Proof.
      intros z g₁ g₂ α.
      use iscontraprop1.
      - exact (op1_has_em_ump_2_unique k Hk α).
      - simple refine (_ ,, _).
        + exact (op1_has_em_ump_2_cell k Hk α).
        + exact (op1_has_em_ump_2_eq k Hk α).
    Defined.
  End Op1Cone.

  Definition op1_has_em
             (HB : has_kleisli B)
    : bicat_has_em (op1_bicat B).
  Proof.
    intro m.
    pose (HB m) as q.
    refine (to_op1_em_cone m (pr1 q) ,, _ ,, _).
    - apply op1_has_em_ump_1.
      exact (pr12 q).
    - apply op1_has_em_ump_2.
      exact (pr22 q).
  Defined.
End EilenbergMooreOpposite.
