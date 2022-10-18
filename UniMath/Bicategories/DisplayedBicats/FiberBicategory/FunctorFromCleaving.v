Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.FiberCategory.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Cartesians.

Local Open Scope cat.
Local Open Scope mor_disp.

Section ProjectionsGlobalCleaving.
  Context {B : bicat}
          {D : disp_bicat B}
          (global_D : global_cleaving D).

  Definition global_lift
             {x y : B}
             (f : x --> y)
             (yy : D y)
    : D x
    := pr1 (global_D x y yy f).

  Definition mor_from_global_lift
             {x y : B}
             (f : x --> y)
             (yy : D y)
    : global_lift f yy -->[ f ] yy
    := pr12 (global_D x y yy f).

  Definition is_cartesian_mor_from_global_lift
             {x y : B}
             (f : x --> y)
             (yy : D y)
    : cartesian_1cell D (mor_from_global_lift f yy)
    := pr22 (global_D x y yy f).

  Section GlobalCleavingOnMor.
    Context (local_D : local_iso_cleaving D)
            {x y : B}
            (f : x --> y).

    Definition global_lift_mor
               {yy₁ yy₂ : D y}
               (ff : yy₁ -->[ id₁ y ] yy₂)
      : global_lift f yy₁ -->[ id₁ x ] global_lift f yy₂
      := cartesian_1cell_lift_1cell
           D
           _
           (is_cartesian_mor_from_global_lift f yy₂)
           (local_iso_cleaving_1cell
              local_D
              (mor_from_global_lift f yy₁ ;; ff)
              (comp_of_invertible_2cell
                 (lunitor_invertible_2cell _)
                 (rinvunitor_invertible_2cell _))).

    Section OnId.
      Context (yy : D y).

      Local Definition global_mor_id_mor
        : global_lift f yy -->[ id₁ x · f] yy
        := local_iso_cleaving_1cell
             local_D
             (mor_from_global_lift f yy)
             (lunitor_invertible_2cell _).

      Local Definition global_mor_id_factor
        : disp_invertible_2cell
            (id2_invertible_2cell (id₁ x · f))
            (id_disp (global_lift f yy) ;; mor_from_global_lift f yy)
            global_mor_id_mor.
      Proof.
        refine (transportf
                  (λ z, disp_invertible_2cell z _ _)
                  _
                  (vcomp_disp_invertible
                     (disp_invertible_2cell_lunitor _)
                     (inverse_of_disp_invertible_2cell
                        (disp_local_iso_cleaving_invertible_2cell
                           local_D
                           (mor_from_global_lift f yy)
                           (lunitor_invertible_2cell f))))).
        abstract
          (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           apply lunitor_linvunitor).
      Defined.

      Definition global_mor_id_cell
        : disp_invertible_2cell
            (rwhisker_of_invertible_2cell
               _
               (id2_invertible_2cell _))
            (local_iso_cleaving_1cell
               local_D
               (mor_from_global_lift f yy ;; id_disp yy)
               (comp_of_invertible_2cell
                  (lunitor_invertible_2cell f)
                  (rinvunitor_invertible_2cell f)))
            global_mor_id_mor.
      Proof.
        refine (transportf
                  (λ z, disp_invertible_2cell z _ _)
                  _
                  (vcomp_disp_invertible
                     (disp_local_iso_cleaving_invertible_2cell
                        local_D
                        (mor_from_global_lift f yy ;; id_disp yy)
                        (comp_of_invertible_2cell
                           (lunitor_invertible_2cell _)
                           (rinvunitor_invertible_2cell _)))
                     (vcomp_disp_invertible
                        (disp_invertible_2cell_runitor _)
                        (inverse_of_disp_invertible_2cell
                           (disp_local_iso_cleaving_invertible_2cell
                              local_D
                              (mor_from_global_lift f yy)
                              (lunitor_invertible_2cell f)))))).
        abstract
          (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rinvunitor_runitor ;
           rewrite id2_left ;
           rewrite id2_rwhisker ;
           apply lunitor_linvunitor).
      Defined.

      Definition global_mor_id
        : disp_invertible_2cell
            (id2_invertible_2cell (id₁ x))
            (global_lift_mor (id_disp yy))
            (id_disp _).
      Proof.
        simple refine (_ ,, _).
        + exact (cartesian_1cell_lift_2cell
                   D
                   _
                   (is_cartesian_mor_from_global_lift f yy)
                   global_mor_id_cell
                   _
                   (id_disp (global_lift f yy) ,, global_mor_id_factor)).
        + use (cartesian_1cell_lift_2cell_invertible
                 D
                 (is_cartesian_mor_from_global_lift f yy)
                 _
                 _
                 _
                 (id_disp (global_lift f yy) ,, global_mor_id_factor)).
          exact (pr2 global_mor_id_cell).
      Defined.
    End OnId.

    Section OnComp.
      Context {yy₁ yy₂ yy₃ : D y}
              (ff : yy₁ -->[ id₁ y] yy₂)
              (gg : yy₂ -->[ id₁ y] yy₃).

      Definition global_mor_comp_mor
        : global_lift f yy₁ -->[ id₁ x · f ] yy₃
        := local_iso_cleaving_1cell
             local_D
             (mor_from_global_lift f yy₁ ;; ff ;; gg)
             (comp_of_invertible_2cell
                (lunitor_invertible_2cell _)
                (comp_of_invertible_2cell
                   (rinvunitor_invertible_2cell _)
                   (rinvunitor_invertible_2cell _))).

      Definition global_mor_comp_factor
        : disp_invertible_2cell
            (id2_invertible_2cell (id₁ x · f))
            (local_iso_cleaving_1cell local_D
               (global_lift_mor ff ;; global_lift_mor gg)
               (idempunitor x)
             ;; mor_from_global_lift f yy₃)
            global_mor_comp_mor.
      Proof.
        refine (transportf
                  (λ z, disp_invertible_2cell z _ _)
                  _
                  (vcomp_disp_invertible
                     (vcomp_disp_invertible
                        (disp_invertible_2cell_rwhisker
                           _
                           (disp_local_iso_cleaving_invertible_2cell
                              local_D
                              _
                              _))
                        (vcomp_disp_invertible
                           (disp_invertible_2cell_rassociator _ _ _)
                           (vcomp_disp_invertible
                              (disp_invertible_2cell_lwhisker
                                 _
                                 (pr2 (cartesian_1cell_lift_1cell D
                                         (mor_from_global_lift f yy₃)
                                         _
                                         _)))
                              (vcomp_disp_invertible
                                 (disp_invertible_2cell_lwhisker
                                    _
                                    (disp_local_iso_cleaving_invertible_2cell
                                       local_D
                                       _
                                       _))
                                 (vcomp_disp_invertible
                                    (disp_invertible_2cell_lassociator _ _ _)
                                    (disp_invertible_2cell_rwhisker
                                       _
                                       (vcomp_disp_invertible
                                          (pr2 (cartesian_1cell_lift_1cell
                                                  D
                                                  _
                                                  _
                                                  _))
                                          (disp_local_iso_cleaving_invertible_2cell
                                             local_D
                                             _
                                             _))))))))
                     (inverse_of_disp_invertible_2cell
                        (disp_local_iso_cleaving_invertible_2cell
                           local_D
                           _
                           _)))).
        abstract
          (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn ;
           rewrite lwhisker_id2, !id2_left ;
           rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lunitor_lwhisker ;
           rewrite runitor_lunitor_identity ;
           rewrite !vassocr ;
           rewrite rwhisker_vcomp ;
           rewrite linvunitor_lunitor ;
           rewrite id2_rwhisker ;
           rewrite id2_left ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite lunitor_triangle ;
           rewrite !vassocr ;
           rewrite vcomp_lunitor ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_left ;
           refine (_ @ id2_right _) ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           refine (_ @ id2_left _) ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite <- runitor_triangle ;
           rewrite runitor_lunitor_identity ;
           rewrite lunitor_lwhisker ;
           rewrite rwhisker_vcomp ;
           rewrite rinvunitor_runitor ;
           apply id2_rwhisker).
      Defined.

      Definition global_mor_comp_cell
        : disp_invertible_2cell
            (rwhisker_of_invertible_2cell
               _
               (id2_invertible_2cell _))
            (local_iso_cleaving_1cell
               local_D
               (mor_from_global_lift f yy₁
                ;;
                local_iso_cleaving_1cell local_D (ff ;; gg) (idempunitor y))
               (comp_of_invertible_2cell
                  (lunitor_invertible_2cell f)
                  (rinvunitor_invertible_2cell f)))
            global_mor_comp_mor.
      Proof.
        refine (transportf
                  (λ z, disp_invertible_2cell z _ _)
                  _
                  (vcomp_disp_invertible
                     (disp_local_iso_cleaving_invertible_2cell
                        local_D
                        _
                        _)
                     (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (disp_invertible_2cell_lwhisker
                              _
                              (disp_local_iso_cleaving_invertible_2cell
                                 local_D
                                 _
                                 _))
                           (disp_invertible_2cell_lassociator _ _ _))
                        (inverse_of_disp_invertible_2cell
                           (disp_local_iso_cleaving_invertible_2cell
                              local_D
                              _
                              _))))).
        abstract
          (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ; cbn ;
           rewrite id2_rwhisker ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_left ;
           refine (_ @ id2_right _) ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite id2_left ;
           refine (_ @ id2_right _) ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite id2_right ;
           rewrite <- runitor_triangle ;
           rewrite !vassocr ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite runitor_lunitor_identity ;
           apply idpath).
      Defined.

      Definition global_mor_comp
        : disp_invertible_2cell
            (id2_invertible_2cell _)
            (global_lift_mor
               (local_iso_cleaving_1cell local_D (ff ;; gg) (idempunitor y)))
            (local_iso_cleaving_1cell local_D
               (global_lift_mor ff ;; global_lift_mor gg)
               (idempunitor x)).
      Proof.
        simple refine (_ ,, _).
        - exact (cartesian_1cell_lift_2cell
                   D
                   _
                   (is_cartesian_mor_from_global_lift f yy₃)
                   global_mor_comp_cell
                   _
                   (local_iso_cleaving_1cell
                      local_D
                      (global_lift_mor ff ;; global_lift_mor gg)
                      (idempunitor x)
                    ,,
                    global_mor_comp_factor)).
        - use (cartesian_1cell_lift_2cell_invertible
                 D
                 (is_cartesian_mor_from_global_lift f yy₃)
                 _
                 _
                 _
                 (_ ,, _)).
          exact (pr2 global_mor_comp_cell).
      Defined.
    End OnComp.
  End GlobalCleavingOnMor.
End ProjectionsGlobalCleaving.

Section FiberFunctor.
  Context {B : bicat}
          (D : disp_bicat B)
          (HD₁ : disp_2cells_isaprop D)
          (HD₂ : disp_univalent_2_1 D)
          (global_D : global_cleaving D)
          (local_D : local_iso_cleaving D)
          {x y : B}
          (f : x --> y).

  Definition functor_from_cleaving_data
    : functor_data
        (discrete_fiber_category D HD₁ HD₂ local_D y)
        (discrete_fiber_category D HD₁ HD₂ local_D x).
  Proof.
    use make_functor_data.
    - exact (λ yy, global_lift global_D f yy).
    - exact (λ yy₁ yy₂ ff, global_lift_mor global_D local_D f ff).
  Defined.

  Definition functor_from_cleaving_is_functor
    : is_functor functor_from_cleaving_data.
  Proof.
    split.
    - intros yy.
      apply (disp_isotoid_2_1 _ HD₂ (idpath _)).
      exact (global_mor_id global_D local_D f yy).
    - intros yy₁ yy₂ yy₃ ff gg ; cbn in *.
      apply (disp_isotoid_2_1 _ HD₂ (idpath _)).
      exact (global_mor_comp global_D local_D f ff gg).
  Qed.

  Definition functor_from_cleaving
    : discrete_fiber_category D HD₁ HD₂ local_D y
      ⟶
      discrete_fiber_category D HD₁ HD₂ local_D x.
  Proof.
    use make_functor.
    - exact functor_from_cleaving_data.
    - exact functor_from_cleaving_is_functor.
  Defined.
End FiberFunctor.
