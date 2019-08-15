(**
Dependent product of diplayed bicategories.
If we have a type `J` and a family indexed by `J` of displayed bicategories on `J`,
then we can assemble this into a displayed bicategory whose objects are dependent functions.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp.

Section DispDepprod.
  Context {B : bicat}
          (I : UU)
          (D : I → disp_bicat B).

  Definition disp_depprod_cat_ob_mor : disp_cat_ob_mor B.
  Proof.
    use tpair.
    - exact (λ x, ∏ (i : I), D i x).
    - exact (λ x y xx yy f, ∏ (i : I), xx i -->[ f ] yy i).
  Defined.

  Definition disp_depprod_cat_data : disp_cat_data B.
  Proof.
    use tpair.
    - exact disp_depprod_cat_ob_mor.
    - split.
      + exact (λ x xx i, id_disp (xx i)).
      + exact (λ x y z f g xx yy zz ff gg i, ff i;;gg i).
  Defined.

  Definition disp_depprod_disp_2cell_struct
    : disp_2cell_struct disp_depprod_cat_ob_mor
    := λ x y f g α xx yy ff gg, ∏ (i : I), ff i ==>[ α ] gg i.

  Definition disp_depprod_disp_prebicat_ops
    : disp_prebicat_ops (disp_depprod_cat_data,, disp_depprod_disp_2cell_struct).
  Proof.
    repeat split.
    - exact (λ a b f aa bb ff i, disp_id2 (ff i)).
    - exact (λ a b f aa bb ff i, disp_lunitor (ff i)).
    - exact (λ a b f aa bb ff i, disp_runitor (ff i)).
    - exact (λ a b f aa bb ff i, disp_linvunitor (ff i)).
    - exact (λ a b f aa bb ff i, disp_rinvunitor (ff i)).
    - exact (λ a b c d f g h aa bb cc dd ff gg hh i,
             disp_rassociator (ff i) (gg i) (hh i)).
    - exact (λ a b c d f g h aa bb cc dd ff gg hh i,
             disp_lassociator (ff i) (gg i) (hh i)).
    - exact (λ a b f g h x y aa bb ff gg hh xx yy i, xx i •• yy i).
    - exact (λ a b c f g1 g2 x aa bb cc ff gg1 gg2 xx i, ff i ◃◃ xx i).
    - exact (λ a b c f1 f2 g x aa bb cc ff1 ff2 gg xx i, xx i ▹▹ gg i).
  Defined.

  Definition disp_depprod_prebicat_data : disp_prebicat_data B.
  Proof.
    use tpair.
    - use tpair.
      + exact disp_depprod_cat_data.
      + exact disp_depprod_disp_2cell_struct.
    - exact disp_depprod_disp_prebicat_ops.
  Defined.

  Definition disp_depprod_prebicat_laws_help
             {a b : B}
             {f g : a --> b}
             {x y : f ==> g}
             {aa : ∏ (i : I), D i a} {bb : ∏ (i : I), D i b}
             {ff : ∏ (i : I), aa i -->[ f ] bb i}
             {gg : ∏ (i : I), aa i -->[ g ] bb i}
             (xx : ∏ (i : I), ff i ==>[ y ] gg i)
             (p : x = y)
             (i : I)
    : transportb (λ α : f ==> g, ff i ==>[ α ] gg i) p (xx i)
      =
      transportb (λ α : f ==> g, ∏ (i : I), ff i ==>[ α ] gg i) p xx i.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition disp_depprod_prebicat_laws
    : disp_prebicat_laws disp_depprod_prebicat_data.
  Proof.
    repeat split
    ; intro ; intros
    ; use funextsec ; intro
    ; refine (_ @ disp_depprod_prebicat_laws_help _ _ _).
    - apply disp_id2_left.
    - apply disp_id2_right.
    - apply disp_vassocr.
    - apply disp_lwhisker_id2.
    - apply disp_id2_rwhisker.
    - apply disp_lwhisker_vcomp.
    - apply disp_rwhisker_vcomp.
    - apply disp_vcomp_lunitor.
    - apply disp_vcomp_runitor.
    - apply disp_lwhisker_lwhisker.
    - apply disp_rwhisker_lwhisker.
    - apply disp_rwhisker_rwhisker.
    - apply disp_vcomp_whisker.
    - apply disp_lunitor_linvunitor.
    - apply disp_linvunitor_lunitor.
    - apply disp_runitor_rinvunitor.
    - apply disp_rinvunitor_runitor.
    - apply disp_lassociator_rassociator.
    - apply disp_rassociator_lassociator.
    - apply disp_runitor_rwhisker.
    - apply disp_lassociator_lassociator.
  Qed.

  Definition disp_depprod_prebicat : disp_prebicat B.
  Proof.
    use tpair.
    - exact disp_depprod_prebicat_data.
    - exact disp_depprod_prebicat_laws.
  Defined.

  Definition disp_depprod_bicat : disp_bicat B.
  Proof.
    use tpair.
    - exact disp_depprod_prebicat.
    - intros a b f g x aa bb ff gg.
      use impred_isaset.
      intro i.
      apply (D i).
  Defined.

  Definition disp_2cells_isaprop_depprod
             (HD : ∏ (i : I), disp_2cells_isaprop (D i))
    : disp_2cells_isaprop disp_depprod_bicat.
  Proof.
    intro; intros.
    use impred.
    intro i.
    apply HD.
  Qed.

  Definition disp_depprod_bicat_disp_is_invertible_2cell_map
             {a b : B}
             {f g : B ⟦ a, b ⟧}
             {x : f ==> g}
             {xinv : is_invertible_2cell x}
             {aa : disp_depprod_bicat a}
             {bb : disp_depprod_bicat b}
             {ff : aa -->[ f] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
             (Hx : ∏ (i : I), is_disp_invertible_2cell xinv (xx i))
    : is_disp_invertible_2cell xinv xx.
  Proof.
    use tpair.
    - exact (λ i, pr1 (Hx i)).
    - split.
      + use funextsec.
        intro i.
        refine (_ @ disp_depprod_prebicat_laws_help _ _ _).
        exact (disp_vcomp_rinv ((xx i ,, Hx i) : disp_invertible_2cell (x ,, xinv) _ _)).
      + use funextsec.
        intro i.
        refine (_ @ disp_depprod_prebicat_laws_help _ _ _).
        exact (disp_vcomp_linv ((xx i ,, Hx i) : disp_invertible_2cell (x ,, xinv) _ _)).
  Defined.

  Definition disp_locally_groupoid_depprod
             (HD : ∏ (i : I), disp_locally_groupoid (D i))
    : disp_locally_groupoid disp_depprod_bicat.
  Proof.
    intros a b f g x aa bb ff gg xx.
    apply disp_depprod_bicat_disp_is_invertible_2cell_map.
    intro i.
    apply HD.
  Qed.

  Definition disp_depprod_bicat_disp_invertible_2cell_map
             {a b : B}
             {f : B ⟦ a, b ⟧}
             {aa : disp_depprod_bicat a}
             {bb : disp_depprod_bicat b}
             (ff : aa -->[ f] bb)
             (gg : aa -->[ f] bb)
    : (∏ (i : I), disp_invertible_2cell (id2_invertible_2cell f) (ff i) (gg i))
        →
        disp_invertible_2cell (id2_invertible_2cell f) ff gg.
  Proof.
    intros x.
    use tpair.
    - exact (λ i, x i).
    - apply disp_depprod_bicat_disp_is_invertible_2cell_map.
      exact (λ i, pr2 (x i)).
  Defined.

  Definition disp_depprod_bicat_disp_is_invertible_2cell_pr
             {a b : B}
             {f g : B ⟦ a, b ⟧}
             {x : f ==> g}
             {xinv : is_invertible_2cell x}
             {aa : disp_depprod_bicat a}
             {bb : disp_depprod_bicat b}
             {ff : aa -->[ f] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
             (Hx : is_disp_invertible_2cell xinv xx)
    : ∏ (i : I), is_disp_invertible_2cell xinv (xx i).
  Proof.
    intro i.
    use tpair.
    - exact (pr1 Hx i).
    - split.
      + refine (_ @ !(disp_depprod_prebicat_laws_help (disp_id2 ff) _ _)).
        exact (eqtohomot (disp_vcomp_rinv
                            ((xx ,, Hx) : disp_invertible_2cell (x ,, xinv) _ _)) i).
      + refine (_ @ !(disp_depprod_prebicat_laws_help (disp_id2 gg) _ _)).
        exact (eqtohomot (disp_vcomp_linv
                            ((xx ,, Hx) : disp_invertible_2cell (x ,, xinv) _ _)) i).
  Defined.

  Definition disp_depprod_bicat_disp_invertible_2cell_inv_map
             {a b : B}
             {f : B ⟦ a, b ⟧}
             {aa : disp_depprod_bicat a}
             {bb : disp_depprod_bicat b}
             (ff : aa -->[ f] bb)
             (gg : aa -->[ f] bb)
    : disp_invertible_2cell (id2_invertible_2cell f) ff gg
      →
      (∏ (i : I), disp_invertible_2cell (id2_invertible_2cell f) (ff i) (gg i)).
  Proof.
    intros x i.
    use tpair.
    - exact (pr1 x i).
    - exact (disp_depprod_bicat_disp_is_invertible_2cell_pr _ (pr2 x) i).
  Defined.

  Definition disp_depprod_bicat_disp_invertible_2cell_weq
             {a b : B}
             {f : B ⟦ a, b ⟧}
             {aa : disp_depprod_bicat a}
             {bb : disp_depprod_bicat b}
             (ff : aa -->[ f] bb)
             (gg : aa -->[ f] bb)
    : (∏ (i : I), disp_invertible_2cell (id2_invertible_2cell f) (ff i) (gg i))
        ≃
        disp_invertible_2cell (id2_invertible_2cell f) ff gg.
  Proof.
    use make_weq.
    - exact (disp_depprod_bicat_disp_invertible_2cell_map ff gg).
    - use gradth.
      + exact (disp_depprod_bicat_disp_invertible_2cell_inv_map ff gg).
      + intros x.
        use funextsec.
        intro i.
        use subtypePath.
        { intro ; apply isaprop_is_disp_invertible_2cell. }
        apply idpath.
      + intros x.
        use subtypePath.
        { intro ; apply isaprop_is_disp_invertible_2cell. }
        apply idpath.
  Defined.

  Section DepProdBicatDispLocallyUnivalent.
    Variable (HD_2_1 : ∏ (i : I), disp_univalent_2_1 (D i)).

    Definition disp_depprod_bicat_idtotiso_2_1
               {a b : B}
               {f : B ⟦ a, b ⟧}
               {aa : disp_depprod_bicat a}
               {bb : disp_depprod_bicat b}
               (ff : aa -->[ f] bb)
               (gg : aa -->[ f] bb)
      : ff = gg ≃ disp_invertible_2cell (id2_invertible_2cell f) ff gg
      := ((disp_depprod_bicat_disp_invertible_2cell_weq ff gg)
            ∘ weqonsecfibers
            _ _ (λ i, make_weq _ (HD_2_1 i _ _ _ _ (idpath _) _ _ (ff i) (gg i)))
            ∘ invweq (weqfunextsec _ _ _))%weq.

    Definition disp_depprod_univalent_2_1
      : disp_univalent_2_1 disp_depprod_bicat.
    Proof.
      apply fiberwise_local_univalent_is_univalent_2_1.
      intros a b f aa bb ff gg.
      use weqhomot.
      - exact (disp_depprod_bicat_idtotiso_2_1 ff gg).
      - intros p.
        induction p.
        use subtypePath.
        { intro ; apply isaprop_is_disp_invertible_2cell. }
        apply idpath.
    Defined.
  End DepProdBicatDispLocallyUnivalent.

  Definition disp_depprod_bicat_disp_adjequiv_map
             {a : B}
             (aa bb : disp_depprod_bicat a)
    : (∏ (i : I), disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity a)
                    (aa i) (bb i))
      → disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb.
  Proof.
    intros f.
    use tpair.
    - exact (λ i, f i).
    - use tpair.
      + use tpair.
        * exact (λ i, disp_left_adjoint_right_adjoint _ (f i)).
        * split.
          ** exact (λ i, disp_left_adjoint_unit _ (f i)).
          ** exact (λ i, disp_left_adjoint_counit _ (f i)).
      + split.
        * split.
          ** abstract
               (use funextsec ;
                intro i ;
                refine (pr1 (pr122 (f i)) @ _) ;
                refine ((disp_depprod_prebicat_laws_help _ _ _))).
          ** abstract
               (use funextsec ;
                intro i ;
                refine (pr2 (pr122 (f i)) @ _) ;
                refine ((disp_depprod_prebicat_laws_help _ _ _))).
        * split.
          ** apply disp_depprod_bicat_disp_is_invertible_2cell_map.
             exact (λ i, pr1 (pr222 (f i))).
          ** apply disp_depprod_bicat_disp_is_invertible_2cell_map.
             exact (λ i, pr2 (pr222 (f i))).
  Defined.

  Definition disp_depprod_bicat_disp_adjequiv_inv
             {a : B}
             (aa bb : disp_depprod_bicat a)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb
      → (∏ (i : I), disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity a)
                    (aa i) (bb i)).
  Proof.
    intros f i.
    use tpair.
    - exact (pr1 f i).
    - use tpair.
      + use tpair.
        * exact (disp_left_adjoint_right_adjoint _ f i).
        * split.
          ** exact (disp_left_adjoint_unit _ f i).
          ** exact (disp_left_adjoint_counit _ f i).
      + split.
        * split.
          ** abstract
               (refine (eqtohomot (pr1 (pr122 f)) i @ _) ;
                refine (!(disp_depprod_prebicat_laws_help _ _ _))).
          ** abstract
               (refine (eqtohomot (pr2 (pr122 f)) i @ _) ;
                refine (!(disp_depprod_prebicat_laws_help _ _ _))).
        * split.
          ** exact (disp_depprod_bicat_disp_is_invertible_2cell_pr
                      _ (pr1 (pr222 f)) i).
          ** exact (disp_depprod_bicat_disp_is_invertible_2cell_pr
                      _ (pr2 (pr222 f)) i).
  Defined.

  Variable (HB : is_univalent_2_1 B)
           (HD_2_1 : ∏ (i : I), disp_univalent_2_1 (D i)).

  Definition disp_depprod_bicat_disp_adjequiv_weq
             {a : B}
             (aa bb : disp_depprod_bicat a)
    : (∏ x : I, disp_adjoint_equivalence
                  (internal_adjoint_equivalence_identity a)
                  (aa x) (bb x))
        ≃ disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb.
  Proof.
    use make_weq.
    - exact (disp_depprod_bicat_disp_adjequiv_map aa bb).
    - use gradth.
      + exact (disp_depprod_bicat_disp_adjequiv_inv aa bb).
      + intros f.
        use funextsec.
        intros i.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence
          ; [ exact HB | exact (HD_2_1 i) ].
        }
        apply idpath.
      + intros f.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence
          ; [ exact HB | exact (disp_depprod_univalent_2_1 HD_2_1) ].
        }
        apply idpath.
  Defined.

  Section DepProdBicatDispGloballyUnivalent.
    Variable (HD_2_0 : ∏ (i : I), disp_univalent_2_0 (D i)).

    Definition disp_depprod_bicat_idtotiso_2_0
               {a : B}
               (aa bb : disp_depprod_bicat a)
      : (aa = bb)
          ≃
          disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa bb
      := ((disp_depprod_bicat_disp_adjequiv_weq aa bb)
            ∘ weqonsecfibers
              _ _ (λ i, make_weq _ (HD_2_0 i _ _ (idpath a) _ _))
            ∘ invweq (weqfunextsec _ _ _))%weq.

    Definition disp_depprod_univalent_2_0
      : disp_univalent_2_0 disp_depprod_bicat.
    Proof.
      apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
      intros a aa bb.
      use weqhomot.
      - exact (disp_depprod_bicat_idtotiso_2_0 aa bb).
      - intros p.
        induction p.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence
          ; [ exact HB | exact (disp_depprod_univalent_2_1 HD_2_1) ].
        }
        apply idpath.
    Defined.
  End DepProdBicatDispGloballyUnivalent.
End DispDepprod.
