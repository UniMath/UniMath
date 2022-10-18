(**********************************************************************

 Limits in slices of display map bicategories

 Content
 1. Final objects
 2. Products

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Require Import UniMath.Bicategories.Logic.DisplayMapBicat.

Local Open Scope cat.

(**
 1. Final objects
 *)
Section ArrowSubbicatFinal.
  Context {B : bicat}
          (D : arrow_subbicat B)
          (b : B)
          (H : arrow_subbicat_bifinal D).

  Definition disp_map_slice_bifinal_obj
    : disp_map_slice_bicat D b
    := b ,, id₁ b ,, pr1 H b.

  Definition disp_map_slice_bifinal_1cell_property
    : bifinal_1cell_property disp_map_slice_bifinal_obj.
  Proof.
    intros h.
    refine (pr12 h ,, _ ,, _).
    - exact (pr2 H _ _ (pr12 h)).
    - exact (rinvunitor_invertible_2cell (pr12 h)).
  Defined.

  Definition disp_map_slice_bifinal_2cell_property_eq
             {h : disp_map_slice_bicat D b}
             (α β : h --> disp_map_slice_bifinal_obj)
    : pr122 α
      • ((((rinvunitor (pr1 α) • (pr22 α) ^-1) • pr22 β) • runitor (pr1 β)) ▹ id₁ b)
      =
      pr122 β.
  Proof.
    cbn.
    use vcomp_move_R_pM ; [ apply property_from_invertible_2cell | ].
    use (vcomp_lcancel (runitor _)) ; [ is_iso | ].
    refine (_ @ vcomp_runitor _ _ _).
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    etrans.
    {
      do 3 apply maponpaths_2.
      rewrite <- runitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite runitor_lunitor_identity.
      rewrite !vassocl.
      refine (maponpaths (λ z, _ • z) (vassocr _ _ _) @ _).
      rewrite lwhisker_vcomp.
      rewrite lunitor_linvunitor.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite rassociator_lassociator.
      apply idpath.
    }
    rewrite id2_left.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite <- runitor_triangle.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite runitor_rwhisker.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Definition disp_map_slice_bifinal_2cell_property
             (h : disp_map_slice_bicat D b)
    : bifinal_2cell_property disp_map_slice_bifinal_obj h.
  Proof.
    intros α β.
    simple refine (_ ,, _).
    - exact (rinvunitor _ • (pr22 α)^-1 • pr22 β • runitor _).
    - exact (disp_map_slice_bifinal_2cell_property_eq α β).
  Defined.

  Definition disp_map_slice_bifinal_eq_property
             (h : disp_map_slice_bicat D b)
    : bifinal_eq_property disp_map_slice_bifinal_obj h.
  Proof.
    intros α β p q.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    use (vcomp_lcancel (runitor _)) ; [ is_iso | ].
    rewrite <- !vcomp_runitor.
    apply maponpaths_2.
    apply (vcomp_lcancel (pr122 α) (pr22 α)).
    exact (pr2 p @ !(pr2 q)).
  Qed.

  Definition disp_map_slice_bifinal
    : bifinal_obj (disp_map_slice_bicat D b).
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_bifinal_obj.
    - use make_is_bifinal.
      + exact disp_map_slice_bifinal_1cell_property.
      + exact disp_map_slice_bifinal_2cell_property.
      + exact disp_map_slice_bifinal_eq_property.
  Defined.
End ArrowSubbicatFinal.

(**
 2. Products
 *)
Section DisplayMapBicatProduct.
  Context {B : bicat}
          (D : disp_map_bicat B)
          (D_comp : arrow_subbicat_closed_composition D)
          (D_mor : arrow_subbicat_closed_prod_mor D)
          {pb x y b : B}
          {f : x --> b}
          (Hf : pred_ob D f)
          {g : y --> b}
          (Hg : pred_ob D g)
          (π₁ : pb --> x)
          (π₂ : pb --> y)
          (γ : invertible_2cell (π₁ · f) (π₂ · g))
          (cone : pb_cone f g := make_pb_cone _ π₁ π₂ γ)
          (Hpb : has_pb_ump cone).

  Let ff : disp_map_slice_bicat D b
    := x ,, f ,, Hf.
  Let gg : disp_map_slice_bicat D b
    := y ,, g ,, Hg.

  Definition binprod_cone_in_disp_map_slice
    : @binprod_cone (disp_map_slice_bicat D b) ff gg.
  Proof.
    use make_binprod_cone.
    - refine (pb ,, π₁ · f ,, _).
      apply D_comp.
      + exact (pb_preserves_pred_ob D Hg (mirror_has_pb_ump Hpb)).
      + exact Hf.
    - refine (π₁ ,, _ ,, _) ; cbn.
      + apply D_comp.
        * exact (pb_preserves_pred_ob D Hg (mirror_has_pb_ump Hpb)).
        * exact Hf.
      + exact (id2_invertible_2cell (π₁ · f)).
    - refine (π₂ ,, _ ,, _) ; cbn.
      + use (invertible_pred_mor_1 D (inv_of_invertible_2cell γ)).
        apply D_comp.
        * exact (pb_preserves_pred_ob D Hf Hpb).
        * exact Hg.
      + exact γ.
  Defined.

  Section BinProdUmp1.
    Context (q : @binprod_cone (disp_map_slice_bicat D b) ff gg).

    Let other_cone
      : pb_cone f g
      := make_pb_cone
           (pr1 (binprod_cone_obj q))
           (pr1 (binprod_cone_pr1 q))
           (pr1 (binprod_cone_pr2 q))
           (comp_of_invertible_2cell
              (inv_of_invertible_2cell
                 (pr22 (binprod_cone_pr1 q)))
              (pr22 (binprod_cone_pr2 q))).

    Let φ : invertible_2cell
              (pr121 q)
              (pb_ump_mor Hpb other_cone · (π₁ · f))
      := comp_of_invertible_2cell
           (comp_of_invertible_2cell
              (pr22 (binprod_cone_pr1 q))
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell
                    (pb_ump_mor_pr1 Hpb other_cone))))
           (rassociator_invertible_2cell _ _ _).

    Definition binprod_1_ump_in_disp_map_slice_cell_eq
      : pr22 (binprod_cone_pr1 q)
        • ((pb_ump_mor_pr1 Hpb other_cone)^-1 ▹ f)
        • rassociator _ _ _
        • ((pb_ump_mor Hpb other_cone ◃ γ)
        • lassociator _ _ _)
        • (pb_ump_mor_pr2 Hpb other_cone ▹ g)
        =
        pr122 (binprod_cone_pr2 q).
    Proof.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        exact (pb_ump_mor_cell Hpb other_cone).
      }
      cbn ;
        rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rassociator_lassociator.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rassociator_lassociator.
      rewrite id2_left.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_right.
    Qed.

    Definition binprod_1_ump_in_disp_map_slice_cell
      : binprod_1cell q binprod_cone_in_disp_map_slice.
    Proof.
      use make_binprod_1cell.
      - simple refine (_ ,, _ ,, _) ; cbn.
        + exact (pb_ump_mor Hpb other_cone).
        + use (invertible_pred_mor_1
                 _
                 (inv_of_invertible_2cell (pr22 (binprod_cone_pr1 q)))).
          apply (D_mor
                   _ _ _ _ _ _ _ _ _
                   Hpb
                   _ _ _
                   (comp_of_invertible_2cell
                      (inv_of_invertible_2cell
                         (pr22 (binprod_cone_pr1 q)))
                      (pr22 (binprod_cone_pr2 q)))
                   Hf).
          * exact (invertible_pred_mor_1
                     _
                     (pr22 (binprod_cone_pr1 q))
                     (pr12 (binprod_cone_pr1 q))).
          * exact (invertible_pred_mor_1
                     _
                     (pr22 (binprod_cone_pr1 q))
                     (pr12 (binprod_cone_pr2 q))).
        + exact φ.
      - use make_invertible_2cell.
        + simple refine (_ ,, _).
          * exact (pb_ump_mor_pr1 Hpb other_cone).
          * abstract
              (cbn ;
               rewrite lwhisker_id2, id2_left ;
               rewrite !vassocl ;
               rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker ;
               apply id2_right).
        + use is_invertible_2cell_in_disp_map_slice_bicat.
          apply property_from_invertible_2cell.
      - use make_invertible_2cell.
        + simple refine (_ ,, _).
          * exact (pb_ump_mor_pr2 Hpb other_cone).
          * apply binprod_1_ump_in_disp_map_slice_cell_eq.
        + use is_invertible_2cell_in_disp_map_slice_bicat.
          apply property_from_invertible_2cell.
    Defined.
  End BinProdUmp1.

  Definition binprod_1_ump_in_disp_map_slice
    : binprod_ump_1 binprod_cone_in_disp_map_slice
    := λ q, binprod_1_ump_in_disp_map_slice_cell q.

  Section BinProdUmp2.
    Context {h : disp_map_slice_bicat D b}
            {φ ψ : h --> binprod_cone_in_disp_map_slice}
            (α : φ · binprod_cone_pr1 binprod_cone_in_disp_map_slice
                 ==>
                 ψ · binprod_cone_pr1 binprod_cone_in_disp_map_slice)
            (β : φ · binprod_cone_pr2 binprod_cone_in_disp_map_slice
                 ==>
                 ψ · binprod_cone_pr2 binprod_cone_in_disp_map_slice).

    Definition binprod_2_ump_in_disp_map_slice_cell_unique
      : isaprop
          (∑ χ,
           χ ▹ binprod_cone_pr1 binprod_cone_in_disp_map_slice = α
           ×
           χ ▹ binprod_cone_pr2 binprod_cone_in_disp_map_slice = β).
    Proof.
      use invproofirrelevance.
      intros χ₁ χ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use eq_2cell_disp_map_slice.
      use (pb_ump_eq Hpb).
      - exact (pr1 α).
      - exact (pr1 β).
      - cbn.
        pose (r₁ := pr2 α).
        pose (r₂ := pr2 β).
        cbn in r₁, r₂.
        rewrite !lwhisker_id2, !id2_left in r₁.
        use (vcomp_lcancel (pr22 φ)).
        {
          apply property_from_invertible_2cell.
        }
        rewrite !vassocr.
        rewrite !vassocr in r₂.
        refine (maponpaths (λ z, z • _) r₂ @ _) ; clear r₂.
        refine (_ @ maponpaths (λ z, (z • _) • _) (!r₁)) ; clear r₁.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lassociator_rassociator, id2_right.
        rewrite !vassocr.
        rewrite lassociator_rassociator, id2_left.
        apply idpath.
      - exact (maponpaths pr1 (pr12 χ₁)).
      - exact (maponpaths pr1 (pr22 χ₁)).
      - exact (maponpaths pr1 (pr12 χ₂)).
      - exact (maponpaths pr1 (pr22 χ₂)).
    Qed.

    Definition binprod_2_ump_in_disp_map_slice_cell
      : φ ==> ψ.
    Proof.
      simple refine (_ ,, _).
      - use (pb_ump_cell Hpb _ _ (pr1 α) (pr1 β)) ; cbn.
        abstract
          (pose (r₁ := pr2 α) ;
           pose (r₂ := pr2 β) ;
           cbn in r₁, r₂ ;
           rewrite !lwhisker_id2, !id2_left in r₁ ;
           use (vcomp_lcancel (pr22 φ)) ; [ apply property_from_invertible_2cell | ] ;
           rewrite !vassocr ;
           rewrite !vassocr in r₂ ;
           refine (maponpaths (λ z, z • _) r₂ @ _) ; clear r₂ ;
           refine (_ @ maponpaths (λ z, (z • _) • _) (!r₁)) ; clear r₁ ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite lassociator_rassociator, id2_right ;
           rewrite !vassocr ;
           rewrite lassociator_rassociator, id2_left ;
           apply idpath).
      - abstract
          (cbn ;
           use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
           rewrite !vassocl ;
           rewrite <- rwhisker_rwhisker ;
           rewrite (pb_ump_cell_pr1 Hpb) ;
           pose (pr2 α) as r ;
           cbn in r ;
           rewrite !lwhisker_id2, !id2_left in r ;
           rewrite !vassocr ;
           exact r).
    Defined.

    Definition binprod_2_ump_in_disp_map_slice_cell_pr1
      : binprod_2_ump_in_disp_map_slice_cell ▹ _
        =
        α.
    Proof.
      unfold binprod_2_ump_in_disp_map_slice_cell.
      use eq_2cell_disp_map_slice.
      cbn.
      apply (pb_ump_cell_pr1 Hpb).
    Qed.

    Definition binprod_2_ump_in_disp_map_slice_cell_pr2
      : binprod_2_ump_in_disp_map_slice_cell ▹ _
        =
        β.
    Proof.
      unfold binprod_2_ump_in_disp_map_slice_cell.
      use eq_2cell_disp_map_slice.
      cbn.
      apply (pb_ump_cell_pr2 Hpb).
    Qed.
  End BinProdUmp2.

  Definition binprod_2_ump_in_disp_map_slice
    : binprod_ump_2 binprod_cone_in_disp_map_slice.
  Proof.
    intros h φ ψ α β.
    use iscontraprop1.
    - exact (binprod_2_ump_in_disp_map_slice_cell_unique α β).
    - refine (binprod_2_ump_in_disp_map_slice_cell α β ,, _ ,, _).
      + exact (binprod_2_ump_in_disp_map_slice_cell_pr1 α β).
      + exact (binprod_2_ump_in_disp_map_slice_cell_pr2 α β).
  Defined.

  Definition binprod_ump_in_disp_map_slice
    : has_binprod_ump binprod_cone_in_disp_map_slice.
  Proof.
    split.
    - exact binprod_1_ump_in_disp_map_slice.
    - exact binprod_2_ump_in_disp_map_slice.
  Defined.
End DisplayMapBicatProduct.

Definition disp_map_slice_binprod
           {B : bicat}
           (D : disp_map_bicat B)
           (D_comp : arrow_subbicat_closed_composition D)
           (D_mor : arrow_subbicat_closed_prod_mor D)
           (pb_B : has_pb B)
           (b : B)
  : has_binprod (disp_map_slice_bicat D b).
Proof.
  intros f₁ f₂.
  refine (_ ,, _).
  exact (binprod_ump_in_disp_map_slice
           _
           D_comp
           D_mor
           _ _ _ _ _
           (pr2 (pb_B _ _ _ (pr12 f₁) (pr12 f₂)))).
Defined.
