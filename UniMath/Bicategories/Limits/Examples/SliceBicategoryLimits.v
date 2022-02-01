(*********************************************************************************

 Limits in slice bicategory

 Contents:
 1. Final object
 2. Products

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

Section FinalSlice.
  Context {B : bicat}
          (b : B).

  Let ι : slice_bicat b.
  Proof.
    refine (b ,, _).
    exact (id₁ b).
  Defined.

  Definition bifinal_1cell_property_slice
    : bifinal_1cell_property ι.
  Proof.
    intros f.
    exact (pr2 f ,, rinvunitor_invertible_2cell _).
  Defined.

  Definition bifinal_2cell_property_slice
             (f : slice_bicat b)
    : bifinal_2cell_property ι f.
  Proof.
    intros α β.
    simple refine (_ ,, _).
    - exact (rinvunitor _
             • (pr22 α)^-1
             • pr12 β
             • runitor _).
    - abstract
        (cbn ;
         use vcomp_move_R_pM ; [ apply property_from_invertible_2cell | ] ;
         use (vcomp_lcancel (runitor _)) ; [ is_iso | ] ;
         refine (_ @ vcomp_runitor _ _ _) ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocr ;
         etrans ;
         [ do 3 apply maponpaths_2 ;
           rewrite <- runitor_triangle ;
           rewrite rwhisker_hcomp ;
           rewrite <- triangle_l_inv ;
           rewrite <- lwhisker_hcomp ;
           rewrite runitor_lunitor_identity ;
           rewrite !vassocl ;
           refine (maponpaths (λ z, _ • z) (vassocr _ _ _) @ _) ;
           rewrite lwhisker_vcomp ;
           rewrite lunitor_linvunitor ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           rewrite rassociator_lassociator ;
           apply idpath
         | ] ;
         rewrite id2_left ;
         rewrite !vassocl ;
         do 2 apply maponpaths ;
         rewrite <- runitor_triangle ;
         use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
         rewrite runitor_rwhisker ;
         rewrite runitor_lunitor_identity ;
         apply idpath).
  Defined.

  Definition bifinal_eq_property_slice
             (f : slice_bicat b)
    : bifinal_eq_property ι f.
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
    apply (vcomp_lcancel (pr12 α) (pr22 α)).
    exact (pr2 p @ !(pr2 q)).
  Qed.

  Definition is_bifinal_slice
    : is_bifinal ι.
  Proof.
    refine (_ ,, _).
    - exact bifinal_1cell_property_slice.
    - intro f.
      split.
      + exact (bifinal_2cell_property_slice f).
      + exact (bifinal_eq_property_slice f).
  Defined.

  Definition final_in_slice
    : bifinal_obj (slice_bicat b)
    := ι ,, is_bifinal_slice.
End FinalSlice.

Section ProductSlice.
  Context {B : bicat}
          {pb x y b : B}
          (f : x --> b)
          (g : y --> b)
          (π₁ : pb --> x)
          (π₂ : pb --> y)
          (γ : invertible_2cell (π₁ · f) (π₂ · g))
          (cone : pb_cone f g := make_pb_cone _ π₁ π₂ γ)
          (Hpb : has_pb_ump cone).

  Definition binprod_cone_in_slice
    : @binprod_cone (slice_bicat b) (x ,, f) (y ,, g).
  Proof.
    use make_binprod_cone.
    - exact (pb ,, π₁ · f).
    - exact (π₁ ,, id2_invertible_2cell (π₁ · f)).
    - exact (π₂ ,, γ).
  Defined.

  Section BinProdUmp1.
    Context (q : @binprod_cone (slice_bicat b) (x,, f) (y,, g)).

    Let other_cone
      : pb_cone f g
      := make_pb_cone
           (pr1 (binprod_cone_obj q))
           (pr1 (binprod_cone_pr1 q))
           (pr1 (binprod_cone_pr2 q))
           (comp_of_invertible_2cell
              (inv_of_invertible_2cell
                 (pr2 (binprod_cone_pr1 q)))
              (pr2 (binprod_cone_pr2 q))).

    Let φ : invertible_2cell
              (pr21 q)
              (pb_ump_mor Hpb other_cone · (π₁ · f))
      := comp_of_invertible_2cell
           (comp_of_invertible_2cell
              (pr2 (binprod_cone_pr1 q))
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell
                    (pb_ump_mor_pr1 Hpb other_cone))))
           (rassociator_invertible_2cell _ _ _).

    Definition binprod_1_ump_in_slice_cell
      : binprod_1cell q binprod_cone_in_slice.
    Proof.
      use make_binprod_1cell.
      - simple refine (_ ,, _).
        + exact (pb_ump_mor Hpb other_cone).
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
        + use invertible_2cell_in_slice_bicat.
          apply property_from_invertible_2cell.
      - use make_invertible_2cell.
        + simple refine (_ ,, _).
          * exact (pb_ump_mor_pr2 Hpb other_cone).
          * abstract
              (cbn ;
               rewrite !vassocl ;
               etrans ;
               [ do 3 apply maponpaths ;
                 apply maponpaths_2 ;
                 exact (pb_ump_mor_cell Hpb other_cone)
               | ] ;
               cbn ;
               rewrite !vassocl ;
               rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               rewrite !vassocl ;
               rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker ;
               rewrite id2_left ;
               rewrite !vassocr ;
               rewrite vcomp_rinv ;
               rewrite id2_left ;
               rewrite !vassocl ;
               rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker ;
               apply id2_right).
        + use invertible_2cell_in_slice_bicat.
          apply property_from_invertible_2cell.
    Defined.
  End BinProdUmp1.

  Definition binprod_1_ump_in_slice
    : binprod_ump_1 binprod_cone_in_slice
    := λ q, binprod_1_ump_in_slice_cell q.

  Section BinProdUmp2.
    Context {h : slice_bicat b}
            {φ ψ : h --> binprod_cone_in_slice}
            (α : φ · binprod_cone_pr1 binprod_cone_in_slice
                 ==>
                 ψ · binprod_cone_pr1 binprod_cone_in_slice)
            (β : φ · binprod_cone_pr2 binprod_cone_in_slice
                 ==>
                 ψ · binprod_cone_pr2 binprod_cone_in_slice).

    Definition binprod_2_ump_in_slice_cell_unique
      : isaprop
          (∑ χ,
           χ ▹ binprod_cone_pr1 binprod_cone_in_slice = α
           ×
           χ ▹ binprod_cone_pr2 binprod_cone_in_slice = β).
    Proof.
      use invproofirrelevance.
      intros χ₁ χ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use eq_2cell_slice.
      use (pb_ump_eq Hpb).
      - exact (pr1 α).
      - exact (pr1 β).
      - cbn.
        pose (r₁ := pr2 α).
        pose (r₂ := pr2 β).
        cbn in r₁, r₂.
        rewrite !lwhisker_id2, !id2_left in r₁.
        use (vcomp_lcancel (pr12 φ)).
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

    Definition binprod_2_ump_in_slice_cell
      : φ ==> ψ.
    Proof.
      simple refine (_ ,, _).
      - use (pb_ump_cell Hpb _ _ (pr1 α) (pr1 β)) ; cbn.
        abstract
          (pose (r₁ := pr2 α) ;
           pose (r₂ := pr2 β) ;
           cbn in r₁, r₂ ;
           rewrite !lwhisker_id2, !id2_left in r₁ ;
           use (vcomp_lcancel (pr12 φ)) ; [ apply property_from_invertible_2cell | ] ;
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

    Definition binprod_2_ump_in_slice_cell_pr1
      : binprod_2_ump_in_slice_cell ▹ binprod_cone_pr1 binprod_cone_in_slice
        =
        α.
    Proof.
      unfold binprod_2_ump_in_slice_cell.
      use eq_2cell_slice.
      cbn.
      apply (pb_ump_cell_pr1 Hpb).
    Qed.

    Definition binprod_2_ump_in_slice_cell_pr2
      : binprod_2_ump_in_slice_cell ▹ binprod_cone_pr2 binprod_cone_in_slice
        =
        β.
    Proof.
      unfold binprod_2_ump_in_slice_cell.
      use eq_2cell_slice.
      cbn.
      apply (pb_ump_cell_pr2 Hpb).
    Qed.
  End BinProdUmp2.

  Definition binprod_2_ump_in_slice
    : binprod_ump_2 binprod_cone_in_slice.
  Proof.
    intros h φ ψ α β.
    use iscontraprop1.
    - exact (binprod_2_ump_in_slice_cell_unique α β).
    - refine (binprod_2_ump_in_slice_cell α β ,, _ ,, _).
      + exact (binprod_2_ump_in_slice_cell_pr1 α β).
      + exact (binprod_2_ump_in_slice_cell_pr2 α β).
  Defined.

  Definition binprod_ump_in_slice
    : has_binprod_ump binprod_cone_in_slice.
  Proof.
    split.
    - exact binprod_1_ump_in_slice.
    - exact binprod_2_ump_in_slice.
  Defined.
End ProductSlice.

Definition products_in_slice_bicat
           {B : bicat}
           (pb_B : has_pb B)
           (b : B)
  : has_binprod (slice_bicat b).
Proof.
  intros f₁ f₂.
  exact (_ ,, binprod_ump_in_slice _ _ _ _ _ (pr2 (pb_B _ _ _ (pr2 f₁) (pr2 f₂)))).
Defined.
