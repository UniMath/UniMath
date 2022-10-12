(*********************************************************************************

 Limits in slice bicategory

 Contents:
 1. Final object
 2. Products
 3. Inserters
 4. Equifiers

 *********************************************************************************)
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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

(**
 1. Final object
 *)
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

  Definition bifinal_2cell_property_slice_eq
             {f : slice_bicat b}
             (α β : f --> ι)
    : pr12 α
      • ((((rinvunitor (pr1 α) • (pr22 α) ^-1) • pr12 β) • runitor (pr1 β)) ▹ id₁ b)
      =
      pr12 β.
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
      rewrite !vassocl ;
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
    - exact (bifinal_2cell_property_slice_eq α β).
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

(**
 2. Products
 *)
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

    Definition binprod_1_ump_in_slice_cell_eq
      : pr12 (binprod_cone_pr1 q)
        • ((pb_ump_mor_pr1 Hpb other_cone)^-1 ▹ f)
        • rassociator _ _ _
        • ((pb_ump_mor Hpb other_cone ◃ γ)
        • lassociator _ _ _)
        • (pb_ump_mor_pr2 Hpb other_cone ▹ g)
        =
        pr12 (binprod_cone_pr2 q).
    Proof.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        exact (pb_ump_mor_cell Hpb other_cone).
      }
      cbn.
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
        + use is_invertible_2cell_in_slice_bicat.
          apply property_from_invertible_2cell.
      - use make_invertible_2cell.
        + simple refine (_ ,, _).
          * exact (pb_ump_mor_pr2 Hpb other_cone).
          * exact binprod_1_ump_in_slice_cell_eq.
        + use is_invertible_2cell_in_slice_bicat.
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

(**
 3. Inserters

 We construct inserters in the slice bicategory by using both inserters
 and equifiers in the base. We need to take an equifier to guarantee
 that the obtained 2-cell, satisfies a coherency.
 *)
Section InsertersSlice.
  Context {B : bicat}
          (ins_B : has_inserters B)
          (eq_B : has_equifiers B)
          {b : B}
          {h₁ h₂ : slice_bicat b}
          (α β : h₁ --> h₂).

  Let I : B
    := pr1 (ins_B (pr1 h₁) (pr1 h₂) (pr1 α) (pr1 β)).
  Let p : I --> pr1 h₁
    := pr12 (ins_B (pr1 h₁) (pr1 h₂) (pr1 α) (pr1 β)).
  Let γ : p · pr1 α ==> p · pr1 β
    := pr122 (ins_B (pr1 h₁) (pr1 h₂) (pr1 α) (pr1 β)).
  Let I_cone : inserter_cone (pr1 α) (pr1 β)
    := make_inserter_cone I p γ.
  Let HI : has_inserter_ump I_cone
    := pr222 (ins_B (pr1 h₁) (pr1 h₂) (pr1 α) (pr1 β)).

  Let E : B
    := pr1 (eq_B
              I _
              (p · pr2 h₁) (p · pr1 β · pr2 h₂)
              (((p ◃ pr12 α) • lassociator p (pr1 α) (pr2 h₂)) • (γ ▹ pr2 h₂))
              ((p ◃ pr12 β) • lassociator p (pr1 β) (pr2 h₂))).
  Let p' : E --> I
    := pr12 (eq_B
               I _
               (p · pr2 h₁) (p · pr1 β · pr2 h₂)
               (((p ◃ pr12 α) • lassociator p (pr1 α) (pr2 h₂)) • (γ ▹ pr2 h₂))
               ((p ◃ pr12 β) • lassociator p (pr1 β) (pr2 h₂))).
  Let path : p' ◃ _ = p' ◃ _
    := pr122 (eq_B
                I _
                (p · pr2 h₁) (p · pr1 β · pr2 h₂)
                (((p ◃ pr12 α) • lassociator p (pr1 α) (pr2 h₂)) • (γ ▹ pr2 h₂))
                ((p ◃ pr12 β) • lassociator p (pr1 β) (pr2 h₂))).
  Let E_cone : equifier_cone _ _ _ _
    := make_equifier_cone E p' path.
  Let HE : has_equifier_ump E_cone
    := pr222 (eq_B
                I _
                (p · pr2 h₁) (p · pr1 β · pr2 h₂)
                (((p ◃ pr12 α) • lassociator p (pr1 α) (pr2 h₂)) • (γ ▹ pr2 h₂))
                ((p ◃ pr12 β) • lassociator p (pr1 β) (pr2 h₂))).

  Definition inserter_slice
    : slice_bicat b.
  Proof.
    use make_ob_slice.
    - exact E.
    - exact (p' · p · pr2 h₁).
  Defined.

  Definition inserter_slice_pr1
    : inserter_slice --> h₁.
  Proof.
    use make_1cell_slice.
    - exact (p'· p).
    - apply id2_invertible_2cell.
  Defined.

  Definition inserter_slice_cell_cell
    : p' · p · pr1 α ==> p' · p · pr1 β
    := rassociator _ _ _ • (p' ◃ γ) • lassociator _ _ _.

  Definition inserter_slice_cell_homot
    : cell_slice_homot
        (inserter_slice_pr1 · α)
        (inserter_slice_pr1 · β)
        inserter_slice_cell_cell.
  Proof.
    unfold cell_slice_homot, inserter_slice_cell_cell ; cbn.
    rewrite !id2_left.
    rewrite <- !rwhisker_vcomp.
    use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocr.
    rewrite <- !lwhisker_lwhisker.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite !lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      rewrite !vassocr.
      apply path.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    apply lassociator_lassociator.
  Qed.

  Definition inserter_slice_cell
    : inserter_slice_pr1 · α ==> inserter_slice_pr1 · β.
  Proof.
    use make_2cell_slice.
    - exact inserter_slice_cell_cell.
    - exact inserter_slice_cell_homot.
  Defined.

  Let cone : inserter_cone α β
    := make_inserter_cone
         inserter_slice
         inserter_slice_pr1
         inserter_slice_cell.

  Section InserterSliceUMP1.
    Context (q : inserter_cone α β).

    Definition inserter_ump_1_slice_mor_to_ins
      : pr11 q --> I.
    Proof.
      use (inserter_ump_mor HI).
      - exact (pr1 (inserter_cone_pr1 q)).
      - exact (pr1 (inserter_cone_cell q)).
    Defined.

    Definition inserter_ump_1_slice_mor_path
      : inserter_ump_1_slice_mor_to_ins ◃ (((p ◃ pr12 α) • lassociator _ _ _) • (γ ▹ pr2 h₂))
        =
        inserter_ump_1_slice_mor_to_ins ◃ ((p ◃ pr12 β) • lassociator _ _ _).
    Proof.
      rewrite <- !lwhisker_vcomp.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite !lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      use (vcomp_lcancel ((inserter_ump_mor_pr1 HI _ _)^-1 ▹ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite !vcomp_whisker.
      rewrite !vassocl.
      use (vcomp_lcancel (pr12 (inserter_cone_pr1 q))).
      {
        apply property_from_invertible_2cell.
      }
      pose (pr2 (inserter_cone_cell q)) as m.
      cbn in m.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_hcomp.
          rewrite inverse_pentagon_4.
          rewrite <- rwhisker_hcomp.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite lwhisker_hcomp.
          rewrite inverse_pentagon_4.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      etrans.
      {
        do 3 apply maponpaths_2.
        rewrite !vassocl.
        exact (!m).
      }
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      use vcomp_move_R_Mp ; [ is_iso | ].
      use vcomp_move_R_Mp ; [ is_iso | ].
      cbn.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        apply (inserter_ump_mor_cell HI).
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_left.
    Qed.

    Definition inserter_ump_1_slice_mor_to_eq
      : pr11 q --> E.
    Proof.
      use (equifier_ump_mor HE).
      - exact inserter_ump_1_slice_mor_to_ins.
      - exact inserter_ump_1_slice_mor_path.
    Defined.

    Definition inserter_ump_1_slice_mor_inv2cell
      : invertible_2cell
          (pr21 q)
          (inserter_ump_1_slice_mor_to_eq · (p' · p · pr2 h₁)).
    Proof.
      use make_invertible_2cell.
      - exact (pr12 (inserter_cone_pr1 q)
               • ((inserter_ump_mor_pr1 HI _ _)^-1 ▹ _)
               • ((equifier_ump_mor_pr1 HE _ _)^-1 ▹ _ ▹ _)
               • (rassociator _ _ _ ▹ _)
               • rassociator _ _ _).
      - is_iso.
        apply property_from_invertible_2cell.
    Defined.

    Definition inserter_ump_1_slice_mor
      : q --> cone.
    Proof.
      use make_1cell_slice.
      - exact inserter_ump_1_slice_mor_to_eq.
      - exact inserter_ump_1_slice_mor_inv2cell.
    Defined.

    Definition inserter_ump_1_slice_pr1_cell_cell
      : inserter_ump_1_slice_mor_to_eq · (p' · p)
        ==>
        pr1 (inserter_cone_pr1 q)
      := lassociator _ _ _
         • (equifier_ump_mor_pr1 HE _ _ ▹ _)
         • inserter_ump_mor_pr1 HI _ _.

    Definition inserter_ump_1_slice_pr1_cell_homot
      : cell_slice_homot
          (inserter_ump_1_slice_mor · inserter_slice_pr1)
          (inserter_cone_pr1 q)
          inserter_ump_1_slice_pr1_cell_cell.
    Proof.
      unfold cell_slice_homot, inserter_ump_1_slice_pr1_cell_cell ; cbn.
      rewrite !vassocl.
      refine (_ @ id2_right _).
      apply maponpaths.
      rewrite lwhisker_id2.
      rewrite id2_left.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      apply vcomp_linv.
    Qed.

    Definition inserter_ump_1_slice_pr1_cell
      : inserter_ump_1_slice_mor · inserter_slice_pr1
        ==>
        inserter_cone_pr1 q.
    Proof.
      use make_2cell_slice.
      - exact inserter_ump_1_slice_pr1_cell_cell.
      - exact inserter_ump_1_slice_pr1_cell_homot.
    Defined.

    Definition inserter_ump_1_slice_pr1
      : invertible_2cell
          (inserter_ump_1_slice_mor · inserter_slice_pr1)
          (inserter_cone_pr1 q).
    Proof.
      use make_invertible_2cell.
      - exact inserter_ump_1_slice_pr1_cell.
      - use is_invertible_2cell_in_slice_bicat ; cbn.
        unfold inserter_ump_1_slice_pr1_cell_cell.
        is_iso ; apply property_from_invertible_2cell.
    Defined.

    Definition inserter_ump_1_slice_cell
      : (_ ◃ inserter_cone_cell cone)
        • lassociator _ _ _
        • (inserter_ump_1_slice_pr1 ▹ β)
        =
        lassociator _ _ _
        • (inserter_ump_1_slice_pr1 ▹ α)
        • inserter_cone_cell q.
    Proof.
      use eq_2cell_slice.
      cbn ; unfold inserter_ump_1_slice_pr1_cell_cell, inserter_slice_cell_cell ; cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite lassociator_lassociator.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      do 2 refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        apply (inserter_ump_mor_cell HI).
      }
      rewrite !vassocl.
      apply idpath.
    Qed.
  End InserterSliceUMP1.

  Definition inserter_ump_1_slice
    : has_inserter_ump_1 cone.
  Proof.
    intro q.
    use make_inserter_1cell.
    - exact (inserter_ump_1_slice_mor q).
    - exact (inserter_ump_1_slice_pr1 q).
    - exact (inserter_ump_1_slice_cell q).
  Defined.

  Local Lemma inserter_ump_path_help
        {h : slice_bicat b}
        {u₁ u₂ : h --> cone}
        (ζ : u₁ · inserter_cone_pr1 cone ==> u₂ · inserter_cone_pr1 cone)
        (r : rassociator _ _ _
             • (u₁ ◃ inserter_cone_cell cone)
             • lassociator _ _ _
             • (ζ ▹ β)
             =
             (ζ ▹ α)
             • rassociator _ _ _
             • (u₂ ◃ inserter_cone_cell cone)
             • lassociator _ _ _)
    : rassociator _ _ _
      • (_ ◃ inserter_cone_cell I_cone)
      • lassociator _ _ _
      • ((rassociator _ _ _ • pr1 ζ • lassociator _ _ _) ▹ pr1 β)
      =
      (rassociator _ _ _ • pr1 ζ • lassociator _ _ _ ▹ pr1 α)
      • rassociator _ _ _
      • (_ ◃ inserter_cone_cell I_cone)
      • lassociator _ _ _.
  Proof.
    cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    pose (r' := maponpaths pr1 r).
    cbn in r'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite rwhisker_hcomp.
      rewrite !vassocr.
      rewrite inverse_pentagon_2.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- lassociator_lassociator.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      exact (!r').
    }
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite inverse_pentagon_6.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    rewrite !vassocr.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    unfold inserter_slice_cell_cell.
    rewrite !vassocr.
    rewrite lassociator_rassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Section InserterUMP2Slice.
    Context {h : slice_bicat b}
            {u₁ u₂ : h --> cone}
            (ζ : u₁ · inserter_cone_pr1 cone ==> u₂ · inserter_cone_pr1 cone)
            (r : rassociator _ _ _
                 • (u₁ ◃ inserter_cone_cell cone)
                 • lassociator _ _ _
                 • (ζ ▹ β)
                 =
                 (ζ ▹ α)
                 • rassociator _ _ _
                 • (u₂ ◃ inserter_cone_cell cone)
                 • lassociator _ _ _).

    Definition inserter_ump_2_slice_cell_cell
      : pr1 u₁ ==> pr1 u₂.
    Proof.
      use (equifier_ump_cell HE).
      use (inserter_ump_cell HI).
      - exact (rassociator _ _ _ • pr1 ζ • lassociator _ _ _).
      - exact (inserter_ump_path_help ζ r).
    Defined.

    Definition inserter_ump_2_slice_cell_homot
      : cell_slice_homot
          u₁ u₂
          inserter_ump_2_slice_cell_cell.
    Proof.
      unfold cell_slice_homot, inserter_ump_2_slice_cell_cell ; cbn.
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker.
      use (vcomp_rcancel (lassociator _ _ _ ▹ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite <- rwhisker_rwhisker.
      rewrite (equifier_ump_cell_pr1 HE).
      rewrite (inserter_ump_cell_pr1 HI).
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      pose (pr2 ζ) as q.
      cbn in q.
      rewrite !lwhisker_id2, !id2_left in q.
      exact q.
    Qed.

    Definition inserter_ump_2_slice_cell
      : u₁ ==> u₂.
    Proof.
      use make_2cell_slice.
      - exact inserter_ump_2_slice_cell_cell.
      - exact inserter_ump_2_slice_cell_homot.
    Defined.

    Definition inserter_ump_2_slice_pr1
      : inserter_ump_2_slice_cell ▹ inserter_slice_pr1 = ζ.
    Proof.
      use eq_2cell_slice ; cbn.
      unfold inserter_ump_2_slice_cell_cell.
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- rwhisker_rwhisker.
      rewrite (equifier_ump_cell_pr1 HE).
      rewrite (inserter_ump_cell_pr1 HI).
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    Qed.
  End InserterUMP2Slice.

  Definition inserter_ump_2_slice
    : has_inserter_ump_2 cone.
  Proof.
    intros h u₁ u₂ ζ r.
    simple refine (_ ,, _).
    - exact (inserter_ump_2_slice_cell ζ r).
    - exact (inserter_ump_2_slice_pr1 ζ r).
  Defined.

  Definition inserter_ump_eq_slice
    : has_inserter_ump_eq cone.
  Proof.
    intros h u₁ u₂ ζ r φ₁ φ₂ s₁ s₂.
    use eq_2cell_slice.
    use (equifier_ump_eq HE).
    - use (inserter_ump_cell HI).
      + exact (rassociator _ _ _ • pr1 ζ • lassociator _ _ _).
      + exact (inserter_ump_path_help ζ r).
    - use (inserter_ump_eq HI).
      + exact (rassociator _ _ _ • pr1 ζ • lassociator _ _ _).
      + exact (inserter_ump_path_help ζ r).
      + rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite rwhisker_rwhisker.
        apply maponpaths_2.
        exact (maponpaths pr1 s₁).
      + apply (inserter_ump_cell_pr1 HI).
    - use (inserter_ump_eq HI).
      + exact (rassociator _ _ _ • pr1 ζ • lassociator _ _ _).
      + exact (inserter_ump_path_help ζ r).
      + rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite rwhisker_rwhisker.
        apply maponpaths_2.
        exact (maponpaths pr1 s₂).
      + apply (inserter_ump_cell_pr1 HI).
  Qed.

  Definition inserter_ump_slice
    : has_inserter_ump cone
    := inserter_ump_1_slice ,, inserter_ump_2_slice ,, inserter_ump_eq_slice.
End InsertersSlice.

Definition inserters_in_slice_bicat
           {B : bicat}
           (ins_B : has_inserters B)
           (eq_B : has_equifiers B)
           (b : B)
  : has_inserters (slice_bicat b).
Proof.
  intros h₁ h₂ α β.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (inserter_slice ins_B eq_B α β).
  - exact (inserter_slice_pr1 ins_B eq_B α β).
  - exact (inserter_slice_cell ins_B eq_B α β).
  - exact (inserter_ump_slice ins_B eq_B α β).
Defined.

(**
 4. Equifiers
 *)
Section EquifierSlice.
  Context {B : bicat}
          (b : B)
          {eq h₁ h₂ : slice_bicat b}
          {f₁ f₂ : h₁ --> h₂}
          (α β : f₁ ==> f₂)
          (e : eq --> h₁)
          (p : e ◃ α = e ◃ β)
          (cone := make_equifier_cone (pr1 eq) (pr1 e) (maponpaths pr1 p))
          (H : has_equifier_ump cone).

  Section EquifierUMP1.
    Context (q : equifier_cone f₁ f₂ α β).

    Definition equifier_ump_1_slice_mor_mor
      : pr11 q --> pr1 eq
      := equifier_ump_mor
           H
           (pr1 (equifier_cone_pr1 q))
           (maponpaths pr1 (equifier_cone_eq q)).

    Definition equifier_ump_1_slice_mor_inv2cell
      : invertible_2cell
          (pr21 q)
          (equifier_ump_1_slice_mor_mor · pr2 eq)
      := comp_of_invertible_2cell
           (pr2 (equifier_cone_pr1 q))
           (inv_of_invertible_2cell
              (comp_of_invertible_2cell
                 (lwhisker_of_invertible_2cell _ (pr2 e))
                 (comp_of_invertible_2cell
                    (lassociator_invertible_2cell _ _ _)
                    (rwhisker_of_invertible_2cell
                       _
                       (equifier_ump_mor_pr1 H _ _))))).

    Definition equifier_ump_1_slice_mor
      : q --> eq.
    Proof.
      use make_1cell_slice.
      - exact equifier_ump_1_slice_mor_mor.
      - exact equifier_ump_1_slice_mor_inv2cell.
    Defined.

    Definition equifier_ump_1_slice_pr1_cell_cell
      : equifier_ump_1_slice_mor_mor · pr1 e ==> pr1 (equifier_cone_pr1 q)
      := equifier_ump_mor_pr1 H _ _.

    Definition equifier_ump_1_slice_pr1_cell_homot
      : cell_slice_homot
          (equifier_ump_1_slice_mor · e)
          (equifier_cone_pr1 q)
          equifier_ump_1_slice_pr1_cell_cell.
    Proof.
      unfold cell_slice_homot ; cbn.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_right.
    Qed.

    Definition equifier_ump_1_slice_pr1_cell
      : equifier_ump_1_slice_mor · e ==> equifier_cone_pr1 q.
    Proof.
      use make_2cell_slice.
      - exact equifier_ump_1_slice_pr1_cell_cell.
      - exact equifier_ump_1_slice_pr1_cell_homot.
    Defined.

    Definition equifier_ump_1_slice_pr1
      : invertible_2cell
          (equifier_ump_1_slice_mor · e)
          (equifier_cone_pr1 q).
    Proof.
      use make_invertible_2cell.
      - exact equifier_ump_1_slice_pr1_cell.
      - use is_invertible_2cell_in_slice_bicat.
        apply property_from_invertible_2cell.
    Defined.
  End EquifierUMP1.

  Definition equifier_ump_1_in_slice
    : has_equifier_ump_1 (make_equifier_cone eq e p).
  Proof.
    intro q.
    use make_equifier_1cell.
    - exact (equifier_ump_1_slice_mor q).
    - exact (equifier_ump_1_slice_pr1 q).
  Defined.

  Section EquifierUMP2.
    Context {g : slice_bicat b}
            (u₁ u₂ : g --> eq)
            (γ : u₁ · e ==> u₂ · e).

    Definition equifier_ump_2_in_slice_cell_cell
      : pr1 u₁ ==> pr1 u₂
      := equifier_ump_cell H (pr1 γ).

    Definition equifier_ump_2_in_slice_cell_path
      : cell_slice_homot
          u₁ u₂
          equifier_ump_2_in_slice_cell_cell.
    Proof.
      unfold cell_slice_homot.
      unfold equifier_ump_2_in_slice_cell_cell.
      use (vcomp_rcancel ((_ ◃ pr12 e) • lassociator _ _ _)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      refine (_ @ pr2 γ) ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_rwhisker.
      do 2 apply maponpaths.
      apply (equifier_ump_cell_pr1 H).
    Qed.

    Definition equifier_ump_2_in_slice_cell
      : u₁ ==> u₂.
    Proof.
      use make_2cell_slice.
      - exact equifier_ump_2_in_slice_cell_cell.
      - exact equifier_ump_2_in_slice_cell_path.
    Defined.

    Definition equifier_ump_2_in_slice_pr1
      : equifier_ump_2_in_slice_cell ▹ e = γ.
    Proof.
      use eq_2cell_slice ; cbn.
      apply (equifier_ump_cell_pr1 H).
    Qed.
  End EquifierUMP2.

  Definition equifier_ump_2_in_slice
    : has_equifier_ump_2 (make_equifier_cone eq e p)
    := λ g u₁ u₂ γ,
       equifier_ump_2_in_slice_cell u₁ u₂ γ
       ,,
       equifier_ump_2_in_slice_pr1 u₁ u₂ γ.

  Definition equifier_ump_eq_in_slice
    : has_equifier_ump_eq (make_equifier_cone eq e p).
  Proof.
    intros g u₁ u₂ γ φ₁ φ₂ q₁ q₂.
    use eq_2cell_slice.
    use (equifier_ump_eq H).
    - exact (pr1 γ).
    - exact (maponpaths pr1 q₁).
    - exact (maponpaths pr1 q₂).
  Qed.

  Definition equifier_ump_in_slice
    : has_equifier_ump (make_equifier_cone eq e p)
    := equifier_ump_1_in_slice
       ,,
       equifier_ump_2_in_slice
       ,,
       equifier_ump_eq_in_slice.
End EquifierSlice.

Definition equifiers_in_slice_bicat
           {B : bicat}
           (ins_B : has_equifiers B)
           (b : B)
  : has_equifiers (slice_bicat b).
Proof.
  intros h₁ h₂ f₁ f₂ α β.
  pose (e := ins_B (pr1 h₁) (pr1 h₂) (pr1 f₁) (pr1 f₂) (pr1 α) (pr1 β)).
  simple refine (make_ob_slice (pr12 e · pr2 h₁)
                 ,,
                 make_1cell_slice _ _
                 ,,
                 _
                 ,,
                 _).
  - exact (pr12 e).
  - apply id2_invertible_2cell.
  - abstract
      (use eq_2cell_slice ; cbn ;
       exact (pr122 e)).
  - apply equifier_ump_in_slice.
    exact (pr222 e).
Defined.
