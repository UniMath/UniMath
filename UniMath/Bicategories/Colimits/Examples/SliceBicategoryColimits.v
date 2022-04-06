(*********************************************************************************

 Colimits in slice bicategory

 Contents:
 1. Initial object
 2. Coproducts

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
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
 1. Initial object
 *)
Section InitialSlice.
  Context {B : bicat}
          (I : biinitial_obj B)
          (b : B).

  Let κ : slice_bicat b
    := pr1 I ,, is_biinitial_1cell_property (pr2 I) b.

  Definition biinitial_1cell_property_slice
    : biinitial_1cell_property κ.
  Proof.
    intros f.
    refine (is_biinitial_1cell_property (pr2 I) _ ,, _) ; cbn.
    apply (is_biinitial_invertible_2cell_property (pr2 I)).
  Defined.

  Definition biinitial_2cell_property_slice
             (f : slice_bicat b)
    : biinitial_2cell_property κ f.
  Proof.
    intros g₁ g₂.
    simple refine (_ ,, _).
    - apply (is_biinitial_2cell_property (pr2 I)).
    - apply (is_biinitial_eq_property (pr2 I)).
  Defined.

  Definition biinitial_eq_property_slice
             (f : slice_bicat b)
    : biinitial_eq_property κ f.
  Proof.
    intros g₁ g₂ α β.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    apply (is_biinitial_eq_property (pr2 I)).
  Qed.

  Definition is_biinitial_slice
    : is_biinitial κ.
  Proof.
    refine (_ ,, _).
    - exact biinitial_1cell_property_slice.
    - intro f.
      split.
      + exact (biinitial_2cell_property_slice f).
      + exact (biinitial_eq_property_slice f).
  Defined.

  Definition biinitial_in_slice
    : biinitial_obj (slice_bicat b)
    := κ ,, is_biinitial_slice.
End InitialSlice.

(**
 2. Coproducts
 *)
Section CoproductSlice.
  Context {B : bicat}
          (HB : has_bincoprod B)
          (b : B)
          {x₁ x₂ : B}
          (h₁ : x₁ --> b)
          (h₂ : x₂ --> b).

  Let sum_cone : bincoprod_cocone x₁ x₂
    := pr1 (HB x₁ x₂).
  Let sum : B
    := sum_cone.
  Let ι₁ : x₁ --> sum
    := bincoprod_cocone_inl sum_cone.
  Let ι₂ : x₂ --> sum
    := bincoprod_cocone_inr sum_cone.
  Let ump : has_bincoprod_ump sum_cone
    := pr2 (HB x₁ x₂).

  Let hh₁ : slice_bicat b := x₁ ,, h₁.
  Let hh₂ : slice_bicat b := x₂ ,, h₂.

  Let sum_slice : slice_bicat b
    := sum ,, bincoprod_ump_1cell ump h₁ h₂.
  Let inl_slice : hh₁ --> sum_slice
    := ι₁ ,, inv_of_invertible_2cell (bincoprod_ump_1cell_inl ump _ h₁ h₂).
  Let inr_slice : hh₂ --> sum_slice
    := ι₂ ,, inv_of_invertible_2cell (bincoprod_ump_1cell_inr ump _ h₁ h₂).

  Definition slice_coprod_cone
    : bincoprod_cocone hh₁ hh₂.
  Proof.
    use make_bincoprod_cocone.
    - exact sum_slice.
    - exact inl_slice.
    - exact inr_slice.
  Defined.

  Section UMP1.
    Context (q : bincoprod_cocone hh₁ hh₂).

    Definition slice_coprod_ump_1_map_mor
      : sum --> pr11 q.
    Proof.
      use (bincoprod_ump_1cell ump).
      - exact (pr1 (bincoprod_cocone_inl q)).
      - exact (pr1 (bincoprod_cocone_inr q)).
    Defined.

    Definition slice_coprod_ump_1_map_inv2cell
      : invertible_2cell
          (bincoprod_ump_1cell ump h₁ h₂)
          (slice_coprod_ump_1_map_mor · pr21 q).
    Proof.
      use make_invertible_2cell.
      - use (bincoprod_ump_2cell ump).
        + exact (bincoprod_ump_1cell_inl _ _ _ _
                 • pr1 (pr2 (bincoprod_cocone_inl q))
                 • ((bincoprod_ump_1cell_inl _ _ _ _)^-1 ▹ _)
                 • rassociator _ _ _).
        + exact (bincoprod_ump_1cell_inr _ _ _ _
                 • pr1 (pr2 (bincoprod_cocone_inr q))
                 • ((bincoprod_ump_1cell_inr _ _ _ _)^-1 ▹ _)
                 • rassociator _ _ _).
      - use bincoprod_ump_2cell_invertible.
        + is_iso ; apply property_from_invertible_2cell.
        + is_iso ; apply property_from_invertible_2cell.
    Defined.

    Definition slice_coprod_ump_1_map
      : slice_coprod_cone --> q.
    Proof.
      use make_1cell_slice ; cbn.
      - exact slice_coprod_ump_1_map_mor.
      - exact slice_coprod_ump_1_map_inv2cell.
    Defined.

    Definition slice_coprod_ump_1_map_inl_cell
      : ι₁ · slice_coprod_ump_1_map_mor
        ==>
        pr1 (bincoprod_cocone_inl q)
      := bincoprod_ump_1cell_inl
           ump
           _
           (pr1 (bincoprod_cocone_inl q))
           (pr1 (bincoprod_cocone_inr q)).

    Definition slice_coprod_ump_1_map_inl_eq
      : cell_slice_homot
          (bincoprod_cocone_inl slice_coprod_cone · slice_coprod_ump_1_map)
          (bincoprod_cocone_inl q)
          slice_coprod_ump_1_map_inl_cell.
    Proof.
      unfold cell_slice_homot.
      cbn.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply bincoprod_ump_2cell_inl.
      }
      rewrite !vassocr.
      rewrite vcomp_linv, id2_left.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_right.
    Qed.

    Definition slice_coprod_ump_1_map_inl
      : invertible_2cell
          (bincoprod_cocone_inl slice_coprod_cone · slice_coprod_ump_1_map)
          (bincoprod_cocone_inl q).
    Proof.
      use make_invertible_2cell.
      - use make_2cell_slice.
        + exact slice_coprod_ump_1_map_inl_cell.
        + exact slice_coprod_ump_1_map_inl_eq.
      - use is_invertible_2cell_in_slice_bicat.
        apply property_from_invertible_2cell.
    Defined.

    Definition slice_coprod_ump_1_map_inr_cell
      : ι₂ · slice_coprod_ump_1_map_mor
        ==>
        pr1 (bincoprod_cocone_inr q)
      := bincoprod_ump_1cell_inr
           ump
           _
           (pr1 (bincoprod_cocone_inl q))
           (pr1 (bincoprod_cocone_inr q)).

    Definition slice_coprod_ump_1_map_inr_eq
      : cell_slice_homot
          (bincoprod_cocone_inr slice_coprod_cone · slice_coprod_ump_1_map)
          (bincoprod_cocone_inr q)
          slice_coprod_ump_1_map_inr_cell.
    Proof.
      unfold cell_slice_homot.
      cbn.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply bincoprod_ump_2cell_inr.
      }
      rewrite !vassocr.
      rewrite vcomp_linv, id2_left.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_right.
    Qed.

    Definition slice_coprod_ump_1_map_inr
      : invertible_2cell
          (bincoprod_cocone_inr slice_coprod_cone · slice_coprod_ump_1_map)
          (bincoprod_cocone_inr q).
    Proof.
      use make_invertible_2cell.
      - use make_2cell_slice.
        + exact slice_coprod_ump_1_map_inr_cell.
        + exact slice_coprod_ump_1_map_inr_eq.
      - use is_invertible_2cell_in_slice_bicat.
        apply property_from_invertible_2cell.
    Defined.
  End UMP1.

  Definition slice_coprod_ump_1
    : bincoprod_ump_1 slice_coprod_cone.
  Proof.
    intros q.
    use make_bincoprod_1cell.
    - exact (slice_coprod_ump_1_map q).
    - exact (slice_coprod_ump_1_map_inl q).
    - exact (slice_coprod_ump_1_map_inr q).
  Defined.

  Definition slice_coprod_ump_unique
             {q : slice_bicat b}
             {φ ψ : slice_coprod_cone --> q}
             (α : bincoprod_cocone_inl slice_coprod_cone · φ
                  ==>
                  bincoprod_cocone_inl slice_coprod_cone · ψ)
             (β : bincoprod_cocone_inr slice_coprod_cone · φ
                  ==>
                  bincoprod_cocone_inr slice_coprod_cone · ψ)
    : isaprop
        (∑ (γ : φ ==> ψ),
         bincoprod_cocone_inl slice_coprod_cone ◃ γ = α
         ×
         bincoprod_cocone_inr slice_coprod_cone ◃ γ = β).
  Proof.
    use invproofirrelevance.
    intros γ₁ γ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    use eq_2cell_slice.
    use (bincoprod_ump_2cell_unique_alt ump).
    - exact (maponpaths pr1 (pr12 γ₁) @ !(maponpaths pr1 (pr12 γ₂))).
    - exact (maponpaths pr1 (pr22 γ₁) @ !(maponpaths pr1 (pr22 γ₂))).
  Qed.

  Definition slice_coprod_ump_2
    : bincoprod_ump_2 slice_coprod_cone.
  Proof.
    intros q φ ψ α β.
    use iscontraprop1.
    - exact (slice_coprod_ump_unique α β).
    - simple refine ((_ ,, _) ,, _ ,, _).
      + exact (bincoprod_ump_2cell ump (pr1 α) (pr1 β)).
      + cbn.
        use (bincoprod_ump_2cell_unique_alt ump).
        * abstract
            (rewrite <- lwhisker_vcomp ;
             use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
             rewrite !vassocl ;
             rewrite rwhisker_lwhisker ;
             rewrite bincoprod_ump_2cell_inl ;
             use (vcomp_lcancel ((bincoprod_ump_1cell_inl ump b h₁ h₂) ^-1)) ; [ is_iso | ] ;
             rewrite !vassocr ;
             pose (pr2 α) as p ;
             cbn in p ;
             rewrite !vassocr in p ;
             exact p).
        * abstract
            (rewrite <- lwhisker_vcomp ;
             use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
             rewrite !vassocl ;
             rewrite rwhisker_lwhisker ;
             rewrite bincoprod_ump_2cell_inr ;
             use (vcomp_lcancel ((bincoprod_ump_1cell_inr ump b h₁ h₂) ^-1)) ; [ is_iso | ] ;
             rewrite !vassocr ;
             pose (pr2 β) as p ;
             cbn in p ;
             rewrite !vassocr in p ;
             exact p).
      + abstract
          (use eq_2cell_slice ; cbn ;
           apply bincoprod_ump_2cell_inl).
      + abstract
          (use eq_2cell_slice ; cbn ;
           apply bincoprod_ump_2cell_inr).
  Defined.
End CoproductSlice.

Definition has_bincoprod_slice_bicat
           {B : bicat}
           (HB : has_bincoprod B)
           (b : B)
  : has_bincoprod (slice_bicat b).
Proof.
  intros h₁ h₂.
  refine (slice_coprod_cone HB b (pr2 h₁) (pr2 h₂) ,, _).
  split.
  - exact (slice_coprod_ump_1 HB b (pr2 h₁) (pr2 h₂)).
  - exact (slice_coprod_ump_2 HB b (pr2 h₁) (pr2 h₂)).
Defined.
