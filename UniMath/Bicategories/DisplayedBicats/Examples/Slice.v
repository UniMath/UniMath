(**
 Slice bicategories

 Contents:
 1. Definition of the slice displayed bicategory
 2. The univalence of the slice displayed bicategory
 3. The slice bicategory
 4. Invertible 2-cells in slice bicategory
 5. Adjoint equivalences in slice bicategory
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section SliceBicat.
  Context {B : bicat}
          (b : B).

  (**
   1. Definition of the slice displayed bicategory
   *)
  Definition slice_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a, a --> b).
    - exact (λ a₁ a₂ fa₁ fa₂ g, invertible_2cell fa₁ (g · fa₂)).
  Defined.

  Definition slice_disp_cat_id_comp
    : disp_cat_id_comp B slice_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a fa, linvunitor_invertible_2cell _).
    - exact (λ a₁ a₂ a₃ g₁ g₂ fa₁ fa₂ fa₃ α β,
             comp_of_invertible_2cell
               α
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     β)
                  (lassociator_invertible_2cell _ _ _))).
  Defined.

  Definition slice_disp_cat_data
    : disp_cat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact slice_disp_cat_ob_mor.
    - exact slice_disp_cat_id_comp.
  Defined.

  Definition slice_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (_ ,, _).
    - exact slice_disp_cat_data.
    - intros a₁ a₂ g₁ g₂ α fa₁ fa₂ β₁ β₂ ; cbn in *.
      exact (pr1 β₁ • (α ▹ _) = β₂).
  Defined.

  Definition slice_disp_prebicat_ops
    : disp_prebicat_ops slice_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split ; cbn.
    - intros.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intros.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      rewrite linvunitor_lunitor.
      apply id2_right.
    - intros.
      rewrite !vassocl.
      rewrite <- lunitor_lwhisker.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply id2_right.
    - intros.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ].
      use vcomp_move_R_Mp ; [ is_iso | ].
      cbn.
      rewrite lunitor_triangle.
      apply idpath.
    - intros.
      apply maponpaths.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite triangle_l_inv.
      apply idpath.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ].
      refine (!_).
      apply lassociator_lassociator.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply lassociator_lassociator.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? p q.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite p.
      exact q.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? p.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      exact p.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? p.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      exact p.
  Qed.

  Definition slice_disp_prebicat_data
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact slice_disp_prebicat_1_id_comp_cells.
    - exact slice_disp_prebicat_ops.
  Defined.

  Definition slice_disp_prebicat_laws
    : disp_prebicat_laws slice_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply cellset_property.
  Qed.

  Definition slice_disp_prebicat
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact slice_disp_prebicat_data.
    - exact slice_disp_prebicat_laws.
  Defined.

  Definition slice_disp_bicat
    : disp_bicat B.
  Proof.
    simple refine (_ ,, _).
    - exact slice_disp_prebicat.
    - cbn.
      intro ; intros.
      apply isasetaprop.
      apply cellset_property.
  Defined.

  Definition disp_2cells_isaprop_slice
    : disp_2cells_isaprop slice_disp_bicat.
  Proof.
    intro ; intros.
    apply cellset_property.
  Defined.

  Definition disp_locally_sym_slice
    : disp_locally_sym slice_disp_bicat.
  Proof.
    intros a₁ a₂ g₁ g₂ α fa₁ fa₂ β₁ β₂ p ; cbn in *.
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite vcomp_rinv.
    rewrite id2_rwhisker.
    apply id2_right.
  Qed.

  Definition disp_locally_groupoid_slice_disp_bicat
    : disp_locally_groupoid slice_disp_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_slice.
    - exact disp_2cells_isaprop_slice.
  Defined.

  (**
   2. The univalence of the slice displayed bicategory
   *)
  Definition disp_univalent_2_1_slice
    : disp_univalent_2_1 slice_disp_bicat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros x y f g xx ff gg.
    use isweqimplimpl.
    - intros α.
      use subtypePath.
      {
        intro.
        apply isaprop_is_invertible_2cell.
      }
      refine (_ @ pr1 α) ; cbn.
      rewrite id2_rwhisker, id2_right.
      apply idpath.
    - apply isaset_invertible_2cell.
    - use invproofirrelevance.
      intros α β.
      use subtypePath.
      {
        intro.
        apply isaprop_is_disp_invertible_2cell.
      }
      apply disp_2cells_isaprop_slice.
  Qed.

  Definition slice_inv2cell_to_disp_adj_equiv
             {x : B}
             {f g : slice_disp_bicat x}
             (α : invertible_2cell f g)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) f g.
  Proof.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, (_ ,, _))).
    - exact (comp_of_invertible_2cell
               α
               (linvunitor_invertible_2cell _)).
    - exact (comp_of_invertible_2cell
               (inv_of_invertible_2cell α)
               (linvunitor_invertible_2cell _)).
    - abstract
        (cbn ;
         rewrite linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite vcomp_rinv ;
         rewrite id2_left ;
         rewrite lwhisker_hcomp ;
         rewrite triangle_l_inv ;
         rewrite <- rwhisker_hcomp ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         rewrite !vassocl ;
         refine (_ @ id2_right _) ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite vcomp_linv ;
         rewrite id2_left ;
         rewrite !vassocl ;
         use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
         rewrite id2_right ;
         rewrite lunitor_runitor_identity ;
         rewrite runitor_rwhisker ;
         apply idpath).
    - split ; apply disp_2cells_isaprop_slice.
    - split ; apply disp_locally_groupoid_slice_disp_bicat.
  Defined.

  Definition slice_disp_adj_equiv_to_inv2cell
             {x : B}
             {f g : slice_disp_bicat x}
             (α : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    f g)
    : invertible_2cell f g
    := comp_of_invertible_2cell
         (pr1 α)
         (lunitor_invertible_2cell _).

  Definition slice_inv2cell_weq_disp_adj_equiv
             (HB : is_univalent_2_1 B)
             {x : B}
             (f g : slice_disp_bicat x)
    : invertible_2cell f g
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) f g.
  Proof.
    use make_weq.
    - exact slice_inv2cell_to_disp_adj_equiv.
    - use gradth.
      + exact slice_disp_adj_equiv_to_inv2cell.
      + abstract
          (intros α ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite linvunitor_lunitor ;
           apply id2_right).
      + abstract
          (intros α ;
           use subtypePath ;
           [ intro ;
             apply (isaprop_disp_left_adjoint_equivalence
                      _ _
                      HB
                      disp_univalent_2_1_slice)
           | ] ;
           use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite lunitor_linvunitor ;
           apply id2_right).
  Defined.

  Definition disp_univalent_2_0_slice
             (HB : is_univalent_2_1 B)
    : disp_univalent_2_0 slice_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x f g.
    use weqhomot.
    - exact (slice_inv2cell_weq_disp_adj_equiv HB f g
             ∘ make_weq _ (HB _ _ f g))%weq.
    - abstract
        (intro p ; cbn in p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_disp_left_adjoint_equivalence
                    _ _
                    HB
                    disp_univalent_2_1_slice)
         | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         cbn ;
         apply id2_left).
  Defined.

  Definition disp_univalent_2_slice
             (HB : is_univalent_2_1 B)
    : disp_univalent_2 slice_disp_bicat.
  Proof.
    split.
    - exact (disp_univalent_2_0_slice HB).
    - exact disp_univalent_2_1_slice.
  Defined.
End SliceBicat.

(**
 3. The slice bicategory
 *)
Definition slice_bicat
           {B : bicat}
           (b : B)
  : bicat
  := total_bicat (slice_disp_bicat b).

Definition is_univalent_2_1_slice_bicat
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : is_univalent_2_1 (slice_bicat b).
Proof.
  use total_is_univalent_2_1.
  - exact HB.
  - exact (disp_univalent_2_1_slice b).
Defined.

Definition is_univalent_2_0_slice_bicat
           {B : bicat}
           (HB : is_univalent_2 B)
           (b : B)
  : is_univalent_2_0 (slice_bicat b).
Proof.
  use total_is_univalent_2_0.
  - exact (pr1 HB).
  - exact (disp_univalent_2_0_slice b (pr2 HB)).
Defined.

Definition is_univalent_2_slice_bicat
           {B : bicat}
           (HB : is_univalent_2 B)
           (b : B)
  : is_univalent_2 (slice_bicat b).
Proof.
  split.
  - exact (is_univalent_2_0_slice_bicat HB b).
  - exact (is_univalent_2_1_slice_bicat (pr2 HB) b).
Defined.

Definition make_ob_slice
           {B : bicat}
           {b : B}
           {y : B}
           (f : y --> b)
  : slice_bicat b
  := y ,, f.

Definition make_1cell_slice
           {B : bicat}
           {b : B}
           {f₁ f₂ : slice_bicat b}
           (g : pr1 f₁ --> pr1 f₂)
           (α : invertible_2cell (pr2 f₁) (g · pr2 f₂))
  : f₁ --> f₂
  := g ,, α.

Definition cell_slice_homot
           {B : bicat}
           {b : B}
           {f₁ f₂ : slice_bicat b}
           (α β : f₁ --> f₂)
           (γ : pr1 α ==> pr1 β)
  : UU
  := pr12 α • (γ ▹ pr2 f₂) = pr12 β.

Definition make_2cell_slice
           {B : bicat}
           {b : B}
           {f₁ f₂ : slice_bicat b}
           {α β : f₁ --> f₂}
           (γ : pr1 α ==> pr1 β)
           (p : cell_slice_homot α β γ)
  : α ==> β
  := γ ,, p.

Definition eq_2cell_slice
           {B : bicat}
           {b : B}
           {y₁ y₂ : slice_bicat b}
           {f g : y₁ --> y₂}
           {α β : f ==> g}
           (p : pr1 α = pr1 β)
  : α = β.
Proof.
  use subtypePath.
  {
    intro.
    apply cellset_property.
  }
  exact p.
Qed.

(**
 4. Invertible 2-cells in slice bicategory
 *)
Definition is_invertible_2cell_in_slice_bicat
           {B : bicat}
           {b : B}
           {f₁ f₂ : slice_bicat b}
           {g₁ g₂ : f₁ --> f₂}
           {α : g₁ ==> g₂}
           (Hα : is_invertible_2cell (pr1 α))
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  simple refine (_ ,, _).
  - exact Hα.
  - apply (disp_locally_groupoid_slice_disp_bicat
             _ _ _ _ _
             (make_invertible_2cell Hα)).
Defined.

(**
  5. Adjoint equivalences in slice bicategory
 *)
Section LeftAdjointEquivalenceSlice.
  Context {B : bicat}
          {b : B}
          {f₁ f₂ : slice_bicat b}
          (l : f₁ --> f₂)
          (Hl : left_adjoint_equivalence (pr1 l)).

  Let r : pr1 f₂ --> pr1 f₁
    := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (pr1 l · r)
    := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · pr1 l) (id₁ _)
    := left_equivalence_counit_iso Hl.

  Definition left_adjoint_equivalence_in_slice_right_adj_cell
    : invertible_2cell (pr2 f₂) (r · pr2 f₁)
    := comp_of_invertible_2cell
         (linvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (rwhisker_of_invertible_2cell
               _
               (inv_of_invertible_2cell ε))
            (comp_of_invertible_2cell
               (rassociator_invertible_2cell _ _ _)
               (lwhisker_of_invertible_2cell
                  _
                  (inv_of_invertible_2cell (pr2 l))))).

  Definition left_adjoint_equivalence_in_slice_right_adj
    : f₂ --> f₁
    := make_1cell_slice r (left_adjoint_equivalence_in_slice_right_adj_cell).

  Let slice_r : f₂ --> f₁ := left_adjoint_equivalence_in_slice_right_adj.

  Definition left_adjoint_equivalence_in_slice_unit_eq
    : cell_slice_homot (id₁ f₁) (l · slice_r) η.
  Proof.
    unfold cell_slice_homot.
    cbn.
    rewrite !vassocr.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite lwhisker_lwhisker.
    rewrite !vassocr.
    use vcomp_move_L_Mp ; [ is_iso | ] ; cbn -[η ε].
    rewrite !vassocl.
    rewrite vcomp_whisker.
    rewrite !vassocr.
    rewrite lwhisker_hcomp.
    rewrite <- linvunitor_natural.
    rewrite !vassocl.
    apply maponpaths.
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[η ε].
    rewrite !vassocl.
    rewrite <- lassociator_lassociator.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_hcomp.
    rewrite triangle_l_inv.
    rewrite <- rwhisker_hcomp.
    rewrite !rwhisker_vcomp.
    apply maponpaths.
    do 2 (use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[η ε]).
    refine (!(id2_left _) @ _).
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[η ε].
    exact (!(pr1 (axioms_of_left_adjoint Hl))).
  Qed.

  Definition left_adjoint_equivalence_in_slice_unit
    : id₁ f₁ ==> l · slice_r.
  Proof.
    use make_2cell_slice.
    - exact η.
    - exact left_adjoint_equivalence_in_slice_unit_eq.
  Defined.

  Definition left_adjoint_equivalence_in_slice_counit_eq
    : cell_slice_homot (slice_r · l) (id₁ f₂) ε.
  Proof.
    unfold cell_slice_homot ; cbn.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
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

  Definition left_adjoint_equivalence_in_slice_counit
    : slice_r · l ==> id₁ f₂.
  Proof.
    use make_2cell_slice.
    - exact ε.
    - exact left_adjoint_equivalence_in_slice_counit_eq.
  Defined.

  Definition left_adjoint_equivalence_in_slice_bicat
    : left_adjoint_equivalence l.
  Proof.
    use equiv_to_adjequiv.
    simple refine ((slice_r
                    ,,
                    (left_adjoint_equivalence_in_slice_unit
                     ,,
                     left_adjoint_equivalence_in_slice_counit))
                   ,,
                   (_ ,, _)).
    - use is_invertible_2cell_in_slice_bicat.
      apply property_from_invertible_2cell.
    - use is_invertible_2cell_in_slice_bicat.
      apply property_from_invertible_2cell.
  Defined.
End LeftAdjointEquivalenceSlice.
