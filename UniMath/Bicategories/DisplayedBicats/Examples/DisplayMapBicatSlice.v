(**
 Slice bicategories of display map bicategories

 Contents:
 1. Definition of the slice displayed bicategory of display map bicategories
 2. The univalence of the slice displayed bicategory of display map bicategories
 3. The slice bicategory of display map bicategories
 4. Invertible 2-cells
 5. Adjoint equivalences
 6. Discreteness
 7. Instantiations
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
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Logic.DisplayMapBicat.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

Section DispMapSliceBicat.
  Context {B : bicat}
          (D : arrow_subbicat B)
          (b : B).

  (**
   1. Definition of the slice displayed bicategory of display map bicategories
   *)
  Definition disp_map_slice_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a, ∑ (f : a --> b), pred_ob D f).
    - exact (λ a₁ a₂ fa₁ fa₂ g,
             pred_mor D (pr1 fa₁) (pr1 fa₂) g
             ×
             invertible_2cell (pr1 fa₁) (g · pr1 fa₂)).
  Defined.

  Definition disp_map_slice_disp_cat_id_comp
    : disp_cat_id_comp B disp_map_slice_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a fa,
             id_pred_mor D _
             ,,
             linvunitor_invertible_2cell (pr1 fa)).
    - exact (λ a₁ a₂ a₃ g₁ g₂ fa₁ fa₂ fa₃ α β,
             comp_pred_mor D (pr1 α) (pr1 β)
             ,,
             comp_of_invertible_2cell
               (pr2 α)
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     (pr2 β))
                  (lassociator_invertible_2cell _ _ _))).
  Defined.

  Definition disp_map_slice_disp_cat_data
    : disp_cat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_cat_ob_mor.
    - exact disp_map_slice_disp_cat_id_comp.
  Defined.

  Definition disp_map_slice_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_cat_data.
    - intros a₁ a₂ g₁ g₂ α fa₁ fa₂ β₁ β₂ ; cbn in *.
      exact (pr12 β₁ • (α ▹ _) = pr12 β₂).
  Defined.

  Definition disp_map_slice_disp_prebicat_ops
    : disp_prebicat_ops disp_map_slice_disp_prebicat_1_id_comp_cells.
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

  Definition disp_map_slice_disp_prebicat_data
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat_1_id_comp_cells.
    - exact disp_map_slice_disp_prebicat_ops.
  Defined.

  Definition disp_map_slice_disp_prebicat_laws
    : disp_prebicat_laws disp_map_slice_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply cellset_property.
  Qed.

  Definition disp_map_slice_disp_prebicat
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat_data.
    - exact disp_map_slice_disp_prebicat_laws.
  Defined.

  Definition disp_map_slice_disp_bicat
    : disp_bicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat.
    - cbn.
      intro ; intros.
      apply isasetaprop.
      apply cellset_property.
  Defined.

  Definition disp_2cells_isaprop_disp_map_slice
    : disp_2cells_isaprop disp_map_slice_disp_bicat.
  Proof.
    intro ; intros.
    apply cellset_property.
  Defined.

  Definition disp_locally_sym_disp_map_slice
    : disp_locally_sym disp_map_slice_disp_bicat.
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

  Definition disp_locally_groupoid_disp_map_slice_disp_bicat
    : disp_locally_groupoid disp_map_slice_disp_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_disp_map_slice.
    - exact disp_2cells_isaprop_disp_map_slice.
  Defined.

  (**
   2. The univalence of the slice displayed bicategory of display map bicategories
   *)
  Definition disp_univalent_2_1_disp_map_slice
             (HD : arrow_subbicat_props D)
    : disp_univalent_2_1 disp_map_slice_disp_bicat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros x y f g xx ff gg.
    use isweqimplimpl.
    - intros α.
      use pathsdirprod.
      + apply HD.
      + use subtypePath.
        {
          intro.
          apply isaprop_is_invertible_2cell.
        }
        refine (_ @ pr1 α) ; cbn.
        rewrite id2_rwhisker, id2_right.
        apply idpath.
    - use isasetdirprod.
      + apply isasetaprop.
        apply HD.
      + apply isaset_invertible_2cell.
    - use invproofirrelevance.
      intros α β.
      use subtypePath.
      {
        intro.
        apply isaprop_is_disp_invertible_2cell.
      }
      apply disp_2cells_isaprop_disp_map_slice.
  Qed.

  Definition disp_map_slice_inv2cell_to_disp_adj_equiv
             (HB : is_univalent_2 B)
             {x : B}
             {f g : disp_map_slice_disp_bicat x}
             (α : invertible_2cell (pr1 f) (pr1 g))
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) f g.
  Proof.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, (_ ,, _))).
    - simple refine (_ ,, _).
      + apply (arrow_subbicat_contains_equiv_over_id HB).
        * apply internal_adjoint_equivalence_identity.
        * exact (comp_of_invertible_2cell
                   α
                   (linvunitor_invertible_2cell _)).
      + exact (comp_of_invertible_2cell
                 α
                 (linvunitor_invertible_2cell _)).
    - simple refine (_ ,, _).
      + apply (arrow_subbicat_contains_equiv_over_id HB).
        * apply internal_adjoint_equivalence_identity.
        * exact (comp_of_invertible_2cell
                 (inv_of_invertible_2cell α)
                 (linvunitor_invertible_2cell _)).
      + exact (comp_of_invertible_2cell
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
    - abstract (split ; apply disp_2cells_isaprop_disp_map_slice).
    - abstract (split ; apply disp_locally_groupoid_disp_map_slice_disp_bicat).
  Defined.

  Definition disp_map_slice_disp_adj_equiv_to_inv2cell
             {x : B}
             {f g : disp_map_slice_disp_bicat x}
             (α : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    f g)
    : invertible_2cell (pr1 f) (pr1 g)
    := comp_of_invertible_2cell
         (pr21 α)
         (lunitor_invertible_2cell _).

  Definition disp_map_slice_inv2cell_weq_disp_adj_equiv
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
             {x : B}
             (f g : disp_map_slice_disp_bicat x)
    : invertible_2cell (pr1 f) (pr1 g)
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) f g.
  Proof.
    use make_weq.
    - exact (disp_map_slice_inv2cell_to_disp_adj_equiv HB).
    - use gradth.
      + exact disp_map_slice_disp_adj_equiv_to_inv2cell.
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
                      (pr2 HB)
                      (disp_univalent_2_1_disp_map_slice HD))
           | ] ;
           use pathsdirprod ;
           [ apply HD
           | use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
             cbn ;
             rewrite !vassocl ;
             rewrite lunitor_linvunitor ;
             apply id2_right]).
  Defined.

  Definition disp_univalent_2_0_disp_map_slice
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
    : disp_univalent_2_0 disp_map_slice_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x f g.
    use weqhomot.
    - refine (disp_map_slice_inv2cell_weq_disp_adj_equiv HB HD f g
              ∘ make_weq _ (pr2 HB _ _ (pr1 f) (pr1 g))
              ∘ path_sigma_hprop _ _ _ _)%weq.
      apply HD.
    - abstract
        (intro p ; cbn in p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_disp_left_adjoint_equivalence
                    _ _
                    (pr2 HB)
                    (disp_univalent_2_1_disp_map_slice HD))
         | ] ;
         use pathsdirprod ; [ apply HD | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         cbn ;
         apply id2_left).
  Defined.

  Definition disp_univalent_2_disp_map_slice
             (HB : is_univalent_2 B)
             (HD : arrow_subbicat_props D)
    : disp_univalent_2 disp_map_slice_disp_bicat.
  Proof.
    split.
    - exact (disp_univalent_2_0_disp_map_slice HB HD).
    - exact (disp_univalent_2_1_disp_map_slice HD).
  Defined.
End DispMapSliceBicat.

(**
 3. The slice bicategory of display map bicategories
 *)
Definition disp_map_slice_bicat
           {B : bicat}
           (D : arrow_subbicat B)
           (b : B)
  : bicat
  := total_bicat (disp_map_slice_disp_bicat D b).

Definition is_univalent_2_1_disp_map_slice
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (D : arrow_subbicat B)
           (HD : arrow_subbicat_props D)
           (b : B)
  : is_univalent_2_1 (disp_map_slice_bicat D b).
Proof.
  use total_is_univalent_2_1.
  - exact HB.
  - exact (disp_univalent_2_1_disp_map_slice _ _ HD).
Defined.

Definition is_univalent_2_0_disp_map_slice
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : arrow_subbicat B)
           (HD : arrow_subbicat_props D)
           (b : B)
  : is_univalent_2_0 (disp_map_slice_bicat D b).
Proof.
  use total_is_univalent_2_0.
  - exact (pr1 HB).
  - exact (disp_univalent_2_0_disp_map_slice _ _ HB HD).
Defined.

Definition is_univalent_2_disp_map_slice
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : arrow_subbicat B)
           (HD : arrow_subbicat_props D)
           (b : B)
  : is_univalent_2 (disp_map_slice_bicat D b).
Proof.
  split.
  - exact (is_univalent_2_0_disp_map_slice HB D HD b).
  - exact (is_univalent_2_1_disp_map_slice (pr2 HB) D HD b).
Defined.

Definition eq_2cell_disp_map_slice
           {B : bicat}
           {D : arrow_subbicat B}
           {b : B}
           {y₁ y₂ : disp_map_slice_bicat D b}
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
 4. Invertible 2-cells
 *)
Definition is_invertible_2cell_in_disp_map_slice_bicat
           {B : bicat}
           {D : arrow_subbicat B}
           {b : B}
           {f₁ f₂ : disp_map_slice_bicat D b}
           {g₁ g₂ : f₁ --> f₂}
           {α : g₁ ==> g₂}
           (Hα : is_invertible_2cell (pr1 α))
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  simple refine (_ ,, _).
  - exact Hα.
  - apply (disp_locally_groupoid_disp_map_slice_disp_bicat
             _ _ _ _ _ _
             (make_invertible_2cell Hα)).
Defined.

(**
 5. Adjoint equivalences
 *)
Section LeftAdjointEquivalenceDispMapSlice.
  Context {B : bicat}
          (HB : is_univalent_2 B)
          {D : arrow_subbicat B}
          {b : B}
          {f₁ f₂ : disp_map_slice_bicat D b}
          (l : f₁ --> f₂)
          (Hl : left_adjoint_equivalence (pr1 l)).

  Let r : pr1 f₂ --> pr1 f₁
    := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (pr1 l · r)
    := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · pr1 l) (id₁ _)
    := left_equivalence_counit_iso Hl.

  Definition left_adjoint_equivalence_in_disp_map_slice_right_adj_cell
    : invertible_2cell (pr12 f₂) (r · pr12 f₁)
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
                  (inv_of_invertible_2cell (pr22 l))))).

  Definition left_adjoint_equivalence_in_disp_map_slice_right_adj
    : f₂ --> f₁.
  Proof.
    refine (r ,, (_ ,, _)).
    - apply (arrow_subbicat_contains_equiv_over_id HB).
      + exact (inv_adjequiv (pr1 l ,, Hl)).
      + exact left_adjoint_equivalence_in_disp_map_slice_right_adj_cell.
    - exact left_adjoint_equivalence_in_disp_map_slice_right_adj_cell.
  Defined.

  Let slice_r : f₂ --> f₁ := left_adjoint_equivalence_in_disp_map_slice_right_adj.

  Definition left_adjoint_equivalence_in_disp_map_slice_unit_eq
    : linvunitor _ • (η ▹ _)
      =
      pr122 l
      • (_ ◃ (linvunitor _ • (ε^-1 ▹ _) • rassociator _ _ _ • (_ ◃ (pr22 l)^-1)))
      • lassociator _ _ _.
  Proof.
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

  Definition left_adjoint_equivalence_in_disp_map_slice_unit
    : id₁ f₁ ==> l · slice_r.
  Proof.
    simple refine (_ ,, _).
    - exact η.
    - abstract
        (cbn ;
         rewrite !vassocr ;
         exact left_adjoint_equivalence_in_disp_map_slice_unit_eq).
  Defined.

  Definition left_adjoint_equivalence_in_disp_map_slice_counit_eq
    : linvunitor _
      • (ε^-1 ▹ _)
      • rassociator _ _ _
      • (_ ◃ (pr22 l)^-1)
      • (_ ◃ pr122 l)
      • lassociator _ _ _
      • (ε ▹ _)
      =
      linvunitor _.
  Proof.
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

  Definition left_adjoint_equivalence_in_disp_map_slice_counit
    : slice_r · l ==> id₁ f₂.
  Proof.
    simple refine (_ ,, _).
    - exact ε.
    - abstract
        (cbn ;
         rewrite !vassocr ;
         exact left_adjoint_equivalence_in_disp_map_slice_counit_eq).
  Defined.

  Definition left_adjoint_equivalence_in_disp_map_slice_bicat
    : left_adjoint_equivalence l.
  Proof.
    use equiv_to_adjequiv.
    simple refine ((slice_r
                    ,,
                    (left_adjoint_equivalence_in_disp_map_slice_unit
                     ,,
                     left_adjoint_equivalence_in_disp_map_slice_counit))
                    ,,
                    (_ ,, _)).
    - use is_invertible_2cell_in_disp_map_slice_bicat.
      apply property_from_invertible_2cell.
    - use is_invertible_2cell_in_disp_map_slice_bicat.
      apply property_from_invertible_2cell.
  Defined.
End LeftAdjointEquivalenceDispMapSlice.

(**
 6. Discreteness
 *)
Definition locally_groupoid_disp_map_slice
           {B : bicat}
           {D : arrow_subbicat B}
           (HD : contained_in_conservative D)
           (b : B)
  : locally_groupoid (disp_map_slice_bicat D b).
Proof.
  intros x y f g α.
  use is_invertible_2cell_in_disp_map_slice_bicat.
  apply (HD _ _ _ (pr22 y)).
  use eq_is_invertible_2cell.
  - exact ((pr22 f)^-1 • pr122 g).
  - abstract
      (pose (pr2 α) as p ;
       cbn in p ;
       rewrite <- p ;
       rewrite !vassocr ;
       rewrite vcomp_linv ;
       rewrite id2_left ;
       apply idpath).
  - is_iso.
    apply property_from_invertible_2cell.
Defined.

Definition isaprop_2cell_disp_map_slice
           {B : bicat}
           {D : arrow_subbicat B}
           (HD : contained_in_faithful D)
           (b : B)
  : isaprop_2cells (disp_map_slice_bicat D b).
Proof.
  intros x y f g α β.
  use eq_2cell_disp_map_slice.
  apply (faithful_1cell_eq_cell (HD _ _ _ (pr22 y))).
  pose (p := pr2 α @ !(pr2 β)).
  use (vcomp_lcancel (pr22 f)) ; [ apply property_from_invertible_2cell | ].
  exact p.
Qed.

Definition is_discrete_disp_map_slice
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : arrow_subbicat B}
           (HD₁ : arrow_subbicat_props D)
           (HD₂ : contained_in_discrete D)
           (b : B)
  : is_discrete_bicat (disp_map_slice_bicat D b).
Proof.
  repeat split.
  - exact (is_univalent_2_1_disp_map_slice HB D HD₁ b).
  - apply locally_groupoid_disp_map_slice.
    apply discrete_contained_in_conservative.
    exact HD₂.
  - apply isaprop_2cell_disp_map_slice.
    apply discrete_contained_in_faithful.
    exact HD₂.
Defined.

Definition discrete_disp_map_slice
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : arrow_subbicat B}
           (HD₁ : arrow_subbicat_props D)
           (HD₂ : contained_in_discrete D)
           (b : B)
  : category
  := discrete_bicat_to_category
       (is_discrete_disp_map_slice HB HD₁ HD₂ b).

(**
 7. Instantiations
 *)
Definition sfib_slice
           {B : bicat}
           (b : B)
  : bicat
  := disp_map_slice_bicat (sfib_subbicat B) b.

Definition sopfib_slice
           {B : bicat}
           (b : B)
  : bicat
  := disp_map_slice_bicat (sopfib_subbicat B) b.

Definition disc_sfib_slice
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : category
  := discrete_disp_map_slice
       HB
       (discrete_sfib_subbicat_props B HB)
       (discrete_sfib_disp_map_bicat_in_discrete B)
       b.

Definition disc_sopfib_slice
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (b : B)
  : category
  := discrete_disp_map_slice
       HB
       (discrete_sopfib_subbicat_props B HB)
       (discrete_sopfib_disp_map_bicat_in_discrete B)
       b.
