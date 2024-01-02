(*****************************************************************************************

 Companion pairs

 Contents
 1. Definition of companion pairs
 2. Identity companion pairs
 3. Composition of companion pairs
 4. Cells between companion pairs
 5. Companions of adjoint equivalences
 6. Uniqueness of companion pairs
 7. Companions of horizontal morphisms
 8. Verity double bicategories with all companion pairs

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.Examples.TransposeDoubleBicat.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Definition of companion pairs *)
Definition are_companions
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
           (v : x -|-> y)
  : UU
  := ∑ (φ : square_double_bicat h (id_h y) v (id_v y))
       (ψ : square_double_bicat (id_h x) h (id_v x) v),
     (runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
     ×
     (runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _).

Definition make_are_companions
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
           (v : x -|-> y)
           (φ : square_double_bicat h (id_h y) v (id_v y))
           (ψ : square_double_bicat (id_h x) h (id_v x) v)
           (p : runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
           (q : runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _)
  : are_companions h v
  := φ ,, ψ ,, p ,, q.

Definition unit_are_companions
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
  : square_double_bicat h (id_h y) v (id_v y)
  := pr1 c.

Definition counit_are_companions
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
  : square_double_bicat (id_h x) h (id_v x) v
  := pr12 c.

Proposition are_companions_left
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : runitor _ ▹s (linvunitor _ ◃s counit_are_companions c ⋆v unit_are_companions c)
    =
    id_h_square_bicat _.
Proof.
  exact (pr122 c).
Defined.

Proposition are_companions_left'
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : counit_are_companions c ⋆v unit_are_companions c
    =
    rinvunitor _ ▹s (lunitor _ ◃s id_h_square_bicat _).
Proof.
  rewrite <- (are_companions_left c).
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite lwhisker_square_id.
  rewrite <- rwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition are_companions_right
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : runitor _ ▿s (linvunitor _ ▵s counit_are_companions c ⋆h unit_are_companions c)
    =
    id_v_square_bicat _.
Proof.
  exact (pr222 c).
Defined.

Proposition are_companions_right'
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : counit_are_companions c ⋆h unit_are_companions c
    =
    rinvunitor _ ▿s (lunitor _ ▵s id_v_square_bicat _).
Proof.
  rewrite <- (are_companions_right c).
  rewrite !dwhisker_uwhisker_square.
  rewrite <- uwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite uwhisker_square_id.
  rewrite <- dwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition eq_are_companions
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            {c₁ c₂ : are_companions h v}
            (p : unit_are_companions c₁ = unit_are_companions c₂)
            (q : counit_are_companions c₁ = counit_are_companions c₂)
  : c₁ = c₂.
Proof.
  use total2_paths_f.
  - exact p.
  - use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply isaset_square_double_bicat.
    }
    rewrite pr1_transportf.
    rewrite transportf_const.
    exact q.
Qed.

(** * 2. Identity companion pairs *)
Definition id_are_companions
           {B : verity_double_bicat}
           (x : B)
  : are_companions (id_h x) (id_v x).
Proof.
  use make_are_companions.
  - apply id_v_square_bicat.
  - apply id_v_square_bicat.
  - abstract
      (refine (_ @ rwhisker_square_id _ _) ;
       rewrite <- rinvunitor_runitor ;
       rewrite rwhisker_square_comp ;
       apply maponpaths ;
       rewrite id_h_square_bicat_id ;
       rewrite lunitor_v_comp_square' ;
       rewrite rwhisker_lwhisker_square ;
       rewrite <- lwhisker_square_comp ;
       rewrite linvunitor_lunitor ;
       rewrite lwhisker_square_id ;
       rewrite lunitor_V_id_is_left_unit_V_id ;
       apply idpath).
  - abstract
      (refine (_ @ dwhisker_square_id _ _) ;
       rewrite <- rinvunitor_runitor ;
       rewrite dwhisker_square_comp ;
       apply maponpaths ;
       rewrite <- !id_h_square_bicat_id ;
       rewrite lunitor_h_comp_square' ;
       rewrite dwhisker_uwhisker_square ;
       rewrite <- uwhisker_square_comp ;
       rewrite linvunitor_lunitor ;
       rewrite uwhisker_square_id ;
       rewrite lunitor_V_id_is_left_unit_V_id ;
       apply idpath).
Defined.

(** * 3. Composition of companion pairs *)

Definition comp_diag₁
           {B : verity_double_bicat}
           {x y z : B}
           {v₁ : x -|-> y}
           {v₂ : y -|-> z}
           {h₁ : x --> y}
           {h₂ : y --> z}
           (s₁ : square_double_bicat h₁ (id_h y) v₁ (id_v y))
           (s₂ : square_double_bicat h₂ (id_h z) v₂ (id_v z))
  : square_double_bicat (h₁ · h₂) (id_h z) (v₁ · v₂) (id_v z)
  := lunitor _ ▹s
       (lunitor _ ▿s ((s₁ ⋆h id_v_square_bicat h₂)
                      ⋆v
                      (id_h_square_bicat v₂ ⋆h s₂))).

Definition comp_diag₂
           {B : verity_double_bicat}
           {x y z : B}
           {v₁ : x -|-> y}
           {v₂ : y -|-> z}
           {h₁ : x --> y}
           {h₂ : y --> z}
           (s₁ : square_double_bicat (id_h x) h₁ (id_v x) v₁)
           (s₂ : square_double_bicat (id_h y) h₂ (id_v y) v₂)
  : square_double_bicat (id_h x) (h₁ · h₂) (id_v x) (v₁ · v₂)
  := linvunitor _ ◃s
       (linvunitor _
          ▵s ((s₁ ⋆h id_h_square_bicat _)
              ⋆v
              (id_v_square_bicat h₁ ⋆h s₂))).

Proposition comp_diag_v
            {B : verity_double_bicat}
            {x y z : B}
            {v₁ : x -|-> y}
            {v₂ : y -|-> z}
            {h₁ : x --> y}
            {h₂ : y --> z}
            (s₁ : square_double_bicat h₁ (id_h y) v₁ (id_v y))
            (s₂ : square_double_bicat h₂ (id_h z) v₂ (id_v z))
            (s₃ : square_double_bicat (id_h x) h₁ (id_v x) v₁)
            (s₄ : square_double_bicat (id_h y) h₂ (id_v y) v₂)
  : linvunitor _ ◃s (runitor _ ▹s comp_diag₂ s₃ s₄ ⋆v comp_diag₁ s₁ s₂)
    =
    (linvunitor _ • (_ ◃ (_ ◃ linvunitor _)) • lassociator _ _ _) ◃s
      ((rassociator _ _ _ • (_ ◃ (lunitor _ • runitor _))) ▹s
         ((s₃ ⋆v s₁) ⋆v (s₄ ⋆v s₂))).
Proof.
(*
    unfold comp_diag₁.
    rewrite r_rwhisker_v_comp_square.
    rewrite <- rwhisker_square_comp.
    unfold comp_diag₂.
    rewrite !vassocl.
    rewrite lwhisker_square_comp.
    apply maponpaths.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite l_lwhisker_v_comp_square.
    rewrite rwhisker_lwhisker_square.
    rewrite <- uwhisker_vcomp_square.
    rewrite <- dwhisker_vcomp_square.
    etrans.
    {
      rewrite runitor_h_comp_square'.
      rewrite dwhisker_uwhisker_square.
      rewrite <- !uwhisker_vcomp_square.
      rewrite dwhisker_uwhisker_square.
      rewrite <- uwhisker_square_comp.
      rewrite lunitor_h_comp_square'.
      rewrite <- !dwhisker_vcomp_square.
      rewrite <- dwhisker_square_comp.
      rewrite lassociator_v_comp_square'.
      rewrite <- lwhisker_dwhisker_square.
      rewrite <- lwhisker_uwhisker_square.
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_square_comp.
      rewrite <- rwhisker_dwhisker_square.
      rewrite <- rwhisker_uwhisker_square.
      rewrite <- rwhisker_square_comp.
      etrans.
      {
        do 4 apply maponpaths.
        apply maponpaths.
        apply lassociator_v_comp_square''.
      }
      rewrite r_lwhisker_v_comp_square.
      rewrite r_rwhisker_v_comp_square.
      rewrite <- lwhisker_dwhisker_square.
      rewrite <- lwhisker_uwhisker_square.
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_square_comp.
      rewrite <- rwhisker_dwhisker_square.
      rewrite <- rwhisker_uwhisker_square.
      rewrite <- rwhisker_square_comp.
      rewrite <- double_bicat_interchange.
      rewrite lunitor_v_comp_square'.
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_hcomp_square.
      rewrite l_lwhisker_v_comp_square.
      rewrite r_lwhisker_v_comp_square.
      rewrite <- lwhisker_dwhisker_square.
      rewrite <- lwhisker_uwhisker_square.
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_square_comp.
      rewrite runitor_v_comp_square'.
      rewrite <- rwhisker_hcomp_square.
      rewrite l_rwhisker_v_comp_square.
      rewrite r_rwhisker_v_comp_square.
      rewrite <- rwhisker_dwhisker_square.
      rewrite <- rwhisker_uwhisker_square.
      rewrite <- rwhisker_square_comp.
      rewrite <- ud_whisker_vcomp_square.
      etrans.
      {
        do 4 apply maponpaths.
        Search comp_v_square_bicat uwhisker_square.
      apply idpath.
      }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply lassociator_v_comp_square'.
    }
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    etrans.
    {
      do 2 appl
    refine (!_).

      Search "intercha".
      Search interchange.
 *)
Admitted.

Section CompCompanions.
  Context {B : verity_double_bicat}
          {x y z : B}
          {h₁ : x --> y}
          {h₂ : y --> z}
          {v₁ : x -|-> y}
          {v₂ : y -|-> z}
          (c₁ : are_companions h₁ v₁)
          (c₂ : are_companions h₂ v₂).

  Let φ₁ : square_double_bicat h₁ (id_h y) v₁ (id_v y) := unit_are_companions c₁.
  Let ψ₁ : square_double_bicat (id_h x) h₁ (id_v x) v₁ := counit_are_companions c₁.
  Let φ₂ : square_double_bicat h₂ (id_h z) v₂ (id_v z) := unit_are_companions c₂.
  Let ψ₂ : square_double_bicat (id_h y) h₂ (id_v y) v₂ := counit_are_companions c₂.

  Definition comp_are_companions_unit
    : square_double_bicat (h₁ · h₂) (id_h z) (v₁ · v₂) (id_v z)
    := comp_diag₁ φ₁ φ₂.

  Let φ : square_double_bicat (h₁ · h₂) (id_h z) (v₁ · v₂) (id_v z)
    := comp_are_companions_unit.

  Definition comp_are_companions_counit
    : square_double_bicat (id_h x) (h₁ · h₂) (id_v x) (v₁ · v₂)
    := comp_diag₂ ψ₁ ψ₂.

  Let ψ : square_double_bicat (id_h x) (h₁ · h₂) (id_v x) (v₁ · v₂)
    := comp_are_companions_counit.

  Proposition comp_are_companions_left
    : runitor (v₁ · v₂) ▹s (linvunitor (v₁ · v₂) ◃s ψ ⋆v φ)
      =
      id_h_square_bicat (v₁ · v₂).
  Proof.
    rewrite rwhisker_lwhisker_square.
    unfold φ, ψ.
    etrans.
    {
      apply comp_diag_v.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply are_companions_left'.
      }
      apply maponpaths_2.
      apply are_companions_left'.
    }
    rewrite !l_rwhisker_v_comp_square.
    rewrite !r_rwhisker_v_comp_square.
    rewrite !l_lwhisker_v_comp_square.
    rewrite !r_lwhisker_v_comp_square.
    rewrite <- !rwhisker_square_comp.
    rewrite <- !lwhisker_square_comp.
    rewrite rwhisker_lwhisker_square.
    rewrite <- !lwhisker_square_comp.
    refine (_ @ lwhisker_square_id _ _).
    use eq_lwhisker_square.
    {
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_triangle.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite linvunitor_lunitor.
        rewrite lwhisker_id2.
        apply id2_right.
      }
      apply linvunitor_lunitor.
    }
    refine (_ @ rwhisker_square_id _ _).
    use eq_rwhisker_square.
    {
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- lwhisker_vcomp.
        rewrite !vassocr.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite rinvunitor_runitor.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite rinvunitor_runitor.
      apply lwhisker_id2.
    }
    rewrite id_h_square_bicat_comp.
    apply idpath.
  Qed.
End CompCompanions.

Definition companions_to_transpose
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
  : are_companions
      (B := transpose_verity_double_bicat B)
      v
      h.
Proof.
  use make_are_companions.
  - exact (unit_are_companions c).
  - exact (counit_are_companions c).
  - apply (are_companions_right c).
  - apply (are_companions_left c).
Defined.

Definition comp_are_companions
           {B : verity_double_bicat}
           {x y z : B}
           {h₁ : x --> y}
           {h₂ : y --> z}
           {v₁ : x -|-> y}
           {v₂ : y -|-> z}
           (c₁ : are_companions h₁ v₁)
           (c₂ : are_companions h₂ v₂)
  : are_companions (h₁ · h₂) (v₁ · v₂).
Proof.
  use make_are_companions.
  - exact (comp_are_companions_unit c₁ c₂).
  - exact (comp_are_companions_counit c₁ c₂).
  - exact (comp_are_companions_left c₁ c₂).
  - refine (_ @ comp_are_companions_left
                  (B := transpose_verity_double_bicat B)
                  (companions_to_transpose c₁)
                  (companions_to_transpose c₂)).
    do 2 apply maponpaths.
    cbn.
    unfold comp_are_companions_counit, comp_are_companions_unit.
    unfold comp_diag₂, comp_diag₁.
    rewrite lwhisker_uwhisker_square.
    rewrite !double_bicat_interchange.
    apply maponpaths.
    rewrite rwhisker_dwhisker_square.
    apply idpath.
Defined.

(** * 4. Cells between companion pairs *)
Definition cell_are_companions
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : h₂ ==> h₁)
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h₁ v₁)
           (c₂ : are_companions h₂ v₂)
  : v₁ ==> v₂
  := let φ₁ := unit_are_companions c₁ in
     let ψ₂ := τ ▿s counit_are_companions c₂ in
     square_to_vertical_cell H (linvunitor _ ◃s (runitor _ ▹s ψ₂ ⋆v φ₁)).

Proposition cell_are_companions_id
            {B : verity_double_bicat}
            (H : vertical_cells_are_squares B)
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : cell_are_companions H (id2 h) c c = id2 v.
Proof.
  unfold cell_are_companions.
  rewrite <- (square_to_vertical_cell_id H).
  apply maponpaths.
  rewrite dwhisker_square_id.
  rewrite are_companions_left'.
  rewrite <- rwhisker_square_comp.
  rewrite rinvunitor_runitor.
  rewrite rwhisker_square_id.
  rewrite <- lwhisker_square_comp.
  rewrite linvunitor_lunitor.
  rewrite lwhisker_square_id.
  apply idpath.
Qed.

Proposition cell_are_companions_comp
            {B : verity_double_bicat}
            (H : vertical_cells_are_squares B)
            {x y : B}
            {h₁ h₂ h₃ : x --> y}
            (τ₁ : h₂ ==> h₁)
            (τ₂ : h₃ ==> h₂)
            {v₁ v₂ v₃ : x -|-> y}
            (c₁ : are_companions h₁ v₁)
            (c₂ : are_companions h₂ v₂)
            (c₃ : are_companions h₃ v₃)
  : cell_are_companions H (τ₂ • τ₁) c₁ c₃
    =
    cell_are_companions H τ₁ c₁ c₂ • cell_are_companions H τ₂ c₂ c₃.
Proof.
  unfold cell_are_companions.
  rewrite <- square_to_vertical_cell_comp.
  apply maponpaths.
  unfold comp_ver_globular_square.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    rewrite <- lwhisker_hcomp_square.
    apply maponpaths.
    rewrite <- rwhisker_lwhisker_square.
    rewrite <- rwhisker_hcomp_square.
    apply idpath.
  }
  rewrite <- lwhisker_dwhisker_square.
  rewrite <- lwhisker_uwhisker_square.
  apply maponpaths.
  rewrite <- rwhisker_dwhisker_square.
  rewrite <- rwhisker_uwhisker_square.
  apply maponpaths.
  etrans.
  {
    do 2 apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply lunitor_v_comp_square''.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply runitor_v_comp_square''.
    }
    rewrite <- rwhisker_hcomp_square.
    apply maponpaths.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_hcomp_square.
    apply maponpaths.
    rewrite lrwhisker_hcomp_square.
    rewrite <- rwhisker_square_comp.
    rewrite r_rwhisker_v_comp_square.
    rewrite <- rwhisker_square_comp.
    rewrite !vassocr.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    rewrite id2_right.
    rewrite l_lwhisker_v_comp_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths.
      apply lassociator_v_comp_square'.
    }
    rewrite <- lrwhisker_hcomp_square.
    rewrite <- !lwhisker_square_comp.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- linvunitor_assoc.
      apply lunitor_linvunitor.
    }
    rewrite lwhisker_square_id.
    rewrite <- rwhisker_hcomp_square.
    apply maponpaths.
    rewrite double_bicat_interchange.
    rewrite double_bicat_interchange.
    rewrite l_dwhisker_h_comp_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply are_companions_right'.
    }
    rewrite uwhisker_id_v_square.
    rewrite <- !dwhisker_square_comp.
    rewrite <- ud_whisker_vcomp_square.
    rewrite lunitor_v_comp_square'.
    apply idpath.
  }
  rewrite r_rwhisker_v_comp_square.
  rewrite <- !rwhisker_lwhisker_square.
  rewrite <- !rwhisker_square_comp.
  rewrite r_lwhisker_v_comp_square.
  rewrite <- !lwhisker_square_comp.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite <- runitor_triangle.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    rewrite runitor_lunitor_identity.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply lwhisker_id2.
  }
  rewrite rwhisker_square_id.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite runitor_lunitor_identity.
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply id2_rwhisker.
  }
  rewrite lwhisker_square_id.
  rewrite ud_whisker_vcomp_square.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite r_dwhisker_h_comp_square.
    rewrite <- !dwhisker_square_comp.
    apply maponpaths_2.
    rewrite !vassocr.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    apply idpath.
  }
  rewrite dwhisker_vcomp_square.
  rewrite uwhisker_vcomp_square.
  rewrite <- !id_h_square_bicat_id.
  rewrite lunitor_h_comp_square'.
  rewrite runitor_h_comp_square'.
  rewrite <- !dwhisker_vcomp_square.
  rewrite <- uwhisker_vcomp_square.
  rewrite <- !dwhisker_square_comp.
  rewrite lunitor_runitor_identity.
  rewrite rinvunitor_runitor.
  rewrite dwhisker_square_id.
  rewrite dwhisker_uwhisker_square.
  rewrite <- uwhisker_vcomp_square.
  rewrite <- uwhisker_square_comp.
  rewrite linvunitor_lunitor.
  rewrite uwhisker_square_id.
  rewrite ud_whisker_vcomp_square.
  apply maponpaths_2.
  rewrite <- dwhisker_square_comp.
  apply maponpaths_2.
  rewrite !vassocl.
  rewrite rinvunitor_runitor.
  rewrite !id2_right.
  rewrite !vassocr.
  rewrite linvunitor_lunitor.
  rewrite id2_left.
  apply idpath.
Qed.

Definition inv2cell_are_companions
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : invertible_2cell h₁ h₂)
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h₁ v₁)
           (c₂ : are_companions h₂ v₂)
  : invertible_2cell v₁ v₂.
Proof.
  use make_invertible_2cell.
  - exact (cell_are_companions H (τ^-1) c₁ c₂).
  - use make_is_invertible_2cell.
    + exact (cell_are_companions H τ c₂ c₁).
    + abstract
        (rewrite <- cell_are_companions_comp ;
         rewrite vcomp_rinv ;
         apply cell_are_companions_id).
    + abstract
        (rewrite <- cell_are_companions_comp ;
         rewrite vcomp_linv ;
         apply cell_are_companions_id).
Defined.

(** * 5. Companions of adjoint equivalences *)
Section CompanionOfAdjequiv.
  Context {B : verity_double_bicat}
          (H : vertical_cells_are_squares B)
          {x y : B}
          {h : x --> y}
          {v : x -|-> y}
          (c : are_companions h v)
          (Hh : left_adjoint_equivalence h)
          {v' : y -|-> x}
          (c' : are_companions (left_adjoint_right_adjoint Hh) v').

  Let h' : y --> x := left_adjoint_right_adjoint Hh.
  Let η : invertible_2cell (id_h x) (h · h')
    := left_equivalence_unit_iso Hh.
  Let ε : invertible_2cell (h' · h) (id_h y)
    := left_equivalence_counit_iso Hh.

  Definition companion_of_adjequiv_equiv
    : left_equivalence v.
  Proof.
    simple refine ((v' ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (inv2cell_are_companions
               H
               η
               (id_are_companions x)
               (comp_are_companions c c')).
    - exact (inv2cell_are_companions
               H
               ε
               (comp_are_companions c' c)
               (id_are_companions y)).
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition companion_of_adjequiv
    : left_adjoint_equivalence v.
  Proof.
    use equiv_to_adjequiv.
    exact companion_of_adjequiv_equiv.
  Defined.
End CompanionOfAdjequiv.

(** * 6. Uniqueness of companion pairs *)
Definition square_between_companions
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h v₁)
           (c₂ : are_companions h v₂)
  : square_double_bicat (id_h x) (id_h y) v₁ v₂
  := linvunitor _ ◃s (runitor _ ▹s counit_are_companions c₂ ⋆v unit_are_companions c₁).

Section ComparionPairUnique.
  Context {B : verity_double_bicat}
          {x y : B}
          {h : x --> y}
          {v₁ v₂ : x -|-> y}
          (c₁ : are_companions h v₁)
          (c₂ : are_companions h v₂).

  Let γ₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := square_between_companions c₁ c₂.

  Let γ₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₁
    := square_between_companions c₂ c₁.

  Proposition comp_square_between_companions
    : comp_ver_globular_square γ₁ γ₂ = id_h_square_bicat v₁.
  Proof.
    unfold γ₁, γ₂, square_between_companions.
    unfold comp_ver_globular_square.

    pose (p₁ := are_companions_left c₁).
    refine (_ @ p₁).
    etrans.
    {
      unfold comp_ver_globular_square.
      rewrite <- lwhisker_hcomp_square.
      apply maponpaths.
      rewrite lrwhisker_hcomp_square.
      rewrite <- rwhisker_hcomp_square.
      apply idpath.
    }
    rewrite <- rwhisker_lwhisker_square.
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_uwhisker_square.
    apply maponpaths.
    rewrite <- lwhisker_dwhisker_square.
    rewrite <- lwhisker_uwhisker_square.
    apply maponpaths.
  Admitted.

  Proposition square_between_companions_unit
    : lunitor (id_h y) ▿s (linvunitor h ▵s γ₁ ⋆h unit_are_companions c₂)
      =
      unit_are_companions c₁.
  Proof.
    unfold γ₁, square_between_companions.
    etrans.
    {
      do 2 apply maponpaths.
  Admitted.

  Proposition square_between_companions_counit
    : runitor h ▿s (linvunitor (id_h x) ▵s counit_are_companions c₁ ⋆h γ₁)
      =
      counit_are_companions c₂.
  Proof.
  Admitted.
End ComparionPairUnique.

(** * 7. Companions of horizontal morphisms *)
Definition hor_companion
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
  : UU
  := ∑ (v : x -|-> y), are_companions h v.

Coercion mor_of_hor_companion
         {B : verity_double_bicat}
         {x y : B}
         {h : x --> y}
         (c : hor_companion h)
  : x -|-> y
  := pr1 c.

Coercion are_companions_hor_companion
         {B : verity_double_bicat}
         {x y : B}
         {h : x --> y}
         (c : hor_companion h)
  : are_companions h c
  := pr2 c.

Proposition eq_companion_of_hor
            {B : verity_double_bicat}
            (H : vertical_cells_are_squares B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
            {x y : B}
            {h : x --> y}
            {φ₁ φ₂ : hor_companion h}
            (p : pr1 φ₁ = pr1 φ₂)
            (q₁ : lunitor _ ▿s
                    (linvunitor _ ▵s
                       (v_sq_idtoiso_2_1 p ⋆h unit_are_companions φ₂))
                  =
                  unit_are_companions φ₁)
            (q₂ : runitor _ ▿s
                    (linvunitor _ ▵s
                       (counit_are_companions φ₁ ⋆h v_sq_idtoiso_2_1 p))
                  =
                  counit_are_companions φ₂)
  : φ₁ = φ₂.
Proof.
  induction φ₁ as [ v₁ [ c₁ [ Hh₁ Hv₁ ] ] ].
  induction φ₂ as [ v₂ [ c₂ [ Hh₂ Hv₂ ] ] ].
  cbn in p.
  induction p.
  cbn in *.
  apply maponpaths.
  use eq_are_companions.
  - refine (!q₁ @ _).
    unfold vertical_cell_to_square.
    rewrite lwhisker_square_id.
    rewrite lunitor_h_comp_square'.
    rewrite !dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite <- dwhisker_square_comp.
    rewrite !linvunitor_lunitor.
    rewrite uwhisker_square_id, dwhisker_square_id.
    apply idpath.
  - refine (_ @ q₂).
    unfold vertical_cell_to_square.
    rewrite lwhisker_square_id.
    rewrite runitor_h_comp_square'.
    rewrite !dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite <- dwhisker_square_comp.
    rewrite runitor_lunitor_identity.
    rewrite linvunitor_lunitor.
    rewrite rinvunitor_runitor.
    rewrite uwhisker_square_id, dwhisker_square_id.
    apply idpath.
Qed.

Proposition isaprop_companion_pair
            {B : verity_double_bicat}
            (H : vertical_cells_are_squares B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
            {x y : B}
            (h : x --> y)
  : isaprop (∑ (v : x -|-> y), are_companions h v).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use (eq_companion_of_hor H HB_2_1).
  - use (v_sq_isotoid_2_1 H HB_2_1).
    use make_invertible_vertical_square.
    + use make_invertible_vertical_square_data.
      * exact (square_between_companions (pr2 φ₁) (pr2 φ₂)).
      * exact (square_between_companions (pr2 φ₂) (pr2 φ₁)).
    + split.
      * apply comp_square_between_companions.
      * apply comp_square_between_companions.
  - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
    apply square_between_companions_unit.
  - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
    apply square_between_companions_counit.
Qed.

(** * 8. Verity double bicategories with all companion pairs *)
Definition all_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y),
     ∑ (v : x -|-> y), are_companions h v.

Proposition isaprop_all_companions
            (B : verity_double_bicat)
            (H : vertical_cells_are_squares B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
  : isaprop (all_companions B).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro h.
  apply isaprop_companion_pair.
  - exact H.
  - exact HB_2_1.
Qed.

Definition all_equivs_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y)
       (Hh : left_adjoint_equivalence h),
     ∑ (v : x -|-> y), are_companions h v.

Proposition isaprop_all_equivs_companions
            (B : verity_double_bicat)
            (H : vertical_cells_are_squares B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
  : isaprop (all_equivs_companions B).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro h.
  use impred ; intro Hh.
  apply isaprop_companion_pair.
  - exact H.
  - exact HB_2_1.
Qed.

Definition all_companions_to_all_equivs_companions
           (B : verity_double_bicat)
           (H : all_companions B)
  : all_equivs_companions B
  := λ x y h _, H x y h.

Definition all_equivs_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           (H' : all_equivs_companions B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use companion_of_adjequiv.
  - exact H.
  - exact h.
  - exact c.
  - exact Hh.
  - exact (pr1 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
  - exact (pr2 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
Defined.

Definition all_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           (H' : all_companions B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use all_equivs_companions_adjequiv.
  - exact H.
  - use all_companions_to_all_equivs_companions.
    exact H'.
  - exact h.
  - exact c.
  - exact Hh.
Defined.

Definition univalent_2_0_all_equivs_companions
           (B : verity_double_bicat)
           (H : is_univalent_2_0 (hor_bicat_of_verity_double_bicat B))
  : all_equivs_companions B.
Proof.
  assert (∏ (x y : B)
            (h : adjoint_equivalence x y),
           ∑ (v : x -|-> y), are_companions h v)
    as H'.
  {
    use (J_2_0 H) ; cbn.
    intros x.
    exact (_ ,, id_are_companions x).
  }
  intros x y h Hh.
  exact (H' x y (h ,, Hh)).
Defined.
