(*****************************************************************************************

 Companion pairs

 In this file, we define the notion of companion pairs in Verity double bicategories.
 Companion pairs give a relation between horizontal and vertical morphisms in a Verity
 double bicategory. More specifically, two morphisms form a companion pair if they form
 an adjoint equivalence together. As such, companion pairs are used to define equivalences
 in Verity double bicategories, namely gregarious equivalences.

 We define the notion of companion pair, and we give two standard examples, namely the
 identity and the composition. Furthermore, we define Verity double bicategories in which
 all horizontal morphisms have companion pairs. We also define horizontally invariant
 Verity double bicategories, which are Verity double bicategories in which every horizontal
 adjoint equivalence has a companion pair (see Definition 4.1.7 in "Higher Dimensional
 Categories, From Double to Multiple Categories" by Grandis). Horizontally invariant Verity
 double bicategories are useful in the study of univalent Verity double bicategories,
 because for those univalence is equivalent to univalence of the horizontal bicategory.

 References:
 - Higher Dimensional Categories, From Double to Multiple Categories
   Marco Grandis

 Contents
 1. Definition of companion pairs
 2. Identity companion pairs
 3. Composition of companion pairs
 4. Verity double bicategories with all companion pairs
 5. Companions of horizontal morphisms

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
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
    := comp_diag_dr_corner φ₁ φ₂.

  Let φ : square_double_bicat (h₁ · h₂) (id_h z) (v₁ · v₂) (id_v z)
    := comp_are_companions_unit.

  Definition comp_are_companions_counit
    : square_double_bicat (id_h x) (h₁ · h₂) (id_v x) (v₁ · v₂)
    := comp_diag_ul_corner ψ₁ ψ₂.

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
      apply comp_ul_dr_corner.
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
  - abstract
      (refine (_ @ comp_are_companions_left
                     (B := transpose_verity_double_bicat B)
                     (companions_to_transpose c₁)
                     (companions_to_transpose c₂)) ;
       do 2 apply maponpaths ;
       cbn ;
       unfold comp_are_companions_counit, comp_are_companions_unit ;
       cbn ;
       rewrite lwhisker_uwhisker_square ;
       rewrite !double_bicat_interchange ;
       apply maponpaths ;
       rewrite rwhisker_dwhisker_square ;
       apply idpath).
Defined.

(** * 4. Verity double bicategories with all companion pairs *)
Definition all_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y),
     ∑ (v : x -|-> y), are_companions h v.

Definition weakly_hor_invariant
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y)
       (Hh : left_adjoint_equivalence h),
     ∑ (v : x -|-> y), are_companions h v.

Definition all_companions_to_weakly_hor_invariant
           (B : verity_double_bicat)
           (H : all_companions B)
  : weakly_hor_invariant B
  := λ x y h _, H x y h.

Definition univalent_2_0_weakly_hor_invariant
           (B : verity_double_bicat)
           (H : is_univalent_2_0 (hor_bicat_of_verity_double_bicat B))
  : weakly_hor_invariant B.
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

(** * 5. Companions of horizontal morphisms *)
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
            (H : vertically_saturated B)
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
