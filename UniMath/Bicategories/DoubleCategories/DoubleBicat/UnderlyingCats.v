(*****************************************************************************************

 Underlying (bi)categories of Verity double bicategories

 Every Verity double bicategory has several underlying (bi)categories.
 - The underlying horizontal bicategory ([hor_bicat_of_verity_double_bicat]).
 - The underlying vertical bicategory ([ver_bicat_of_verity_double_bicat]).
 - The underlying horizontal hom-category ([hom_h]) whose objects are horizontal 1-cells
   and whose morphisms are horizontal 2-cells.
 - The underlying vertical hom-category ([hom_v]) whose objects are vertical 1-cells and
   whose morphisms are vertical 2-cells.
 - The underlying hom-category of squares and horizontal cylinders
 - The underlying hom-category of squares and vertical cylinders
 In this file, we define each of these categories.

 Contents
 1. The underlying horizontal bicategory
 2. The underlying vertical bicategory
 3. The underlying horizontal hom-category
 4. The underlying vertical hom-category
 5. The underlying category of squares and horizontal cylinders
 6. The underlying category of squares and vertical cylinders

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
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.

Local Open Scope cat.
Local Open Scope double_bicat.

Section UnderlyingCategories.
  Context (B : verity_double_bicat).

  (** * 1. The underlying horizontal bicategory *)
  Definition hor_bicat_of_verity_double_bicat
    : bicat
    := B.

  (** * 2. The underlying vertical bicategory *)
  Definition ver_bicat_of_verity_double_bicat
    : bicat
    := ver_bicat_of_ver_bicat_sq_bicat B.

  (** * 3. The underlying horizontal hom-category *)
  Definition hom_h
             (x y : B)
    : category
    := hom (C := hor_bicat_of_verity_double_bicat) x y.

  (** * 4. The underlying vertical hom-category *)
  Definition hom_v
             (x y : B)
    : category
    := hom (C := ver_bicat_of_verity_double_bicat) x y.

  (** * 5. The underlying category of squares and horizontal cylinders *)
  Section HorCyl.
    Context {w x y z : B}
            (v₁ : w -|-> x)
            (v₂ : y -|-> z).

    Definition hor_cyl_twosided_disp_cat_ob_mor
      : twosided_disp_cat_ob_mor (hom_h w y) (hom_h x z).
    Proof.
      simple refine (_ ,, _).
      - exact (λ (h : w --> y) (k : x --> z), square_double_bicat h k v₁ v₂).
      - exact (λ (h₁ h₂ : w --> y) (k₁ k₂ : x --> z)
                 (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
                 (s₂ : square_double_bicat h₂ k₂ v₁ v₂)
                 (τ₁ : h₁ ==> h₂)
                 (τ₂ : k₁ ==> k₂),
               is_hor_cylinder s₁ s₂ τ₁ τ₂).
    Defined.

    Definition hor_cyl_twosided_disp_cat_id_comp
      : twosided_disp_cat_id_comp hor_cyl_twosided_disp_cat_ob_mor.
    Proof.
      split.
      - intros h k s ; cbn.
        rewrite dwhisker_square_id.
        rewrite uwhisker_square_id.
        apply idpath.
      - intros h₁ h₂ h₃ k₁ k₂ k₃ s₁ s₂ s₃ τ₁ τ₂ θ₁ θ₂ p q ; cbn in *.
        rewrite uwhisker_square_comp.
        rewrite dwhisker_square_comp.
        rewrite p.
        rewrite dwhisker_uwhisker_square.
        rewrite q.
        apply idpath.
    Qed.

    Definition hor_cyl_twosided_disp_cat_data
      : twosided_disp_cat_data (hom_h w y) (hom_h x z).
    Proof.
      simple refine (_ ,, _).
      - exact hor_cyl_twosided_disp_cat_ob_mor.
      - exact hor_cyl_twosided_disp_cat_id_comp.
    Defined.

    Proposition hor_cyl_twosided_disp_cat_axioms
      : twosided_disp_cat_axioms hor_cyl_twosided_disp_cat_data.
    Proof.
      repeat split.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isasetaprop.
        apply isaset_square_double_bicat.
    Qed.

    Definition hor_cyl_twosided_disp_cat
      : twosided_disp_cat (hom_h w y) (hom_h x z).
    Proof.
      simple refine (_ ,, _).
      - exact hor_cyl_twosided_disp_cat_data.
      - exact hor_cyl_twosided_disp_cat_axioms.
    Defined.

    Proposition is_univalent_hor_cyl_twosided_disp_cat
      : is_univalent_twosided_disp_cat hor_cyl_twosided_disp_cat.
    Proof.
      intros h₁ h₂ k₁ k₂ p₁ p₂ s₁ s₂.
      induction p₁, p₂ ; cbn.
      use isweqimplimpl.
      - intros f.
        pose (p := pr1 f) ; cbn in p.
        rewrite uwhisker_square_id in p.
        rewrite dwhisker_square_id in p.
        exact p.
      - apply isaset_square_double_bicat.
      - use isaproptotal2.
        + intro.
          apply isaprop_is_iso_twosided_disp.
        + intros.
          apply isaset_square_double_bicat.
    Qed.
  End HorCyl.

  (** * 6. The underlying category of squares and vertical cylinders *)
  Section VerCyl.
    Context {w x y z : B}
            (h₁ : w --> x)
            (h₂ : y --> z).

    Definition ver_cyl_twosided_disp_cat_ob_mor
      : twosided_disp_cat_ob_mor (hom_v w y) (hom_v x z).
    Proof.
      simple refine (_ ,, _).
      - exact (λ (v₁ : w -|-> y) (v₂ : x -|-> z), square_double_bicat h₁ h₂ v₁ v₂).
      - exact (λ (u₁ u₂ : w -|-> y) (v₁ v₂ : x -|-> z)
                 (s₁ : square_double_bicat h₁ h₂ u₁ v₁)
                 (s₂ : square_double_bicat h₁ h₂ u₂ v₂)
                 (τ₁ : u₁ =|=> u₂)
                 (τ₂ : v₁ =|=> v₂),
               is_ver_cylinder s₁ s₂ τ₁ τ₂).
    Defined.

    Definition ver_cyl_twosided_disp_cat_id_comp
      : twosided_disp_cat_id_comp ver_cyl_twosided_disp_cat_ob_mor.
    Proof.
      split.
      - intros h k s ; cbn.
        rewrite lwhisker_square_id.
        rewrite rwhisker_square_id.
        apply idpath.
      - intros u₁ u₂ u₃ v₁ v₂ v₃ s₁ s₂ s₃ τ₁ τ₂ θ₁ θ₂ p q ; cbn in *.
        rewrite lwhisker_square_comp.
        rewrite rwhisker_square_comp.
        rewrite q.
        rewrite <- rwhisker_lwhisker_square.
        rewrite p.
        apply idpath.
    Qed.

    Definition ver_cyl_twosided_disp_cat_data
      : twosided_disp_cat_data (hom_v w y) (hom_v x z).
    Proof.
      simple refine (_ ,, _).
      - exact ver_cyl_twosided_disp_cat_ob_mor.
      - exact ver_cyl_twosided_disp_cat_id_comp.
    Defined.

    Proposition ver_cyl_twosided_disp_cat_axioms
      : twosided_disp_cat_axioms ver_cyl_twosided_disp_cat_data.
    Proof.
      repeat split.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isaset_square_double_bicat.
      - intro ; intros.
        apply isasetaprop.
        apply isaset_square_double_bicat.
    Qed.

    Definition ver_cyl_twosided_disp_cat
      : twosided_disp_cat (hom_v w y) (hom_v x z).
    Proof.
      simple refine (_ ,, _).
      - exact ver_cyl_twosided_disp_cat_data.
      - exact ver_cyl_twosided_disp_cat_axioms.
    Defined.

    Proposition is_univalent_ver_cyl_twosided_disp_cat
      : is_univalent_twosided_disp_cat ver_cyl_twosided_disp_cat.
    Proof.
      intros u₁ u₂ v₁ v₂ p₁ p₂ s₁ s₂.
      induction p₁, p₂ ; cbn.
      use isweqimplimpl.
      - intros f.
        pose (p := pr1 f) ; cbn in p.
        rewrite lwhisker_square_id in p.
        rewrite rwhisker_square_id in p.
        exact (!p).
      - apply isaset_square_double_bicat.
      - use isaproptotal2.
        + intro.
          apply isaprop_is_iso_twosided_disp.
        + intros.
          apply isaset_square_double_bicat.
    Qed.
  End VerCyl.
End UnderlyingCategories.
