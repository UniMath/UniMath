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
 - The underlying hom-category of vertical morphisms and squares whose horizontal sides
   are identities.
 - The underlying hom-category of horizontal morphisms and squares whose vertical sides
   are identities.
 In this file, we define each of these categories.

 Contents
 1. The underlying horizontal bicategory
 2. The underlying vertical bicategory
 3. The underlying horizontal hom-category
 4. The underlying vertical hom-category
 5. The underlying category of squares and horizontal cylinders
 6. The underlying category of squares and vertical cylinders
 7. The underlying category of vertical morphisms and squares
 8. The underlying category of horizontal morphisms and squares

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
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.

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

  (** * 7. The underlying category of vertical morphisms and squares *)
  Section VHomSquare.
    Context (x y : B).

    Definition hom_v_sq_precategory_ob_mor
      : precategory_ob_mor.
    Proof.
      use make_precategory_ob_mor.
      - exact (x -|-> y).
      - exact (λ (v₁ v₂ : x -|-> y), square_double_bicat (id_h x) (id_h y) v₁ v₂).
    Defined.

    Definition hom_v_sq_precategory_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - exact hom_v_sq_precategory_ob_mor.
      - exact (λ v, id_h_square_bicat v).
      - exact (λ _ _ _ s₁ s₂, comp_ver_globular_square s₁ s₂).
    Defined.

    Proposition hom_v_sq_precategory_laws
      : is_precategory hom_v_sq_precategory_data.
    Proof.
      use make_is_precategory_one_assoc.
      - intros v₁ v₂ s ; cbn.
        rewrite lunitor_h_comp_square'.
        rewrite <- dwhisker_square_comp.
        rewrite linvunitor_lunitor.
        rewrite dwhisker_square_id.
        rewrite <- uwhisker_square_comp.
        rewrite linvunitor_lunitor.
        rewrite uwhisker_square_id.
        apply idpath.
      - intros v₁ v₂ s ; cbn.
        rewrite runitor_h_comp_square'.
        rewrite <- dwhisker_square_comp.
        rewrite lunitor_runitor_identity.
        rewrite rinvunitor_runitor.
        rewrite dwhisker_square_id.
        rewrite runitor_lunitor_identity.
        rewrite <- uwhisker_square_comp.
        rewrite linvunitor_lunitor.
        rewrite uwhisker_square_id.
        apply idpath.
      - intros v₁ v₂ v₃ v₄ s₁ s₂ s₃ ; cbn.
        do 2 apply maponpaths.
        rewrite r_uwhisker_h_comp_square.
        rewrite r_dwhisker_h_comp_square.
        rewrite l_uwhisker_h_comp_square.
        rewrite l_dwhisker_h_comp_square.
        rewrite lassociator_h_comp_square'.
        rewrite !dwhisker_uwhisker_square.
        rewrite <- uwhisker_square_comp.
        rewrite <- !dwhisker_square_comp.
        use eq_uwhisker_square.
        {
          rewrite lwhisker_hcomp.
          rewrite triangle_l_inv.
          rewrite <- rwhisker_hcomp.
          rewrite lunitor_V_id_is_left_unit_V_id.
          apply idpath.
        }
        use eq_dwhisker_square.
        {
          rewrite lunitor_lwhisker.
          rewrite runitor_lunitor_identity.
          apply idpath.
        }
        apply idpath.
    Qed.

    Definition hom_v_sq_precategory
      : precategory.
    Proof.
      use make_precategory.
      - exact hom_v_sq_precategory_data.
      - exact hom_v_sq_precategory_laws.
    Defined.

    Definition hom_v_sq
      : category.
    Proof.
      use make_category.
      - exact hom_v_sq_precategory.
      - abstract
          (intros v w ;
           apply isaset_square_double_bicat).
    Defined.
  End VHomSquare.

  (** *  8. The underlying category of horizontal morphisms and squares *)
  Section HHomSquare.
    Context (x y : B).

    Definition hom_h_sq_precategory_ob_mor
      : precategory_ob_mor.
    Proof.
      use make_precategory_ob_mor.
      - exact (x --> y).
      - exact (λ (h₁ h₂ : x --> y), square_double_bicat h₁ h₂ (id_v x) (id_v y)).
    Defined.

    Definition hom_h_sq_precategory_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - exact hom_h_sq_precategory_ob_mor.
      - exact (λ h, id_v_square_bicat h).
      - exact (λ _ _ _ s₁ s₂, comp_hor_globular_square s₁ s₂).
    Defined.

    Proposition hom_h_sq_precategory_laws
      : is_precategory hom_h_sq_precategory_data.
    Proof.
      use make_is_precategory_one_assoc.
      - intros h₁ h₂ s ; cbn.
        etrans.
        {
          do 2 apply maponpaths.
          apply lunitor_v_comp_square'.
        }
        rewrite <- rwhisker_square_comp.
        rewrite (linvunitor_lunitor (C := ver_bicat_of_verity_double_bicat)).
        rewrite rwhisker_square_id.
        rewrite <- lwhisker_square_comp.
        rewrite (linvunitor_lunitor (C := ver_bicat_of_verity_double_bicat)).
        rewrite lwhisker_square_id.
        apply idpath.
      - intros v₁ v₂ s ; cbn.
        etrans.
        {
          do 2 apply maponpaths.
          apply runitor_v_comp_square'.
        }
        rewrite <- rwhisker_square_comp.
        rewrite (lunitor_runitor_identity (C := ver_bicat_of_verity_double_bicat)).
        rewrite (rinvunitor_runitor (C := ver_bicat_of_verity_double_bicat)).
        rewrite rwhisker_square_id.
        rewrite <- lwhisker_square_comp.
        rewrite (runitor_lunitor_identity (C := ver_bicat_of_verity_double_bicat)).
        rewrite (linvunitor_lunitor (C := ver_bicat_of_verity_double_bicat)).
        rewrite lwhisker_square_id.
        apply idpath.
      - intros v₁ v₂ v₃ v₄ s₁ s₂ s₃ ; cbn.
        do 2 apply maponpaths.
        rewrite r_lwhisker_v_comp_square.
        rewrite r_rwhisker_v_comp_square.
        rewrite l_lwhisker_v_comp_square.
        rewrite l_rwhisker_v_comp_square.
        etrans.
        {
          do 2 apply maponpaths.
          apply lassociator_v_comp_square''.
        }
        rewrite !rwhisker_lwhisker_square.
        rewrite <- !rwhisker_square_comp.
        rewrite <- !lwhisker_square_comp.
        use eq_lwhisker_square.
        {
          rewrite lwhisker_hcomp.
          rewrite (triangle_l_inv (C := ver_bicat_of_verity_double_bicat)).
          rewrite <- rwhisker_hcomp.
          rewrite (lunitor_V_id_is_left_unit_V_id (C := ver_bicat_of_verity_double_bicat)).
          apply idpath.
        }
        use eq_rwhisker_square.
        {
          rewrite (lunitor_lwhisker (C := ver_bicat_of_verity_double_bicat)).
          apply maponpaths.
          apply (runitor_lunitor_identity (C := ver_bicat_of_verity_double_bicat)).
        }
        apply idpath.
    Qed.

    Definition hom_h_sq_precategory
      : precategory.
    Proof.
      use make_precategory.
      - exact hom_h_sq_precategory_data.
      - exact hom_h_sq_precategory_laws.
    Defined.

    Definition hom_h_sq
      : category.
    Proof.
      use make_category.
      - exact hom_h_sq_precategory.
      - abstract
          (intros v w ;
           apply isaset_square_double_bicat).
    Defined.
  End HHomSquare.
End UnderlyingCategories.
