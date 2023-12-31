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
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.

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





(* file on derived laws *)
Proposition lunitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_v_square_bicat h₁ ⋆v s
    =
    linvunitor v₂ ▹s (lunitor v₁ ◃s s).
Proof.
  rewrite lunitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : lunitor v₂ ▹s (linvunitor v₁ ◃s id_v_square_bicat h₁ ⋆v s)
    =
    s.
Proof.
  rewrite lunitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !linvunitor_lunitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_h_square_bicat v₁ ⋆h s
    =
    linvunitor h₂ ▿s (lunitor h₁ ▵s s).
Proof.
  rewrite <- lunitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆v id_v_square_bicat h₂
    =
    rinvunitor v₂ ▹s (runitor v₁ ◃s s).
Proof.
  rewrite runitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor v₂ ▹s (rinvunitor v₁ ◃s s ⋆v id_v_square_bicat h₂)
    =
    s.
Proof.
  rewrite runitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆h id_h_square_bicat v₂
    =
    rinvunitor h₂ ▿s (runitor h₁ ▵s s).
Proof.
  rewrite <- runitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor h₂ ▿s (rinvunitor h₁ ▵s s ⋆h id_h_square_bicat v₂)
    =
    s.
Proof.
  rewrite runitor_h_comp_square'.
  rewrite !dwhisker_uwhisker_square.
  rewrite <- uwhisker_square_comp.
  rewrite <- dwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite dwhisker_square_id.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.



(* file on cells and squares *)
Section VerticalCellsAreSquares.
  Context {B : verity_double_bicat}
          (HB : vertical_cells_are_squares B).

  Definition vertical_cell_to_square_weq
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : v₁ =|=> v₂ ≃ square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := make_weq _ (HB x y v₁ v₂).

  Definition square_to_vertical_cell
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
    : v₁ =|=> v₂
    := invmap (vertical_cell_to_square_weq v₁ v₂) s.

  Proposition square_to_vertical_cell_to_square
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (s : square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
    : vertical_cell_to_square (square_to_vertical_cell s) = s.
  Proof.
    apply (homotweqinvweq (vertical_cell_to_square_weq v₁ v₂)).
  Qed.

  Proposition vertical_cell_to_square_to_vertical_cell
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (τ : v₁ =|=> v₂)
    : square_to_vertical_cell (vertical_cell_to_square τ) = τ.
  Proof.
    apply (homotinvweqweq (vertical_cell_to_square_weq v₁ v₂)).
  Qed.

  Proposition vertical_cell_to_square_id
              {x y : B}
              (v : x -|-> y)
    : vertical_cell_to_square (id₂ v) = id_h_square_bicat v.
  Proof.
    unfold vertical_cell_to_square.
    rewrite lwhisker_square_id.
    apply idpath.
  Qed.

  Proposition square_to_vertical_cell_id
              {x y : B}
              (v : x -|-> y)
    : square_to_vertical_cell (id_h_square_bicat v) = id2 v.
  Proof.
    use (invmaponpathsweq (vertical_cell_to_square_weq v v)) ; cbn.
    rewrite square_to_vertical_cell_to_square.
    rewrite vertical_cell_to_square_id.
    apply idpath.
  Qed.

  Definition comp_ver_globular_square
             {x y : B}
             {v₁ v₂ v₃ : x -|-> y}
             (s₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
             (s₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₃)
    : square_double_bicat (id₁ _) (id₁ _) v₁ v₃
    := linvunitor _ ▵s (lunitor _ ▿s s₁ ⋆h s₂).

  Proposition vertical_cell_to_square_comp
              {x y : B}
              {v₁ v₂ v₃ : x -|-> y}
              (τ : v₁ =|=> v₂)
              (θ : v₂ =|=> v₃)
    : vertical_cell_to_square (τ • θ)
      =
      comp_ver_globular_square
        (vertical_cell_to_square τ)
        (vertical_cell_to_square θ).
  Proof.
    unfold vertical_cell_to_square, comp_ver_globular_square.
    rewrite lwhisker_square_comp.
    rewrite lrwhisker_hcomp_square.
    rewrite runitor_h_comp_square'.
    rewrite <- dwhisker_square_comp.
    rewrite lunitor_runitor_identity.
    rewrite rinvunitor_runitor.
    rewrite dwhisker_square_id.
    rewrite <- uwhisker_square_comp.
    rewrite runitor_lunitor_identity.
    rewrite linvunitor_lunitor.
    rewrite uwhisker_square_id.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_id_h_square.
    apply idpath.
  Qed.

  Proposition square_to_vertical_cell_comp
              {x y : B}
              {v₁ v₂ v₃ : x -|-> y}
              (s₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
              (s₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₃)
    : square_to_vertical_cell (comp_ver_globular_square s₁ s₂)
      =
      square_to_vertical_cell s₁ • square_to_vertical_cell s₂.
  Proof.
    use (invmaponpathsweq (vertical_cell_to_square_weq v₁ v₃)) ; cbn.
    rewrite vertical_cell_to_square_comp.
    rewrite !square_to_vertical_cell_to_square.
    apply idpath.
  Qed.

  Definition invertible_vertical_square_data
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : UU
    := (square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
       ×
       (square_double_bicat (id₁ _) (id₁ _) v₂ v₁).

  Definition make_invertible_vertical_square_data
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂)
             (s₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₁)
    : invertible_vertical_square_data v₁ v₂
    := s₁ ,, s₂.

  Coercion cell_of_invertible_vertical_square
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (s : invertible_vertical_square_data v₁ v₂)
    : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := pr1 s.

  Definition inv_of_invertible_vertical_square
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square_data v₁ v₂)
    : square_double_bicat (id₁ _) (id₁ _) v₂ v₁
    := pr2 s.

  Definition invertible_vertical_square_laws
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square_data v₁ v₂)
    : UU
    := (comp_ver_globular_square
          s
          (inv_of_invertible_vertical_square s)
        =
        id_h_square_bicat v₁)
       ×
       (comp_ver_globular_square
          (inv_of_invertible_vertical_square s)
          s
        =
        id_h_square_bicat v₂).

  Definition invertible_vertical_square
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : UU
    := ∑ (s : invertible_vertical_square_data v₁ v₂),
       invertible_vertical_square_laws s.

  Definition make_invertible_vertical_square
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square_data v₁ v₂)
             (H : invertible_vertical_square_laws s)
    : invertible_vertical_square v₁ v₂
    := s ,, H.

  Coercion invertible_vertical_square_to_data
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (s : invertible_vertical_square v₁ v₂)
    : invertible_vertical_square_data v₁ v₂
    := pr1 s.

  Proposition invertible_vertical_square_inv_right
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (s : invertible_vertical_square v₁ v₂)
    : comp_ver_globular_square
        s
        (inv_of_invertible_vertical_square s)
      =
      id_h_square_bicat v₁.
  Proof.
    exact (pr12 s).
  Qed.

  Proposition invertible_vertical_square_inv_left
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (s : invertible_vertical_square v₁ v₂)
    : comp_ver_globular_square
        (inv_of_invertible_vertical_square s)
        s
      =
      id_h_square_bicat v₂.
  Proof.
    exact (pr22 s).
  Qed.

  Definition vertical_square_to_invertible_2cell
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square v₁ v₂)
    : invertible_2cell v₁ v₂.
  Proof.
    use make_invertible_2cell.
    - use square_to_vertical_cell.
      exact s.
    - use make_is_invertible_2cell.
      + use square_to_vertical_cell.
        exact (inv_of_invertible_vertical_square s).
      + abstract
          (rewrite <- square_to_vertical_cell_comp ;
           rewrite <- square_to_vertical_cell_id ;
           apply maponpaths ;
           apply invertible_vertical_square_inv_right).
      + abstract
          (rewrite <- square_to_vertical_cell_comp ;
           rewrite <- square_to_vertical_cell_id ;
           apply maponpaths ;
           apply invertible_vertical_square_inv_left).
  Defined.
End VerticalCellsAreSquares.

Section HorizontalCellsAreSquares.
  Context {B : verity_double_bicat}
          (HB : horizontal_cells_are_squares B).

  Definition horizontal_cell_to_square_weq
             {x y : B}
             (h₁ h₂ : x --> y)
    : h₁ ==> h₂ ≃ square_double_bicat h₁ h₂ (id₁ _) (id₁ _)
    := make_weq _ (HB x y h₁ h₂).

  Definition square_to_horizontal_cell
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
    : h₁ ==> h₂
    := invmap (horizontal_cell_to_square_weq h₁ h₂) s.

  Proposition square_to_horizontal_cell_to_square
              {x y : B}
              {h₁ h₂ : x --> y}
              (s : square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
    : horizontal_cell_to_square (square_to_horizontal_cell s) = s.
  Proof.
    apply (homotweqinvweq (horizontal_cell_to_square_weq h₁ h₂)).
  Qed.

  Proposition horizontal_cell_to_square_to_horizontal_cell
              {x y : B}
              {h₁ h₂ : x --> y}
              (τ : h₁ ==> h₂)
    : square_to_horizontal_cell (horizontal_cell_to_square τ) = τ.
  Proof.
    apply (homotinvweqweq (horizontal_cell_to_square_weq h₁ h₂)).
  Qed.

  Proposition horizontal_cell_to_square_id
              {x y : B}
              (h : x --> y)
    : horizontal_cell_to_square (id₂ h) = id_v_square_bicat h.
  Proof.
    unfold horizontal_cell_to_square.
    rewrite uwhisker_square_id.
    apply idpath.
  Qed.

  Proposition square_to_horizontal_cell_id
              {x y : B}
              (h : x --> y)
    : square_to_horizontal_cell (id_v_square_bicat h) = id2 h.
  Proof.
    use (invmaponpathsweq (horizontal_cell_to_square_weq h h)) ; cbn.
    rewrite square_to_horizontal_cell_to_square.
    rewrite horizontal_cell_to_square_id.
    apply idpath.
  Qed.

  Definition comp_hor_globular_square
             {x y : B}
             {h₁ h₂ h₃ : x --> y}
             (s₁ : square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
             (s₂ : square_double_bicat h₂ h₃ (id₁ _) (id₁ _))
    : square_double_bicat h₁ h₃ (id₁ _) (id₁ _)
    := linvunitor _ ◃s (lunitor _ ▹s s₁ ⋆v s₂).

  Proposition horizontal_cell_to_square_comp
              {x y : B}
              {h₁ h₂ h₃ : x --> y}
              (τ : h₁ ==> h₂)
              (θ : h₂ ==> h₃)
    : horizontal_cell_to_square (τ • θ)
      =
      comp_hor_globular_square
        (horizontal_cell_to_square τ)
        (horizontal_cell_to_square θ).
  Proof.
    unfold horizontal_cell_to_square, comp_hor_globular_square.
    rewrite uwhisker_square_comp.
    rewrite ud_whisker_vcomp_square.
    rewrite runitor_v_comp_square'.
    rewrite <- rwhisker_square_comp.
    rewrite lunitor_runitor_identity.
    rewrite rinvunitor_runitor.
    rewrite rwhisker_square_id.
    rewrite <- lwhisker_square_comp.
    rewrite runitor_lunitor_identity.
    rewrite linvunitor_lunitor.
    rewrite lwhisker_square_id.
    rewrite dwhisker_uwhisker_square.
    rewrite <- uwhisker_id_v_square.
    apply idpath.
  Qed.

  Proposition square_to_horizontal_cell_comp
              {x y : B}
              {h₁ h₂ h₃ : x --> y}
              (s₁ : square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
              (s₂ : square_double_bicat h₂ h₃ (id₁ _) (id₁ _))
    : square_to_horizontal_cell (comp_hor_globular_square s₁ s₂)
      =
      square_to_horizontal_cell s₁ • square_to_horizontal_cell s₂.
  Proof.
    use (invmaponpathsweq (horizontal_cell_to_square_weq h₁ h₃)) ; cbn.
    rewrite horizontal_cell_to_square_comp.
    rewrite !square_to_horizontal_cell_to_square.
    apply idpath.
  Qed.

  Definition invertible_horizontal_square_data
             {x y : B}
             (h₁ h₂ : x --> y)
    : UU
    := (square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
       ×
       (square_double_bicat h₂ h₁ (id₁ _) (id₁ _)).

  Definition make_invertible_horizontal_square_data
             {x y : B}
             {h₁ h₂ : x --> y}
             (s₁ : square_double_bicat h₁ h₂ (id₁ _) (id₁ _))
             (s₂ : square_double_bicat h₂ h₁ (id₁ _) (id₁ _))
    : invertible_horizontal_square_data h₁ h₂
    := s₁ ,, s₂.

  Coercion cell_of_invertible_horizontal_square
           {x y : B}
           {h₁ h₂ : x --> y}
           (s : invertible_horizontal_square_data h₁ h₂)
    : square_double_bicat h₁ h₂ (id₁ _) (id₁ _)
    := pr1 s.

  Definition inv_of_invertible_horizontal_square
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square_data h₁ h₂)
    : square_double_bicat h₂ h₁ (id₁ _) (id₁ _)
    := pr2 s.

  Definition invertible_horizontal_square_laws
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square_data h₁ h₂)
    : UU
    := (comp_hor_globular_square
          s
          (inv_of_invertible_horizontal_square s)
        =
        id_v_square_bicat h₁)
       ×
       (comp_hor_globular_square
          (inv_of_invertible_horizontal_square s)
          s
        =
        id_v_square_bicat h₂).

  Definition invertible_horizontal_square
             {x y : B}
             (h₁ h₂ : x --> y)
    : UU
    := ∑ (s : invertible_horizontal_square_data h₁ h₂),
       invertible_horizontal_square_laws s.

  Definition make_invertible_horizontal_square
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square_data h₁ h₂)
             (H : invertible_horizontal_square_laws s)
    : invertible_horizontal_square h₁ h₂
    := s ,, H.

  Coercion invertible_horizontal_square_to_data
           {x y : B}
           {h₁ h₂ : x --> y}
           (s : invertible_horizontal_square h₁ h₂)
    : invertible_horizontal_square_data h₁ h₂
    := pr1 s.

  Proposition invertible_horizontal_square_inv_right
              {x y : B}
              {h₁ h₂ : x --> y}
              (s : invertible_horizontal_square h₁ h₂)
    : comp_hor_globular_square
        s
        (inv_of_invertible_horizontal_square s)
      =
      id_v_square_bicat h₁.
  Proof.
    exact (pr12 s).
  Qed.

  Proposition invertible_horizontal_square_inv_left
              {x y : B}
              {h₁ h₂ : x --> y}
              (s : invertible_horizontal_square h₁ h₂)
    : comp_hor_globular_square
        (inv_of_invertible_horizontal_square s)
        s
      =
      id_v_square_bicat h₂.
  Proof.
    exact (pr22 s).
  Qed.

  Definition horizontal_square_to_invertible_2cell
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square h₁ h₂)
    : invertible_2cell h₁ h₂.
  Proof.
    use make_invertible_2cell.
    - use square_to_horizontal_cell.
      exact s.
    - use make_is_invertible_2cell.
      + use square_to_horizontal_cell.
        exact (inv_of_invertible_horizontal_square s).
      + abstract
          (rewrite <- square_to_horizontal_cell_comp ;
           rewrite <- square_to_horizontal_cell_id ;
           apply maponpaths ;
           apply invertible_horizontal_square_inv_right).
      + abstract
          (rewrite <- square_to_horizontal_cell_comp ;
           rewrite <- square_to_horizontal_cell_id ;
           apply maponpaths ;
           apply invertible_horizontal_square_inv_left).
  Defined.
End HorizontalCellsAreSquares.



(* file on companions *)
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Section CompanionPairs.
  Context {B : verity_double_bicat}.

  Definition are_companions
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
    : UU
    := ∑ (φ : square_double_bicat h (id₁ _) v (id₁ _))
         (ψ : square_double_bicat (id₁ _) h (id₁ _) v),
       (runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
       ×
       (runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _).

  Definition make_are_companions
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (φ : square_double_bicat h (id₁ _) v (id₁ _))
             (ψ : square_double_bicat (id₁ _) h (id₁ _) v)
             (p : runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
             (q : runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _)
    : are_companions h v
    := φ ,, ψ ,, p ,, q.

  Definition unit_are_companions
             {x y : B}
             {h : x --> y}
             {v : x -|-> y}
             (c : are_companions h v)
    : square_double_bicat h (id₁ _) v (id₁ _)
    := pr1 c.

  Definition counit_are_companions
             {x y : B}
             {h : x --> y}
             {v : x -|-> y}
             (c : are_companions h v)
    : square_double_bicat (id₁ _) h (id₁ _) v
    := pr12 c.

  Proposition are_companions_left
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

  Definition id_are_companions
             (x : B)
    : are_companions (id₁ x) (id₁ _).
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

  Section CompCompanions.
    Context {x y z : B}
            {h₁ : x --> y}
            {h₂ : y --> z}
            {v₁ : x -|-> y}
            {v₂ : y -|-> z}
            (c₁ : are_companions h₁ v₁)
            (c₂ : are_companions h₂ v₂).

    Let φ₁ : square_double_bicat h₁ (id₁ y) v₁ (id₁ _) := unit_are_companions c₁.
    Let ψ₁ : square_double_bicat (id₁ x) h₁ (id₁ _) v₁ := counit_are_companions c₁.
    Let φ₂ : square_double_bicat h₂ (id₁ z) v₂ (id₁ _) := unit_are_companions c₂.
    Let ψ₂ : square_double_bicat (id₁ y) h₂ (id₁ _) v₂ := counit_are_companions c₂.

    Definition comp_are_companions_unit
      : square_double_bicat (h₁ · h₂) (id₁ z) (v₁ · v₂) (id₁ _)
      := lunitor _ ▹s (lunitor _ ▿s ((φ₁ ⋆h id_v_square_bicat h₂)
                                     ⋆v
                                     (id_h_square_bicat v₂ ⋆h φ₂))).

    Let φ : square_double_bicat (h₁ · h₂) (id₁ z) (v₁ · v₂) (id₁ _)
      := comp_are_companions_unit.

    Definition comp_are_companions_counit
      : square_double_bicat (id₁ x) (h₁ · h₂) (id₁ _) (v₁ · v₂)
      := linvunitor _ ◃s (linvunitor _ ▵s ((ψ₁ ⋆h id_h_square_bicat _)
                                           ⋆v
                                           (id_v_square_bicat h₁ ⋆h ψ₂))).

    Let ψ : square_double_bicat (id₁ x) (h₁ · h₂) (id₁ _) (v₁ · v₂)
      := comp_are_companions_counit.

    Proposition comp_are_companions_left
      : runitor (v₁ · v₂) ▹s (linvunitor (v₁ · v₂) ◃s ψ ⋆v φ)
        =
        id_h_square_bicat (v₁ · v₂).
    Proof.
    Admitted.

    Proposition comp_are_companions_right
      : runitor (h₁ · h₂) ▿s (linvunitor (h₁ · h₂) ▵s ψ ⋆h φ)
        =
        id_v_square_bicat (h₁ · h₂).
    Proof.
    Admitted.

    Definition comp_are_companions
      : are_companions (h₁ · h₂) (v₁ · v₂).
    Proof.
      use make_are_companions.
      - exact φ.
      - exact ψ.
      - exact comp_are_companions_left.
      - exact comp_are_companions_right.
    Defined.
  End CompCompanions.

  Definition cell_are_companions
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
      rewrite lrwhisker_hcomp_square.
      rewrite <- rwhisker_square_comp.
      apply idpath.
    }
  Admitted.

  Definition inv2cell_are_companions
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

  Section CompanionOfAdjequiv.
    Context (H : vertical_cells_are_squares B)
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
            (Hh : left_adjoint_equivalence h)
            {v' : y -|-> x}
            (c' : are_companions (left_adjoint_right_adjoint Hh) v').

    Let h' : y --> x := left_adjoint_right_adjoint Hh.
    Let η : invertible_2cell (id₁ x) (h · h')
      := left_equivalence_unit_iso Hh.
    Let ε : invertible_2cell (h' · h) (id₁ y)
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

  Definition square_between_companions
             {x y : B}
             {h : x --> y}
             {v₁ v₂ : x -|-> y}
             (c₁ : are_companions h v₁)
             (c₂ : are_companions h v₂)
    : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := linvunitor _ ◃s (runitor _ ▹s counit_are_companions c₂ ⋆v unit_are_companions c₁).

  (*
  Section ComparionPairUnique.
    Context {x y : B}
            {h : x --> y}
            {v₁ v₂ : x -|-> y}
            (c₁ : are_companions h v₁)
            (c₂ : are_companions h v₂).

    Let γ₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
      := square_between_companions c₁ c₂.

    Let γ₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₁
      := square_between_companions c₂ c₁.

    Definition koe
      : lunitor _ ▿s (rinvunitor _ ▵s γ₁ ⋆h γ₂) = id_h_square_bicat v₁.
    Proof.
      unfold γ₁, γ₂, square_between_companions.
      pose (p₁ := are_companions_left c₁).
      refine (_ @ p₁).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- lwhisker_hcomp_square.
        apply maponpaths.
        rewrite lrwhisker_hcomp_square.
        rewrite <- rwhisker_hcomp_square.
        apply idpath.
      }
      rewrite <- rwhisker_lwhisker_square.
      rewrite <- rwhisker_uwhisker_square.
      rewrite <- rwhisker_dwhisker_square.
      apply maponpaths.
      rewrite <- lwhisker_uwhisker_square.
      rewrite <- lwhisker_dwhisker_square.
      apply maponpaths.
      refine (!_).

      pose (q₂ := are_companions_right c₂).
      rewrite <-


        Check double_bicat_interchange.

        assert UU.
        {
          refine ((counit_are_companions c₂ ⋆v unit_are_companions c₁)
                  ⋆h
                  (counit_are_companions c₁ ⋆v unit_are_companions c₂)
                  =
                 _).
          Search comp_h_square_bicat.

        rewrite lrwhisker_hcomp_square.
        rewrite rwhisker_square_comp.
        rewrite double_bicat_interchange.
      cbn.
      refine ().
      Check γ₂ ⋆h γ₁.
      Check γ₁ ⋆h γ₂.
  End ComparionPairUnique.
   *)
End CompanionPairs.

Definition all_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y),
     ∑ (v : x -|-> y), are_companions h v.

Definition all_equivs_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y)
       (Hh : left_adjoint_equivalence h),
     ∑ (v : x -|-> y), are_companions h v.

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



Require Import UniMath.Bicategories.Core.AdjointUnique.

Section GregariousEquivalence.
  Context {B : verity_double_bicat}.

  Definition is_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
    : UU
    := are_companions h v
       ×
       left_adjoint_equivalence h
       ×
       left_adjoint_equivalence v.

  Coercion is_gregarious_equivalence_to_are_companions
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (H : is_gregarious_equivalence h v)
    : are_companions h v
    := pr1 H.

  Definition gregarious_equivalence
             (x y : B)
    : UU
    := ∑ (h : x --> y)
         (v : x -|-> y),
       is_gregarious_equivalence h v.

  Definition make_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (H : is_gregarious_equivalence h v)
    : gregarious_equivalence x y
    := h ,, v ,, H.

  Definition id_is_gregarious_equivalence
             (x : B)
    : is_gregarious_equivalence (id₁ x) (id₁ _).
  Proof.
    repeat split.
    - apply id_are_companions.
    - apply internal_adjoint_equivalence_identity.
    - apply internal_adjoint_equivalence_identity.
  Defined.

  Definition id_gregarious_equivalence
             (x : B)
    : gregarious_equivalence x x.
  Proof.
    use make_gregarious_equivalence.
    - apply id₁.
    - apply id₁.
    - apply id_is_gregarious_equivalence.
  Defined.

  Definition id_to_gregarious_equivalence
             {x y : B}
             (p : x = y)
    : gregarious_equivalence x y.
  Proof.
    induction p.
    exact (id_gregarious_equivalence x).
  Defined.

  Definition is_hor_gregarious_equivalence
             {x y : B}
             (h : x --> y)
    : UU
    := ∑ (v : x -|-> y), is_gregarious_equivalence h v.

  Coercion is_hor_gregarious_equivalence_to_mor
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : x -|-> y
    := pr1 v.

  Coercion is_hor_gregarious_equivalence_to_is_gregarious_equivalence
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : is_gregarious_equivalence h v
    := pr2 v.

  Lemma path_is_hor_gregarious_equivalence
        (HB_2_1 : is_univalent_2_1 B)
        (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
        {x y : B}
        {h : x --> y}
        (φ₁ φ₂ : is_hor_gregarious_equivalence h)
        (p : pr1 φ₁ = pr1 φ₂)
        (q₁ : lunitor _ ▿s (linvunitor _ ▵s vertical_cell_to_square (idtoiso_2_1 (C := ver_bicat_of_verity_double_bicat B) _ _ p)
             ⋆h
             unit_are_companions φ₂) = unit_are_companions φ₁)
        (q₂ : runitor _ ▿s (linvunitor _ ▵s counit_are_companions φ₁ ⋆h vertical_cell_to_square (idtoiso_2_1 (C := ver_bicat_of_verity_double_bicat B) _ _ p)) = counit_are_companions φ₂)
    : φ₁ = φ₂.
  Proof.
    induction φ₁ as [ v₁ [ c₁ [ Hh₁ Hv₁ ] ] ].
    induction φ₂ as [ v₂ [ c₂ [ Hh₂ Hv₂ ] ] ].
    cbn in p.
    induction p.
    cbn in *.
    apply maponpaths.
    repeat (use dirprodeq).
    - cbn.
      use eq_are_companions.
      + refine (!q₁ @ _).
        unfold vertical_cell_to_square.
        rewrite lwhisker_square_id.
        rewrite lunitor_h_comp_square'.
        rewrite !dwhisker_uwhisker_square.
        rewrite <- uwhisker_square_comp.
        rewrite <- dwhisker_square_comp.
        rewrite !linvunitor_lunitor.
        rewrite uwhisker_square_id, dwhisker_square_id.
        apply idpath.
      + refine (_ @ q₂).
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
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1.
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1'.
  Qed.

  Proposition isaprop_is_hor_gregarious_equivalence
              (H : vertical_cells_are_squares B)
              (HB_2_1 : is_univalent_2_1 B)
              (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
              {x y : B}
              (h : x --> y)
    : isaprop (is_hor_gregarious_equivalence h).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use (path_is_hor_gregarious_equivalence HB_2_1 HB_2_1').
    - use (isotoid_2_1 HB_2_1').
      use (vertical_square_to_invertible_2cell H).
      use make_invertible_vertical_square.
      + use make_invertible_vertical_square_data.
        * use (square_between_companions φ₁).
          apply (pr12 φ₂).
        * use (square_between_companions φ₂).
          apply (pr12 φ₁).
      + admit.
    - rewrite idtoiso_2_1_isotoid_2_1.
      cbn.
      rewrite square_to_vertical_cell_to_square.
      unfold square_between_companions.
      admit.
    - rewrite idtoiso_2_1_isotoid_2_1.
      cbn.
      rewrite square_to_vertical_cell_to_square.
      unfold square_between_companions.
      admit.
  Admitted.

  Definition hor_left_adjoint_equivalence_to_gregarious_equivalence
             (H : vertical_cells_are_squares B)
             (H' : all_equivs_companions B)
             {x y : B}
             (h : x --> y)
             (Hh : left_adjoint_equivalence h)
    : is_hor_gregarious_equivalence h.
  Proof.
    pose (c := H' _ _ h Hh).
    induction c as [ v c ].
    refine (v ,, _).
    repeat split.
    - exact c.
    - exact Hh.
    - use all_equivs_companions_adjequiv.
      + exact H.
      + exact H'.
      + exact h.
      + exact c.
      + exact Hh.
  Qed.

  Definition hor_gregarious_equivalence_to_left_adjoint_equivalence
             {x y : B}
             (h : x --> y)
             (Hh : is_hor_gregarious_equivalence h)
    : left_adjoint_equivalence h.
  Proof.
    apply Hh.
  Qed.

  Definition hor_left_adjoint_equivalence_weq_gregarious_equivalence
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : all_equivs_companions B)
             (H' : vertical_cells_are_squares B)
             {x y : B}
             (h : x --> y)
    : left_adjoint_equivalence h ≃ is_hor_gregarious_equivalence h.
  Proof.
    use weqimplimpl.
    - apply (hor_left_adjoint_equivalence_to_gregarious_equivalence H' H).
    - apply hor_gregarious_equivalence_to_left_adjoint_equivalence.
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1.
    - apply (isaprop_is_hor_gregarious_equivalence H' HB_2_1 HB_2_1').
  Qed.
End GregariousEquivalence.



Section Univalence.
  Context (B : verity_double_bicat).

  Definition hor_locally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_1 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_locally_univalent_verity_double_bicat
    : isaprop hor_locally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  Definition ver_locally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_1 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_locally_univalent_verity_double_bicat
    : isaprop ver_locally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  Definition locally_univalent_verity_double_bicat
    : UU
    := hor_locally_univalent_verity_double_bicat
       ×
       ver_locally_univalent_verity_double_bicat.

  Proposition isaprop_locally_univalent_verity_double_bicat
    : isaprop locally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_locally_univalent_verity_double_bicat.
    - exact isaprop_ver_locally_univalent_verity_double_bicat.
  Qed.

  Definition hor_globally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_0 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_globally_univalent_verity_double_bicat
    : isaprop hor_globally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  Definition ver_globally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_0 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_globally_univalent_verity_double_bicat
    : isaprop ver_globally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  Definition globally_univalent_verity_double_bicat
    : UU
    := hor_globally_univalent_verity_double_bicat
       ×
       ver_globally_univalent_verity_double_bicat.

  Proposition isaprop_globally_univalent_verity_double_bicat
    : isaprop globally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_globally_univalent_verity_double_bicat.
    - exact isaprop_ver_globally_univalent_verity_double_bicat.
  Qed.

  Definition gregarious_univalent_verity_double_bicat
    : UU
    := ∏ (x y : B), isweq (@id_to_gregarious_equivalence B x y).

  Proposition isaprop_gregarious_univalent_verity_double_bicat
    : isaprop gregarious_univalent_verity_double_bicat.
  Proof.
    do 2 (use impred ; intro).
    apply isapropisweq.
  Qed.

  Definition hor_globally_univalent_to_gregarious_univalent
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
             (HB : hor_globally_univalent_verity_double_bicat)
      : gregarious_univalent_verity_double_bicat.
  Proof.
    intros x y.
    use weqhomot.
    - refine (weqfibtototal
                _ _
                (hor_left_adjoint_equivalence_weq_gregarious_equivalence HB_2_1 HB_2_1' _ H)
              ∘ make_weq _ (HB x y))%weq.
      use univalent_2_0_all_equivs_companions.
      apply HB.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply (isaprop_is_hor_gregarious_equivalence H HB_2_1 HB_2_1').
      }
      apply idpath.
  Qed.

  Definition gregarious_univalent_to_hor_globally_univalent
             (H' : all_equivs_companions B)
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
             (HB : gregarious_univalent_verity_double_bicat)
    : hor_globally_univalent_verity_double_bicat.
  Proof.
    intros x y.
    use weqhomot.
    - exact (weqfibtototal
               _ _
               (λ h, invweq
                       (hor_left_adjoint_equivalence_weq_gregarious_equivalence
                          HB_2_1 HB_2_1' H' H h))
             ∘ make_weq _ (HB x y))%weq.
      - intro p.
        induction p.
        use subtypePath.
        {
          intro.
          apply isaprop_left_adjoint_equivalence.
          exact HB_2_1.
        }
        apply idpath.
    Qed.

  Definition hor_globally_univalent_weq_gregarious_univalent
             (H' : all_equivs_companions B)
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
    : hor_globally_univalent_verity_double_bicat
      ≃
      gregarious_univalent_verity_double_bicat.
  Proof.
    use weqimplimpl.
    - exact (hor_globally_univalent_to_gregarious_univalent HB_2_1 HB_2_1' H).
    - exact (gregarious_univalent_to_hor_globally_univalent H' HB_2_1 HB_2_1' H).
    - exact isaprop_hor_globally_univalent_verity_double_bicat.
    - exact isaprop_gregarious_univalent_verity_double_bicat.
  Defined.
End Univalence.
