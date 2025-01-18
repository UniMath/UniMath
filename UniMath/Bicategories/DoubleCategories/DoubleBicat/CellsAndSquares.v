(*****************************************************************************************

 Cells and squares in a Verity double bicategory

 In a Verity double bicategory, there are horizontal 2-cells, vertical 2-cells, and
 squares. It is often the case that  the horizontal and the vertical 2-cells can be
 expressed as certain squares. In this file, we define these conditions and we prove
 properties about such Verity double bicategories.

 Contents
 1. Maps from cells to squares
 2. The conditions that cells can be expressed as certain squares
 3. Verity double bicategories in which vertical cells are the same as squares
 3.1. Identity squares and vertical cells
 3.2. Composition of squares and vertical cells
 3.3. Invertible squares and vertical cells
 4. Verity double bicategories in which horizontal cells are the same as squares
 4.1. Identity squares and horizontal cells
 4.2. Composition of squares and horizontal cells
 4.3. Invertible squares and horizontal cells

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
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Maps from cells to squares *)
Definition vertical_cell_to_square
           {B : verity_double_bicat}
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (τ : v₁ =|=> v₂)
  : square_double_bicat (id_h x) (id_h y) v₁ v₂
  := τ ◃s id_h_square_bicat v₂.

Definition horizontal_cell_to_square
           {B : verity_double_bicat}
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : h₁ ==> h₂)
  : square_double_bicat h₁ h₂ (id_v x) (id_v y)
  := τ ▵s id_v_square_bicat h₂.

(** * 2. The conditions that cells can be expressed as certain squares *)
Definition vertically_saturated
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (v₁ v₂ : x -|-> y),
     isweq (@vertical_cell_to_square B x y v₁ v₂).

Definition horizontally_saturated
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h₁ h₂ : x --> y),
     isweq (@horizontal_cell_to_square B x y h₁ h₂).

Definition is_weak_double_cat
           (B : verity_double_bicat)
  : UU
  := vertically_saturated B × horizontally_saturated B.

(** * 3. Verity double bicategories in which vertical cells are the same as squares *)
Section VerticalCellsAreSquares.
  Context {B : verity_double_bicat}.

  Definition vertical_cell_to_square_weq
             (HB : vertically_saturated B)
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : v₁ =|=> v₂ ≃ square_double_bicat (id_h x) (id_h y) v₁ v₂
    := make_weq _ (HB x y v₁ v₂).

  Definition square_to_vertical_cell
             (HB : vertically_saturated B)
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : square_double_bicat (id_h x) (id_h y) v₁ v₂)
    : v₁ =|=> v₂
    := invmap (vertical_cell_to_square_weq HB v₁ v₂) s.

  Proposition square_to_vertical_cell_to_square
              (HB : vertically_saturated B)
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (s : square_double_bicat (id_h x) (id_h y) v₁ v₂)
    : vertical_cell_to_square (square_to_vertical_cell HB s) = s.
  Proof.
    apply (homotweqinvweq (vertical_cell_to_square_weq HB v₁ v₂)).
  Qed.

  Proposition vertical_cell_to_square_to_vertical_cell
              (HB : vertically_saturated B)
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (τ : v₁ =|=> v₂)
    : square_to_vertical_cell HB (vertical_cell_to_square τ) = τ.
  Proof.
    apply (homotinvweqweq (vertical_cell_to_square_weq HB v₁ v₂)).
  Qed.

  (** * 3.1. Identity squares and vertical cells *)
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
              (HB : vertically_saturated B)
              {x y : B}
              (v : x -|-> y)
    : square_to_vertical_cell HB (id_h_square_bicat v) = id2 v.
  Proof.
    use (invmaponpathsweq (vertical_cell_to_square_weq HB v v)) ; cbn.
    rewrite square_to_vertical_cell_to_square.
    rewrite vertical_cell_to_square_id.
    apply idpath.
  Qed.

  (** * 3.2. Composition of squares and vertical cells *)
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
              (HB : vertically_saturated B)
              {x y : B}
              {v₁ v₂ v₃ : x -|-> y}
              (s₁ : square_double_bicat (id_h x) (id_h y) v₁ v₂)
              (s₂ : square_double_bicat (id_h x) (id_h y) v₂ v₃)
    : square_to_vertical_cell HB (comp_ver_globular_square s₁ s₂)
      =
      square_to_vertical_cell HB s₁ • square_to_vertical_cell HB s₂.
  Proof.
    use (invmaponpathsweq (vertical_cell_to_square_weq HB v₁ v₃)) ; cbn.
    rewrite vertical_cell_to_square_comp.
    rewrite !square_to_vertical_cell_to_square.
    apply idpath.
  Qed.

  (** * 3.3. Invertible squares and vertical cells *)
  Definition invertible_vertical_square_data
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : UU
    := (square_double_bicat (id_h x) (id_h y) v₁ v₂)
       ×
       (square_double_bicat (id_h x) (id_h y) v₂ v₁).

  Definition make_invertible_vertical_square_data
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s₁ : square_double_bicat (id_h x) (id_h y) v₁ v₂)
             (s₂ : square_double_bicat (id_h x) (id_h y) v₂ v₁)
    : invertible_vertical_square_data v₁ v₂
    := s₁ ,, s₂.

  Coercion cell_of_invertible_vertical_square
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (s : invertible_vertical_square_data v₁ v₂)
    : square_double_bicat (id_h x) (id_h y) v₁ v₂
    := pr1 s.

  Definition inv_of_invertible_vertical_square
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square_data v₁ v₂)
    : square_double_bicat (id_h x) (id_h y) v₂ v₁
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

  Proposition isaprop_invertible_vertical_square_laws
              {x y : B}
              {v₁ v₂ : x -|-> y}
              (s : invertible_vertical_square_data v₁ v₂)
    : isaprop (invertible_vertical_square_laws s).
  Proof.
    apply isapropdirprod ; apply isaset_square_double_bicat.
  Qed.

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
             (HB : vertically_saturated B)
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (s : invertible_vertical_square v₁ v₂)
    : invertible_2cell v₁ v₂.
  Proof.
    use make_invertible_2cell.
    - use (square_to_vertical_cell HB).
      exact s.
    - use make_is_invertible_2cell.
      + use (square_to_vertical_cell HB).
        exact (inv_of_invertible_vertical_square s).
      + abstract
          (rewrite <- (square_to_vertical_cell_comp HB) ;
           rewrite <- (square_to_vertical_cell_id HB) ;
           apply maponpaths ;
           apply invertible_vertical_square_inv_right).
      + abstract
          (rewrite <- (square_to_vertical_cell_comp HB) ;
           rewrite <- (square_to_vertical_cell_id HB) ;
           apply maponpaths ;
           apply invertible_vertical_square_inv_left).
  Defined.

  Definition invertible_2cell_to_vertical_square
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (τ : invertible_2cell v₁ v₂)
    : invertible_vertical_square v₁ v₂.
  Proof.
    use make_invertible_vertical_square.
    - use make_invertible_vertical_square_data.
      + exact (vertical_cell_to_square τ).
      + exact (vertical_cell_to_square (τ^-1)).
    - split.
      + abstract
          (cbn -[comp_ver_globular_square] ;
           refine (_ @ vertical_cell_to_square_id _) ;
           rewrite <- vertical_cell_to_square_comp ;
           apply maponpaths ;
           apply (vcomp_rinv τ)).
      + abstract
          (cbn -[comp_ver_globular_square] ;
           refine (_ @ vertical_cell_to_square_id _) ;
           rewrite <- vertical_cell_to_square_comp ;
           apply maponpaths ;
           apply (vcomp_linv τ)).
  Defined.

  Definition vertical_square_weq_invertible_2cell
             (HB : vertically_saturated B)
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : invertible_vertical_square v₁ v₂ ≃ invertible_2cell v₁ v₂.
  Proof.
    use weq_iso.
    - exact (vertical_square_to_invertible_2cell HB).
    - exact invertible_2cell_to_vertical_square.
    - abstract
        (intro s ;
         use subtypePath ; [ intro ; apply isaprop_invertible_vertical_square_laws | ] ;
         use dirprodeq ; apply square_to_vertical_cell_to_square).
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply vertical_cell_to_square_to_vertical_cell).
  Defined.
End VerticalCellsAreSquares.

(** * 4. Verity double bicategories in which horizontal cells are the same as squares *)
Section HorizontalCellsAreSquares.
  Context {B : verity_double_bicat}.

  Definition horizontal_cell_to_square_weq
             (HB : horizontally_saturated B)
             {x y : B}
             (h₁ h₂ : x --> y)
    : h₁ ==> h₂ ≃ square_double_bicat h₁ h₂ (id_v x) (id_v y)
    := make_weq _ (HB x y h₁ h₂).

  Definition square_to_horizontal_cell
             (HB : horizontally_saturated B)
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : square_double_bicat h₁ h₂ (id_v x) (id_v y))
    : h₁ ==> h₂
    := invmap (horizontal_cell_to_square_weq HB h₁ h₂) s.

  Proposition square_to_horizontal_cell_to_square
              (HB : horizontally_saturated B)
              {x y : B}
              {h₁ h₂ : x --> y}
              (s : square_double_bicat h₁ h₂ (id_v x) (id_v y))
    : horizontal_cell_to_square (square_to_horizontal_cell HB s) = s.
  Proof.
    apply (homotweqinvweq (horizontal_cell_to_square_weq HB h₁ h₂)).
  Qed.

  Proposition horizontal_cell_to_square_to_horizontal_cell
              (HB : horizontally_saturated B)
              {x y : B}
              {h₁ h₂ : x --> y}
              (τ : h₁ ==> h₂)
    : square_to_horizontal_cell HB (horizontal_cell_to_square τ) = τ.
  Proof.
    apply (homotinvweqweq (horizontal_cell_to_square_weq HB h₁ h₂)).
  Qed.

  (** * 4.1. Identity squares and horizontal cells *)
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
              (HB : horizontally_saturated B)
              {x y : B}
              (h : x --> y)
    : square_to_horizontal_cell HB (id_v_square_bicat h) = id2 h.
  Proof.
    use (invmaponpathsweq (horizontal_cell_to_square_weq HB h h)) ; cbn.
    rewrite square_to_horizontal_cell_to_square.
    rewrite horizontal_cell_to_square_id.
    apply idpath.
  Qed.

  (** * 4.2. Composition of squares and horizontal cells *)
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
              (HB : horizontally_saturated B)
              {x y : B}
              {h₁ h₂ h₃ : x --> y}
              (s₁ : square_double_bicat h₁ h₂ (id_v x) (id_v y))
              (s₂ : square_double_bicat h₂ h₃ (id_v x) (id_v y))
    : square_to_horizontal_cell HB (comp_hor_globular_square s₁ s₂)
      =
      square_to_horizontal_cell HB s₁ • square_to_horizontal_cell HB s₂.
  Proof.
    use (invmaponpathsweq (horizontal_cell_to_square_weq HB h₁ h₃)) ; cbn.
    rewrite horizontal_cell_to_square_comp.
    rewrite !square_to_horizontal_cell_to_square.
    apply idpath.
  Qed.

  (** * 4.3. Invertible squares and horizontal cells *)
  Definition invertible_horizontal_square_data
             {x y : B}
             (h₁ h₂ : x --> y)
    : UU
    := (square_double_bicat h₁ h₂ (id_v x) (id_v y))
       ×
       (square_double_bicat h₂ h₁ (id_v x) (id_v y)).

  Definition make_invertible_horizontal_square_data
             {x y : B}
             {h₁ h₂ : x --> y}
             (s₁ : square_double_bicat h₁ h₂ (id_v x) (id_v y))
             (s₂ : square_double_bicat h₂ h₁ (id_v x) (id_v y))
    : invertible_horizontal_square_data h₁ h₂
    := s₁ ,, s₂.

  Coercion cell_of_invertible_horizontal_square
           {x y : B}
           {h₁ h₂ : x --> y}
           (s : invertible_horizontal_square_data h₁ h₂)
    : square_double_bicat h₁ h₂ (id_v x) (id_v y)
    := pr1 s.

  Definition inv_of_invertible_horizontal_square
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square_data h₁ h₂)
    : square_double_bicat h₂ h₁ (id_v x) (id_v y)
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

  Proposition isaprop_invertible_horizontal_square_laws
              {x y : B}
              {h₁ h₂ : x --> y}
              (s : invertible_horizontal_square_data h₁ h₂)
    : isaprop (invertible_horizontal_square_laws s).
  Proof.
    apply isapropdirprod ; apply isaset_square_double_bicat.
  Qed.

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
             (HB : horizontally_saturated B)
             {x y : B}
             {h₁ h₂ : x --> y}
             (s : invertible_horizontal_square h₁ h₂)
    : invertible_2cell h₁ h₂.
  Proof.
    use make_invertible_2cell.
    - use (square_to_horizontal_cell HB).
      exact s.
    - use make_is_invertible_2cell.
      + use (square_to_horizontal_cell HB).
        exact (inv_of_invertible_horizontal_square s).
      + abstract
          (rewrite <- (square_to_horizontal_cell_comp HB) ;
           rewrite <- (square_to_horizontal_cell_id HB) ;
           apply maponpaths ;
           apply invertible_horizontal_square_inv_right).
      + abstract
          (rewrite <- (square_to_horizontal_cell_comp HB) ;
           rewrite <- (square_to_horizontal_cell_id HB) ;
           apply maponpaths ;
           apply invertible_horizontal_square_inv_left).
  Defined.

  Definition invertible_2cell_to_horizontal_square
             {x y : B}
             {h₁ h₂ : x --> y}
             (τ : invertible_2cell h₁ h₂)
    : invertible_horizontal_square h₁ h₂.
  Proof.
    use make_invertible_horizontal_square.
    - use make_invertible_horizontal_square_data.
      + exact (horizontal_cell_to_square τ).
      + exact (horizontal_cell_to_square (τ^-1)).
    - split.
      + abstract
          (cbn -[comp_hor_globular_square] ;
           refine (_ @ horizontal_cell_to_square_id _) ;
           rewrite <- horizontal_cell_to_square_comp ;
           apply maponpaths ;
           exact (vcomp_rinv τ)).
      + abstract
          (cbn -[comp_hor_globular_square] ;
           refine (_ @ horizontal_cell_to_square_id _) ;
           rewrite <- horizontal_cell_to_square_comp ;
           apply maponpaths ;
           exact (vcomp_linv τ)).
  Defined.

  Definition horizontal_square_weq_invertible_2cell
             (HB : horizontally_saturated B)
             {x y : B}
             (h₁ h₂ : x --> y)
    : invertible_horizontal_square h₁ h₂ ≃ invertible_2cell h₁ h₂.
  Proof.
    use weq_iso.
    - exact (horizontal_square_to_invertible_2cell HB).
    - exact invertible_2cell_to_horizontal_square.
    - abstract
        (intro s ;
         use subtypePath ; [ intro ; apply isaprop_invertible_horizontal_square_laws | ] ;
         use dirprodeq ; apply square_to_horizontal_cell_to_square).
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply horizontal_cell_to_square_to_horizontal_cell).
  Defined.
End HorizontalCellsAreSquares.
