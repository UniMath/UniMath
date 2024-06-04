(** Pseudo transformations and pseudo transformations between pseudofunctors. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Definition pstrans_data
           {C D : bicat}
           (F G : psfunctor C D)
  : UU.
Proof.
  refine (map1cells C D⟦_,_⟧).
  - apply F.
  - apply G.
Defined.

Definition make_pstrans_data
           {C D : bicat}
           {F G : psfunctor C D}
           (η₁ : ∏ (X : C), F X --> G X)
           (η₂ : ∏ (X Y : C) (f : X --> Y), invertible_2cell (η₁ X · #G f) (#F f · η₁ Y))
  : pstrans_data F G
  := (η₁ ,, η₂).

Definition pstrans
           {C D : bicat}
           (F G : psfunctor C D)
  : UU
  := psfunctor_bicat C D ⟦F,G⟧.

Definition pscomponent_of
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ (X : C), F X --> G X
  := pr111 η.

Coercion pscomponent_of : pstrans >-> Funclass.

Definition psnaturality_of
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y : C} (f : X --> Y), invertible_2cell (η X · #G f) (#F f · η Y)
  := pr211 η.

Definition is_pstrans
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans_data F G)
  : UU
  := (∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
      (pr1 η X ◃ ##G α)
        • pr2 η _ _ g
      =
      (pr2 η _ _ f)
        • (##F α ▹ pr1 η Y))
     ×
     (∏ (X : C),
      (pr1 η X ◃ psfunctor_id G X)
        • pr2 η _ _ (id₁ X)
      =
      (runitor (pr1 η X))
        • linvunitor (pr1 η X)
        • (psfunctor_id F X ▹ pr1 η X))
     ×
     (∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
      (pr1 η X ◃ psfunctor_comp G f g)
        • pr2 η _ _ (f · g)
      =
      (lassociator (pr1 η X) (#G f) (#G g))
        • (pr2 η _ _ f ▹ (#G g))
        • rassociator (#F f) (pr1 η Y) (#G g)
        • (#F f ◃ pr2 η _ _ g)
        • lassociator (#F f) (#F g) (pr1 η Z)
        • (psfunctor_comp F f g ▹ pr1 η Z)).

Definition make_pstrans
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans_data F G)
           (Hη : is_pstrans η)
  : pstrans F G.
Proof.
  refine ((η ,, _) ,, tt).
  repeat split ; cbn ; intros ; apply Hη.
Defined.

Definition psnaturality_natural
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
    (η X ◃ ##G α)
      • psnaturality_of η g
    =
    (psnaturality_of η f)
      • (##F α ▹ η Y)
  := pr121 η.

Definition psnaturality_inv_natural
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
    (psnaturality_of η f)^-1
      • (η X ◃ ##G α)
    =
    (##F α ▹ η Y)
      • (psnaturality_of η g)^-1.
Proof.
  intros X Y f g α.
  use vcomp_move_L_Mp.
  { is_iso. }
  etrans.
  {
    apply vassocl.
  }
  use vcomp_move_R_pM.
  { is_iso. }
  cbn.
  exact (psnaturality_natural η X Y f g α).
Qed.

Definition pstrans_id
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ (X : C),
    (η X ◃ psfunctor_id G X)
      • psnaturality_of η (id₁ X)
    =
    (runitor (η X))
      • linvunitor (η X)
      • (psfunctor_id F X ▹ η X)
  := pr122(pr1 η).

Definition pstrans_comp
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y Z : C} (f : X --> Y) (g : Y --> Z),
    (η X ◃ psfunctor_comp G f g)
      • psnaturality_of η (f · g)
    =
    (lassociator (η X) (#G f) (#G g))
      • (psnaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η Y) (#G g)
      • (#F f ◃ psnaturality_of η g)
      • lassociator (#F f) (#F g) (η Z)
      • (psfunctor_comp F f g ▹ η Z)
  := pr222(pr1 η).

Definition pstrans_id_alt
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ (X : C),
    cell_from_invertible_2cell (psnaturality_of η (id₁ X))
    =
    (η X ◃ (psfunctor_id G X)^-1)
      • runitor (η X)
      • linvunitor (η X)
      • (psfunctor_id F X ▹ η X).
Proof.
  intros X.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (pstrans_id η X).
Qed.

Proposition pstrans_id_inv
            {B₁ B₂ : bicat}
            {F G : psfunctor B₁ B₂}
            (τ : pstrans F G)
            (x : B₁)
  : (psnaturality_of τ (id₁ x))^-1 • (τ x ◃ (psfunctor_id G x)^-1)
    =
    ((psfunctor_id F x)^-1 ▹ τ x) • lunitor _ • rinvunitor _.
Proof.
  use vcomp_move_L_pM ; [ is_iso | ].
  use vcomp_move_R_Mp ; [ is_iso | ].
  use vcomp_move_L_pM; [ is_iso | ].
  cbn -[psfunctor_id].
  rewrite !vassocr.
  exact (!(pstrans_id τ x)).
Qed.

Proposition pstrans_id_inv_alt
            {B₁ B₂ : bicat}
            {F G : psfunctor B₁ B₂}
            (τ : pstrans F G)
            (x : B₁)
  : (psfunctor_id F x ▹ τ x) • (psnaturality_of τ (id₁ x))^-1
    =
    lunitor _ • rinvunitor _ • (τ x ◃ psfunctor_id G x).
Proof.
  use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ].
  rewrite !vassocr.
  use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ].
  cbn -[psfunctor_id].
  apply pstrans_id_inv.
Qed.

Definition pstrans_comp_alt
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y Z : C} (f : X --> Y) (g : Y --> Z),
    cell_from_invertible_2cell (psnaturality_of η (f · g))
    =
    (η X ◃ (psfunctor_comp G f g)^-1)
      • lassociator (η X) (#G f) (#G g)
      • (psnaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η Y) (#G g)
      • (#F f ◃ psnaturality_of η g)
      • lassociator (#F f) (#F g) (η Z)
      • (psfunctor_comp F f g ▹ η Z).
Proof.
  intros X Y Z f g.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (pstrans_comp η f g).
Qed.

Definition pstrans_inv_comp_alt
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y Z : C} (f : X --> Y) (g : Y --> Z),
    (psnaturality_of η (f · g))^-1
    =
    ((psfunctor_comp F f g)^-1 ▹ η Z)
      • rassociator (#F f) (#F g) (η Z)
      • (#F f ◃ ((psnaturality_of η g)^-1))
      • lassociator (#F f) (η Y) (#G g)
      • ((psnaturality_of η f)^-1 ▹ (#G g))
      • (rassociator (η X) (#G f) (#G g))
      • (η X ◃ (psfunctor_comp G f g)).
Proof.
  intros X Y Z f g.
  use vcomp_move_L_pM.
  { is_iso. }
  use vcomp_move_R_Mp.
  { is_iso. }
  use vcomp_move_L_pM.
  { is_iso. apply (psfunctor_comp G). }
  simpl.
  rewrite pstrans_comp_alt.
  rewrite !vassocl.
  reflexivity.
Qed.

Definition id_pstrans
           {C D : bicat}
           (F : psfunctor C D)
  : pstrans F F
  := id₁ F.

Definition comp_pstrans
           {C D : bicat}
           {F₁ F₂ F₃ : psfunctor C D}
           (σ₁ : pstrans F₁ F₂) (σ₂ : pstrans F₂ F₃)
  : pstrans F₁ F₃
  := σ₁ · σ₂.

(** Pseudo adjoint equivalence is pointwise adjoint equivalence *)
Definition pointwise_adjequiv
           {B₁ B₂ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (σ : pstrans F₁ F₂)
           (Hf : left_adjoint_equivalence σ)
  : ∏ (X : B₁), left_adjoint_equivalence (σ X).
Proof.
  intro X.
  pose (pr1 (left_adjoint_equivalence_total_disp_weq _ _ Hf)) as t₁.
  pose (pr1 (left_adjoint_equivalence_total_disp_weq _ _ t₁)) as t₂.
  pose (pr1 (left_adjoint_equivalence_total_disp_weq _ _ t₂)) as t₃.
  exact (is_adjequiv_to_all_is_adjequiv _ _ _ t₃ X).
Defined.

Definition pstrans_to_pstrans_data
           {B₁ B₂ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (α : pstrans F₁ F₂)
  : pstrans_data F₁ F₂
  := pr11 α.

Definition pstrans_to_is_pstrans
           {B₁ B₂ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (α : pstrans F₁ F₂)
  : is_pstrans (pstrans_to_pstrans_data α)
  := pr21 α.

(** A pointwise adjoint equivalence is an adjoint equivalence *)
Section PointwiseAdjequivIsAdjequiv.
  Context {B₁ B₂ : bicat}
          (HB₂ : is_univalent_2 B₂)
          {F₁ F₂ : psfunctor B₁ B₂}
          (σ : pstrans F₁ F₂)
          (Hf : ∏ (x : B₁), left_adjoint_equivalence (σ x)).

  Definition pointwise_adjequiv_to_adjequiv_base
    : left_adjoint_equivalence (pr111 σ).
  Proof.
    apply all_is_adjequiv_to_is_adjequiv.
    exact Hf.
  Defined.

  Definition pointwise_adjequiv_to_adjequiv_1cell
    : left_adjoint_equivalence (pr11 σ).
  Proof.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    - exact pointwise_adjequiv_to_adjequiv_base.
    - apply map1cells_disp_left_adjoint_equivalence.
      exact HB₂.
  Qed.

  Definition pointwise_adjequiv_to_adjequiv_data
    : left_adjoint_equivalence (pr1 σ).
  Proof.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    - exact pointwise_adjequiv_to_adjequiv_1cell.
    - use (pair_left_adjoint_equivalence
               (map2cells_disp_cat B₁ B₂)
               (disp_dirprod_bicat
                  (identitor_disp_cat B₁ B₂)
                  (compositor_disp_cat B₁ B₂))
               (_ ,, pointwise_adjequiv_to_adjequiv_1cell)).
      simple refine (_ ,, _).
      + apply map2cells_disp_left_adjequiv.
        exact HB₂.
      + use (pair_left_adjoint_equivalence
               (identitor_disp_cat B₁ B₂)
               (compositor_disp_cat B₁ B₂)).
        simple refine (_ ,, _).
        * apply identitor_disp_left_adjequiv.
          exact HB₂.
        * apply compositor_disp_left_adjequiv.
          exact HB₂.
  Defined.

  Definition pointwise_adjequiv_to_adjequiv
    : left_adjoint_equivalence σ.
  Proof.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    - exact pointwise_adjequiv_to_adjequiv_data.
    - apply disp_left_adjoint_equivalence_fullsubbicat.
  Qed.
End PointwiseAdjequivIsAdjequiv.

Definition right_adjoint_pointwise_adjequiv
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {F₁ F₂ : psfunctor B₁ B₂}
           (σ : pstrans F₁ F₂)
           (H : ∏ (x : B₁), left_adjoint_equivalence (σ x))
           (x : B₁)
  : (left_adjoint_right_adjoint (pointwise_adjequiv_to_adjequiv HB₂ σ H) : pstrans F₂ F₁) x
    =
    left_adjoint_right_adjoint (H x).
Proof.
  assert (H x
          =
          pointwise_adjequiv
            _
            (pointwise_adjequiv_to_adjequiv HB₂ σ H)
            x)
    as p.
  {
    apply isaprop_left_adjoint_equivalence.
    apply HB₂.
  }
  rewrite p.
  apply idpath.
Qed.

(** Pseudotansformations between psfunctor data *)
Definition pstrans_data_on_data
           {C D : bicat}
           (F G : psfunctor_data C D)
  : UU.
Proof.
  refine (map1cells C D⟦_,_⟧).
  - apply F.
  - apply G.
Defined.

Definition make_pstrans_data_on_data
           {C D : bicat}
           {F G : psfunctor_data C D}
           (η₁ : ∏ (X : C), F X --> G X)
           (η₂ : ∏ (X Y : C) (f : X --> Y), invertible_2cell (η₁ X · #G f) (#F f · η₁ Y))
  : pstrans_data_on_data F G
  := (η₁ ,, η₂).

Definition psfunctor_data_on_cells
           {C D : bicat}
           (F : psfunctor_data C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 F a b f g x.

Section LocalNotation.
  Local Notation "'##'" := (PseudoFunctorBicat.psfunctor_on_cells).

  Definition is_pstrans_on_data
             {C D : bicat}
             {F G : psfunctor_data C D}
             (η : pstrans_data_on_data F G)
    : UU
    := (∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
        (pr1 η X ◃ ##G α)
          • pr2 η _ _ g
        =
        (pr2 η _ _ f)
          • (##F α ▹ pr1 η Y))
         ×
         (∏ (X : C),
          (pr1 η X ◃ PseudoFunctorBicat.psfunctor_id G X)
            • pr2 η _ _ (id₁ X)
          =
          (runitor (pr1 η X))
            • linvunitor (pr1 η X)
            • (PseudoFunctorBicat.psfunctor_id F X ▹ pr1 η X))
         ×
         (∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
          (pr1 η X ◃ PseudoFunctorBicat.psfunctor_comp G f g)
            • pr2 η _ _ (f · g)
          =
          (lassociator (pr1 η X) (#G f) (#G g))
            • (pr2 η _ _ f ▹ (#G g))
            • rassociator (#F f) (pr1 η Y) (#G g)
            • (#F f ◃ pr2 η _ _ g)
            • lassociator (#F f) (#F g) (pr1 η Z)
            • (PseudoFunctorBicat.psfunctor_comp F f g ▹ pr1 η Z)).

  Definition pstrans_on_data
             {C D : bicat}
             (F G : psfunctor_data C D)
    : UU
    := ∑ (η : pstrans_data_on_data F G), is_pstrans_on_data η.

  Definition pstrans_on_data_to_pstrans
             {C D : bicat}
             {F G : psfunctor C D}
             (η : pstrans_on_data (pr1 F) (pr1 G))
    : pstrans F G
    := η ,, tt.
End LocalNotation.
