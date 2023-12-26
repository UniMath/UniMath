(************************************************************************************

 Properties of local equivalences

 In this file, we enumerate several properties of local equivalences.

 Every pseudofunctor `F` gives rise to a functor `x --> y ⟶ F x --> F y`. If `F` is
 a local equivalence, then we also have a functor in the converse direction. For this
 action we also construct analogous pseudofunctoriality actions, namely an identitor
 and a compositor that witness the preservation of the identity and composition of
 1-cells. We also prove the usual pseudofunctoriality laws together with several
 variations of them.

 Contents
 1. Action on 1-cells and 2-cells
 2. Unit and counit
 3. Functoriality of the action on 2-cells
 4. Action on invertible 2-cells
 5. Identitor and compositor
 6. Pseudofunctor laws

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Properties.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section LocalEquivalencePseudoFunctoriality.
  Context {B₁ B₂ : bicat}
          {HB₁ : is_univalent_2_1 B₁}
          {HB₂ : is_univalent_2_1 B₂}
          {F : psfunctor B₁ B₂}
          (HF : local_equivalence HB₁ HB₂ F).

  (** * 1. Action on 1-cells and 2-cells *)
  Definition local_equivalence_inv_onecell
             {x y : B₁}
             (f : F x --> F y)
    : x --> y
    := local_equivalence_right_adjoint HF x y f.

  Definition local_equivalence_inv_twocell
             {x y : B₁}
             {f g : F x --> F y}
             (τ : f ==> g)
    : local_equivalence_inv_onecell f
      ==>
      local_equivalence_inv_onecell g
    := #(local_equivalence_right_adjoint HF x y) τ.

  (** * 2. Unit and counit *)
  Definition local_equivalence_unit_inv2cell
             {x y : B₁}
             (f : x --> y)
    : invertible_2cell f (local_equivalence_inv_onecell (#F f))
    := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso (local_equivalence_unit HF x y) f).

  Definition local_equivalence_counit_inv2cell
             {x y : B₁}
             (f : F x --> F y)
    : invertible_2cell (#F (local_equivalence_inv_onecell f)) f
    := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso (local_equivalence_counit HF x y) f).

  Proposition local_equivalence_unit_natural
              {x y : B₁}
              {f g : x --> y}
              (τ : f ==> g)
    : τ • local_equivalence_unit_inv2cell g
      =
      local_equivalence_unit_inv2cell f • local_equivalence_inv_twocell (##F τ).
  Proof.
    exact (nat_trans_ax (local_equivalence_unit HF x y) _ _ τ).
  Qed.

  Proposition local_equivalence_inv_twocell_psfunctor
              {x y : B₁}
              {f g : x --> y}
              (τ : f ==> g)
    : local_equivalence_inv_twocell (##F τ)
      =
      (local_equivalence_unit_inv2cell f)^-1 • τ • local_equivalence_unit_inv2cell g.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn.
    refine (!_).
    apply local_equivalence_unit_natural.
  Qed.

  Proposition local_equivalence_unit_natural_alt
              {x y : B₁}
              {f g : x --> y}
              (τ : f ==> g)
    : (local_equivalence_unit_inv2cell f)^-1 • τ
      =
      local_equivalence_inv_twocell (##F τ) • (local_equivalence_unit_inv2cell g)^-1.
  Proof.
    rewrite local_equivalence_inv_twocell_psfunctor.
    rewrite !vassocl.
    rewrite vcomp_rinv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition local_equivalence_counit_natural
              {x y : B₁}
              {f g : F x --> F y}
              (τ : f ==> g)
    : ##F (local_equivalence_inv_twocell τ) • local_equivalence_counit_inv2cell g
      =
      local_equivalence_counit_inv2cell f • τ.
  Proof.
    exact (nat_trans_ax (local_equivalence_counit HF x y) _ _ τ).
  Qed.

  Proposition psfunctor_local_equivalence_inv_twocell
              {x y : B₁}
              {f g : F x --> F y}
              (τ : f ==> g)
    : ##F (local_equivalence_inv_twocell τ)
      =
      local_equivalence_counit_inv2cell f • τ • (local_equivalence_counit_inv2cell g)^-1.
  Proof.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    cbn.
    apply local_equivalence_counit_natural.
  Qed.

  Proposition local_equivalence_counit_natural_alt
              {x y : B₁}
              {f g : F x --> F y}
              (τ : f ==> g)
    : (local_equivalence_counit_inv2cell f)^-1 • ##F (local_equivalence_inv_twocell τ)
      =
      τ • (local_equivalence_counit_inv2cell g)^-1.
  Proof.
    rewrite psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  Qed.

  Proposition local_equivalence_triangle1
              {x y : B₁}
              (f : x --> y)
    : ##F (local_equivalence_unit_inv2cell f)
      • local_equivalence_counit_inv2cell (#F f)
      =
      id2 (#F f).
  Proof.
    pose (nat_trans_eq_pointwise (internal_triangle1 (HF x y)) f) as p.
    cbn in p.
    rewrite !id2_left, !id2_right in p.
    exact p.
  Qed.

  Proposition local_equivalence_triangle1_inv
              {x y : B₁}
              (f : x --> y)
    : (local_equivalence_counit_inv2cell (#F f))^-1
      • ##F ((local_equivalence_unit_inv2cell f)^-1)
      =
      id2 (#F f).
  Proof.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    rewrite id2_right.
    refine (!(id2_right _) @ _).
    use vcomp_move_R_pM.
    {
      exact (psfunctor_is_iso
               F
               (inv_of_invertible_2cell (local_equivalence_unit_inv2cell f))).
    }
    cbn.
    refine (!_).
    apply local_equivalence_triangle1.
  Qed.

  Proposition local_equivalence_unit_triangle
              {x y : B₁}
              (f : x --> y)
    : ##F (local_equivalence_unit_inv2cell f)
      =
      (local_equivalence_counit_inv2cell (#F f))^-1.
  Proof.
    refine (_ @ id2_left _).
    use vcomp_move_L_Mp ; [ is_iso | ].
    apply local_equivalence_triangle1.
  Qed.

  Proposition local_equivalence_unit_triangle_inv
              {x y : B₁}
              (f : x --> y)
    : (psfunctor_inv2cell F (local_equivalence_unit_inv2cell f))^-1
      =
      (local_equivalence_counit_inv2cell (#F f)).
  Proof.
    refine (!_).
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ].
    apply local_equivalence_triangle1.
  Qed.

  Proposition local_equivalence_triangle2
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_unit_inv2cell (local_equivalence_inv_onecell f)
      • local_equivalence_inv_twocell (local_equivalence_counit_inv2cell f)
      =
      id2 (local_equivalence_inv_onecell f).
  Proof.
    pose (nat_trans_eq_pointwise (internal_triangle2 (HF x y)) f) as p.
    cbn in p.
    rewrite !id2_left, !id2_right in p.
    exact p.
  Qed.

  Proposition local_equivalence_counit_triangle
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_inv_twocell (local_equivalence_counit_inv2cell f)
      =
      (local_equivalence_unit_inv2cell (local_equivalence_inv_onecell f))^-1.
  Proof.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ].
    apply local_equivalence_triangle2.
  Qed.

  (** * 3. Functoriality of the action on 2-cells *)
  Proposition local_equivalence_inv_twocell_id
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_inv_twocell (id2 f)
      =
      id2 _.
  Proof.
    exact (functor_id (local_equivalence_right_adjoint HF x y) f).
  Qed.

  Proposition local_equivalence_inv_twocell_comp
              {x y : B₁}
              {f g h : F x --> F y}
              (τ : f ==> g)
              (θ : g ==> h)
    : local_equivalence_inv_twocell (τ • θ)
      =
      local_equivalence_inv_twocell τ • local_equivalence_inv_twocell θ.
  Proof.
    exact (functor_comp (local_equivalence_right_adjoint HF x y) τ θ).
  Qed.

  (** * 4. Action on invertible 2-cells *)
  Definition local_equivalence_inv_inv2cell
             {x y : B₁}
             {f g : F x --> F y}
             (τ : invertible_2cell f g)
    : invertible_2cell
        (local_equivalence_inv_onecell f)
        (local_equivalence_inv_onecell g).
  Proof.
    use make_invertible_2cell.
    - exact (local_equivalence_inv_twocell τ).
    - use make_is_invertible_2cell.
      + exact (local_equivalence_inv_twocell (τ^-1)).
      + abstract
          (rewrite <- local_equivalence_inv_twocell_comp ;
           rewrite vcomp_rinv ;
           apply local_equivalence_inv_twocell_id).
      + abstract
          (rewrite <- local_equivalence_inv_twocell_comp ;
           rewrite vcomp_linv ;
           apply local_equivalence_inv_twocell_id).
  Defined.

  Proposition local_equivalence_counit_triangle_inv
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_inv_inv2cell (local_equivalence_counit_inv2cell f)^-1
      =
      (local_equivalence_unit_inv2cell (local_equivalence_inv_onecell f)).
  Proof.
    refine (!_).
    refine (_ @ id2_left _).
    use vcomp_move_L_Mp ; [ is_iso | ].
    apply local_equivalence_triangle2.
  Qed.

  (** * 5. Identitor and compositor *)
  Definition local_equivalence_inv_onecell_id
             (x : B₁)
    : invertible_2cell
        (local_equivalence_inv_onecell (id₁ (F x)))
        (id₁ x)
    := comp_of_invertible_2cell
         (local_equivalence_inv_inv2cell (psfunctor_id F x))
         (inv_of_invertible_2cell (local_equivalence_unit_inv2cell (id₁ x))).

  Definition local_equivalence_inv_onecell_comp
             {x y z : B₁}
             (f : F x --> F y)
             (g : F y --> F z)
    : invertible_2cell
        (local_equivalence_inv_onecell (f · g))
        (local_equivalence_inv_onecell f · local_equivalence_inv_onecell g).
  Proof.
    refine (comp_of_invertible_2cell
              (local_equivalence_inv_inv2cell _)
              (inv_of_invertible_2cell (local_equivalence_unit_inv2cell _))).
    refine (comp_of_invertible_2cell
              _
              (psfunctor_comp F _ _)).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell _ _)
              (lwhisker_of_invertible_2cell _ _)).
    - exact (inv_of_invertible_2cell (local_equivalence_counit_inv2cell f)).
    - exact (inv_of_invertible_2cell (local_equivalence_counit_inv2cell g)).
  Defined.

  (** * 6. Pseudofunctor laws *)
  Proposition local_equivalence_eq_two_cell
              {x y : B₁}
              {f g : x --> y}
              {τ θ : f ==> g}
              (p : ##F τ = ##F θ)
    : τ = θ.
  Proof.
    use (vcomp_rcancel (local_equivalence_unit_inv2cell _)).
    {
      apply property_from_invertible_2cell.
    }
    rewrite !local_equivalence_unit_natural.
    do 2 apply maponpaths.
    exact p.
  Qed.

  Opaque local_equivalence_inv_onecell
    local_equivalence_unit_inv2cell
    local_equivalence_counit_inv2cell
    local_equivalence_inv_twocell.

  Proposition local_equivalence_twocell_lwhisker
              {x y z : B₁}
              (f : F x --> F y)
              {g₁ g₂ : F y --> F z}
              (τ : g₁ ==> g₂)
    : local_equivalence_inv_twocell (f ◃ τ)
      • local_equivalence_inv_onecell_comp f g₂
      =
      local_equivalence_inv_onecell_comp f g₁
      • (_ ◃ local_equivalence_inv_twocell τ).
  Proof.
    cbn -[psfunctor_comp].
    use local_equivalence_eq_two_cell.
    rewrite !psfunctor_vcomp.
    rewrite !psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite lwhisker_vcomp.
      rewrite <- local_equivalence_counit_natural_alt.
      rewrite <- lwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- psfunctor_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- local_equivalence_counit_natural_alt.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite <- !psfunctor_vcomp.
    apply maponpaths.
    rewrite local_equivalence_unit_natural_alt.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_lwhisker_alt
              {x y z : B₁}
              (f : F x --> F y)
              {g₁ g₂ : F y --> F z}
              (τ : g₁ ==> g₂)
    : local_equivalence_inv_twocell (f ◃ τ)
      =
      local_equivalence_inv_onecell_comp f g₁
      • (_ ◃ local_equivalence_inv_twocell τ)
      • (local_equivalence_inv_onecell_comp f g₂)^-1.
  Proof.
    rewrite <- local_equivalence_twocell_lwhisker.
    rewrite !vassocl.
    rewrite vcomp_rinv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_lwhisker_inv
              {x y z : B₁}
              (f : F x --> F y)
              {g₁ g₂ : F y --> F z}
              (τ : g₁ ==> g₂)
    : (local_equivalence_inv_onecell_comp f g₁)^-1
      • local_equivalence_inv_twocell (f ◃ τ)
      =
      (_ ◃ local_equivalence_inv_twocell τ)
      • (local_equivalence_inv_onecell_comp f g₂)^-1.
  Proof.
    use vcomp_move_R_pM ; [ is_iso | ].
    rewrite !vassocr.
    apply local_equivalence_twocell_lwhisker_alt.
  Qed.

  Proposition local_equivalence_twocell_rwhisker
              {x y z : B₁}
              {f₁ f₂ : F x --> F y}
              (τ : f₁ ==> f₂)
              (g : F y --> F z)
    : local_equivalence_inv_twocell (τ ▹ g)
      • local_equivalence_inv_onecell_comp f₂ g
      =
      local_equivalence_inv_onecell_comp f₁ g
      • (local_equivalence_inv_twocell τ ▹ _).
  Proof.
    cbn -[psfunctor_comp].
    use local_equivalence_eq_two_cell.
    rewrite !psfunctor_vcomp.
    rewrite !psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      rewrite rwhisker_vcomp.
      rewrite <- local_equivalence_counit_natural_alt.
      rewrite <- rwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- psfunctor_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- local_equivalence_counit_natural_alt.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite <- !psfunctor_vcomp.
    apply maponpaths.
    rewrite local_equivalence_unit_natural_alt.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_rwhisker_alt
              {x y z : B₁}
              {f₁ f₂ : F x --> F y}
              (τ : f₁ ==> f₂)
              (g : F y --> F z)
    : local_equivalence_inv_twocell (τ ▹ g)
      =
      local_equivalence_inv_onecell_comp f₁ g
      • (local_equivalence_inv_twocell τ ▹ _)
      • (local_equivalence_inv_onecell_comp f₂ g)^-1.
  Proof.
    rewrite <- local_equivalence_twocell_rwhisker.
    rewrite !vassocl.
    rewrite vcomp_rinv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_rwhisker_inv
              {x y z : B₁}
              {f₁ f₂ : F x --> F y}
              (τ : f₁ ==> f₂)
              (g : F y --> F z)
    : (local_equivalence_inv_onecell_comp f₁ g)^-1
      • local_equivalence_inv_twocell (τ ▹ g)
      =
      (local_equivalence_inv_twocell τ ▹ _)
      • (local_equivalence_inv_onecell_comp f₂ g)^-1.
  Proof.
    use vcomp_move_R_pM ; [ is_iso | ].
    rewrite !vassocr.
    apply local_equivalence_twocell_rwhisker_alt.
  Qed.

  Proposition local_equivalence_twocell_lunitor
              {x y : B₁}
              (f : F x --> F y)
    : lunitor (local_equivalence_inv_onecell f)
      =
      ((local_equivalence_inv_onecell_id x)^-1 ▹ _)
      • (local_equivalence_inv_onecell_comp _ _)^-1
      • local_equivalence_inv_twocell (lunitor f).
  Proof.
    cbn -[psfunctor_id psfunctor_comp].
    use local_equivalence_eq_two_cell.
    rewrite <- rwhisker_vcomp.
    rewrite !psfunctor_vcomp.
    rewrite !psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 7 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    }
    rewrite psfunctor_F_lunitor.
    rewrite <- vcomp_lunitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn -[psfunctor_id psfunctor_comp].
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite psfunctor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite local_equivalence_triangle1.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_right.
    }
    rewrite !rwhisker_vcomp.
    apply maponpaths.
    rewrite local_equivalence_counit_natural.
    rewrite !vassocr.
    rewrite local_equivalence_triangle1.
    apply id2_left.
  Qed.

  Proposition local_equivalence_twocell_F_lunitor
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_inv_onecell_comp _ _
      • ((local_equivalence_inv_onecell_id x) ▹ _)
      • lunitor (local_equivalence_inv_onecell f)
      =
      local_equivalence_inv_twocell (lunitor f).
  Proof.
    rewrite local_equivalence_twocell_lunitor.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite vcomp_rinv.
    apply id2_left.
  Qed.

  Proposition local_equivalence_twocell_linvunitor
              {x y : B₁}
              (f : F x --> F y)
    : linvunitor (local_equivalence_inv_onecell f)
      =
      local_equivalence_inv_twocell (linvunitor f)
      • local_equivalence_inv_onecell_comp _ _
      • (local_equivalence_inv_onecell_id x ▹ _).
  Proof.
    refine (!(id2_left _) @ _ @ id2_right _).
    rewrite <- lunitor_linvunitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite local_equivalence_twocell_lunitor.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      apply id2_left.
    }
    rewrite <- local_equivalence_inv_twocell_comp.
    rewrite linvunitor_lunitor.
    rewrite local_equivalence_inv_twocell_id.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_runitor
              {x y : B₁}
              (f : F x --> F y)
    : runitor (local_equivalence_inv_onecell f)
      =
      (_ ◃ (local_equivalence_inv_onecell_id y)^-1)
      • (local_equivalence_inv_onecell_comp _ _)^-1
      • local_equivalence_inv_twocell (runitor f).
  Proof.
    cbn -[psfunctor_id psfunctor_comp].
    use local_equivalence_eq_two_cell.
    rewrite <- lwhisker_vcomp.
    rewrite !psfunctor_vcomp.
    rewrite !psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 7 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    }
    rewrite psfunctor_F_runitor.
    rewrite <- vcomp_runitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn -[psfunctor_id psfunctor_comp].
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite psfunctor_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite local_equivalence_triangle1.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite vcomp_rinv.
    rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    rewrite local_equivalence_counit_natural.
    rewrite !vassocr.
    rewrite local_equivalence_triangle1.
    apply id2_left.
  Qed.

  Proposition local_equivalence_twocell_F_runitor
              {x y : B₁}
              (f : F x --> F y)
    : local_equivalence_inv_onecell_comp _ _
      • (_ ◃ local_equivalence_inv_onecell_id y)
      • runitor (local_equivalence_inv_onecell f)
      =
      local_equivalence_inv_twocell (runitor f).
  Proof.
    rewrite local_equivalence_twocell_runitor.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite vcomp_rinv.
    apply id2_left.
  Qed.

  Proposition local_equivalence_twocell_rinvunitor
              {x y : B₁}
              (f : F x --> F y)
    : rinvunitor (local_equivalence_inv_onecell f)
      =
      local_equivalence_inv_twocell (rinvunitor f)
      • local_equivalence_inv_onecell_comp _ _
      • (_ ◃ local_equivalence_inv_onecell_id y).
  Proof.
    refine (!(id2_left _) @ _ @ id2_right _).
    rewrite <- runitor_rinvunitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite local_equivalence_twocell_runitor.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      apply id2_left.
    }
    rewrite <- local_equivalence_inv_twocell_comp.
    rewrite rinvunitor_runitor.
    rewrite local_equivalence_inv_twocell_id.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_lassociator
              {w x y z : B₁}
              (f : F w --> F x)
              (g : F x --> F y)
              (h : F y --> F z)
    : local_equivalence_inv_twocell (lassociator _ _ _)
      • local_equivalence_inv_onecell_comp (f · g) h
      • (local_equivalence_inv_onecell_comp f g ▹ _)
      =
      local_equivalence_inv_onecell_comp f (g · h)
      • (_ ◃ local_equivalence_inv_onecell_comp g h)
      • lassociator _ _ _.
  Proof.
    cbn -[psfunctor_comp].
    use local_equivalence_eq_two_cell.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !psfunctor_vcomp.
    rewrite !psfunctor_local_equivalence_inv_twocell.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !vassocr.
      rewrite local_equivalence_triangle1_inv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite psfunctor_rwhisker.
      rewrite !vassocl.
      rewrite psfunctor_rwhisker.
      apply idpath.
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      rewrite !vassocr.
      rewrite local_equivalence_counit_natural_alt.
      rewrite !vassocl.
      rewrite local_equivalence_triangle1_inv.
      rewrite id2_right.
      apply idpath.
    }
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      rewrite !vassocr.
      apply (psfunctor_lassociator F).
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite local_equivalence_triangle1_inv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite psfunctor_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite psfunctor_lwhisker.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite !vassocr.
      rewrite local_equivalence_counit_natural_alt.
      rewrite !vassocl.
      rewrite local_equivalence_triangle1_inv.
      rewrite id2_right.
      apply idpath.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    rewrite vcomp_whisker.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_rassociator
              {w x y z : B₁}
              (f : F w --> F x)
              (g : F x --> F y)
              (h : F y --> F z)
    : local_equivalence_inv_onecell_comp (f · g) h
      • (local_equivalence_inv_onecell_comp f g ▹ _)
      • rassociator _ _ _
      =
      local_equivalence_inv_twocell (rassociator _ _ _)
      • local_equivalence_inv_onecell_comp f (g · h)
      • (_ ◃ local_equivalence_inv_onecell_comp g h).
  Proof.
    refine (!(id2_left _) @ _).
    rewrite <- local_equivalence_inv_twocell_id.
    rewrite <- rassociator_lassociator.
    rewrite local_equivalence_inv_twocell_comp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite local_equivalence_twocell_lassociator.
    rewrite !vassocl.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition local_equivalence_twocell_rassociator_inv
              {w x y z : B₁}
              (f : F w --> F x)
              (g : F x --> F y)
              (h : F y --> F z)
    : rassociator _ _ _
      • (_ ◃ (local_equivalence_inv_onecell_comp g h)^-1)
      • (local_equivalence_inv_onecell_comp f (g · h))^-1
      =
      ((local_equivalence_inv_onecell_comp f g)^-1 ▹ _)
      • (local_equivalence_inv_onecell_comp (f · g) h)^-1
      • local_equivalence_inv_twocell (rassociator _ _ _).
  Proof.
    use vcomp_move_L_pM ; [ is_iso | ].
    rewrite !vassocr.
    do 2 (use vcomp_move_R_Mp ; [ is_iso | ]).
    exact (local_equivalence_twocell_rassociator f g h).
  Qed.
End LocalEquivalencePseudoFunctoriality.
