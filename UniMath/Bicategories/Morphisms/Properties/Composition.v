(**
 Properties of composition

 Contents:
 1. Composition of equivalences
 2. Composition of adjoint equivalences
 3. Composition of faithful 1-cells
 4. Composition of fully faithful 1-cells
 5. Composition of discrete 1-cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

(**
 1. Composition of equivalences
 *)
Section CompositionEquivalence.
  Context {B : bicat}
          {a b c : B}
          (l₁ : a --> b)
          (l₂ : b --> c)
          (Hl₁ : left_equivalence l₁)
          (Hl₂ : left_equivalence l₂).

  Let r₁ : b --> a := left_adjoint_right_adjoint Hl₁.
  Let r₂ : c --> b := left_adjoint_right_adjoint Hl₂.

  Let η₁ : invertible_2cell (id₁ a) (l₁ · r₁)
    := left_equivalence_unit_iso Hl₁.
  Let η₂ : invertible_2cell (id₁ b) (l₂ · r₂)
    := left_equivalence_unit_iso Hl₂.

  Let ε₁ : invertible_2cell (r₁ · l₁) (id₁ b)
    := left_equivalence_counit_iso Hl₁.
  Let ε₂ : invertible_2cell (r₂ · l₂) (id₁ c)
    := left_equivalence_counit_iso Hl₂.

  Let ηc : id₁ a ==> l₁ · l₂ · (r₂ · r₁)
    := η₁
       • (rinvunitor _
          • (l₁ ◃ η₂)
          • lassociator _ _ _ ▹ r₁)
       • rassociator _ _ _.

  Let εc : r₂ · r₁ · (l₁ · l₂) ==> id₁ c
    := rassociator _ _ _
       • (r₂ ◃ (lassociator _ _ _
                • (ε₁ ▹ l₂)
                • lunitor _))
       • ε₂.

  Definition comp_equiv
    : left_equivalence (l₁ · l₂).
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (r₂ · r₁).
    - exact ηc.
    - exact εc.
    - cbn ; unfold ηc.
      is_iso.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
    - cbn ; unfold εc.
      is_iso.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
  Defined.
End CompositionEquivalence.

(**
 2. Composition of adjoint equivalences
 *)
Definition comp_adjequiv
           {B : bicat}
           {a b c : B}
           (l₁ : adjoint_equivalence a b)
           (l₂ : adjoint_equivalence b c)
  : adjoint_equivalence a c.
Proof.
  use (equiv_to_adjequiv (l₁ · l₂)).
  use comp_equiv.
  - exact l₁.
  - exact l₂.
Defined.

Lemma unique_adjoint_equivalence_comp
      {B : bicat}
      (HB : is_univalent_2 B)
      {a b c : B}
  : ∏ (f : adjoint_equivalence a b) (g : adjoint_equivalence b c),
    comp_adjequiv f g = comp_adjoint_equivalence (pr1 HB) a b c f g.
Proof.
  use (J_2_0 (pr1 HB) (λ a b f, _)).
  intros x g; simpl.
  unfold comp_adjoint_equivalence.
  rewrite J_2_0_comp.
  use subtypePath.
  {
    intro.
    exact (isaprop_left_adjoint_equivalence _ (pr2 HB)).
  }
  cbn.
  apply (isotoid_2_1 (pr2 HB)).
  use make_invertible_2cell.
  - exact (lunitor (pr1 g)).
  - is_iso.
Qed.


(**
 3. Composition of faithful 1-cells
 *)
Definition comp_faithful
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : faithful_1cell f)
           (Hg : faithful_1cell g)
  : faithful_1cell (f · g).
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  apply (faithful_1cell_eq_cell Hf).
  apply (faithful_1cell_eq_cell Hg).
  use (vcomp_rcancel (rassociator _ _ _)).
  {
    is_iso.
  }
  rewrite !rwhisker_rwhisker_alt.
  rewrite p.
  apply idpath.
Qed.

(**
 4. Composition of fully faithful 1-cells
 *)
Definition comp_fully_faithful
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : fully_faithful_1cell f)
           (Hg : fully_faithful_1cell g)
  : fully_faithful_1cell (f · g).
Proof.
  use make_fully_faithful.
  - exact (comp_faithful
             (fully_faithful_1cell_faithful Hf)
             (fully_faithful_1cell_faithful Hg)).
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + apply (fully_faithful_1cell_inv_map Hf).
      apply (fully_faithful_1cell_inv_map Hg).
      exact (rassociator _ _ _ • αf • lassociator _ _ _).
    + abstract
        (cbn ;
         use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
         rewrite !vassocl ;
         rewrite <- rwhisker_rwhisker ;
         rewrite !fully_faithful_1cell_inv_map_eq ;
         rewrite !vassocr ;
         rewrite lassociator_rassociator ;
         rewrite id2_left ;
         apply idpath).
Defined.

(**
 5. Composition of conservative 1-cells
 *)
Definition comp_conservative
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : conservative_1cell f)
           (Hg : conservative_1cell g)
  : conservative_1cell (f · g).
Proof.
  intros x g₁ g₂ α Hα.
  apply Hf.
  apply Hg.
  use eq_is_invertible_2cell.
  - exact (rassociator _ _ _ • (α ▹ f · g) • lassociator _ _ _).
  - abstract
      (rewrite !vassocl ;
       rewrite <- rwhisker_rwhisker ;
       rewrite !vassocr ;
       rewrite rassociator_lassociator ;
       apply id2_left).
  - use is_invertible_2cell_vcomp.
    + use is_invertible_2cell_vcomp.
      * is_iso.
      * exact Hα.
    + is_iso.
Defined.

(**
 5. Composition of discrete 1-cells
 *)
Definition comp_discrete
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : discrete_1cell f)
           (Hg : discrete_1cell g)
  : discrete_1cell (f · g).
Proof.
  split.
  - apply comp_faithful.
    + exact (pr1 Hf).
    + exact (pr1 Hg).
  - apply comp_conservative.
    + exact (pr2 Hf).
    + exact (pr2 Hg).
Defined.
