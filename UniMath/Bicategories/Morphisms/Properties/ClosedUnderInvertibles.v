(**
 Properties of morphisms are closed under invertible 2-cells

 Contents:
 1. Equivalences are closed under invertible 2-cells
 2. Adjoint quivalences are closed under invertible 2-cells
 3. Faithful 1-cells are closed under invertible 2-cells
 4. Fully faithful 1-cells are closed under invertible 2-cells
 5. Conservative 1-cells are closed under invertible 2-cells
 6. Discrete 1-cells are closed under invertible 2-cells
 7. Internal Street fibrations are closed under invertible 2-cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.

Local Open Scope cat.

(**
 1. Equivalences are closed under invertible 2-cells
 *)
Definition left_equivalence_invertible
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           (g_equiv : left_equivalence g)
           {α : f ==> g}
           (Hα : is_invertible_2cell α)
  : left_equivalence f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (left_adjoint_right_adjoint g_equiv).
  - exact ((left_adjoint_unit g_equiv)
           • ((Hα^-1) ▹ left_adjoint_right_adjoint g_equiv)).
  - exact ((left_adjoint_right_adjoint g_equiv ◃ α)
           • (left_adjoint_counit g_equiv)).
  - cbn.
    is_iso.
    apply g_equiv.
  - cbn.
    is_iso.
    apply g_equiv.
Defined.

(**
 2. Adjoint quivalences are closed under invertible 2-cells
 *)
Definition left_adjoint_equivalence_invertible
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           (g_equiv : left_adjoint_equivalence g)
           {α : f ==> g}
           (Hα : is_invertible_2cell α)
  : left_adjoint_equivalence f.
Proof.
  use equiv_to_adjequiv.
  exact (left_equivalence_invertible g_equiv Hα).
Defined.

(**
 3. Faithful 1-cells are closed under invertible 2-cells
 *)
Definition faithful_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
  : faithful_1cell f₁ → faithful_1cell f₂.
Proof.
  intros Hf₁ z g₁ g₂ α₁ α₂ p.
  apply (faithful_1cell_eq_cell Hf₁).
  use (vcomp_rcancel (_ ◃ β)).
  {
    is_iso.
  }
  rewrite !vcomp_whisker.
  rewrite p.
  apply idpath.
Qed.

(**
 4. Fully faithful 1-cells are closed under invertible 2-cells
 *)
Definition fully_faithful_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
           (Hf₁ : fully_faithful_1cell f₁)
  : fully_faithful_1cell f₂.
Proof.
  use make_fully_faithful.
  - exact (faithful_invertible β Hβ (fully_faithful_1cell_faithful Hf₁)).
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + apply (fully_faithful_1cell_inv_map Hf₁).
      exact ((g₁ ◃ β) • αf • (g₂ ◃ Hβ^-1)).
    + abstract
        (cbn ;
         use (vcomp_rcancel (_ ◃ Hβ^-1)) ; [ is_iso | ] ;
         rewrite vcomp_whisker ;
         rewrite fully_faithful_1cell_inv_map_eq ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite lwhisker_id2 ;
         rewrite id2_left ;
         apply idpath).
Qed.

(**
 5. Conservative 1-cells are closed under invertible 2-cells
 *)
Definition conservative_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
           (Hf₁ : conservative_1cell f₁)
  : conservative_1cell f₂.
Proof.
  intros x g₁ g₂ α Hα.
  apply Hf₁.
  use eq_is_invertible_2cell.
  - exact ((g₁ ◃ β) • (α ▹ f₂) • (g₂ ◃ Hβ^-1)).
  - abstract
      (rewrite <- vcomp_whisker ;
       rewrite !vassocl ;
       rewrite lwhisker_vcomp ;
       rewrite vcomp_rinv ;
       rewrite lwhisker_id2 ;
       apply id2_right).
  - use is_invertible_2cell_vcomp.
    + use is_invertible_2cell_vcomp.
      * is_iso.
      * exact Hα.
    + is_iso.
Defined.

(**
 6. Discrete 1-cells are closed under invertible 2-cells
 *)
Definition discrete_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
           (Hf₁ : discrete_1cell f₁)
  : discrete_1cell f₂.
Proof.
  split.
  - exact (faithful_invertible β Hβ (pr1 Hf₁)).
  - exact (conservative_invertible β Hβ (pr2 Hf₁)).
Defined.

(**
 7. Internal Street fibrations are closed under invertible 2-cells
 *)
Section Cartesian2CellInvertible.
  Context {B : bicat}
          {a b : B}
          {f₁ f₂ : a --> b}
          (β : f₁ ==> f₂)
          (Hβ : is_invertible_2cell β)
          {x : B}
          {g₁ g₂ : x --> a}
          {α : g₁ ==> g₂}
          (Hα : is_cartesian_2cell_sfib f₁ α).

  Definition is_cartesian_2cell_invertible_unique
             {h : x --> a}
             {γ : h ==> g₂}
             {δp : h · f₂ ==> g₁ · f₂}
             (q : γ ▹ f₂ = δp • (α ▹ f₂))
    : isaprop (∑ (δ : h ==> g₁), δ ▹ f₂ = δp × δ • α = γ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
    use (is_cartesian_2cell_sfib_factor_unique
           _
           Hα
           _
           γ
           ((h ◃ β) • δp • (_ ◃ Hβ^-1))).
    - rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      apply maponpaths.
      exact q.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite vcomp_whisker.
      rewrite (pr12 φ₁).
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite vcomp_whisker.
      rewrite (pr12 φ₂).
      apply idpath.
    - apply (pr22 φ₁).
    - apply (pr22 φ₂).
  Qed.

  Definition is_cartesian_2cell_invertible
    : is_cartesian_2cell_sfib f₂ α.
  Proof.
    intros h γ δp q.
    use iscontraprop1.
    - exact (is_cartesian_2cell_invertible_unique q).
    - simple refine (_ ,, _ ,, _).
      + refine (is_cartesian_2cell_sfib_factor
                  _
                  Hα
                  γ
                  ((h ◃ β) • δp • (_ ◃ Hβ^-1))
                  _).
        abstract
          (rewrite !vassocl ;
           rewrite <- vcomp_whisker ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite vcomp_whisker ;
           apply maponpaths ;
           exact q).
      + abstract
          (use (vcomp_rcancel (_ ◃ Hβ^-1)) ; [ is_iso | ] ;
           rewrite vcomp_whisker ;
           rewrite is_cartesian_2cell_sfib_factor_over ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           rewrite id2_left ;
           apply idpath).
      + abstract
          (cbn ;
           apply is_cartesian_2cell_sfib_factor_comm).
  Defined.
End Cartesian2CellInvertible.

Section InvertibleFromInternalSFib.
  Context {B : bicat}
          {a b : B}
          {f₁ f₂ : a --> b}
          (β : f₁ ==> f₂)
          (Hβ : is_invertible_2cell β)
          (Hf₁ : internal_sfib f₁).

  Definition internal_sfib_cleaving_invertible
    : internal_sfib_cleaving f₂.
  Proof.
    intros x g₁ g₂ α.
    pose (ℓ := pr1 Hf₁ x g₁ g₂ (α • (g₂ ◃ Hβ^-1))).
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (pr1 ℓ).
    - exact (pr12 ℓ).
    - exact (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell
                  _
                  (inv_of_invertible_2cell (β ,, Hβ)))
               (pr122 ℓ)).
    - apply (is_cartesian_2cell_invertible β Hβ).
      exact (pr1 (pr222 ℓ)).
    - abstract
        (simpl ;
         rewrite !vassocl ;
         use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
         rewrite <- vcomp_whisker ;
         use vcomp_move_R_Mp ; [ is_iso ; apply Hβ | ] ; cbn ;
         rewrite !vassocl ;
         exact (pr2 (pr222 ℓ))).
  Defined.

  Definition lwhisker_is_cartesian_invertible
    : lwhisker_is_cartesian f₂.
  Proof.
    intros x y h g₁ g₂ γ Hγ.
    apply (is_cartesian_2cell_invertible β Hβ).
    apply (pr2 Hf₁).
    apply (is_cartesian_2cell_invertible _ (is_invertible_2cell_inv Hβ)).
    exact Hγ.
  Defined.

  Definition internal_sfib_invertible
    : internal_sfib f₂.
  Proof.
    split.
    - exact internal_sfib_cleaving_invertible.
    - exact lwhisker_is_cartesian_invertible.
  Defined.
End InvertibleFromInternalSFib.
