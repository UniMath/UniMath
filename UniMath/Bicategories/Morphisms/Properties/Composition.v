(**
 Properties of composition

 Contents:
 1. Composition of equivalences
 2. Composition of adjoint equivalences
 3. Composition of faithful 1-cells
 4. Composition of fully faithful 1-cells
 5. Composition of discrete 1-cells
 6. Composition of Street fibrations
 7. Composition of Street opfibrations
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
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.

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

Definition comp_left_adjoint_equivalence
           {B : bicat}
           {a b c : B}
           {l₁ : a --> b}
           (Hl₁ : left_adjoint_equivalence l₁)
           {l₂ : b --> c}
           (Hl₂ : left_adjoint_equivalence l₂)
  : left_adjoint_equivalence (l₁ · l₂).
Proof.
  exact (comp_adjequiv (l₁ ,, Hl₁) (l₂ ,, Hl₂)).
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

(**
 6. Composition of Street fibrations
 *)
Section CompositionOfSFib.
  Context {B : bicat}
          {a b c : B}
          {f : a --> b}
          {g : b --> c}
          (Hf : internal_sfib f)
          (Hg : internal_sfib g).

  Section CompCartesian.
    Context {z : B}
            {h₁ h₂ : z --> a}
            (α : h₁ ==> h₂)
            (Hα₁ : is_cartesian_2cell_sfib f α)
            (Hα₂ : is_cartesian_2cell_sfib g (α ▹ f)).

    Section ToCartesianComp.
      Context {k : z --> a}
              {β : k ==> h₂}
              {δp : k · (f · g) ==> h₁ · (f · g)}
              (q : β ▹ f · g = δp • (α ▹ f · g)).

      Local Lemma to_is_cartesian_2cell_comp_factor_help
        : (β ▹ f) ▹ g
          =
          rassociator k f g • δp • lassociator h₁ f g • ((α ▹ f) ▹ g).
      Proof.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite rwhisker_rwhisker.
        rewrite q.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker.
        apply idpath.
      Qed.

      Let ζ : k · f ==> h₁ · f
        := is_cartesian_2cell_sfib_factor
             _
             Hα₂
             (β ▹ f)
             (rassociator _ _ _ • δp • lassociator _ _ _)
             to_is_cartesian_2cell_comp_factor_help.

      Definition to_is_cartesian_2cell_comp_factor
        : k ==> h₁.
      Proof.
        simple refine (is_cartesian_2cell_sfib_factor _ Hα₁ β ζ _).
        abstract
          (unfold ζ ;
           rewrite is_cartesian_2cell_sfib_factor_comm ;
           apply idpath).
      Defined.

      Definition to_is_cartesian_2cell_comp_over
        : to_is_cartesian_2cell_comp_factor ▹ f · g = δp.
      Proof.
        unfold to_is_cartesian_2cell_comp_factor, ζ.
        use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !is_cartesian_2cell_sfib_factor_over.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        rewrite id2_right.
        apply idpath.
      Qed.

      Definition to_is_cartesian_2cell_comp_comm
        : to_is_cartesian_2cell_comp_factor • α = β.
      Proof.
        unfold to_is_cartesian_2cell_comp_factor.
        rewrite is_cartesian_2cell_sfib_factor_comm.
        apply idpath.
      Qed.

      Definition to_is_cartesian_2cell_comp_unique
        : isaprop (∑ (δ : k ==> h₁), δ ▹ f · g = δp × δ • α = β).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use (is_cartesian_2cell_sfib_factor_unique _ Hα₁ _ β ζ).
        - unfold ζ.
          rewrite is_cartesian_2cell_sfib_factor_comm.
          apply idpath.
        - use (is_cartesian_2cell_sfib_factor_unique
                 _ Hα₂
                 _
                 (β ▹ f)
                 (rassociator _ _ _ • δp • lassociator _ _ _)
                 to_is_cartesian_2cell_comp_factor_help).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite rwhisker_rwhisker.
            apply maponpaths_2.
            exact (pr12 φ₁).
          + apply is_cartesian_2cell_sfib_factor_over.
          + rewrite !rwhisker_vcomp.
            rewrite (pr22 φ₁).
            apply idpath.
          + apply is_cartesian_2cell_sfib_factor_comm.
        - use (is_cartesian_2cell_sfib_factor_unique
                 _ Hα₂
                 _
                 (β ▹ f)
                 (rassociator _ _ _ • δp • lassociator _ _ _)
                 to_is_cartesian_2cell_comp_factor_help).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite rwhisker_rwhisker.
            apply maponpaths_2.
            exact (pr12 φ₂).
          + apply is_cartesian_2cell_sfib_factor_over.
          + rewrite !rwhisker_vcomp.
            rewrite (pr22 φ₂).
            apply idpath.
          + apply is_cartesian_2cell_sfib_factor_comm.
        - exact (pr22 φ₁).
        - exact (pr22 φ₂).
      Qed.
    End ToCartesianComp.

    Definition to_is_cartesian_2cell_comp
      : is_cartesian_2cell_sfib (f · g) α.
    Proof.
      intros k β δp q.
      use iscontraprop1.
      - exact (to_is_cartesian_2cell_comp_unique q).
      - exact (to_is_cartesian_2cell_comp_factor q
               ,,
               to_is_cartesian_2cell_comp_over q
               ,,
               to_is_cartesian_2cell_comp_comm q).
    Defined.
  End CompCartesian.

  Section CompCleaving.
    Context {z : B}
            {h₁ : z --> c}
            {h₂ : z --> a}
            (α : h₁ ==> h₂ · (f · g)).

    Let ℓ₁ : z --> b
      := pr1 (pr1 Hg z h₁ (h₂ · f) (α • lassociator _ _ _)).
    Let γ₁ : ℓ₁ ==> h₂ · f
      := pr12 (pr1 Hg z h₁ (h₂ · f) (α • lassociator _ _ _)).
    Let β₁ : invertible_2cell (ℓ₁ · g) h₁
      := pr122 (pr1 Hg z h₁ (h₂ · f) (α • lassociator _ _ _)).
    Let Hγ₁ : is_cartesian_2cell_sfib g γ₁
      := pr1 (pr222 (pr1 Hg z h₁ (h₂ · f) (α • lassociator _ _ _))).
    Let p₁ : γ₁ ▹ g = β₁ • (α • lassociator h₂ f g)
      := pr2 (pr222 (pr1 Hg z h₁ (h₂ · f) (α • lassociator _ _ _))).

    Let ℓ₂ : z --> a
      := pr1 (pr1 Hf z ℓ₁ h₂ γ₁).
    Let γ₂ : ℓ₂ ==> h₂
      := pr12 (pr1 Hf z ℓ₁ h₂ γ₁).
    Let β₂ : invertible_2cell (ℓ₂ · f) ℓ₁
      := pr122 (pr1 Hf z ℓ₁ h₂ γ₁).
    Let Hγ₂ : is_cartesian_2cell_sfib f γ₂
      := pr1 (pr222 (pr1 Hf z ℓ₁ h₂ γ₁)).
    Let p₂ : γ₂ ▹ f = β₂ • γ₁
      := pr2 (pr222 (pr1 Hf z ℓ₁ h₂ γ₁)).

    Definition comp_sfib_cleaving_lift
      : z --> a
      := ℓ₂.

    Definition comp_sfib_cleaving_cell
      : comp_sfib_cleaving_lift ==> h₂
      := γ₂.

    Definition comp_sfib_cleaving_cell_over_f
      : comp_sfib_cleaving_cell ▹ f = β₂ • γ₁
      := p₂.

    Definition comp_sfib_cleaving_cell_g_cartesian
      : is_cartesian_2cell_sfib g γ₁
      := Hγ₁.

    Definition comp_sfib_cleaving_cell_f_cartesian
      : is_cartesian_2cell_sfib f comp_sfib_cleaving_cell
      := Hγ₂.

    Definition comp_sfib_cleaving_over
      : invertible_2cell (comp_sfib_cleaving_lift · (f · g)) h₁
      := comp_of_invertible_2cell
           (comp_of_invertible_2cell
              (lassociator_invertible_2cell _ _ _)
              (rwhisker_of_invertible_2cell
                 _
                 β₂))
           β₁.

    Definition comp_sfib_cleaving_is_cartesian_2cell
      : is_cartesian_2cell_sfib (f · g) comp_sfib_cleaving_cell.
    Proof.
      use to_is_cartesian_2cell_comp.
      - exact Hγ₂.
      - unfold comp_sfib_cleaving_cell.
        use (is_cartesian_eq _ (!p₂)).
        use vcomp_is_cartesian_2cell_sfib.
        + apply invertible_is_cartesian_2cell_sfib.
          apply property_from_invertible_2cell.
        + exact Hγ₁.
    Defined.

    Definition comp_sfib_cleaving_comm
      : comp_sfib_cleaving_cell ▹ f · g
        =
        comp_sfib_cleaving_over • α.
    Proof.
      unfold comp_sfib_cleaving_cell, comp_sfib_cleaving_over ; cbn.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite <- rwhisker_rwhisker_alt.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact p₂.
      }
      rewrite <- rwhisker_vcomp.
      rewrite p₁.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      apply idpath.
    Qed.
  End CompCleaving.

  Definition comp_sfib_cleaving
    : internal_sfib_cleaving (f · g)
    := λ z h₁ h₂ α,
       comp_sfib_cleaving_lift α
       ,,
       comp_sfib_cleaving_cell α
       ,,
       comp_sfib_cleaving_over α
       ,,
       comp_sfib_cleaving_is_cartesian_2cell α
       ,,
       comp_sfib_cleaving_comm α.

  Section FromCompCartesian.
    Context {z : B}
            {h₁ h₂ : z --> a}
            (α : h₁ ==> h₂)
            (Hα : is_cartesian_2cell_sfib (f · g) α).

    Local Lemma from_is_cartesian_2cell_eq
      : α ▹ f · g
        =
        (comp_sfib_cleaving_over (α ▹ f · g))^-1
        • (comp_sfib_cleaving_cell (α ▹ f · g) ▹ f · g).
    Proof.
      use vcomp_move_L_pM ; [ is_iso | ].
      rewrite comp_sfib_cleaving_comm.
      apply idpath.
    Qed.

    Let ζ : invertible_2cell h₁ (comp_sfib_cleaving_lift (α ▹ f · g))
      := invertible_between_cartesians
           Hα
           (comp_sfib_cleaving_is_cartesian_2cell (α ▹ (f · g)))
           (inv_of_invertible_2cell (comp_sfib_cleaving_over (α ▹ f · g)))
           from_is_cartesian_2cell_eq.

    Local Lemma from_is_cartesian_2cell_comp_eq
      : ζ • comp_sfib_cleaving_cell (α ▹ (f · g))
        =
        α.
    Proof.
      apply is_cartesian_2cell_sfib_factor_comm.
    Qed.

    Definition from_is_cartesian_2cell_comp
      : is_cartesian_2cell_sfib f α.
    Proof.
      use (is_cartesian_eq _ from_is_cartesian_2cell_comp_eq).
      use vcomp_is_cartesian_2cell_sfib.
      - use invertible_is_cartesian_2cell_sfib.
        apply property_from_invertible_2cell.
      - apply comp_sfib_cleaving_cell_f_cartesian.
    Defined.

    Local Lemma from_is_cartesian_2cell_comp_rwhisker_eq
      : ((ζ ▹ f) • (comp_sfib_cleaving_cell (α ▹ f · g) ▹ f))
        =
        α ▹ f.
    Proof.
      rewrite rwhisker_vcomp.
      rewrite from_is_cartesian_2cell_comp_eq.
      apply idpath.
    Qed.

    Definition from_is_cartesian_2cell_comp_rwhisker
      : is_cartesian_2cell_sfib g (α ▹ f).
    Proof.
      use (is_cartesian_eq _ from_is_cartesian_2cell_comp_rwhisker_eq).
      use vcomp_is_cartesian_2cell_sfib.
      - use invertible_is_cartesian_2cell_sfib.
        is_iso.
        apply property_from_invertible_2cell.
      - rewrite comp_sfib_cleaving_cell_over_f.
        use vcomp_is_cartesian_2cell_sfib.
        + use invertible_is_cartesian_2cell_sfib.
          apply property_from_invertible_2cell.
        + apply comp_sfib_cleaving_cell_g_cartesian.
    Defined.
  End FromCompCartesian.

  Definition comp_lwhisker_is_cartesian
    : lwhisker_is_cartesian (f · g).
  Proof.
    intros x y h k₁ k₂ γ Hγ.
    use to_is_cartesian_2cell_comp.
    - apply (pr2 Hf).
      exact (from_is_cartesian_2cell_comp _ Hγ).
    - assert (((h ◃ γ) ▹ f) • rassociator _ _ _
              =
              rassociator _ _ _ • (h ◃ (γ ▹ f)))
        as r.
      {
        abstract
          (rewrite rwhisker_lwhisker_rassociator ;
           apply idpath).
      }
      refine (is_cartesian_2cell_sfib_postcomp
                _
                ((h ◃ γ) ▹ f)
                _ _
                r).
      + apply invertible_is_cartesian_2cell_sfib.
        is_iso.
      + use vcomp_is_cartesian_2cell_sfib.
        * apply invertible_is_cartesian_2cell_sfib.
          is_iso.
        * apply Hg.
          apply from_is_cartesian_2cell_comp_rwhisker.
          exact Hγ.
  Defined.

  Definition comp_sfib
    : internal_sfib (f · g).
  Proof.
    split.
    - exact comp_sfib_cleaving.
    - exact comp_lwhisker_is_cartesian.
  Defined.
End CompositionOfSFib.

Definition comp_mor_preserves_cartesian
           {B : bicat}
           {x y z : B}
           {f : x --> y}
           (Hf : internal_sfib f)
           {g : y --> z}
           (Hg : internal_sfib g)
  : mor_preserves_cartesian (f · g) g f.
Proof.
  intros w h₁ h₂ γ Hγ.
  apply from_is_cartesian_2cell_comp_rwhisker.
  - exact Hf.
  - exact Hg.
  - exact Hγ.
Defined.

(**
 7. Composition of Street opfibrations
 *)
Definition from_is_opcartesian_2cell_comp_rwhisker
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           (Hf : internal_sopfib f)
           {g : b --> c}
           (Hg : internal_sopfib g)
           {z : B}
           {h₁ h₂ : z --> a}
           {α : h₁ ==> h₂}
           (Hα : is_opcartesian_2cell_sopfib (f · g) α)
  : is_opcartesian_2cell_sopfib g (α ▹ f).
Proof.
  use is_cartesian_to_is_opcartesian_sfib.
  use from_is_cartesian_2cell_comp_rwhisker.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
  - apply internal_sopfib_is_internal_sfib.
    exact Hg.
  - use is_opcartesian_to_is_cartesian_sfib.
    exact Hα.
Defined.

Definition comp_sopfib
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : internal_sopfib f)
           (Hg : internal_sopfib g)
  : internal_sopfib (f · g).
Proof.
  apply internal_sfib_is_internal_sopfib.
  use comp_sfib.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
  - apply internal_sopfib_is_internal_sfib.
    exact Hg.
Defined.

Definition comp_mor_preserves_opcartesian
           {B : bicat}
           {x y z : B}
           {f : x --> y}
           (Hf : internal_sopfib f)
           {g : y --> z}
           (Hg : internal_sopfib g)
  : mor_preserves_opcartesian (f · g) g f.
Proof.
  intros w h₁ h₂ γ Hγ.
  apply from_is_opcartesian_2cell_comp_rwhisker.
  - exact Hf.
  - exact Hg.
  - exact Hγ.
Defined.
