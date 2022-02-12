(**
 Preservation of morphisms by pullbacks

 Contents:
 1. Pullbacks of faithful 1-cells
 2. Pullbacks of fully faithful 1-cells
 3. Pullbacks of conservative 1-cells
 4. Pullbacks of discrete 1-cells
 5. Pullbacks of Street fibrations
 6. Pullbacks of Street opfibrations
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.

Local Open Scope cat.

(**
 1. Pullbacks of faithful 1-cells
 *)
Definition pb_of_faithful_1cell
           {B : bicat}
           {x₁ x₂ y₁ y₂ : B}
           {p₁ : x₁ --> y₁}
           {p₂ : x₁ --> x₂}
           {f : y₁ --> y₂}
           {g : x₂ --> y₂}
           {γ : invertible_2cell (p₁ · f) (p₂ · g)}
           (pb := make_pb_cone x₁ p₁ p₂ γ)
           (H : has_pb_ump pb)
           (Hg : faithful_1cell g)
  : faithful_1cell p₁.
Proof.
  intros z h₁ h₂ α β p.
  use (pb_ump_eq
         H
         h₁ h₂
         (α ▹ _) (α ▹ _)).
  - rewrite !vassocl.
    rewrite rwhisker_rwhisker_alt.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite  lassociator_rassociator.
      apply id2_left.
    }
    rewrite <- vcomp_whisker.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  - apply idpath.
  - apply idpath.
  - exact (!p).
  - cbn.
    use (faithful_1cell_eq_cell Hg).
    use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
    rewrite !rwhisker_rwhisker.
    apply maponpaths_2.
    use (vcomp_lcancel (_ ◃ γ)) ; [ is_iso ; apply property_from_invertible_2cell | ].
    rewrite <- !vcomp_whisker.
    apply maponpaths_2.
    use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
    rewrite <- !rwhisker_rwhisker.
    do 2 apply maponpaths.
    exact (!p).
Qed.

(**
 2. Pullbacks of fully faithful 1-cells
 *)
Section PbOfFullyFaithful.
  Context {B : bicat}
          {x₁ x₂ y₁ y₂ : B}
          {p₁ : x₁ --> y₁}
          {p₂ : x₁ --> x₂}
          {f : y₁ --> y₂}
          {g : x₂ --> y₂}
          {γ : invertible_2cell (p₁ · f) (p₂ · g)}
          (pb := make_pb_cone x₁ p₁ p₂ γ)
          (H : has_pb_ump pb)
          (Hg : fully_faithful_1cell g).

  Section Fullness.
    Context {z : B}
            {h₁ h₂ : z --> x₁}
            (αf : h₁ · p₁ ==> h₂ · p₁).

    Let ψ : h₁ · p₂ · g ==> h₂ · p₂ · g
      := rassociator _ _ _
         • (_ ◃ γ^-1)
         • lassociator _ _ _
         • (αf ▹ _)
         • rassociator _ _ _
         • (_ ◃ γ)
         • lassociator _ _ _.

    Let ζ : h₁ · p₂ ==> h₂ · p₂
      := fully_faithful_1cell_inv_map Hg ψ.

    Local Lemma pb_of_fully_faithful_1cell_2cell_help_eq
      : (h₁ ◃ γ)
        • lassociator h₁ p₂ g
        • (ζ ▹ g)
        • rassociator h₂ p₂ g
        =
        lassociator h₁ p₁ f
        • (αf ▹ f)
        • rassociator h₂ p₁ f
        • (h₂ ◃ γ).
    Proof.
      unfold ζ.
      rewrite fully_faithful_1cell_inv_map_eq.
      unfold ψ.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition pb_of_fully_faithful_1cell_2cell
      : h₁ ==> h₂.
    Proof.
      use (pb_ump_cell H h₁ h₂ αf).
      - exact ζ.
      - exact pb_of_fully_faithful_1cell_2cell_help_eq.
    Defined.

    Definition pb_of_fully_faithful_1cell_2cell_eq
      : pb_of_fully_faithful_1cell_2cell ▹ p₁ = αf.
    Proof.
      unfold pb_of_fully_faithful_1cell_2cell.
      apply (pb_ump_cell_pr1 H).
    Qed.
  End Fullness.

  Definition pb_of_fully_faithful_1cell
    : fully_faithful_1cell p₁.
  Proof.
    use make_fully_faithful.
    - exact (pb_of_faithful_1cell H (pr1 Hg)).
    - intros z h₁ h₂ αf.
      exact (pb_of_fully_faithful_1cell_2cell αf
             ,,
             pb_of_fully_faithful_1cell_2cell_eq αf).
  Defined.
End PbOfFullyFaithful.

(**
 3. Pullbacks of conservative 1-cells
 *)
Section PbOfConservative.
  Context {B : bicat}
          {x₁ x₂ y₁ y₂ : B}
          {p₁ : x₁ --> y₁}
          {p₂ : x₁ --> x₂}
          {f : y₁ --> y₂}
          {g : x₂ --> y₂}
          {γ : invertible_2cell (p₁ · f) (p₂ · g)}
          (pb := make_pb_cone x₁ p₁ p₂ γ)
          (H : has_pb_ump pb)
          (Hg : conservative_1cell g).

  Section ReflectIso.
    Context {z : B}
            {h₁ h₂ : z --> x₁}
            {α : h₁ ==> h₂}
            (Hα : is_invertible_2cell (α ▹ p₁)).

    Definition pb_reflect_iso_help
      : is_invertible_2cell (α ▹ p₂).
    Proof.
      apply (Hg z (h₁ · p₂) (h₂ · p₂) (α ▹ p₂)).
      use eq_is_invertible_2cell.
      - exact (rassociator _ _ _
               • (_ ◃ γ^-1)
               • lassociator _ _ _
               • ((α ▹ p₁) ▹ f)
               • rassociator _ _ _
               • (_ ◃ γ)
               • lassociator _ _ _).
      - abstract
          (rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite rwhisker_rwhisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite <- vcomp_whisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !rwhisker_rwhisker ;
           rewrite !vassocl ;
           rewrite lassociator_rassociator ;
           apply id2_right).
      - use is_invertible_2cell_vcomp ; [ | is_iso ].
        use is_invertible_2cell_vcomp ; [ | is_iso ; apply property_from_invertible_2cell ].
        use is_invertible_2cell_vcomp ; [ | is_iso ].
        use is_invertible_2cell_vcomp ; [ is_iso | ].
        apply is_invertible_2cell_rwhisker.
        exact Hα.
    Defined.

    Local Lemma pb_reflect_iso_eq
      : (h₁ ◃ γ)
        • lassociator h₁ p₂ g
        • ((α ▹ p₂) ▹ g)
        • rassociator h₂ p₂ g
        =
        lassociator h₁ p₁ f
        • ((α ▹ p₁) ▹ f)
        • rassociator h₂ p₁ f
        • (h₂ ◃ γ).
    Proof.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      }
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition pb_reflect_iso
      : is_invertible_2cell α.
    Proof.
      simple refine (eq_is_invertible_2cell
                       _
                       (is_invertible_2cell_pb_ump_cell
                          H
                          pb_reflect_iso_eq
                          Hα
                          pb_reflect_iso_help)).
      use (pb_ump_eq H h₁ h₂ (α ▹ p₁) (α ▹ p₂)).
      - apply pb_reflect_iso_eq.
      - apply pb_ump_cell_pr1.
      - apply pb_ump_cell_pr2.
      - apply idpath.
      - apply idpath.
    Defined.
  End ReflectIso.

  Definition pb_of_conservative_1cell
    : conservative_1cell p₁.
  Proof.
    intros z h₁ h₂ α Hα.
    exact (pb_reflect_iso Hα).
  Defined.
End PbOfConservative.

(**
 4. Pullbacks of discrete 1-cells
 *)
Definition pb_of_discrete_1cell
           {B : bicat}
           {x₁ x₂ y₁ y₂ : B}
           {p₁ : x₁ --> y₁}
           {p₂ : x₁ --> x₂}
           {f : y₁ --> y₂}
           {g : x₂ --> y₂}
           {γ : invertible_2cell (p₁ · f) (p₂ · g)}
           (pb := make_pb_cone x₁ p₁ p₂ γ)
           (H : has_pb_ump pb)
           (Hg : discrete_1cell g)
  : discrete_1cell p₁.
Proof.
  split.
  - exact (pb_of_faithful_1cell H (pr1 Hg)).
  - exact (pb_of_conservative_1cell H (pr2 Hg)).
Defined.

(**
 5. Pullbacks of Street fibrations
 *)
Section PullbackOfSFib.
  Context {B : bicat}
          {e₁ e₂ b₁ b₂ : B}
          {p₁ : e₁ --> b₁}
          {p₂ : e₂ --> b₂}
          {fe : e₁ --> e₂}
          {fb : b₁ --> b₂}
          {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
          (pb := make_pb_cone e₁ fe p₁ γ)
          (H : has_pb_ump pb)
          (Hf : internal_sfib p₂).

  Section ToPBCartesian.
    Context {x : B}
            {g₁ g₂ : x --> e₁}
            (α : g₁ ==> g₂)
            (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
            {h : x --> e₁}
            {β : h ==> g₂}
            {δp : h · p₁ ==> g₁ · p₁}
            (q : β ▹ p₁ = δp • (α ▹ p₁)).

    Definition to_pb_cartesian_unique
      : isaprop (∑ δ, δ ▹ p₁ = δp × δ • α = β).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use (pb_ump_eq H).
      - exact (pr1 φ₁ ▹ fe).
      - exact δp.
      - cbn.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ].
        cbn.
        rewrite <- rwhisker_rwhisker.
        apply maponpaths.
        rewrite (pr12 φ₁).
        apply idpath.
      - apply idpath.
      - exact (pr12 φ₁).
      - cbn.
        use (is_cartesian_2cell_sfib_factor_unique _ Hα).
        + exact (β ▹ fe).
        + exact (rassociator _ _ _
                 • (h ◃ γ)
                 • lassociator _ _ _
                 • (δp ▹ _)
                 • rassociator _ _ _
                 • (g₁ ◃ γ^-1)
                 • lassociator _ _ _).
        + rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
          rewrite !rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite <- vcomp_whisker.
          rewrite !vassocr.
          use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite <- rwhisker_rwhisker_alt.
          rewrite !vassocr.
          use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite rwhisker_vcomp.
          rewrite q.
          apply idpath.
        + rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
          rewrite !rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
          rewrite <- rwhisker_rwhisker_alt.
          apply maponpaths_2.
          apply maponpaths.
          exact (pr12 φ₂).
        + rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
          rewrite !rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
          rewrite <- rwhisker_rwhisker_alt.
          apply maponpaths_2.
          apply maponpaths.
          exact (pr12 φ₁).
        + rewrite rwhisker_vcomp.
          rewrite (pr22 φ₂).
          apply idpath.
        + rewrite rwhisker_vcomp.
          rewrite (pr22 φ₁).
          apply idpath.
      - exact (pr12 φ₂).
    Qed.

    Let φ : h · fe · p₂ ==> g₁ · fe · p₂
      := rassociator _ _ _
         • (h ◃ γ)
         • lassociator _ _ _
         • (δp ▹ fb)
         • rassociator _ _ _
         • (g₁ ◃ γ^-1)
         • lassociator _ _ _.

    Local Proposition φ_eq
      : (β ▹ fe) ▹ p₂ = φ • ((α ▹ fe) ▹ p₂).
    Proof.
      unfold φ ; clear φ.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_rwhisker_alt.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      apply maponpaths.
      exact q.
    Qed.

    Let to_pb_cartesian_cell_on_pr1
      : h · fe ==> g₁ · fe
      := is_cartesian_2cell_sfib_factor _ Hα _ _ φ_eq.

    Local Definition to_pb_cartesian_cell_eq
      : (h ◃ γ)
          • lassociator h p₁ fb
          • (δp ▹ fb)
          • rassociator g₁ p₁ fb
        =
        lassociator h fe p₂
                    • (to_pb_cartesian_cell_on_pr1 ▹ p₂)
                    • rassociator g₁ fe p₂
                    • (g₁ ◃ γ).
    Proof.
      unfold to_pb_cartesian_cell_on_pr1, φ.
      rewrite is_cartesian_2cell_sfib_factor_over.
      rewrite !vassocr.
      rewrite lassociator_rassociator, id2_left.
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lassociator_rassociator, id2_left.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition to_pb_cartesian_cell
      : h ==> g₁.
    Proof.
      use (pb_ump_cell H).
      - exact to_pb_cartesian_cell_on_pr1.
      - exact δp.
      - exact to_pb_cartesian_cell_eq.
    Defined.

    Definition to_pb_cartesian_comm
      : to_pb_cartesian_cell • α = β.
    Proof.
      unfold to_pb_cartesian_cell.
      use (pb_ump_eq H).
      - exact (to_pb_cartesian_cell_on_pr1 • (α ▹ fe)).
      - exact (δp • (α ▹ p₁)).
      - cbn ; unfold to_pb_cartesian_cell_on_pr1.
        rewrite <- q.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        rewrite is_cartesian_2cell_sfib_factor_over.
        rewrite rwhisker_rwhisker_alt.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite lassociator_rassociator, id2_left.
        rewrite <- vcomp_whisker.
        rewrite !vassocr.
        apply maponpaths_2.
        unfold φ.
        rewrite !vassocr.
        rewrite lassociator_rassociator, id2_left.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 5 apply maponpaths.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          apply id2_left.
        }
        rewrite <- vcomp_whisker.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker_alt.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite <- q.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          rewrite vcomp_whisker.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite lwhisker_id2.
        apply id2_left.
      - cbn ; unfold to_pb_cartesian_cell_on_pr1.
        rewrite <- rwhisker_vcomp.
        apply maponpaths_2.
        apply (pb_ump_cell_pr1 H).
      - cbn ; unfold to_pb_cartesian_cell_on_pr1.
        rewrite <- rwhisker_vcomp.
        apply maponpaths_2.
        apply (pb_ump_cell_pr2 H).
      - cbn ; unfold to_pb_cartesian_cell_on_pr1.
        refine (!_).
        apply is_cartesian_2cell_sfib_factor_comm.
      - exact q.
    Qed.
  End ToPBCartesian.

  Definition to_pb_cartesian
             {x : B}
             {g₁ g₂ : x --> e₁}
             (α : g₁ ==> g₂)
             (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
    : is_cartesian_2cell_sfib p₁ α.
  Proof.
    intros h β δp q.
    use iscontraprop1.
    - exact (to_pb_cartesian_unique α Hα q).
    - simple refine (_ ,, _ ,, _).
      + exact (to_pb_cartesian_cell α Hα q).
      + apply (pb_ump_cell_pr2 H).
      + exact (to_pb_cartesian_comm α Hα q).
  Defined.

  Section Cleaving.
    Context {x : B}
            {h₁ : x --> b₁}
            {h₂ : x --> e₁}
            (α : h₁ ==> h₂ · p₁).

    Let x_to_e₂ : x --> e₂.
    Proof.
      use (internal_sfib_cleaving_lift_mor
             _ Hf).
      - exact (h₁ · fb).
      - exact (h₂ · fe).
      - exact ((α ▹ _)
                 • rassociator _ _ _
                 • (h₂ ◃ γ^-1)
                 • lassociator _ _ _).
    Defined.

    Definition pb_of_sfib_cleaving_cone
      : pb_cone p₂ fb.
    Proof.
      use make_pb_cone.
      - exact x.
      - exact x_to_e₂.
      - exact h₁.
      - apply internal_sfib_cleaving_com.
    Defined.

    Definition pb_of_sfib_cleaving_mor
      : x --> e₁
      := pb_ump_mor H pb_of_sfib_cleaving_cone.

    Definition pb_of_sfib_cleaving_cell
      : pb_of_sfib_cleaving_mor ==> h₂.
    Proof.
      use (pb_ump_cell H).
      - exact (pb_ump_mor_pr1 H pb_of_sfib_cleaving_cone
                              •
                              internal_sfib_cleaving_lift_cell _ _ _).
      - exact (pb_ump_mor_pr2 H pb_of_sfib_cleaving_cone • α).
      - abstract
          (simpl ;
           rewrite !vassocl ;
           etrans ;
           [ apply maponpaths_2 ;
             exact (pb_ump_mor_cell H pb_of_sfib_cleaving_cone)
           | ] ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           cbn ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite rassociator_lassociator ;
           rewrite id2_left ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             apply idpath
           | ] ;
           refine (!_) ;
           etrans ;
           [ apply maponpaths_2 ;
             apply internal_sfib_cleaving_over
           | ] ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           apply id2_right).
    Defined.

    Definition pb_of_sfib_cleaving_over
      : invertible_2cell (pb_of_sfib_cleaving_mor · p₁) h₁
      := pb_ump_mor_pr2 H pb_of_sfib_cleaving_cone.

    Definition pb_of_sfib_cleaving_commute
      : pb_of_sfib_cleaving_cell ▹ p₁ = pb_of_sfib_cleaving_over • α.
    Proof.
      apply (pb_ump_cell_pr2 H).
    Defined.

    Definition pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib
      : is_cartesian_2cell_sfib p₁ pb_of_sfib_cleaving_cell.
    Proof.
      apply to_pb_cartesian.
      refine (is_cartesian_eq _ (!(pb_ump_cell_pr1 H _ _ _ _ _)) _).
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        apply property_from_invertible_2cell.
      - apply internal_sfib_cleaving_is_cartesian.
    Defined.
  End Cleaving.

  Definition pb_of_sfib_cleaving
    : internal_sfib_cleaving p₁
    := λ x h₁ h₂ α,
       pb_of_sfib_cleaving_mor α
       ,,
       pb_of_sfib_cleaving_cell α
       ,,
       pb_of_sfib_cleaving_over α
       ,,
       pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib α
       ,,
       pb_of_sfib_cleaving_commute α.

  Section FromPBCartesian.
    Context {x : B}
            {g₁ g₂ : x --> e₁}
            (α : g₁ ==> g₂)
            (Hα : is_cartesian_2cell_sfib p₁ α).

    Let g₀ : x --> e₁
      := pb_of_sfib_cleaving_mor (α ▹ p₁).

    Let β : g₀ ==> g₂
      := pb_of_sfib_cleaving_cell (α ▹ p₁).

    Let Hβ : is_cartesian_2cell_sfib p₁ β.
    Proof.
      apply pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib.
    Defined.

    Local Lemma path_for_invertible_between_cartesians
      : α ▹ p₁ = (pb_of_sfib_cleaving_over (α ▹ p₁))^-1 • (β ▹ p₁).
    Proof.
      unfold β.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pb_of_sfib_cleaving_commute.
      }
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    Qed.

    Let δ : invertible_2cell g₁ g₀
      := invertible_between_cartesians
           Hα
           Hβ
           (inv_of_invertible_2cell (pb_of_sfib_cleaving_over (α ▹ p₁)))
           path_for_invertible_between_cartesians.

    Definition from_pb_cartesian
      : is_cartesian_2cell_sfib p₂ (α ▹ fe).
    Proof.
      assert (p : δ • β = α).
      {
        apply is_cartesian_2cell_sfib_factor_comm.
      }
      use (is_cartesian_eq _ (maponpaths (λ z, z ▹ fe) p)).
      use (is_cartesian_eq _ (rwhisker_vcomp _ _ _)).
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        is_iso.
        apply property_from_invertible_2cell.
      - unfold β, pb_of_sfib_cleaving_cell.
        rewrite (pb_ump_cell_pr1 H).
        use vcomp_is_cartesian_2cell_sfib.
        + apply invertible_is_cartesian_2cell_sfib.
          apply property_from_invertible_2cell.
        + apply internal_sfib_cleaving_is_cartesian.
    Defined.
  End FromPBCartesian.

  Definition pb_lwhisker_is_cartesian
    : lwhisker_is_cartesian p₁.
  Proof.
    intros x y h f g α Hα.
    apply to_pb_cartesian.
    use is_cartesian_eq.
    - exact (rassociator _ _ _ • (h ◃ (α ▹ fe)) • lassociator _ _ _).
    - abstract
        (rewrite rwhisker_lwhisker_rassociator ;
         rewrite !vassocl ;
         rewrite rassociator_lassociator ;
         apply id2_right).
    - use vcomp_is_cartesian_2cell_sfib.
      + use vcomp_is_cartesian_2cell_sfib.
        * apply invertible_is_cartesian_2cell_sfib.
          is_iso.
        * apply (pr2 Hf).
          apply from_pb_cartesian.
          exact Hα.
      + apply invertible_is_cartesian_2cell_sfib.
        is_iso.
  Defined.

  Definition pb_of_sfib
    : internal_sfib p₁.
  Proof.
    split.
    - exact pb_of_sfib_cleaving.
    - exact pb_lwhisker_is_cartesian.
  Defined.

  Definition mor_preserves_cartesian_pb_pr1
    : mor_preserves_cartesian p₁ p₂ fe.
  Proof.
    intros x f g δ Hδ.
    apply from_pb_cartesian.
    exact Hδ.
  Defined.

  Definition mor_preserves_cartesian_pb_ump_mor
             {e₀ b₀ : B}
             (p₀ : e₀ --> b₀)
             (h₁ : e₀ --> e₂)
             (h₂ : b₀ --> b₁)
             (δ : invertible_2cell (h₁ · p₂) (p₀ · h₂ · fb))
             (cone := make_pb_cone e₀ h₁ (p₀ · h₂) δ)
             (Hh₁ : mor_preserves_cartesian p₀ p₂ h₁)
    : mor_preserves_cartesian
        p₀
        p₁
        (pb_ump_mor H cone).
  Proof.
    intros x f g ζ Hζ.
    apply to_pb_cartesian.
    assert (H₁ : is_cartesian_2cell_sfib p₂ (rassociator g (pb_ump_mor H cone) fe)) .
    {
      apply invertible_is_cartesian_2cell_sfib.
      is_iso.
    }
    assert (H₂ : is_cartesian_2cell_sfib p₂ ((g ◃ pb_ump_mor_pr1 H cone))).
    {
      apply invertible_is_cartesian_2cell_sfib.
      is_iso.
      apply property_from_invertible_2cell.
    }
    assert (H₃ : is_cartesian_2cell_sfib
                   p₂
                   (rassociator f (pb_ump_mor H cone) fe
                    • ((f ◃ pb_ump_mor_pr1 H cone)
                    • (ζ ▹ pb_cone_pr1 cone)))).
    {
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        is_iso.
      - use vcomp_is_cartesian_2cell_sfib.
        + apply invertible_is_cartesian_2cell_sfib.
          is_iso.
          apply property_from_invertible_2cell.
        + apply Hh₁.
          exact Hζ.
    }
    use (is_cartesian_2cell_sfib_postcomp
           p₂
           _
           (vcomp_is_cartesian_2cell_sfib _ H₁ H₂)
           H₃).
    abstract
      (rewrite vassocr ;
       rewrite rwhisker_rwhisker_alt ;
       rewrite vassocl ;
       rewrite vcomp_whisker ;
       apply idpath).
  Defined.
End PullbackOfSFib.

(**
 6. Pullbacks of Street fibrations
 *)
Definition pb_of_sopfib
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           (Hf : internal_sopfib p₂)
  : internal_sopfib p₁.
Proof.
  apply internal_sfib_is_internal_sopfib.
  use (@pb_of_sfib
         (op2_bicat B)
         e₁ e₂ b₁ b₂
         p₁ p₂ fe fb).
  - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
  - apply to_op2_has_pb_ump.
    exact H.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
Defined.

Definition mor_preserves_opcartesian_pb_pr1
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           (Hf : internal_sopfib p₂)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  apply mor_preserves_cartesian_to_mor_preserves_opcartesian.
  use (@mor_preserves_cartesian_pb_pr1
         (op2_bicat B)
         e₁ e₂ b₁ b₂
         p₁ p₂ fe fb).
  - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
  - apply to_op2_has_pb_ump.
    exact H.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
Defined.

Definition mor_preserves_opcartesian_pb_ump_mor
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           {e₀ b₀ : B}
           (p₀ : e₀ --> b₀)
           (h₁ : e₀ --> e₂)
           (h₂ : b₀ --> b₁)
           (δ : invertible_2cell (h₁ · p₂) (p₀ · h₂ · fb))
           (cone := make_pb_cone e₀ h₁ (p₀ · h₂) δ)
           (Hh₁ : mor_preserves_opcartesian p₀ p₂ h₁)
  : mor_preserves_opcartesian
      p₀
      p₁
      (pb_ump_mor H cone).
Proof.
  apply mor_preserves_cartesian_to_mor_preserves_opcartesian.
  exact (@mor_preserves_cartesian_pb_ump_mor
           (op2_bicat B)
           e₁ e₂ b₁ b₂
           p₁ p₂ fe fb
           _
           (to_op2_has_pb_ump _ H)
           e₀ b₀ p₀
           h₁ h₂
           (inv_of_invertible_2cell
              (bicat_invertible_2cell_is_op2_bicat_invertible_2cell
                 _ _
                 δ))
           (mor_preserves_opcartesian_to_mor_preserves_cartesian
              Hh₁)).
Defined.
