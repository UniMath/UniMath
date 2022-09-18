(******************************************************************************

 Distributive law

 In this file, we define distributive laws in bicategories. We give two
 definitions: one that makes use of monad functors and the other makes use of
 monad opfunctors. We also show that the two definitions are equivalen.t

 Contents
 1. First definition
 2. Second definition
 3. The equivalence

 ******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInOp1Bicat.

Local Open Scope cat.

Section DistributiveLaw.
  Context {B : bicat}
          {x : B}
          {dm₁ dm₂ : disp_mnd B x}.

  Let m₁ : mnd B := x ,, dm₁.
  Let m₂ : mnd B := x ,, dm₂.

  Let f : x --> x := endo_of_mnd m₁.
  Let g : x --> x := endo_of_mnd m₂.

  Let η₁ : id₁ _ ==> f := unit_of_mnd m₁.
  Let η₂ : id₁ _ ==> g := unit_of_mnd m₂.

  Let μ₁ : f · f ==> f := mult_of_mnd m₁.
  Let μ₂ : g · g ==> g := mult_of_mnd m₂.

  (**
   1. First definition
   *)
  Section Laws.
    Context (α : g · f ==> f · g).

    Definition distr_law_unit_law_1
      : UU
      := linvunitor g • (η₁ ▹ g)
         =
         (rinvunitor g • (g ◃ η₁)) • α.

    Definition distr_law_mu_law_1
      : UU
      := lassociator _ _ _
         • (α ▹ f)
         • rassociator _ _ _
         • (f ◃ α)
         • lassociator _ _ _
         • (μ₁ ▹ g)
         =
         (g ◃ μ₁)
         • α.

    Definition distr_law_unit_law_2
      : UU
      := lunitor _ • rinvunitor _ • (f ◃ η₂)
         =
         (η₂ ▹ f) • α.

    Definition distr_law_mu_law_2
      : UU
      := rassociator _ _ _
         • (g ◃ α)
         • lassociator _ _ _
         • (α ▹ g)
         • rassociator _ _ _
         • (f ◃ μ₂)
         =
         (μ₂ ▹ f)
         • α.
  End Laws.

  Definition is_distr_law
             (α : g · f ==> f · g)
    : UU
    := distr_law_unit_law_1 α
       ×
       distr_law_mu_law_1 α
       ×
       distr_law_unit_law_2 α
       ×
       distr_law_mu_law_2 α.

  Definition isaprop_is_distr_law
             (α : g · f ==> f · g)
    : isaprop (is_distr_law α).
  Proof.
    repeat (use isapropdirprod) ; apply cellset_property.
  Qed.

  Definition distr_law
    : UU
    := ∑ (α : g · f ==> f · g), is_distr_law α.

  Coercion cell_from_distr_law
           (α : distr_law)
    : g · f ==> f · g
    := pr1 α.

  Section Projections.
    Context (α : distr_law).

    Definition unit_law_1_from_distr_law
      : linvunitor g • (η₁ ▹ g)
        =
        (rinvunitor g • (g ◃ η₁)) • α
      := pr12 α.

    Definition mu_law_1_from_distr_law
      : lassociator _ _ _
        • (α ▹ f)
        • rassociator _ _ _
        • (f ◃ α)
        • lassociator _ _ _
        • (μ₁ ▹ g)
        =
        (g ◃ μ₁)
        • α
      := pr122 α.

    Definition unit_law_2_from_distr_law
      : lunitor _ • rinvunitor _ • (f ◃ η₂)
        =
        (η₂ ▹ f) • α
      := pr1 (pr222 α).

    Definition mu_law_2_from_distr_law
      : rassociator _ _ _
        • (g ◃ α)
        • lassociator _ _ _
        • (α ▹ g)
        • rassociator _ _ _
        • (f ◃ μ₂)
        =
        (μ₂ ▹ f)
        • α
      := pr2 (pr222 α).

    Definition mnd_mor_from_distr_law
      : m₁ --> m₁.
    Proof.
      use make_mnd_mor.
      - use make_mnd_mor_data.
        + exact g.
        + exact (pr1 α).
      - split.
        + exact unit_law_1_from_distr_law.
        + exact mu_law_1_from_distr_law.
    Defined.

    Definition mnd_unit_cell_from_distr_law
      : id₁ _ ==> mnd_mor_from_distr_law.
    Proof.
      use make_mnd_cell.
      - exact η₂.
      - exact unit_law_2_from_distr_law.
    Defined.

    Definition mnd_mu_cell_from_distr_law
      : mnd_mor_from_distr_law · mnd_mor_from_distr_law
        ==>
        mnd_mor_from_distr_law.
    Proof.
      use make_mnd_cell.
      - exact μ₂.
      - exact mu_law_2_from_distr_law.
    Defined.
  End Projections.

  (**
   2. Second definition
   *)
  Definition is_distr_law_op
             (α : g · f ==> f · g)
    : UU
    := (rinvunitor f • (f ◃ unit_of_mnd m₂)
        =
        linvunitor f • (unit_of_mnd m₂ ▹ f) • α)
       ×
       (rassociator _ _ _
        • (_ ◃ α)
        • lassociator _ _ _
        • (α ▹ _)
        • rassociator _ _ _
        • (f ◃ μ₂)
        =
        (μ₂ ▹ f) • α)
       ×
       (runitor g • linvunitor g • (η₁ ▹ endo_of_mnd m₂) = (g ◃ η₁) • α)
       ×
       (lassociator _ _ _
        • (α ▹ f)
        • rassociator _ _ _
        • (f ◃ α)
        • lassociator _ _ _
        • (μ₁ ▹ g)
        =
        (g ◃ μ₁) • α).

  Definition isaprop_is_distr_law_op
             (α : g · f ==> f · g)
    : isaprop (is_distr_law_op α).
  Proof.
    repeat (use isapropdirprod) ; apply cellset_property.
  Qed.

  Section FunctorsFromDistrLawOp.
    Context (α : g · f ==> f · g)
            (Hα : is_distr_law_op α).

    Definition mnd_opfunctor_from_distr_law_op
      : mnd_opmor m₂ m₂.
    Proof.
      use make_mnd_opmor.
      - use make_mnd_opmor_data.
        + exact f.
        + exact α.
      - split.
        + apply Hα.
        + apply Hα.
    Defined.

    Definition mnd_unit_cell_from_distr_law_op
      : mnd_opcell
          (mnd_id_opmor _)
          mnd_opfunctor_from_distr_law_op.
    Proof.
      use make_mnd_opcell.
      - exact η₁.
      - apply Hα.
    Defined.

    Definition mnd_mu_cell_from_distr_law_op
      : mnd_opcell
          (mnd_opmor_comp
             mnd_opfunctor_from_distr_law_op
             mnd_opfunctor_from_distr_law_op)
          mnd_opfunctor_from_distr_law_op.
    Proof.
      use make_mnd_opcell.
      - exact μ₁.
      - apply Hα.
    Defined.
  End FunctorsFromDistrLawOp.

  (**
   3. The equivalence
   *)
  Definition is_distr_law_to_is_distr_law_op
             (α : g · f ==> f · g)
             (Hα : is_distr_law α)
    : is_distr_law_op α.
  Proof.
    repeat split.
    - rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      exact (pr122 Hα).
    - exact (pr222 Hα).
    - rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      exact (pr1 Hα).
    - exact (pr12 Hα).
  Qed.

  Definition is_distr_law_op_to_is_distr_law
             (α : g · f ==> f · g)
             (Hα : is_distr_law_op α)
    : is_distr_law α.
  Proof.
    repeat split ; red.
    - rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      exact (pr122 Hα).
    - exact (pr222 Hα).
    - rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      exact (pr1 Hα).
    - exact (pr12 Hα).
  Qed.

  Definition is_distr_law_weq_is_distr_law_op
             (α : g · f ==> f · g)
    : is_distr_law α ≃ is_distr_law_op α.
  Proof.
    use weqimplimpl.
    - exact (is_distr_law_to_is_distr_law_op α).
    - exact (is_distr_law_op_to_is_distr_law α).
    - apply isaprop_is_distr_law.
    - apply isaprop_is_distr_law_op.
  Defined.
End DistributiveLaw.

Arguments distr_law {_ _} _ _.
