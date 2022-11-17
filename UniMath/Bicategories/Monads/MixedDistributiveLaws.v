(******************************************************************************

 Mixed distributive laws distributive laws in bicategories

 Monads in the bicategory of comonads are the same as mixed distributive laws

 ******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInOp2Bicat.

Local Open Scope cat.

Section MixedDistributiveLaw.
  Context {B : bicat}
          (m₁ : comnd B)
          (m₂ : disp_mnd B (ob_of_comnd m₁)).

  Let x : B := ob_of_comnd m₁.
  Let e : x --> x := endo_of_comnd m₁.
  Let ε : e ==> id₁ _ := counit_of_comnd m₁.
  Let δ : e ==> e · e := comult_of_comnd m₁.

  Let f : x --> x := pr11 m₂.
  Let η : id₁ _ ==> f := pr121 m₂.
  Let μ : f · f ==> f := pr221 m₂.

  Definition mixed_distr_law_data
    : UU
    := e · f ==> f · e.

  Definition mixed_distr_law_laws
             (τ : mixed_distr_law_data)
    : UU
    := ((ε ▹ f)
        • lunitor f
        =
        τ
        • (f ◃ ε)
        • runitor f)
       ×
       ((δ ▹ f)
        • rassociator e e f
        • (e ◃ τ)
        • lassociator e f e
        • (τ ▹ e)
        • rassociator f e e
        =
        τ
        • (f ◃ δ))
       ×
       ((e ◃ η)
        • τ
        =
        runitor e
        • linvunitor e
        • (η ▹ e))
       ×
       ((e ◃ μ)
        • τ
        =
        lassociator e f f
        • (τ ▹ f)
        • rassociator f e f
        • (f ◃ τ)
        • lassociator f f e
        • (μ ▹ e)).

  Definition mixed_distr_law
    : UU
    := ∑ (τ : mixed_distr_law_data), mixed_distr_law_laws τ.

  Definition make_mixed_distr_law
             (τ : mixed_distr_law_data)
             (Hτ : mixed_distr_law_laws τ)
    : mixed_distr_law
    := τ ,, Hτ.

  Coercion mixed_distr_law_to_cell
           (τ : mixed_distr_law)
    : e · f ==> f · e
    := pr1 τ.
End MixedDistributiveLaw.

Section FromBicatToMixedDistrLaw.
  Context {B : bicat}
          (m : mnd (op2_bicat (mnd (op2_bicat B)))).

  Let x : B := pr1 (ob_of_mnd m).
  Let e : x --> x := pr112 (ob_of_mnd m).
  Let ε : e ==> id₁ _ := pr1 (pr212 (ob_of_mnd m)).
  Let δ : e ==> e · e := pr2 (pr212 (ob_of_mnd m)).

  Let f : x --> x := pr1 (endo_of_mnd m).
  Let η : id₁ _ ==> f := pr1 (unit_of_mnd m).
  Let μ : f · f ==> f := pr1 (mult_of_mnd m).

  Definition to_comnd_data_of_mixed_distr_law
    : comnd_data B.
  Proof.
    use make_comnd_data.
    - exact x.
    - exact e.
    - exact ε.
    - exact δ.
  Defined.

  Definition to_comnd_laws_of_mixed_distr_law
    : comnd_laws to_comnd_data_of_mixed_distr_law.
  Proof.
    repeat split.
    - unfold comnd_counit_left_law.
      rewrite !vassocl.
      exact (pr122 (ob_of_mnd m)).
    - unfold comnd_counit_right_law.
      rewrite !vassocl.
      exact (pr1 (pr222 (ob_of_mnd m))).
    - unfold comnd_comult_assoc_law.
      rewrite !vassocl.
      exact (pr2 (pr222 (ob_of_mnd m))).
  Qed.

  Definition to_comnd_of_mixed_distr_law
    : comnd B.
  Proof.
    use make_comnd.
    - exact to_comnd_data_of_mixed_distr_law.
    - exact to_comnd_laws_of_mixed_distr_law.
  Defined.

  Definition to_mnd_data_of_mixed_distr_law
    : mnd_data B.
  Proof.
    use make_mnd_data.
    - exact x.
    - exact f.
    - exact η.
    - exact μ.
  Defined.

  Definition to_is_mnd_of_mixed_distr_law
    : is_mnd B to_mnd_data_of_mixed_distr_law.
  Proof.
    repeat split.
    - exact (maponpaths pr1 (mnd_unit_left m)).
    - exact (maponpaths pr1 (mnd_unit_right m)).
    - exact (maponpaths pr1 (mnd_mult_assoc m)).
  Qed.

  Definition to_mnd_of_mixed_distr_law
    : mnd B.
  Proof.
    use make_mnd.
    - exact to_mnd_data_of_mixed_distr_law.
    - exact to_is_mnd_of_mixed_distr_law.
  Defined.

  Definition to_cell_of_mixed_distr_law
    : mixed_distr_law_data
        to_comnd_of_mixed_distr_law
        (pr2 to_mnd_of_mixed_distr_law)
    := pr112 (endo_of_mnd m).

  Definition to_laws_of_mixed_distr_law
    : mixed_distr_law_laws _ _ to_cell_of_mixed_distr_law.
  Proof.
    repeat split.
    - cbn.
      rewrite !vassocl.
      exact (pr1 (pr212 (endo_of_mnd m))).
    - cbn.
      rewrite !vassocl.
      exact (pr2 (pr212 (endo_of_mnd m))).
    - exact (pr112 (unit_of_mnd m)).
    - refine (pr112 (mult_of_mnd m) @ _).
      cbn.
      rewrite !vassocl.
      apply idpath.
  Qed.

  Definition to_mixed_distr_law
    : mixed_distr_law
        to_comnd_of_mixed_distr_law
        (pr2 to_mnd_of_mixed_distr_law).
  Proof.
    use make_mixed_distr_law.
    - exact to_cell_of_mixed_distr_law.
    - exact to_laws_of_mixed_distr_law.
  Defined.
End FromBicatToMixedDistrLaw.
