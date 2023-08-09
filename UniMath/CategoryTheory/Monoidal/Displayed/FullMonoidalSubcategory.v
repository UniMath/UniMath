(** constructs the full monoidal subcategory through a displayed monoidal category *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section FullSubcategory.

  Import BifunctorNotations.
  Import MonoidalNotations.

  Context {C: category} (V : monoidal C)
    (P : C -> UU) (Punit : P I_{V}) (Ptensor : ∏ x y, P x -> P y -> P (x ⊗_{V} y)).

Definition full_monoidal_sub_disp_data : disp_monoidal_data (disp_full_sub C P) V.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * exact Ptensor.
      * abstract (split; intros; exact tt).
    + abstract (split5; red; intros; apply isProofIrrelevantUnit).
  - exists Punit.
    abstract (split7; try (intros c Pc; exact tt);
              red; intros; exact tt).
Defined.

Lemma full_monoidal_sub_disp_laws : disp_monoidal_laws full_monoidal_sub_disp_data.
Proof.
  repeat split; try red; intros; apply isProofIrrelevantUnit.
Qed.

Definition full_monoidal_sub_disp : disp_monoidal (disp_full_sub C P) V.
Proof.
  use tpair.
  - apply full_monoidal_sub_disp_data.
  - apply full_monoidal_sub_disp_laws.
Defined.

Definition full_monoidal_subcat : monoidal (total_category (disp_full_sub C P))
  := total_monoidal full_monoidal_sub_disp.

End FullSubcategory.
