(*****************************************************************************

 Monads in the bicategory of monads

 Monads in the bicategory of monads in `B` are the same as distributive laws
 in `B`.

 Contents
 1. From monads to distributive laws
 2. From distributive laws to monads

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.DistributiveLaws.

Local Open Scope cat.

(**
 1. From monads to distributive laws
 *)
Section ToMonadsInMonads.
  Context {B : bicat}
          (m : mnd (mnd B)).

  Let m₁ : mnd B := ob_of_mnd m.

  Let x : B := ob_of_mnd m₁.

  Let dm₁ : disp_mnd B x := pr2 m₁.

  Let fm : m₁ --> m₁ := endo_of_mnd m.

  Let ηm : id₁ _ ==> fm := unit_of_mnd m.

  Let μm : fm · fm ==> fm := mult_of_mnd m.

  Definition other_mnd_data
    : disp_mnd_data B x.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (mor_of_mnd_mor fm).
    - exact (cell_of_mnd_cell ηm).
    - exact (cell_of_mnd_cell μm).
  Defined.

  Definition other_mnd_is_mnd
    : is_mnd B (x ,, other_mnd_data).
  Proof.
    repeat split.
    - exact (maponpaths pr1 (mnd_unit_left m)).
    - exact (maponpaths pr1 (mnd_unit_right m)).
    - exact (maponpaths pr1 (mnd_mult_assoc m)).
  Qed.

  Definition other_mnd
    : disp_mnd B x
    := other_mnd_data ,, other_mnd_is_mnd.

  Let dm₂ : disp_mnd B x := other_mnd.

  Definition mnd_mnd_to_is_distr_law
    : @is_distr_law _ _ dm₁ dm₂ (mnd_mor_endo fm).
  Proof.
    repeat split ; red ; cbn.
    - exact (mnd_mor_unit fm).
    - exact (mnd_mor_mu fm).
    - exact (mnd_cell_endo ηm).
    - exact (mnd_cell_endo μm).
  Defined.

  Definition mnd_mnd_to_distr_law
    : distr_law dm₁ dm₂
    := mnd_mor_endo fm ,, mnd_mnd_to_is_distr_law.
End ToMonadsInMonads.

(**
 2. From distributive laws to monads
 *)
Section FromMonadsInMonads.
  Context {B : bicat}
          {x : B}
          {dm₁ dm₂ : disp_mnd B x}
          (l : distr_law dm₁ dm₂).

  Definition distr_law_to_mnd_mnd_ob
    : mnd B
    := x ,, dm₁.

  Definition distr_law_to_mnd_mnd_endo_data
    : mnd_mor_data distr_law_to_mnd_mnd_ob distr_law_to_mnd_mnd_ob.
  Proof.
    use make_mnd_mor_data.
    - exact (pr11 dm₂).
    - exact (cell_from_distr_law l).
  Defined.

  Definition distr_law_to_mnd_mnd_endo_laws
    : mnd_mor_laws distr_law_to_mnd_mnd_endo_data.
  Proof.
    split.
    - exact (unit_law_1_from_distr_law l).
    - exact (mu_law_1_from_distr_law l).
  Defined.

  Definition distr_law_to_mnd_mnd_endo
    : distr_law_to_mnd_mnd_ob --> distr_law_to_mnd_mnd_ob.
  Proof.
    use make_mnd_mor.
    - exact distr_law_to_mnd_mnd_endo_data.
    - exact distr_law_to_mnd_mnd_endo_laws.
  Defined.

  Definition distr_law_to_mnd_mnd_unit
    : id₁ distr_law_to_mnd_mnd_ob ==> distr_law_to_mnd_mnd_endo.
  Proof.
    use make_mnd_cell.
    - exact (pr121 dm₂).
    - exact (unit_law_2_from_distr_law l).
  Defined.

  Definition distr_law_to_mnd_mnd_mult
    : distr_law_to_mnd_mnd_endo · distr_law_to_mnd_mnd_endo
      ==>
      distr_law_to_mnd_mnd_endo.
  Proof.
    use make_mnd_cell.
    - exact (pr221 dm₂).
    - exact (mu_law_2_from_distr_law l).
  Defined.

  Definition distr_law_to_mnd_mnd_data
    : mnd_data (mnd B).
  Proof.
    use make_mnd_data.
    - exact distr_law_to_mnd_mnd_ob.
    - exact distr_law_to_mnd_mnd_endo.
    - exact distr_law_to_mnd_mnd_unit.
    - exact distr_law_to_mnd_mnd_mult.
  Defined.

  Definition distr_law_to_mnd_mnd_is_mnd
    : is_mnd (mnd B) distr_law_to_mnd_mnd_data.
  Proof.
    refine (_ ,, _ ,, _) ; use eq_mnd_cell ; cbn.
    - apply dm₂.
    - apply dm₂.
    - apply dm₂.
  Qed.

  Definition distr_law_to_mnd_mnd
    : mnd (mnd B).
  Proof.
    use make_mnd.
    - exact distr_law_to_mnd_mnd_data.
    - exact distr_law_to_mnd_mnd_is_mnd.
  Defined.
End FromMonadsInMonads.
