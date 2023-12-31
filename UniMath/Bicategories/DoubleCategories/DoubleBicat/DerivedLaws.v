Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.

Local Open Scope cat.
Local Open Scope double_bicat.

Proposition lunitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_v_square_bicat h₁ ⋆v s
    =
    linvunitor v₂ ▹s (lunitor v₁ ◃s s).
Proof.
  rewrite lunitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : lunitor v₂ ▹s (linvunitor v₁ ◃s id_v_square_bicat h₁ ⋆v s)
    =
    s.
Proof.
  rewrite lunitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !linvunitor_lunitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_h_square_bicat v₁ ⋆h s
    =
    linvunitor h₂ ▿s (lunitor h₁ ▵s s).
Proof.
  rewrite <- lunitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆v id_v_square_bicat h₂
    =
    rinvunitor v₂ ▹s (runitor v₁ ◃s s).
Proof.
  rewrite runitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor v₂ ▹s (rinvunitor v₁ ◃s s ⋆v id_v_square_bicat h₂)
    =
    s.
Proof.
  rewrite runitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆h id_h_square_bicat v₂
    =
    rinvunitor h₂ ▿s (runitor h₁ ▵s s).
Proof.
  rewrite <- runitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor h₂ ▿s (rinvunitor h₁ ▵s s ⋆h id_h_square_bicat v₂)
    =
    s.
Proof.
  rewrite runitor_h_comp_square'.
  rewrite !dwhisker_uwhisker_square.
  rewrite <- uwhisker_square_comp.
  rewrite <- dwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite dwhisker_square_id.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.
