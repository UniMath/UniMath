(* ******************************************************************************* *)
(** * Modifications between pseudo transformations
    Niccolò Veltri, Niels van der Weide
    April 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.

Local Open Scope cat.

Definition modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := prebicat_cells (psfunctor_bicat B B') σ τ.

Definition modification_data
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := ∏ (X : B), σ X ==> τ X.

Definition is_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification_data σ τ)
  : UU
  := ∏ (X Y : B) (f : X --> Y),
       psnaturality_of σ f • (m Y ▻ #F f)
       =
       #G f ◅ m X • psnaturality_of τ f.

Definition modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : ∏ (X : B), σ X ==> τ X
  := pr111 m.

Coercion modcomponent_of : modification >-> Funclass.

Definition modnaturality_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : is_modification m
  := pr211 m.

Definition mod_inv_naturality_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : ∏ (X Y : B) (f : X --> Y),
    (m Y ▻ #F f) • (psnaturality_of τ f)^-1
    =
    (psnaturality_of σ f)^-1 • (#G f ◅ m X).
Proof.
  intros X Y f.
  use vcomp_move_L_pM.
  { is_iso. }
  rewrite vassocr.
  use vcomp_move_R_Mp.
  { is_iso. }
  exact (modnaturality_of m X Y f).
Qed.

Definition make_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification_data σ τ)
           (Hm : is_modification m)
  : modification σ τ
  := (((m ,, Hm) ,, (tt ,, tt ,, tt)),, tt).

Definition modification_eq
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           {m m' : modification σ τ}
           (p : ∏ (X : B), m X = m' X)
  : m = m'.
Proof.
  use subtypePath.
  { intro. simpl.
    exact isapropunit.
  }
  use subtypePath.
  { intro. simpl.
    repeat (apply isapropdirprod) ; apply isapropunit.
  }
  use subtypePath.
  { intro. simpl.
    repeat (apply impred ; intro).
    apply B'.
  }
  use funextsec.
  exact p.
Qed.

Definition isaset_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : isaset (modification σ τ).
Proof.
  repeat (apply isaset_total2).
  - apply impred_isaset ; intro.
    apply B'.
  - intro.
    repeat (apply impred_isaset ; intro).
    apply isasetaprop.
    apply B'.
  - intro ; simpl.
    repeat (apply isaset_dirprod) ; apply isasetunit.
  - intro ; apply isasetunit.
Qed.

Definition is_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : UU
  := @is_invertible_2cell (psfunctor_bicat B B') _ _ _ _ m.

Definition invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := @invertible_2cell (psfunctor_bicat B B') _ _ σ τ.

Definition modcomponent_eq
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           {m m' : modification σ τ}
           (p : m = m')
  : ∏ (X : B), m X = m' X.
Proof.
  intro X.
  induction p.
  apply idpath.
Qed.

Definition invertible_modification_data
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := ∏ (X : B), invertible_2cell (σ X) (τ X).

Coercion invertible_modification_data_to_modification_data
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : invertible_modification_data σ τ)
  : modification_data σ τ.
Proof.
  intro X.
  exact (m X).
Defined.

Definition is_invertible_modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
           (Hm : is_invertible_modification m)
  : ∏ (X : B), is_invertible_2cell (m X).
Proof.
  intro X.
  use make_is_invertible_2cell.
  - exact ((Hm^-1 : modification _ _) X).
  - exact (modcomponent_eq (vcomp_rinv Hm) X).
  - exact (modcomponent_eq (vcomp_lid Hm) X).
Defined.

Definition make_is_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
           (Hm : ∏ (X : B), is_invertible_2cell (m X))
  : is_invertible_modification m.
Proof.
  use make_is_invertible_2cell.
  - use make_modification.
    + exact (λ X, (Hm X)^-1).
    + intros X Y f.
      simpl.
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      rewrite <- vassocr.
      use vcomp_move_L_pM.
      { is_iso. }
      symmetry.
      simpl.
      apply (modnaturality_of m).
  - use modification_eq.
    intro X.
    cbn.
    exact (vcomp_rinv (Hm X)).
  - use modification_eq.
    intro X.
    cbn.
    exact (vcomp_lid (Hm X)).
Defined.

Definition invertible_modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : invertible_modification σ τ)
  : ∏ (X : B), invertible_2cell (σ X) (τ X).
Proof.
  intro X.
  use make_invertible_2cell.
  - exact ((cell_from_invertible_2cell m : modification _ _) X).
  - apply is_invertible_modcomponent_of.
    exact (property_from_invertible_2cell m).
Defined.

Definition make_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : invertible_modification_data σ τ)
           (Hm : is_modification m)
  : invertible_modification σ τ.
Proof.
  use make_invertible_2cell.
  - use make_modification.
    + unfold modification_data.
      apply m.
    + exact Hm.
  - apply make_is_invertible_modification.
    intro.
    apply m.
Defined.
