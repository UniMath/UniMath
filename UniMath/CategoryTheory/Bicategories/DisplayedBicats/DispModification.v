(* ------------------------------------------------------------------------- *)
(** Displayed modifications.
    Contents:
      - Definition of displayed pseudofunctors.
      - Identity and composition of displayed pseudofunctors.                *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.

Import PseudoFunctor.Notations.

Local Open Scope cat.

(** ** Definition of displayed modifications *)

Section DispModification.

Context {B₁ : bicat} {D₁ : disp_bicat B₁}
        {B₂ : bicat} {D₂ : disp_bicat B₂}
        {F₁ F₂ : psfunctor B₁ B₂}
        (α β : pstrans F₁ F₂)
        (FF₁ : disp_psfunctor D₁ D₂ F₁)
        (FF₂ : disp_psfunctor D₁ D₂ F₂)
        (αα : disp_pstrans FF₁ FF₂ α)
        (ββ : disp_pstrans FF₁ FF₂ β)
        (m : invertible_modification α β).

(** *** Data *)

Definition disp_invmodification_data : UU
  := ∏ (x : B₁) (xx : D₁ x),
     disp_invertible_2cell (invertible_modcomponent_of m x) (αα x xx) (ββ x xx).

Definition total_invmodification_data (mmdata : disp_invmodification_data)
  : invertible_modification_data (total_pstrans _ _ _ αα) (total_pstrans _ _ _ ββ)
  := λ (x : total_bicat D₁),
     (iso_in_E_weq (αα (pr1 x) (pr2 x)) (ββ (pr1 x) (pr2 x)))
       (invertible_modcomponent_of m (pr1 x),, mmdata (pr1 x) (pr2 x)).

Definition is_disp_invmodification (mm : disp_invmodification_data) : UU
  := ∏ (x y : B₁) (f : B₁ ⟦ x, y ⟧)
       (xx : D₁ x) (yy : D₁ y) (ff : xx -->[ f] yy),
     disp_psnaturality_of FF₁ FF₂ α αα ff
       •• (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff ◃◃ mm y yy) =
     transportb
       (λ p, _ ==>[p] _)
       (modnaturality_of (pr1 m) x y f)
       ((mm x xx ▹▹ disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
          •• disp_psnaturality_of FF₁ FF₂ β ββ ff).

Definition disp_invmodification : UU
  := ∑ mm : disp_invmodification_data, is_disp_invmodification mm.

Coercion disp_invmodification_to_disp_invmodification_data (αα : disp_invmodification)
  : disp_invmodification_data
  := pr1 αα.

Lemma is_disp_invmodification_from_total (mm : disp_invmodification_data)
  : is_modification (total_invmodification_data mm) → is_disp_invmodification mm.
Proof.
  intros Hmm.
  pose (Em := make_modification _ Hmm).
  intros x y f xx yy ff.
  pose (P := !fiber_paths (@modnaturality_of _ _ _ _ _ _ Em (x,,xx) (y,,yy) (f,,ff))).
  symmetry.
  etrans. { apply maponpaths. exact P. }
  unfold transportb.
  rewrite transport_f_f.
  rewrite transportf_set.
  * apply idpath.
  * apply B₂.
Qed.

Lemma total_invmodification_laws (mm : disp_invmodification)
  : is_modification (total_invmodification_data mm).
Proof.
  intros x y f.
  use total2_paths_b.
  - apply (modnaturality_of (pr1 m) (pr1 x) (pr1 y) (pr1 f)).
  - apply mm.
Qed.

Definition total_invmodification (mm : disp_invmodification)
  : invertible_modification (total_pstrans _ _ _ αα) (total_pstrans _ _ _ ββ).
Proof.
  use make_invertible_modification.
  - exact (total_invmodification_data mm).
  - exact (total_invmodification_laws mm).
Defined.

End DispModification.
