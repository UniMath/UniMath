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
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.

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
        (m : modification α β).

(** *** Data *)


Definition disp_modification_data : UU
  := ∏ (x : B₁) (xx : D₁ x), (αα x xx) ==>[m x] (ββ x xx).

Definition total_modification_data (mmdata : disp_modification_data)
  : modification_data (total_pstrans _ _ _ αα) (total_pstrans _ _ _ ββ)
  := λ (x : total_bicat D₁), m (pr1 x),, mmdata (pr1 x) (pr2 x).

Definition is_disp_modification (mm : disp_modification_data) : UU
  := ∏ (x y : B₁) (f : B₁ ⟦ x, y ⟧)
       (xx : D₁ x) (yy : D₁ y) (ff : xx -->[ f] yy),
     disp_psnaturality_of FF₁ FF₂ α αα ff
       •• (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff ◃◃ mm y yy) =
     transportb
       (λ p, _ ==>[p] _)
       (modnaturality_of m x y f)
       ((mm x xx ▹▹ disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
          •• disp_psnaturality_of FF₁ FF₂ β ββ ff).

Definition disp_modification : UU
  := ∑ mm : disp_modification_data, is_disp_modification mm.

Coercion disp_modification_to_disp_modification_data (αα : disp_modification)
  : disp_modification_data
  := pr1 αα.

Lemma is_disp_modification_from_total (mm : disp_modification_data)
  : is_modification (total_modification_data mm) → is_disp_modification mm.
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

Lemma total_modification_laws (mm : disp_modification)
  : is_modification (total_modification_data mm).
Proof.
  intros x y f.
  use total2_paths_b.
  - apply (modnaturality_of m (pr1 x) (pr1 y) (pr1 f)).
  - apply mm.
Qed.

Definition is_invertible_disp_modification (mm : disp_modification) : UU
  := ∑ (m_inv : is_invertible_modification m), ∏ (x : B₁) (xx : D₁ x),
       (* Each underlying displayed 2-cell is invertible *)
       is_disp_invertible_2cell (@is_invertible_modcomponent_of _ _ _ _ _ _ m m_inv x) (pr1 mm x xx).

End DispModification.

(** Invertible displayed modifications *)

Section DispInvModification.

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

Definition disp_modification_of_invmodification (mm : disp_invmodification) :
  disp_modification α β FF₁ FF₂ αα ββ (pr1 m).
Proof.
  use tpair.
  - intros x xx. exact (pr1 mm x xx).
  - simpl. exact (pr2 mm).
Defined.

Lemma is_invertible_disp_invmodification (mm : disp_invmodification) :
  is_invertible_disp_modification _ _ _ _ _ _ _ (disp_modification_of_invmodification mm).
Proof.
  use tpair.
  - exact (pr2 m).
  - simpl. intros x xx.
    exact (pr2 (pr1 mm x xx)).
Qed.

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

End DispInvModification.

Lemma make_disp_invmodification
      {B₁ : bicat} {D₁ : disp_bicat B₁}
      {B₂ : bicat} {D₂ : disp_bicat B₂}
      {F₁ F₂ : psfunctor B₁ B₂}
      {α β : pstrans F₁ F₂}
      {FF₁ : disp_psfunctor D₁ D₂ F₁}
      {FF₂ : disp_psfunctor D₁ D₂ F₂}
      (αα : disp_pstrans FF₁ FF₂ α)
      (ββ : disp_pstrans FF₁ FF₂ β)
      (m : modification α β)
      (Hm : is_invertible_modification m)
      (mm : disp_modification _ _ _ _ αα ββ m)
      (Hmm : ∏ x xx, is_disp_invertible_2cell (is_invertible_modcomponent_of m Hm x) (pr1 mm x xx))
  :
  disp_invmodification _ _ _ _ αα ββ (m,,Hm).
Proof.
  use tpair.
  - intros x xx. use tpair.
    + exact (pr1 mm x xx).
    + simpl. exact (Hmm x xx).
  - simpl. exact (pr2 mm).
Defined.
