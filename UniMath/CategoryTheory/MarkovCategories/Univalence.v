(*********************************************
Univalence 

We define what it means for a Markov category to be univalent

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.

Import MonoidalNotations.

Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.

Local Open Scope cat.
Local Open Scope moncat.

Definition idtodet_iso
           {C : markov_category}
           {x y : C}
           (p : x = y)
  : deterministic_iso x y.
Proof.
  induction p.
  apply identity_deterministic_iso.
Defined.

Definition is_markov_univalent
           (C : markov_category)
  : UU
  := ∏ (x y : C), isweq (idtodet_iso (x := x) (y := y)).

Proposition isaprop_is_markov_univalent
            (C : markov_category)
  : isaprop (is_markov_univalent C).
Proof.
  do 2 (use impred ; intro).
  apply isapropisweq.
Qed.

Definition all_isos_deterministic
           (C : markov_category)
  : UU
  := ∏ (x y : C) (f : z_iso x y), is_deterministic f.

Proposition isaprop_all_isos_deterministic
            (C : markov_category)
  : isaprop (all_isos_deterministic C).
Proof.
  do 3 (use impred ; intro).
  apply isaprop_is_deterministic.
Qed.

Definition iso_weq_det_iso_all_deterministic
           {C : markov_category}
           (H : all_isos_deterministic C)
           (x y : C)
  : z_iso x y ≃ deterministic_iso x y.
Proof.
  use weq_iso.
  - intro f.
    refine (f ,, _).
    apply H.
  - intro f.
    exact (pr1 f). (* TODO: INFRASTRUCTURE DETERMINISTIC ISO *)
  - abstract
      (intro f ;
      reflexivity).
  - abstract
      (intro f ;
      use subtypePath ; [ intro ; apply isaprop_is_deterministic | ] ;
      reflexivity). 
Defined.

Proposition univalence_weq_markov_univalence
            {C : markov_category}
            (H : all_isos_deterministic C)
  : is_univalent C ≃ is_markov_univalent C.
Proof.
  use weqimplimpl.
  - intros HC x y.
    use weqhomot.
    + refine (iso_weq_det_iso_all_deterministic H x y ∘ _)%weq.
      use make_weq.
      * apply idtoiso.
      * apply HC. 
    + intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_deterministic.
      }
      cbn.
      reflexivity. 
  - intros HC x y.
    use weqhomot.
    + refine (invweq (iso_weq_det_iso_all_deterministic H x y) ∘ _)%weq.
      use make_weq.
      * apply idtodet_iso.
      * apply HC. 
    + intro p.
      induction p.
      cbn.
      reflexivity. 
  - apply isaprop_is_univalent.
  - apply isaprop_is_markov_univalent.
Qed. 