(*********************************************
Univalence 

We define what it means for a Markov category to be univalent,
namely equality of objects is equivalent to deterministic isomorphism.

Markov categories can equivalently be defined as semi-Cartesian monoidal categories
that supply commutative comonoids. More specifically, in a Markov category
every object is equipped with a commutative comonoid structure given by
the copy and delete maps. Note that while deletion is necessarily natural
(because Markov categories are semi-Cartesian), the copy map is not required
to be natural.

A notion of univalence for symmetric monoidal categories that supply some structure
given by a PROP is given in Example 13.2 in "The Univalence Principle" by Ahrens,
North, Shulman and Tsementzis. The indiscernibilities are isomorphism that commute with
the PROP structure. For Markov categories, this means isomorphisms that commute with
both the copy and delete map. Since commutation with the delete map is automatic (the
delete morphism lands in the terminal object), indiscernibilities are given by
isomorphisms that commute with the copy map. Deterministic isomorphisms are exactly
those isomorphisms that satisfy that property. Hence, univalence for Markov categories
should be defined using deterministic isomorphisms.

Note that in many examples of Markov categories deterministic isomorphisms are the same
as ordinary isomorphisms (for example those satisfying the the axioms in `InformationFlowAxioms.v`, 
such as positivity and causality). For those, univalence and Markov univalence are equivalent.

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
- B. Ahrens, P.R. North, M. Shulman, D. Tsementzis - 'The Univalence Principle'
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
Local Open Scope markov.

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