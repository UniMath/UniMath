(**************************************************************************************************

  Schemes

  A scheme is a ringed space such that every point has a neighborhood that is isomorphic to the
  spectrum of a ring. This file defines the category of schemes as a full subcategory of the
  category of ringed spaces, and shows that it is univalent. It then defines schemes and their
  morphisms, together with accessors and constructors.

  Contents
  1. The category of schemes [scheme_cat]
  2. The types and accessors [scheme] [scheme_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.AlgebraicGeometry.PresheafedSpaces.
Require Import UniMath.AlgebraicGeometry.RingedSpaces.
Require Import UniMath.AlgebraicGeometry.Spec.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Topology.Topology.

Local Open Scope cat.

(** 1. The category of schemes *)

Definition is_scheme
  (X : ringed_space)
  : UU
  := ∏ (x : X),
      ∃ (U : Open)
        (H : U x)
        (R : commring),
        z_iso (C := presheafed_space_cat _)
          (presheafed_space_restriction X U)
          (Spec_presheafed_space R).

Definition scheme_cat
  : category
  := full_subcat ringed_space_cat is_scheme.

Lemma is_univalent_scheme_cat
  : is_univalent scheme_cat.
Proof.
  use is_univalent_full_subcat.
  - apply is_univalent_ringed_space_cat.
  - intro X.
    apply impred_isaprop.
    intro x.
    apply propproperty.
Qed.

(** 2. The types and accessors *)

Definition scheme
  : UU
  := scheme_cat.

Coercion scheme_to_ringed_space
  (X : scheme)
  : ringed_space
  := pr1 X.

Definition scheme_is_scheme
  (X : scheme)
  : is_scheme X
  := pr2 X.

Definition make_scheme
  (X : ringed_space)
  (H : is_scheme X)
  := X ,, H.

Definition scheme_morphism
  (X Y : scheme)
  : UU
  := scheme_cat⟦X, Y⟧.

Coercion scheme_morphism_to_ringed_space_morphism
  (X Y : scheme)
  (f : scheme_morphism X Y)
  : ringed_space_morphism X Y
  := pr1 f.

Definition make_scheme_morphism
  {X Y : scheme}
  (f : presheafed_space_morphism X Y)
  : scheme_morphism X Y
  := make_ringed_space_morphism f ,, tt.
