(**************************************************************************************************

  Ringed Spaces

  Ringed spaces are presheafed spaces, such that the presheaf is a sheaf of commutative rings. This
  file defines the category of ringed spaces as a full subcategory of the category of presheafed
  spaces and shows that it is univalent. It then defines the types, constructors and accessors for
  the objects and morphisms in the category.

  Contents
  1. The sheaf property [has_sheaf]
  2. The category [ringed_space_cat]
  3. The types, constructors and accessors [ringed_space] [ringed_space_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.AlgebraicGeometry.PresheafedSpaces.
Require Import UniMath.CategoryTheory.Categories.Commring.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Topology.Topology.

Local Open Scope cat.
Local Open Scope subtype.
Local Open Scope open.

(** * 1. The sheaf property *)


(** * 2. The category *)

Definition ringed_space_cat
  : category
  := full_subcat (presheafed_space_cat commring_category) has_sheaf.

Definition is_univalent_ringed_space_cat
  : is_univalent ringed_space_cat
  := is_univalent_full_subcat _
    (is_univalent_presheafed_space_cat commring_category_is_univalent) _
    isaprop_has_sheaf.

(** * 3. The types, constructors and accessors *)

Definition ringed_space
  : UU
  := ringed_space_cat.

Definition make_ringed_space
  (X : presheafed_space commring_category)
  (H : has_sheaf X)
  : ringed_space
  := X ,, H.

Coercion ringed_space_to_presheafed_space
  (X : ringed_space)
  : presheafed_space commring_category
  := pr1 X.

Definition ringed_space_has_sheaf
  (X : ringed_space)
  : has_sheaf X
  := pr2 X.

Definition ringed_space_has_locality
  (X : ringed_space)
  : has_locality X
  := pr12 X.

Definition ringed_space_has_gluing
  (X : ringed_space)
  : has_gluing X
  := pr22 X.

Definition ringed_space_morphism
  (X Y : ringed_space)
  : UU
  := ringed_space_cat⟦X, Y⟧.

Definition make_ringed_space_morphism
  {X Y : ringed_space}
  (f : presheafed_space_morphism X Y)
  : ringed_space_morphism X Y
  := f ,, tt.

Coercion ringed_space_morphism_to_presheafed_space_morphism
  {X Y : ringed_space}
  (f : ringed_space_morphism X Y)
  : presheafed_space_morphism X Y
  := pr1 f.
