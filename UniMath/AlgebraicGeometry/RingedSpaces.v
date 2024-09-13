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

(* TODO: Show that the restriction of a ringed space is again a ringed space *)

(** * 1. The sheaf property *)

Section SheafProperty.

  Context (X : presheafed_space commring_category).

  Let F (U : Open (T := X)) : commring := presheafed_space_presheaf X U.

  Definition restriction {U V : Open} (H : U ⊆ V) : ringfun (F V) (F U) := #(presheafed_space_presheaf X) H.

  Definition restrict (A : hsubtype Open) (f : F (⋃ A)) (U : A) : F (pr1 U) :=
    restriction (contained_in_union_open U) f.

  Definition has_locality
    : UU
    := ∏ (A : hsubtype Open) (f g : F (⋃ A)),
      (∏ (U : A), restrict A f U = restrict A g U) → f = g.

  Definition has_locality_0
    : UU
    := ∏ (A : hsubtype Open) (f : F (⋃ A)),
      (∏ (U : A), restrict A f U = 0%ring) → f = 0%ring.

  Lemma has_locality_0_to_has_locality
    (H : has_locality_0)
    : has_locality.
  Proof.
    intros A f g Hg.
    apply (grtopathsxy (ringaddabgr (F (⋃ A)))).
    apply H.
    intro U.
    refine (monoidfunmul (rigaddfun (restriction _)) _ _ @ _).
    refine (maponpaths _ (grinvandmonoidfun (ringaddabgr _) (ringaddabgr _) (pr2 (rigaddfun (restriction _))) g) @ _).
    apply (grfrompathsxy (ringaddabgr (F _))).
    exact (Hg U).
  Qed.

  Definition agree_on_intersections {A : hsubtype Open}
                                    (g : ∏ U : A, F (pr1 U)) : UU :=
    ∏ U V : A, restriction (intersection_contained1 _ _) (g U) =
               restriction (intersection_contained2 _ _) (g V).

  Definition has_gluing : UU
    := ∏ (A : hsubtype Open)
      (g : ∏ U : A, F (pr1 U)),
      agree_on_intersections g → ∑ f, ∏ (U : A), restrict A f U = g U.

  Lemma isaprop_gluing
    (H : has_locality)
    (A : hsubtype Open)
    (g : ∏ U : A, F (pr1 U))
    (Hg : agree_on_intersections g)
    : isaprop (∑ f, ∏ (U : A), restrict A f U = g U).
  Proof.
      intros f f'.
      use make_iscontr.
      + use subtypePath.
        * intro h.
          apply impred_isaprop.
          intro x.
          apply setproperty.
        * apply (H A (pr1 f) (pr1 f')).
          intro U.
          exact (pr2 f U @ !pr2 f' U).
      + intro t.
        refine (pr1 (isaset_carrier_subset _ (λ _, make_hProp _ _) f f' t _)).
        apply impred_isaprop.
        intro.
        apply setproperty.
  Qed.

  Definition has_sheaf : UU
    := has_locality
      × has_gluing.

  Definition make_has_sheaf
    (H1 : has_locality)
    (H2 : has_gluing)
    : has_sheaf
    := H1 ,, H2.

  Lemma isaprop_has_sheaf
    : isaprop has_sheaf.
  Proof.
    use (isaprop_total2 (make_hProp _ _) (λ H, make_hProp _ _)).
    - do 4 (apply impred_isaprop; intro).
      apply setproperty.
    - apply impred_isaprop.
      intro A.
      apply impred_isaprop.
      intro g.
      apply impred_isaprop.
      apply isaprop_gluing.
      exact H.
  Qed.

End SheafProperty.

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
