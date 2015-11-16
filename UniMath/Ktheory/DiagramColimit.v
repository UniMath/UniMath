Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories
        UniMath.CategoryTheory.colimits.colimits.
Require UniMath.Ktheory.Representation.

Local Open Scope cat.

Local Coercion coconeIn : cocone >-> Funclass.
Local Coercion vertex : graph >-> UU.
Local Coercion dob : diagram >-> Funclass.

Arguments assoc [C a b c d] f g h.

Ltac set_logic :=
  repeat (
      try intro; try apply isaset_total2; try apply isasetdirprod; try apply homset_property;
      try apply impred_isaset; try apply isasetaprop).

Ltac eqn_logic :=
  repeat (
      try intro; try split; try apply id_right; try apply id_left; try apply assoc;
      try apply funextsec; try apply homset_property; try refine (total2_paths _ _)).

Definition cocone_functor_data {C:Precategory} {Γ: graph} (D: diagram Γ C) : functor_data C SET.
Proof.
  intros. refine (_,,_).
  - intro c. exists (cocone D c). abstract (set_logic) using L1.
  - simpl. intros c c' f φ. exists (λ g, f ∘ φ g).
    abstract (
        intros g g' e; refine (assoc _ _ _ @ _);
        apply (maponpaths (λ h, _ ∘ h)); apply coconeInCommutes) using L2.
Defined.

Definition cocone_functor {C:Precategory}
           {Γ: graph} (D: diagram Γ C) : C ==> SET.
Proof. intros. exists (cocone_functor_data D). abstract eqn_logic using L3. Defined.

Definition type {C:Precategory} {Γ: graph} (D: diagram Γ C) := Representation.Data (cocone_functor D).

Definition Object {C:Precategory} {Γ: graph} {D: diagram Γ C} (r:type D) : ob C
  := Representation.Object r.

Definition Cocone {C:Precategory} {Γ: graph} {D: diagram Γ C} (r:type D) : cocone D (Object r)
  := Representation.Element r.

Coercion Cocone : type >-> cocone.

Definition In {C:Precategory} {Γ: graph} {D: diagram Γ C} (r:type D) (i:vertex Γ) : Hom (D i) (Object r).
Proof. intros. exact (r i). Defined.

Definition hasDiagramColimits (C:Precategory) := ∀ Γ (D: diagram Γ C), type D.

(* Proof. intros. exact (Representation.Element B i). Defined. *)
(* Module Coercions. *)
(*   Coercion representation_to_object : type >-> ob. *)
(* End Coercions. *)
