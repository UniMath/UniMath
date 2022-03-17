Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Local Open Scope cat.

Import Notations.

(** Data **)
Definition tensor (C : category) : UU :=
  bifunctor C C C.
Identity Coercion tensorintobifunctor : tensor >-> bifunctor.

Definition associator_data {C : category} (T : tensor C) : UU :=
  ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

Definition leftunitor {C : category} (T : tensor C) (I : C) : UU :=
  nat_trans (leftwhiskering_functor T (bifunctor_leftid T) (bifunctor_leftcomp T) I) (functor_identity C).
Identity Coercion leftunitorintonattrans : leftunitor >-> nat_trans.

Definition rightunitor {C : category} (T : tensor C) (I : C) : UU :=
  nat_trans (rightwhiskering_functor T (bifunctor_rightid T) (bifunctor_rightcomp T) I) (functor_identity C).
Identity Coercion rightunitorintonattrans : rightunitor >-> nat_trans.

Definition monoidalcategory_data (C : category): UU :=
    ∑ T : tensor C, ∑ I : C,
        (leftunitor T I) × (rightunitor T I) × (associator_data T).

Definition make_monoidalcat_data {C : category} {T : tensor C} {I : C} (lu : leftunitor T I) (ru : rightunitor T I) (α : associator_data T) : monoidalcategory_data C := (T,,I,,lu,,ru,,α).

Definition tensor_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : tensor C := (pr1 MD).
Coercion tensor_from_monoidalcatdata : monoidalcategory_data >-> tensor.

Definition unit_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : C := (pr1 (pr2 MD)).
Coercion unit_from_monoidalcatdata : monoidalcategory_data >-> ob.

Definition leftunitor_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : leftunitor MD MD := (pr1 (pr2 (pr2 MD))).
Coercion leftunitor_from_monoidalcatdata : monoidalcategory_data >-> leftunitor.

Definition rightunitor_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : rightunitor MD MD := (pr1 (pr2 (pr2 (pr2 MD)))).
Coercion rightunitor_from_monoidalcatdata : monoidalcategory_data >-> rightunitor.

Definition associatordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : associator_data MD := (pr2 (pr2 (pr2 (pr2 MD)))).
Coercion associatordata_from_monoidalcatdata : monoidalcategory_data >-> associator_data.


(** Axioms **)
Definition tensor_assoc_nat_leftwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (α x y z) · (x ⊗^{ T}_{l} (y ⊗^{ T}_{l} h)) = ((x ⊗_{ T} y) ⊗^{ T}_{l} h) · (α x y z').

Definition tensor_assoc_nat_rightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x x' y z : C) (f : C⟦x,x'⟧),
    (α x y z) · (f ⊗^{ T}_{r} (y ⊗_{ T} z)) = ((f ⊗^{ T}_{r} y) ⊗^{ T}_{r} z) · (α x' y z).

Definition tensor_assoc_nat_leftrightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y y' z : C) (g : C⟦y,y'⟧),
       (α x y z) · (x ⊗^{ T}_{l} (g ⊗^{ T}_{r} z)) = ((x ⊗^{ T}_{l} g) ⊗^{ T}_{r} z) · (α x y' z).

Definition tensor_assoc_nat1 {C : category} {T : tensor C} {α : associator_data T} (αnl : tensor_assoc_nat_leftwhisker α) (αnr : tensor_assoc_nat_rightwhisker α) (αnlr : tensor_assoc_nat_leftrightwhisker α) {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
       (α x y z) · ((f ⊗^{ T}_{r} (y ⊗_{ T} z)) · (x' ⊗^{ T}_{l} ((g ⊗^{ T}_{r} z) · (y' ⊗^{ T}_{l} h)))) =
         (((f ⊗^{ T}_{r} y) · (x' ⊗^{ T}_{l} g))  ⊗^{ T}_{r} z) · ((x' ⊗_{ T} y') ⊗^{ T}_{l} h) · (α x' y' z').
Proof.
  rewrite assoc.
  rewrite αnr.
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    Check whiskerscommutes.
    rewrite (bifunctor_leftcomp T).
    rewrite assoc.
    rewrite αnlr.
    apply idpath.
  }

  etrans. {
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply αnl.
  }
  rewrite assoc.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite bifunctor_rightcomp.
  apply idpath.
Qed.

Lemma tensor_assoc_nat2 {C : category} {T : tensor C} {α : associator_data T} (αnl : tensor_assoc_nat_leftwhisker α) (αnr : tensor_assoc_nat_rightwhisker α) (αnlr : tensor_assoc_nat_leftrightwhisker α)
      {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
    (f ⊗^{T} (g ⊗^{T} h))∘(α x y z) = (α x' y' z')∘ ((f ⊗^{T} g) ⊗^{T} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (tensor_assoc_nat1 αnl αnr αnlr f g h).
Qed.

Definition tensor_assoc_iso {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (x y z : C), is_z_isomorphism (α x y z).

Definition associator_law {C : category} {T : tensor C} (α : associator_data T) : UU :=
  (tensor_assoc_nat_leftwhisker α) × (tensor_assoc_nat_rightwhisker α) × (tensor_assoc_nat_leftrightwhisker α) × (tensor_assoc_iso α).

Definition tensorassociator_natleft {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_leftwhisker α := pr1 αl.
Definition tensorassociator_natright {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_rightwhisker α := pr1 (pr2 αl).
Definition tensorassociator_natleftright {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_leftrightwhisker α := pr1 (pr2 (pr2 αl)).
Definition tensorassociator_iso {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_iso α := pr2 (pr2 (pr2 αl)).

Definition leftunitor_iso {C : category} {T : tensor C} {I : C} (lu : leftunitor T I) : UU := is_nat_z_iso lu.
Identity Coercion leftunitorisointozisos: leftunitor_iso >-> is_nat_z_iso.

Definition rightunitor_iso {C : category} {T : tensor C} {I : C} (ru : rightunitor T I) : UU := is_nat_z_iso ru.
Identity Coercion rightunitorisointozisos: rightunitor_iso >-> is_nat_z_iso.

Definition triangle_identity {C : category}
           {T : tensor C}
           {I : C}
           (lu : leftunitor T I)
           (ru : rightunitor T I)
           (α : associator_data T)
    := ∏ (x y : C), (α x I y) · (x ⊗^{T}_{l} (lu y)) = (ru x) ⊗^{T}_{r} y.

Definition pentagon_identity {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (w x y z : C),
    ((α w x y) ⊗^{T}_{r} z)·(α w (x⊗_{T} y) z)·(w ⊗^{T}_{l} (α x y z)) =  (α (w⊗_{T}x) y z)·(α w x (y ⊗_{T} z)).

Definition monoidal_laws {C : category} (MD : monoidalcategory_data C) : UU :=
   (associator_law MD) × (leftunitor_iso MD) × (rightunitor_iso MD)
                       × (triangle_identity MD MD MD) × (pentagon_identity MD).

Definition monoidalcategory (C : category) : UU :=
  ∑ (MD : monoidalcategory_data C), (monoidal_laws MD).

Definition monoidalcategorydata_from_moncat {C : category} (M : monoidalcategory C) : monoidalcategory_data C := pr1 M.
Coercion monoidalcategorydata_from_moncat : monoidalcategory >-> monoidalcategory_data.

Definition monoidallaws_from_moncat {C : category} (M : monoidalcategory C) : monoidal_laws M := pr2 M.

Definition moncat_associator {C : category} (M : monoidalcategory C) : associator_law M := pr1 (monoidallaws_from_moncat M).
Definition moncat_leftunitoriso {C : category} (M : monoidalcategory C) : leftunitor_iso M := pr1 (pr2 (monoidallaws_from_moncat M)).
Definition moncat_rightunitoriso {C : category} (M : monoidalcategory C) : rightunitor_iso M := pr1(pr2 (pr2 (monoidallaws_from_moncat M))).
Definition moncat_triangleidentity {C : category} (M : monoidalcategory C) : triangle_identity M M M:= pr1 (pr2 (pr2 (pr2 (monoidallaws_from_moncat M)))).
Definition moncat_pentagonidentity {C : category} (M : monoidalcategory C) : pentagon_identity M := pr2 (pr2 (pr2 (pr2 (monoidallaws_from_moncat M)))).
