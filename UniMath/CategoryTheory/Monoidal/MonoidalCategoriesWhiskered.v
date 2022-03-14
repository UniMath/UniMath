(* In this file we formalize the definition of a monoidal category in a curried format.
The data of a monoidal category consist of:
	- Category C.
	- A functor T : C x C → C, called the tensor which is specified as followed:
		- On the objects: A function Ob(C) → (Ob(C) → Ob(C)) : x → (y → x ⊗_{T} y)
		- On the morphisms: A function C[x,x'] → ( C[y,y'] -> C[ x ⊗_{T} y, x' ⊗_{T} y']) : f→ (g→ f ⊗^{T} g)
	- An object I : C, called the unit.
	- A natural transformation lu : I ⊗_T (-) → (-) with naturality condition
                lu_y ∘ (Id_I ⊗^{T} f) = f ∘ lu_x.
        - A natural transformation ru : (-) ⊗_T I → (-) with naturality condition
                ru_y ∘ (f ⊗^{T} Id_I) = f ∘ ru_x.
        - A natural transformation α : ((-)⊗_T(-))⊗_T(-) → (-)⊗((-)⊗(-)) with naturality condition
                f⊗(g⊗h) ∘ α_{x,y,z} = α_{x',y',z'} ∘ (f⊗g)⊗h.
The properties of a monoidal category are the following:
        - Triangle identity:
                   (Id_x ⊗ lu_y) ∘ α_{x,I,y} = ru_x ⊗^{T} Id_y.
        - Pentagon identity:
                   (Id_w ⊗ α_{x,y,z}) ∘ α_{w,x⊗y,z} ∘ (α_{w,x,y} ⊗ Id_z) = α_{w,x,y⊗z} ∘ α_{w⊗x,y,z}.

*)

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

Definition bifunctor_from_tensor {C : category} (T : tensor C) : bifunctor C C C := T.
Coercion bifunctor_from_tensor : tensor >-> bifunctor.

Definition associator_data {C : category} (T : tensor C) : UU :=
  ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

Definition leftunitor {C : category} (T : tensor C) (I : C) : UU :=
  nat_trans (leftwhiskering_functor T (bifunctor_leftid T) (bifunctor_leftcomp T) I) (functor_identity C).

Definition rightunitor {C : category} (T : tensor C) (I : C) : UU :=
  nat_trans (rightwhiskering_functor T (bifunctor_rightid T) (bifunctor_rightcomp T) I) (functor_identity C).

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
Definition tensor_assoc_nat {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (x x' y y' z z' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧),
     (f ⊗^{T}_{1} (g ⊗^{T}_{1} h))∘(α x y z) = (α x' y' z')∘ ((f ⊗^{T}_{1} g) ⊗^{T}_{1} h).

Definition tensor_assoc_iso {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (x y z : C), is_z_isomorphism (α x y z).

Definition associator_law {C : category} {T : tensor C} (α : associator_data T) : UU :=
  (tensor_assoc_nat α) × (tensor_assoc_iso α).

Definition tensorassociator_nat {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat α := pr1 αl.
Coercion tensorassociator_nat : associator_law >-> tensor_assoc_nat.

Definition tensorassociator_iso {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_iso α := pr2 αl.
Coercion tensorassociator_iso : associator_law >-> tensor_assoc_iso.

Definition leftunitor_iso {C : category} {T : tensor C} {I : C} (lu : leftunitor T I) : UU := is_nat_z_iso (pr1 lu).

Definition rightunitor_iso {C : category} {T : tensor C} {I : C} (ru : rightunitor T I) : UU := is_nat_z_iso (pr1 ru).

Definition triangle_identity {C : category}
           {T : tensor C}
           {I : C}
           (lu : leftunitor T I)
           (ru : rightunitor T I)
           (α : associator_data T)
    := ∏ (x y : C), (α x I y) · (x ⊗^{T}_{l} ((pr1 lu) y)) = ((pr1 ru) x) ⊗^{T}_{r} y.

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
