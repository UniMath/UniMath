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
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.

(** Data **)

  Definition tensor_data (C : category) : UU :=
    ∑ to : C -> C -> C,
            ∏ (x y x' y' : C), C ⟦x,x'⟧ → C ⟦y,y'⟧ -> C ⟦(to x y),(to x' y')⟧.

  Definition tensoronobjects_from_tensordata {C : category} (T : tensor_data C) : C->C->C := pr1 T.
  Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensordata T x y) (at level 31).

  Definition tensoronmorphisms_from_tensordata {C : category} (T : tensor_data C):
    ∏ (x y x' y' : C), C ⟦x,x'⟧ → C ⟦y,y'⟧ -> C ⟦x ⊗_{T} y,x' ⊗_{T} y'⟧
    := pr2 T.
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensordata T  _ _ _ _ f g) (at level 31).

  Definition associator_data {C : category} (T : tensor_data C) : UU :=
    ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

  Definition leftunitor_data {C : category} (T : tensor_data C) (I : C) : UU :=
    ∏ (x : C), C ⟦I ⊗_{T} x, x⟧.

  Definition rightunitor_data {C : category} (T : tensor_data C) (I : C) : UU :=
    ∏ (x : C), C ⟦x ⊗_{T} I, x⟧.

  Definition monoidalcategory_data (C : category): UU :=
    ∑ T : tensor_data C, ∑ I : C,
          (leftunitor_data T I) × (rightunitor_data T I) × (associator_data T).

Definition tensordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : tensor_data C := (pr1 MD).
Coercion tensordata_from_monoidalcatdata : monoidalcategory_data >-> tensor_data.

Definition unit_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : C := (pr1 (pr2 MD)).
Coercion unit_from_monoidalcatdata : monoidalcategory_data >-> ob.

Definition leftunitordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : leftunitor_data MD MD := (pr1 (pr2 (pr2 MD))).
Coercion leftunitordata_from_monoidalcatdata : monoidalcategory_data >-> leftunitor_data.

Definition rightunitordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : rightunitor_data MD MD := (pr1 (pr2 (pr2 (pr2 MD)))).
Coercion rightunitordata_from_monoidalcatdata : monoidalcategory_data >-> rightunitor_data.

Definition associatordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : associator_data MD := (pr2 (pr2 (pr2 (pr2 MD)))).
Coercion associatordata_from_monoidalcatdata : monoidalcategory_data >-> associator_data.


(** Axioms **)
  Definition tensorfunctor_id {C : category} (T : tensor_data C) : UU :=
    ∏ (x y : C),
      (identity x) ⊗^{T} identity y = identity (x ⊗_{T} y).

  Definition tensorfunctor_comp {C : category} (T : tensor_data C) : UU :=
    ∏ (x y x' y' x'' y'' : C), ∏ (f : C ⟦x,x'⟧) (f' : C ⟦x',x''⟧) (g : C ⟦y,y'⟧) (g' : C ⟦y',y''⟧),
      (f' ⊗^{T} g') ∘ (f ⊗^{T} g) = (f'∘f) ⊗^{T} (g'∘g).

  Definition associator_naturality {C : category} {T : tensor_data C} (α : associator_data T) : UU :=
    ∏ (x x' y y' z z' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧),
       (f ⊗^{T} (g ⊗^{T} h))∘(α x y z) = (α x' y' z')∘ ((f ⊗^{T} g) ⊗^{T} h).

  Definition associator_is_natiso {C : category} {T : tensor_data C} (α : associator_data T) : UU :=
    ∏ (x y z : C), is_z_isomorphism (α x y z).

  Definition leftunitor_naturality {C : category} {T : tensor_data C} {I : C} (lu : leftunitor_data T I) : UU :=
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  f∘(lu x) = (lu y)∘((identity I)⊗^{T}f).

  Definition leftunitor_is_natiso {C : category} {T : tensor_data C} {I : C} (lu : leftunitor_data T I) : UU :=
    ∏ (x : C), is_z_isomorphism (lu x).

  Definition rightunitor_naturality {C : category} {T : tensor_data C} {I : C} (ru : rightunitor_data T I) :=
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  f∘(ru x) = (ru y)∘ (f ⊗^{T} (identity I)).

  Definition rightunitor_is_natiso {C : category} {T : tensor_data C} {I : C} (ru : rightunitor_data T I) : UU :=
    ∏ (x : C), is_z_isomorphism (ru x).

  Definition triangle_identity {C : category}
             {T : tensor_data C}
             {I : C}
             (lu : leftunitor_data T I)
             (ru : rightunitor_data T I)
             (α : associator_data T)
    := ∏ (x y : C),  (((identity x)  ⊗^{T} (lu y) ) ∘ (α x I y)) = ((ru x) ⊗^{T} identity y).

  Definition pentagon_identity {C : category} {T : tensor_data C} (α : associator_data T) : UU :=
    ∏ (w x y z : C),
         ((identity w)⊗^{T} (α x y z))
           ∘ ((α w (x⊗_{T} y) z)
           ∘ ((α w x y) ⊗^{T} (identity z))) =  (α w x (y⊗_{T} z)) ∘ (α (w⊗_{T}x) y z).

Definition monoidal_laws {C : category} (MD : monoidalcategory_data C) : UU :=
  (tensorfunctor_id MD) × (tensorfunctor_comp MD) × (associator_naturality MD) × (associator_is_natiso MD) ×
                                                    (leftunitor_naturality MD) × (leftunitor_is_natiso MD) ×
                                                    (rightunitor_naturality MD) × (rightunitor_is_natiso MD) ×
                                                    (triangle_identity MD MD MD) × (pentagon_identity MD).

Definition tensorfunctorialityid_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : tensorfunctor_id MD := pr1 ML.
Coercion tensorfunctorialityid_from_monoidallaws : monoidal_laws >-> tensorfunctor_id.

Definition tensorfunctorialitycomp_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : tensorfunctor_comp MD := pr1 (pr2 ML).
Coercion tensorfunctorialitycomp_from_monoidallaws : monoidal_laws >-> tensorfunctor_comp.

Definition associatornaturality_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : associator_naturality MD := pr1 (pr2 (pr2 ML)).
Coercion associatornaturality_from_monoidallaws : monoidal_laws >-> associator_naturality.

Definition associatorisiso_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : associator_is_natiso MD := pr1 (pr2 (pr2 (pr2 ML))).
Coercion associatorisiso_from_monoidallaws : monoidal_laws >-> associator_is_natiso.

Definition leftunitornaturality_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : leftunitor_naturality MD := pr1 (pr2 (pr2 (pr2 (pr2 ML)))).
Coercion leftunitornaturality_from_monoidallaws : monoidal_laws >-> leftunitor_naturality.

Definition leftunitorisiso_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : leftunitor_is_natiso MD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 ML))))).
Coercion leftunitorisiso_from_monoidallaws : monoidal_laws >-> leftunitor_is_natiso.

Definition rightunitornaturality_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : rightunitor_naturality MD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 ML)))))).
Coercion rightunitornaturality_from_monoidallaws : monoidal_laws >-> rightunitor_naturality.

Definition rightunitorisiso_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : rightunitor_is_natiso MD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 ML))))))).
Coercion rightunitorisiso_from_monoidallaws : monoidal_laws >-> rightunitor_is_natiso.

Definition triangleidentity_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : triangle_identity MD MD MD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 ML)))))))).
Coercion triangleidentity_from_monoidallaws : monoidal_laws >-> triangle_identity.

Definition pentagonidentity_from_monoidallaws {C : category} {MD : monoidalcategory_data C} (ML : monoidal_laws MD) : pentagon_identity MD := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 ML)))))))).
Coercion pentagonidentity_from_monoidallaws : monoidal_laws >-> pentagon_identity.

Definition monoidalcategory (C : category) : UU :=
  ∑ (MD : monoidalcategory_data C), (monoidal_laws MD).

Definition monoidalcategorydata_from_monoidalcategory {C : category} (M : monoidalcategory C) : monoidalcategory_data C := pr1 M.
Coercion monoidalcategorydata_from_monoidalcategory : monoidalcategory >-> monoidalcategory_data.

Definition monoidallaws_from_monoidalcategory {C : category} (M : monoidalcategory C) : monoidal_laws M := pr2 M.
Coercion monoidallaws_from_monoidalcategory : monoidalcategory >-> monoidal_laws.
