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

Local Open Scope cat.

  Definition tensor (C : category) : UU :=
    ∑ tensor_ob : C -> C -> C,
            ∏ (x y x' y' : C), C ⟦x,x'⟧ → C ⟦y,y'⟧ -> C ⟦(tensor_ob x y),(tensor_ob x' y')⟧.

  Definition tensor_cat_struct : UU :=
    ∑ C : category, (tensor C).

  Definition cat_from_tensor_cat (X : tensor_cat_struct) : category := pr1 X.
  Coercion cat_from_tensor_cat : tensor_cat_struct >-> category.

  Definition tensor_from_tensor_cat (X : tensor_cat_struct) : tensor X := pr2 X.
  Coercion tensor_from_tensor_cat : tensor_cat_struct >-> tensor.

  Definition tensoronobjects_from_tensor_cat {C : category} (T : tensor C) : C->C->C := pr1 T.
  Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensor_cat T x y) (at level 31).

  Definition tensoronmorphisms_from_tensor_cat {C : category} (T : tensor C):
    ∏ (x y x' y' : C), C ⟦x,x'⟧ → C ⟦y,y'⟧ -> C ⟦x ⊗_{T} y,x' ⊗_{T} y'⟧
    := pr2 T.
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensor_cat T  _ _ _ _ f g) (at level 31).

  Definition tensor_functor_id {C : category} (T : tensor C) : UU :=
    ∏ (x y : C),
      (identity x) ⊗^{T} identity y = identity (x ⊗_{T} y).

  Definition tensor_functor_comp {C : category} (T : tensor C) : UU :=
    ∏ (x y x' y' x'' y'' : C), ∏ (f : C ⟦x,x'⟧) (f' : C ⟦x',x''⟧) (g : C ⟦y,y'⟧) (g' : C ⟦y',y''⟧),
      (f'∘f) ⊗^{T} (g'∘g) = (f' ⊗^{T} g') ∘ (f ⊗^{T} g).


  Definition associator_on_objects {C : category} (T : tensor C) :=
    ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

  Definition associator_naturality {C : category} (T : tensor C) (α_ob : associator_on_objects T) :=
    ∏ (x x' y y' z z' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧),
      (f ⊗^{T} (g ⊗^{T} h))∘(α_ob x y z) = (α_ob x' y' z')∘ ((f ⊗^{T} g) ⊗^{T} h).

  Definition associator {C : category} (T : tensor C) :=
    ∑ (α_ob : associator_on_objects T), associator_naturality T α_ob.

  (* REMARK:: The associator should be a natural isomorphism, but the isomorphism is not included in the definition *)

  Definition left_unitor_on_objects {C : category} (T : tensor C) (I : C) :=
    ∏ (x : C), C ⟦I ⊗_{T} x, x⟧.

  Definition left_unitor_naturality {C : category} (T : tensor C) (I : C) (λ_ob : left_unitor_on_objects T I) :=
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧), (λ_ob y)∘((identity I)⊗^{T}f) = f∘(λ_ob x).

  Definition left_unitor {C : category} (T : tensor C) (I : C) :=
    ∑ (λ_ob : left_unitor_on_objects T I), left_unitor_naturality T I λ_ob.

  Definition right_unitor_on_objects {C : category} (T : tensor C) (I : C) :=
    ∏ (x : C), C ⟦x ⊗_{T} I, x⟧.

  Definition right_unitor_naturality {C : category} (T : tensor C) (I : C) (ρ_ob : right_unitor_on_objects T I) :=
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧), (ρ_ob y)∘ (f ⊗^{T} (identity I)) = f∘(ρ_ob x).

  Definition right_unitor {C : category} (T : tensor C) (I : C) :=
    ∑ (ρ_ob : right_unitor_on_objects T I), right_unitor_naturality T I ρ_ob.

  Definition triangle_identity {C : category}
             (T : tensor C)
             (I : C)
             (lu : left_unitor T I)
             (ru : right_unitor T I)
             (α : associator T)
    := ∏ (x y : C),  (((identity x)  ⊗^{T} (pr1 lu) y ) ∘ ((pr1 α) x I y)) = (((pr1 ru) x) ⊗^{T} identity y).

  Definition pentagon_identity {C : category} (T : tensor C) (α : associator T) :=
    ∏ (w x y z : C),
         ((identity w)⊗^{T} ((pr1 α) x y z))
           ∘ (((pr1 α) w (x⊗_{T} y) z)
           ∘ (((pr1 α) w x y) ⊗^{T} (identity z))) =  ((pr1 α) w x (y⊗_{T} z)) ∘ ((pr1 α) (w⊗_{T}x) y z).

  Definition monoidal_category  : UU :=
    ∑ C : category, ∑ T : tensor C, ∑ I : C,
            ∑ lu : left_unitor T I,
              ∑ ru : right_unitor T I,
                ∑ α : associator T,
                  (tensor_functor_id T) × (tensor_functor_comp T) ×
                  (triangle_identity T I lu ru α) × (pentagon_identity T α).

  (* Some definitions to extract the data from a monoidal category. *)
  Definition category_extraction_of_monoidalcat (M : monoidal_category) : category := pr1 M.
  Coercion category_extraction_of_monoidalcat : monoidal_category >-> category.

  Definition tensor_extraction_of_monoidalcat (M : monoidal_category) : tensor M := pr1 (pr2 M).
  Coercion tensor_extraction_of_monoidalcat : monoidal_category >-> tensor.

  Definition unit_extraction_of_monoidalcat (M : monoidal_category) : M :=
    pr1 (pr2 (pr2 M)).

  Definition leftunitor_extraction_of_monoidalcat (M : monoidal_category) : left_unitor (tensor_extraction_of_monoidalcat M) (unit_extraction_of_monoidalcat M) :=
    pr1 (pr2 (pr2 (pr2 M))).

  Definition rightunitor_extraction_of_monoidalcat (M : monoidal_category) : right_unitor (tensor_extraction_of_monoidalcat M) (unit_extraction_of_monoidalcat M) :=
    pr1 (pr2 (pr2 (pr2 (pr2 M)))).

  Definition associator_extraction_of_monoidalcat (M : monoidal_category) : associator (tensor_extraction_of_monoidalcat M) :=
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

  Definition tensorfunctorid_identity_extraction_of_monoidalcat (M : monoidal_category) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

  Definition tensorfunctorcomp_identity_extraction_of_monoidalcat (M : monoidal_category) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))).

  Definition triangleidentity_extraction_of_monoidalcat (M : monoidal_category) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))))).

  Definition pentagonidentity_extraction_of_monoidalcat (M : monoidal_category) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))))).
