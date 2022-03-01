Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Section Monoidal_Precategories.

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
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧), f∘(λ_ob x) = (λ_ob y)∘((identity I)⊗^{T}f).

  Definition left_unitor {C : category} (T : tensor C) (I : C) :=
    ∑ (λ_ob : left_unitor_on_objects T I), left_unitor_naturality T I λ_ob.

  Definition right_unitor_on_objects {C : category} (T : tensor C) (I : C) :=
    ∏ (x : C), C ⟦x ⊗_{T} I, x⟧.

  Definition right_unitor_naturality {C : category} (T : tensor C) (I : C) (ρ_ob : right_unitor_on_objects T I) :=
    ∏ (x y : C), ∏ (f : C ⟦x,y⟧), f∘(ρ_ob x) = (ρ_ob y)∘ (f ⊗^{T} (identity I)).

  Definition right_unitor {C : category} (T : tensor C) (I : C) :=
    ∑ (ρ_ob : right_unitor_on_objects T I), right_unitor_naturality T I ρ_ob.

  Definition triangle_identity {C : category}
             (T : tensor C)
             (I : C)
             (lu : left_unitor T I)
             (ru : right_unitor T I)
             (α : associator T)
    := ∏ (x y : C),  (((pr1 ru) x) ⊗^{T} identity y) = (((identity x)  ⊗^{T} (pr1 lu) y ) ∘ ((pr1 α) x I y)).

  Definition pentagon_identity {C : category} (T : tensor C) (α : associator T) :=
    ∏ (w x y z : C),
      ((pr1 α) w x (y⊗_{T} z)) ∘ ((pr1 α) (w⊗_{T}x) y z) =
         ((identity w)⊗^{T} ((pr1 α) x y z))
           ∘ ((pr1 α) w (x⊗_{T} y) z)
           ∘ (((pr1 α) w x y) ⊗^{T} (identity z)).

  Definition monoidal_category  : UU :=
    ∑ C : category, ∑ T : tensor C, ∑ I : C,
            ∑ lu : left_unitor T I,
              ∑ ru : right_unitor T I,
                ∑ α : associator T,
                  (triangle_identity T I lu ru α) × (pentagon_identity T α).


  End Monoidal_Precategories.
