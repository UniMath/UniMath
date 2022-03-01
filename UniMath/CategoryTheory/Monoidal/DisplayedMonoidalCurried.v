
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Section DisplayedCurriedMonoidalCategories.

  (* These notations come from 'MonoidalCategoriesCurried' *)
  Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensor_cat T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensor_cat T  _ _ _ _ f g) (at level 31).

  Definition displayed_tensor_on_objects {C : category} (T : tensor C) (D : disp_cat C) :=
    ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y)).

  Notation "a ⊗_{{ TDO }} b" := (TDO _ _ a b) (at level 31).

  Definition displayed_tensor_on_morphisms {C : category} (T : tensor C) (D : disp_cat C) (TDO : displayed_tensor_on_objects T D) :=
    ∏ (x x' y y' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y'),
      (a -->[f] a') -> (b -->[g] b') -> ((a ⊗_{{TDO}} b)-->[f ⊗^{T} g] (a' ⊗_{{TDO}} b')).

  Notation "f ⊗^{{ TDM }} g" := (TDM _ _ _ _ f g _ _ _ _ _ _ ) (at level 31).

  Definition displayed_tensor {C : category} (T : tensor C) (D : disp_cat C) :=
    ∑ (TDO : displayed_tensor_on_objects T D), (displayed_tensor_on_morphisms T D TDO).

  Proposition total_category_has_tensor {C : category} (T : tensor C) (D : disp_cat C) (TD : displayed_tensor T D) :
    tensor (total_category D).
  Proof.
    unfold tensor.
    split with (λ xa yb, (pr1 xa) ⊗_{T} (pr1 yb) ,, (pr2 xa) ⊗_{{pr1 TD}} (pr2 yb)).
    intros xa yb xa' yb' f g.
    simpl.
    split with (pr1 f ⊗^{T} pr1 g).
    apply (pr2 TD).
    + exact (pr2 f).
    + exact (pr2 g).
  Defined.

End DisplayedCurriedMonoidalCategories.
