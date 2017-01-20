Require Export UniMath.Foundations.PartD
               UniMath.Foundations.Propositions
               UniMath.CategoryTheory.precategories
               UniMath.CategoryTheory.functor_categories.

Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g", left associativity).
Notation "# F" := (functor_on_morphisms F) (at level 3).

Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).
  (* \[[ and \]] in Agda input method *)