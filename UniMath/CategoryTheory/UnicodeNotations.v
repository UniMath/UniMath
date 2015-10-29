Require Export UniMath.Foundations.Basics.All
               UniMath.Foundations.Propositions
               UniMath.CategoryTheory.precategories.

Notation "x → y" := (x -> y)
  (at level 90, y at level 200, right associativity): type_scope.
(* written \to in Agda input method *)

Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)

Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g", left associativity).

Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).
  (* \[[ and \]] in Agda input method *)