
Require Export UniMath.Foundations.Basics.All
               UniMath.Foundations.Propositions
               UniMath.CategoryTheory.precategories.

Notation "x → y" := (x -> y)
  (at level 90, y at level 200, right associativity): type_scope.
(* written \to in Agda input method *)

Notation "∥ A ∥" := (ishinh A) (at level 200) : type_scope.
(* written \|| *)

Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)
Notation "g ;; f" := (compose g f)(at level 50, left associativity).
