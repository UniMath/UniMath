
Require Export Foundations.Generalities.uu0.
Require Export Foundations.hlevel1.hProp.
Require Export UniMath.RezkCompletion.precategories.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'Σ'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "A × B" := (dirprod A B) (at level 80, no associativity) : type_scope.
Notation "X ≃ Y" := (weq X Y) (at level 80, no associativity) : type_scope.
(* written \simeq in Agda input method *) 
Notation "x → y" := (x -> y)
  (at level 90, y at level 200, right associativity): type_scope.
(* written \to in Agda input method *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "∥ A ∥" := (ishinh A) (at level 200) : type_scope.
(* written \|| *)

Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)
Notation "g ;; f" := (compose g f)(at level 50, left associativity).
