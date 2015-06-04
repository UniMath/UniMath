Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UnicodeNotations.


Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Arguments functor_composite {_ _ _} _ _ .

Section Monoidal_Structure_on_Endofunctors.

Variable C : precategory.

Definition ρ_functor (X : functor C C) 
  : nat_trans (functor_composite X (functor_identity C)) X.
Proof.
  exists (λ x, identity (X x) ) .
  intros a b f. simpl. 
  pathvia (#X f).
  - apply id_right.
  - apply pathsinv0, id_left.
Defined.

Definition λ_functor (X : functor C C) 
  : nat_trans (functor_composite (functor_identity C) X) X
  := ρ_functor X.

Definition α_functor (X Y Z : functor C C)
  : nat_trans (functor_composite (functor_composite X Y) Z)
              (functor_composite X (functor_composite Y Z)).
Proof.
  exists (λ x, identity _ ).
  intros a b f; 
  simpl.
  eapply pathscomp0.
  - apply id_right.
  - apply pathsinv0, id_left.
Defined.

End Monoidal_Structure_on_Endofunctors.







