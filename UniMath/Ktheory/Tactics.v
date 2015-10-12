(** * Tactics *)

Require Import UniMath.Foundations.Sets UniMath.Foundations.FunctionalExtensionality.

Ltac prop_logic := 
  intros; simpl;
  repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro); 
  try (apply isapropiscontr); try assumption.

Lemma iscontrweqb' {X Y} (is:iscontr Y) (w:X ≃ Y) : iscontr X.
Proof. intros. apply (iscontrweqb (Y:=Y)). assumption. assumption. Defined.

Ltac intermediate_iscontr' Y' := apply (iscontrweqb' (Y := Y')).

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).
