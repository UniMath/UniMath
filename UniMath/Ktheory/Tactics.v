(** * Tactics *)

Require Import Foundations.hlevel2.hSet funextfun.
Require RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact ((@id G : T -> G) x).

Ltac prop_logic := 
  intros; simpl;
  repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro); 
  try (apply isapropiscontr); try assumption.

Ltac intermediate_path x := apply (pathscomp0 (b := x)).

Ltac intermediate_weq Y' := apply (weqcomp (Y := Y')).

Ltac intermediate_iscontr Y' := apply (iscontrweqb (Y := Y')).

Lemma iscontrweqb' {X Y} (is:iscontr Y) (w:weq X Y) : iscontr X.
Proof. intros. apply (iscontrweqb (Y:=Y)). assumption. assumption. Defined.

Ltac intermediate_iscontr' Y' := apply (iscontrweqb' (Y := Y')).

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).
