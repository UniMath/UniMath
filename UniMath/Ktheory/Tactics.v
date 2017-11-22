(** * Tactics *)
Require Import UniMath.Foundations.Sets UniMath.Foundations.UnivalenceAxiom.

Notation ap := maponpaths (only parsing).

Definition post_cat {X} {x y z:X} {p:y = z} : x = y -> x = z.
Proof. intros q. exact (pathscomp0 q p). Defined.

Definition pre_cat {X} {x y z:X} {p:x = y} : y = z -> x = z.
Proof. intros q. exact (pathscomp0 p q). Defined.

Ltac maponpaths_pre_post_cat :=
  repeat rewrite path_assoc; repeat apply (ap post_cat); repeat rewrite <- path_assoc;
  repeat apply (ap pre_cat); repeat rewrite path_assoc; repeat rewrite maponpathsinv0;
  try reflexivity.

Ltac prop_logic :=
  abstract (intros; simpl;
            repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro);
            try (apply isapropiscontr); try assumption) using _L_.

Lemma iscontrweqb' {X Y} (is:iscontr Y) (w:X ≃ Y) : iscontr X.
Proof. intros. apply (iscontrweqb (Y:=Y)). assumption. assumption. Defined.

Ltac intermediate_iscontr  Y' := apply (iscontrweqb (Y := Y')).
Ltac intermediate_iscontr' Y' := apply (iscontrweqb' (Y := Y')).

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

(* less fancy than [isaprop_goal ig.] is [apply isaprop_goal; intro ig.] *)
Definition isaprop_goal X (ig:isaprop X) (f:isaprop X -> X) : X.
Proof. intros. exact (f ig). Defined.

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).
