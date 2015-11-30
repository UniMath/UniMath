(** * Tactics *)

Unset Automatic Introduction.

Require Import UniMath.Foundations.Basics.PartA.

Notation ap := maponpaths (only parsing).

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact ((@id G : T -> G) x).

Definition post_cat {X} {x y z:X} {q:y = z} : x = y -> x = z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 q p). Defined.

Definition pre_cat {X} {x y z:X} {q:x = y} : y = z -> x = z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 p q). Defined.

Ltac maponpaths_pre_post_cat :=
  repeat rewrite path_assoc; repeat apply (ap post_cat); repeat rewrite <- path_assoc;
  repeat apply (ap pre_cat); repeat rewrite path_assoc; repeat rewrite maponpathsinv0;
  try reflexivity.
