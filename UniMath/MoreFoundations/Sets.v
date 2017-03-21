Require Export UniMath.MoreFoundations.Notations.

Local Open Scope set.

Definition isconst {X:UU} {Y:hSet} (f : X -> Y) : hProp := ∀ x x', f x = f x'.

Definition squash_to_hSet {X : UU} {Y : hSet} (f : X -> Y) : isconst f -> ∥ X ∥ -> Y.
Proof.
  apply squash_to_set, setproperty.
Defined.
