Require Export UniMath.MoreFoundations.Notations.

Local Open Scope set.

Definition isconst {X:UU} {Y:hSet} (f : X -> Y) : hProp := ∀ x x', f x = f x'.
