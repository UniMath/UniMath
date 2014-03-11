Unset Automatic Introduction.

Require Import RezkCompletion.pathnotations.
Require Import Foundations.hlevel2.hSet.
        Import RezkCompletion.pathnotations.PathNotations.

Fixpoint c (m n:nat) : UU.
  intros [|m] [|n].
  * exact unit.
  * exact empty.
  * exact empty.
  * exact (c m n).
Defined.

Fixpoint encode (m n:nat) : m == n -> c m n.
  intros [|m] [|n] p.
  * exact tt.
  * destruct p. exact tt.
  * destruct p.