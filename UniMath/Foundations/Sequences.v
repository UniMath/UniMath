Require Export UniMath.Foundations.StandardFiniteSets.
Unset Automatic Introduction.

Definition Sequence X := Σ n, stn n -> X.

Definition nil {X} : Sequence X.
Proof.
  intros.
  exists 0.
  intros [i b].
  induction (negnatlthn0 _ b).
Defined.

Definition drop {X} : Sequence X -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n].
  - exact nil.                  (* yes, we didn't actually drop one *)
  - exact (n,,x ∘ (dni_allButLast _)).
Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof.
  intros ? [m x] y.
  exists (S m).
  intros [i b].
  induction (natlthorgeh i m) as [c|d].
  { exact (x (i,,c)). }
  { exact y. }
Defined.

Definition concatenate {X} : binop (Sequence X).
Proof.
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ (dni_allButLast _))) (y (lastelement _))). }
Defined.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ (dni_allButLast _))) (y (lastelement _)).
Proof. intros.
       reflexivity.             (* why does this work? *)
Defined.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n IH].
  { apply nil. }
  { exact (concatenate (IH (x ∘ (dni_allButLast _))) (x (lastelement _))). }
Defined.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ (dni_allButLast _))) (x (lastelement n)).
Proof. intros. reflexivity. Defined.

Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  induction z as [n z].
  induction n as [|n IH].
  - reflexivity.
  - rewrite concatenateStep.
    