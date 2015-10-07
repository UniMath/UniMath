Require Export UniMath.Foundations.StandardFiniteSets.
Unset Automatic Introduction.

Definition Sequence X := Σ n, stn n -> X.

Definition length {X} : Sequence X -> nat := pr1.

Definition nil {X} : Sequence X.
Proof.
  intros.
  exists 0.
  intros i.
  induction (negstn0 i).
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

Lemma append_length {X} (x:Sequence X) (y:X) :
  length (append x y) = S (length x).
Proof.

Admitted.

Definition concatenate {X} : binop (Sequence X).
Proof.
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ (dni_allButLast _))) (y (lastelement _))). }
Defined.

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof.


Admitted.

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

Lemma flatten_length {X} (x : Sequence (Sequence X)) :
  length (flatten x) = stnsum (λ i, length ((pr2 x) i)).
Proof.

Abort.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ (dni_allButLast _))) (x (lastelement n)).
Proof. intros. reflexivity. Defined.

Local Definition assoc1 {X} (x y:Sequence X) (z:X) :
  append (concatenate x y) z = concatenate x (append y z).
Proof.
  intros.
  induction x as [m x].
  induction y as [n y].
  refine (total2_paths _ _).
  - change pr1 with (@length X).
    repeat rewrite append_length.
    repeat rewrite concatenate_length.
    simpl.
    apply pathsinv0.
    apply natplusnsm.
  - 

Admitted.

Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  induction z as [n z].
  induction n as [|n IH].
  - reflexivity.
  - repeat rewrite concatenateStep.
    generalize (z (lastelement n)) as w; intros.
    generalize (z ∘ dni_allButLast n) as v; intros.
    rewrite <- assoc1.
    apply (maponpaths (λ t, append t w)).
    apply IH.
Defined.


