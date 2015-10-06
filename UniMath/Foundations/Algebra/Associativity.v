Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

(* move upstream *)
    Local Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).
    Local Notation "g ∘ f" := (funcomp f g) (at level 50, no associativity).

Definition allButFirst {n} : stn n -> stn (S n).
Proof. intros ? [h hm]. now exists (S h). Defined.

Goal ∀ n (h:stn n), allButFirst h = dni n (firstelement n) h.
Proof. intros ? [h hm]. reflexivity. Qed.

Definition allButLast {n} : stn n -> stn (S n).
Proof. intros ? h. destruct h as [h hm]. exists h. now apply natlthtolths. Defined.

Goal ∀ n (h:stn n), allButLast h = dni n (lastelement n) h.
Proof. intros ? [h hm].
       simpl.
       try reflexivity. (* doesn't work *)
       unfold dni; simpl.
       induction (natlthorgeh h n).
       { unfold natlthtolths, stnpair.
         reflexivity. (* works only because the propositional proofs are identical *)
       }
       { induction (b hm). }
Qed.

Lemma stnntosnlt {n} (h:stn n) : allButLast h < allButFirst h.
Proof. intros ? [h hm]. apply natlthnsn. Defined.

Lemma stnntosnle {n} (h:stn n) : allButLast h ≤ allButFirst h.
Proof. intros ? [h hm]. apply natlehnsn. Defined.

Definition foldleft {E} (e:E) (m:E->E->E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldleft].
  + exact e. 
  + exact (m (foldleft (x ∘ allButLast)) (x (lastelement _))).
Defined.  

Definition foldright {E} (e:E) (m:E->E->E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldright].
  + exact e. 
  + exact (m (x (firstelement _)) (foldright (x ∘ allButFirst))).
Defined.  

(* *)


(** * Associativity theorem, as in Bourbaki, Algebra, Theorem 1, page 4. *)

(** approach #1 *)

(* We consider sequences of sequences. *)

Definition Sequence X := Σ n, stn n -> X.

Definition sequenceLength   {X} (x : Sequence X) : nat
  := pr1 x.
Definition sequenceFunction {X} (x : Sequence X) : stn (sequenceLength x) -> X
  := pr2 x.
Coercion sequenceFunction: Sequence >-> Funclass.

Definition nil X : Sequence X.
Proof.
  intros.
  exists 0.
  intros [i b].
  induction (negnatlthn0 _ b).
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

Definition concatenate {X} : Sequence X -> Sequence X -> Sequence X.
Proof.
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ allButLast)) (y (lastelement _))). }
Defined.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n IH].
  { apply nil. }
  { exact (concatenate (IH (x ∘ allButLast)) (x (lastelement _))). }
Defined.

(* Define x0 + x1 + ... + xn as (((...((0+x0) + x1) + x2) ... ) + xn).  This is
the reverse of Bourbaki's choice, because other UniMath proofs by induction go
this way.  See, for example, [stnsum] and [weqstnsum]. It also starts with 0. *)
Definition sequenceSum {M:monoid} (x:Sequence M) : M.
Proof.
  intros ? [n x].
  induction n as [|n sum].     
  Open Scope addmonoid.
  { exact (0). }
  { exact (sum (x ∘ allButLast) + x (lastelement _)). }
  Close Scope addmonoid.
Defined.

Definition sequenceMap {X Y} (f:X->Y) : Sequence X -> Sequence Y.
Proof. intros ? ? ? [n x]. exact (n,,f∘x). Defined.

Definition doubleSum {M:monoid} (x:Sequence (Sequence M)) : M.
Proof.
  intros ? [n x].
  induction n as [|n sum].     
  { exact (0 % addmonoid). }
  { exact ((sum (x ∘ allButLast) + sequenceSum (x (lastelement _))) % addmonoid). }
Defined.

Theorem associativityOfSums1 {M:monoid} (x:Sequence (Sequence M)) :
  sequenceSum (flatten x) = doubleSum x.
Proof.
  Open Scope multmonoid.
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  { 





    destruct (x (lastelement n)) as [m xn].
    
    
    
    induction m as [|m IHm].
    { change (sequenceSum (0,, xn)) with (unel M).
      


      (* ... working here ... *)


  Close Scope multmonoid.
Abort.
