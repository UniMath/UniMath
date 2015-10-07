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

Definition sequenceMap {X Y} (f:X->Y) : Sequence X -> Sequence Y.
Proof. intros ? ? ? [n x]. exact (n,,f∘x). Defined.

Definition nil {X} : Sequence X.
Proof.
  intros.
  exists 0.
  intros [i b].
  induction (negnatlthn0 _ b).
Defined.

Definition postDrop {X} : Sequence X -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n].
  - exact nil.                  (* yes, we didn't actually drop one *)
  - exact (n,,x ∘ allButLast).
Defined.

Definition preDrop {X} : Sequence X -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n].
  - exact nil.                  (* yes, we didn't actually drop one *)
  - exact (n,,x ∘ allButFirst).
Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof.
  intros ? [m x] y.
  exists (S m).
  intros [i b].
  destruct (natlthorgeh i m) as [c|d].
  { exact (x (i,,c)). }
  { exact y. }
Defined.

Definition prepend {X} : X -> Sequence X -> Sequence X.
Proof.
  intros ? y [m x].
  exists (S m).
  intros [i b].
  destruct i as [|i].
  { exact y. }
  { exact (x (i,,b)). }
Defined.

Definition pair_path_in2 {X} (P:X->Type) {x:X} {p q:P x} (e:p = q) : x,,p = x,,q.
(* move upstream and remove copy in Ktheory/Utilities.v *)
Proof. intros. destruct e. reflexivity. Defined.

Lemma prependCheck1 {X x} {y:X} : preDrop (prepend y x) = x.
Proof. intros ? [n x] ?. apply pair_path_in2. apply funextfun. intros [i b].
       reflexivity.
Defined.

Lemma appendCheck1 {X x} {y:X} : postDrop (append x y) = x.
Proof. intros ? [n x] ?. apply pair_path_in2. 
       unfold funcomp.
       apply funextfun; intros [i b].
       simpl.
       induction (natlthorgeh i n) as [p|q].
       { apply maponpaths. apply pair_path_in2. apply isasetbool. }
       { destruct (q b). }
Defined.

Definition concatenate {X} : Sequence X -> Sequence X -> Sequence X.
Proof.
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ allButLast)) (y (lastelement _))). }
Defined.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ allButLast)) (y (lastelement _)).
Proof.
Admitted.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n IH].
  { apply nil. }
  { exact (concatenate (IH (x ∘ allButLast)) (x (lastelement _))). }
Defined.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ allButLast)) (x (lastelement n)).
Proof. intros. reflexivity. Defined.

Open Scope multmonoid.

(* Define x0 * x1 * ... * xn as (((...((0*x0) * x1) * x2) ... ) * xn).  This is
the reverse of Bourbaki's choice, because other UniMath proofs by induction go
this way.  See, for example, [stnsum] and [weqstnsum]. It also starts with 0. *)
Definition sequenceProduct {M:monoid} (x:Sequence M) : M.
Proof.
  intros ? [n x].
  induction n as [|n sequenceProduct].     
  { exact 1. }
  { exact (sequenceProduct (postDrop (S n,,x)) * x (lastelement _)). }
Defined.

Definition sequenceProductStep {M:monoid} {n} (x:stn (S n) -> M) :
  sequenceProduct (S n,,x) = sequenceProduct (n,,x ∘ allButLast) * x (lastelement _).
Proof. intros. reflexivity. Defined.

Definition sequenceProductCheck {M:monoid} (x:Sequence M) (m:M) :
  sequenceProduct (append x m) = sequenceProduct x * m.
Proof. intros ? [n x] ?.
       unfold append.
       rewrite sequenceProductStep.
       unfold funcomp.
       unfold lastelement.
       induction (natlthorgeh n n) as [p|q].
       { destruct (isirreflnatlth _ p). }
       { apply (maponpaths (fun a => a * m)).
         apply (maponpaths (fun x => sequenceProduct (n,,x))).
         apply funextfun; intros [i b].
         simpl.
         induction (natlthorgeh i n) as [r|s].
         { apply (maponpaths x). apply pair_path_in2. apply isasetbool. }
         { destruct (s b). }}
Defined.

Definition doubleProduct {M:monoid} (x:Sequence (Sequence M)) : M.
Proof.
  intros ? [n x].
  induction n as [|n doubleProduct].     
  { exact 1. }
  { exact ((doubleProduct (x ∘ allButLast) * sequenceProduct (x (lastelement _)))). }
Defined.

Lemma doubleProductStep {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  doubleProduct (S n,,x) = doubleProduct (n,,x ∘ allButLast) * sequenceProduct (x (lastelement _)).
Proof. intros. reflexivity. Defined.

Theorem associativityOfProducts {M:monoid} (x:Sequence (Sequence M)) :
  sequenceProduct (flatten x) = doubleProduct x.
Proof.
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  { rewrite flattenStep, doubleProductStep.
    generalize (x (lastelement n)) as z.
    generalize (x ∘ allButLast) as y.
    intros y [m z].
    induction m as [|m IHm].
    { change (sequenceProduct (0,, z)) with (unel M). rewrite runax.
      change (concatenate (flatten (n,, y)) (0,, z)) with (flatten (n,, y)).
      exact (IHn y). }
    { rewrite sequenceProductStep, concatenateStep.
      generalize (z (lastelement m)) as w.
      generalize (z ∘ allButLast) as v.
      intros.
      rewrite <- assocax.
      rewrite sequenceProductCheck.
      apply (maponpaths (fun u => u*w)).
      apply IHm. }
  }
Defined.
