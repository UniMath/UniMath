Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

(* move upstream *)
    Local Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).
    Local Notation "g ∘ f" := (funcomp f g) (at level 50).

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

(*
Define x0 + x1 + ... + xn as (((...((0+x0) + x1) + x2) ... ) + xn).  This is the
reverse of Bourbaki's choice, because other UniMath proofs by induction go
this way.  See especially [stnsum] and [weqstnsum]. It also starts with 0.
*)

Definition monoidSum {E:monoid} {n} (x:stn n -> E): E.
Proof. intros. exact (foldleft (unel _) op x). Defined.

(** approach #1 *)

(* We consider sequences of sequences. *)

Definition Sequence X := Σ n, stn n -> X.

Definition sequenceLength   {X} (x : Sequence X) : nat
  := pr1 x.
Definition sequenceFunction {X} (x : Sequence X) : stn (sequenceLength x) -> X
  := pr2 x.
Coercion sequenceFunction: Sequence >-> Funclass.

Definition sequenceSum {M:monoid} (x:Sequence M) : M.
Proof. intros. exact (monoidSum x). Defined.

Open Scope addmonoid.
Lemma peelOffTerm {E:monoid} {n} (x:stn (S n) -> E):
  sequenceSum (S n,,x) = sequenceSum(n,,x∘allButLast) + x(lastelement _).
Proof. intros. reflexivity. Defined.
Close Scope addmonoid.

Definition sequenceMap {X Y} (f:X->Y) : Sequence X -> Sequence Y.
Proof. intros ? ? ? [n x]. exact (n,,f∘x). Defined.

Definition sequenceSequenceSum {M:monoid} (x:Sequence (Sequence M)) : M
  := sequenceSum (sequenceMap sequenceSum x).

Definition Bisequence X := Σ n (m:stn n->nat), (Σ i, stn (m i)) -> X.

(* We use [weqstnsum] to concatenate standard finite sets.  *)
Definition stntotal: ∀ {n : nat} (m : stn n -> nat), stn (stnsum m) ≃ Σ i, stn (m i).
Proof. intros. exact (invweq (weqstnsum (stn∘m) m (fun _ => idweq _))). Defined.

Section Test.
  (* If m computes on numerals, so does stntotal m, in the sense that you can
     verify the answer *)
  Let b := idpath true.
  Let m := fun (i:stn 4) => pr1 i . (* m is (0,1,2,3) *)
  Let f := stntotal m.
  Goal stnsum m = 6. reflexivity. Defined.
  Goal f (5,,b) = ((3,,b),,(2,,b)). reflexivity. Defined.
  (* But this takes a long time: Eval compute in f (0,,b). *)
End Test.    

Definition flatten_Bisequence {X} : Bisequence X -> Sequence X.
Proof. 
  intros ? [n [m x]].
  exact (stnsum m,,x ∘ stntotal m).
Defined.

Definition toBisequence {X} : Sequence (Sequence X) -> Bisequence X.
Proof.
  intros ? [n x].
  exists n.
  exists (sequenceLength ∘ x).
  intros [i j].
  exact ((x i) j).
Defined.

Definition fromBisequence {X} : Bisequence X -> Sequence (Sequence X).
Proof.
  intros ? [n [m x]].
  exists n.
  intros i.
  exists (m i).
  intros j.
  exact (x (i,,j)).
Defined.  

Definition pair_path_in2 {X} (P:X->Type) {x:X} {p q:P x} (e:p = q) : x,,p = x,,q.
(* move upstream and remove copy in Ktheory/Utilities.v *)
Proof. intros. destruct e. reflexivity. Defined.

Definition Bisequence_weq X : Sequence (Sequence X) ≃ Bisequence X.
Proof.                          (* is this a special case of something else? *)
  intros.
  refine (_,,gradth toBisequence fromBisequence _ _).
  { intros [n x]. simpl.
    apply pair_path_in2.
    apply funextfun; intros i.
    unfold funcomp, sequenceLength.
    destruct (x i); simpl.
    apply pair_path_in2.
    apply funextfun; intros j.
    reflexivity. }
  { intros [n [m x]].
    apply pair_path_in2.
    unfold funcomp, sequenceLength.
    simpl.
    apply pair_path_in2.
    apply funextfun; intros [i j].
    reflexivity.
    }
Defined.

Theorem associativityOfSums1 {M:monoid} (x:Sequence (Sequence M)) :
  sequenceSum (flatten_Bisequence (toBisequence x)) = sequenceSum (sequenceMap sequenceSum x).
Proof.
  Open Scope multmonoid.
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  { unfold sequenceMap.
    rewrite peelOffTerm.
    change ((sequenceSum ∘ x) (lastelement n)) with (sequenceSum (x (lastelement n))).


    destruct (x (lastelement n)) as [m xn].
    
    
    
    induction m as [|m IHm].
    { change (sequenceSum (0,, xn)) with (unel M).
      rewrite runax.
      


      (* ... working here ... *)


  Close Scope multmonoid.
Admitted.

(** approach #2 *)

(* We represent a partition of [stn n] into m subintervals by giving an
   increasing sequence k_0 .. k_m in the range 0..n .  The i-th number k_i is
   the least number not in the any of the first i subintervals, so it's the
   starting number for the i+1-st subinterval.  The first number
   is always 0 and the last number is always n.

   Examples:
       m=n=0   k=(0)          
       m=1     k=(0,n)        [0,n)
       m=2     k=(0,i,n)      [0,i)  [i,n)
               k=(0,n,n)      [0,n)  [n,n)
       m=3     k=(0,i,j,n)    [0,i)  [i,j)  [j,n)
               k=(0,0,n,n)    [0,0)  [0,n)  [n,n)
   *)

Definition enumerateSubinterval {n i j}: i ≤ j -> j ≤ n -> stn (j-i) -> stn n.
Proof.
  intros ? ? ? ij jn [k kji].
  exists (k+i).
  refine (natlthlehtrans _ _ _ _ jn).
  destruct (minusplusnmm _ _ ij).
  now apply natlthandplusr.
Defined.

Section Test2.
    Goal 5 ≤ 7. exact nopathsfalsetotrue. Defined.
    Let a := nopathsfalsetotrue.
    Goal 5 ≤ 7. trivial. Defined.

    Goal 5 < 7. reflexivity. Defined.
    Let b := idpath true.
    Goal 5 < 7. exact b. Defined.
    Goal 5 < 7. trivial. Defined.

    Goal @enumerateSubinterval 7 3 6 a a (0,,b) = (3,,b). reflexivity. Defined.
    Goal @enumerateSubinterval 7 3 6 a a (1,,b) = (4,,b). reflexivity. Defined.
    Goal @enumerateSubinterval 7 3 6 a a (2,,b) = (5,,b). reflexivity. Defined.
End Test2.

Definition monoidSumSubinterval {E:monoid} {n} (x:stn n -> E) i j: i ≤ j -> j ≤ n -> E.
Proof.
  intros ? ? ? ? ? ij jn.
  exact (monoidSum (x ∘ enumerateSubinterval ij jn)).
Defined.

Definition SizedPartition n numparts := 
     Σ k: posetmorphism (stnposet (S numparts)) (stnposet (S n)),
          k (firstelement numparts) = firstelement n
            ×
          k (lastelement numparts) = lastelement n.

Definition Partition n          (* a partition of [stn n], as above *)
  := Σ numparts, SizedPartition n numparts.

Definition monoidSumOfSums {E:monoid} {n} (x:stn n -> E) (P:Partition n) : E.
Proof.  
  intros.
  induction P as [p [[k o] [a b]]].
  simpl in a, b, k.
  apply (@monoidSum E p).
  intros h.
  apply (monoidSumSubinterval x (k (allButLast h)) (k (allButFirst h))).
  { apply o. apply stnntosnle. }
  apply natlthsntoleh. apply stnlt.
Defined.

Open Scope multmonoid.
Open Scope addmonoid.
Theorem associativityOfSums2 (E:monoid) n (x:stn n -> E) (P:Partition n) :
  monoidSum x = monoidSumOfSums x P.
Proof.
  intros.
  induction P as [p Q].
  (* Bourbaki reasons by induction on n, but we allow empty subintervals, so
     we use induction on p. Otherwise we have to prove things like
     0+0+0+0+x+0+0+0+0 = x. *)
  induction p as [|p IH].
  { induction Q as [[k o] [a b]]. now destruct (maponpaths pr1 (!a @ b) : O = n). }
  { 


Admitted.




