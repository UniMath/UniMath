Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

(* move upstream *)
    Local Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).
    Local Notation "g ∘ f" := (funcomp f g) (at level 50).
(* *)

(** * Associativity theorem, as in Bourbaki, Algebra, Theorem 1, page 4. *)

(** define x0 + x1 + ... + xn as x0 + (x1 + (...( + xn)...)). *)
Definition monoidSum {E:monoid} {n} (x:stn n -> E): E.
Proof.
Open Scope addmonoid.
  intros.
  induction n as [|n sum].
  { exact (0). }
  { set (zero := (O,,natgthsn0 n) : stn (S n)). exact (x zero + sum (x ∘ dni _ zero)). }
Close Scope addmonoid.
Defined.

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

Section Test.
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
End Test.

Definition monoidSumSubinterval {E:monoid} {n} (x:stn n -> E) i j: i ≤ j -> j ≤ n -> E.
Proof.
  intros ? ? ? ? ? ij jn.
  exact (monoidSum (x ∘ enumerateSubinterval ij jn)).
Defined.

Definition Partition n          (* a partition of [stn n], as above *)
  := Σ m,
     Σ k: posetmorphism (stnposet (S m)) (stnposet (S n)),
          k (firstelement m) = firstelement n
            ×
          k (lastelement m) = lastelement n.

Definition monoidSumOfSums {E:monoid} {n} (x:stn n -> E) (P:Partition n) : E.
Proof.  
  intros.
  induction P as [m [[k o] [a b]]].
  simpl in a, b, k.
  apply (@monoidSum E m).
  intros [h hm].
  set (i := (h,,natlthtolths _ _ hm) : stn(S m)).
  set (j := (S h,,hm) : stn(S m)).
  apply (monoidSumSubinterval x (k i) (k j)).
  apply o.
  apply natlehnsn.
  apply natlthsntoleh.
  apply stnlt.
Defined.

Theorem associativityOfSums (E:monoid) n (x:stn n -> E) (P:Partition n) :
  monoidSum x = monoidSumOfSums x P.
Proof.
  intros.
Admitted.




