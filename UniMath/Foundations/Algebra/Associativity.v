Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

(* move upstream *)
    Local Notation "x ,, y" := (tpair _ x y) (at level 60, right associativity).
    Local Notation "g ∘ f" := (funcomp f g) (at level 50).
(* *)

(** * Associativity theorem, as in Bourbaki, Algebra, Theorem 1, page 4. *)

(** define x0 + x1 + ... + xn as x0 + (x1 + (...( + xn)...)). *)
Definition monoidSum (E:monoid) n (x:stn n -> E): E.
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
   the least number not in the any of the first i-1 subintervals.  Thus consecutive
   subintervals are defined as half open intervals by consecutive pairs of neighbors
   in k.  Observe that the first number is always 0 and the last number is always n.

   Examples:
       m=1     k=(0,n)      [0,n)
       m=2     k=(0,i,n)    [0,i)  [i,n)
       m=3     k=(0,i,j,n)  [0,i)  [i,j)    [j,n)
   *)

Definition enumerateSubinterval n i j: i ≤ j -> j ≤ n -> stn (j-i) -> stn n.
Proof.
  intros ? ? ? ij jn [k kji].
  exists (k+i).
  refine (natlthlehtrans _ _ _ _ jn).
  assert (u := minusplusnmm _ _ ij).
  assert (t := natlthandplusr _ _ i kji).
  induction (!u).
  exact t.
Defined.

(*

Definition monoidSumOfSums (E:monoid) m n (f:posetmorphism (stnposet m) (stnposet n)): E.
Proof.
  intros.
  

*)










