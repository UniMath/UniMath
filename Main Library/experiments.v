Add Rec LoadPath "../Proof of Extensionality/".

Require Export u12 u01 univ. 

Unset Automatic Introduction. 

(** Universe hierarchy *)

Definition UU0:=u0.UU.
Definition UU1:=u1.UU.
Definition UU2:=u2.UU.


(** * Experiments *)

(** ** Composable sequences of functions. *) 


Fixpoint seqplus (n:nat) : u2.total2 UU1 (fun T:UU1 => (T -> UU0)) := match n with 
O =>  u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) UU0 (fun X:_ => X) |
S m => u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) (u1.total2 (u2.pr21 _ _ (seqplus m)) (fun D:_ => u1.total2 UU0 (fun Y:_ => ((u2.pr22 _ _ (seqplus m) D) -> Y)))) (fun E:_ => u1.pr21 _ _ (u1.pr22 _ _ E))
end. 

Definition seq (n:nat): UU1 := u2.pr21 _ _ (seqplus n). (** The type of composable sequences of functions of length n. *)

Definition lasttype (n:nat) (s:seq n): UU0 := u2.pr22 _ _ (seqplus n) s. (** The last type in the sequence of functions s. *)



(** To univ.v *)

Definition d0:= initintervalpair 1 O (idpath _ _).

Definition d1:= initintervalpair 1 1 (idpath _ _).


(** ** Simplicial objects without degeneracies.


We define inductively, for any n:nat, the following objects:

1. dfsslen n : UU1.  - the type of degeneracy free simplicial objects of dimension less or equal to n in UU0.

2. homdfsslen n: forall X Y : dfsslen n, UU0.  - the type of morphisms from X to Y.

3. compdfsslen n: forall X Y Z: dfsslen n, homdfsslen n X Y -> homdfsslen n Y Z -> homdfsslen n X Z. - the composition opf morphisms which will be strictly associative. 

4. dfskndeltam n : forall m:nat, dfsslen n. - the degeneracy free part of the n-th skeleton of the simplex of dimension m. The morphisms from it to a simplicial object X in the category of degeneracy free objects are the same as morphisms from the complete n-skeleton of m-dimensional simplex to X in the category of simplicial sets. 

For (n =) O we define these ingredients as follows:

1. dfsslen O := UU0.

2. homdfsslen O := fun X Y : dfsslen O => (X -> Y).

3. compdfsslen O := fun X Y Z : dfsslen O => fun  f: X -> Y => fun g Y -> Z =>  fun x:X => (g (f x)).

4. dfskndeltam O := fun m:nat => initinterval m.




For S n  as follows:

1. dfsslen (S n) := u1.total2 (dfsslen n) (fun sknX:_ => (homdfsslen n (dfskndeltam n (S n)) sknX) -> UU0).  In words, a d.f. simplicial object X of dimension (S n) is a pair which consists of a d.f. simplicial object sknX of dimension n together with a mapping which assigns to each morphism from the boundary of n-dimensional simplex to sknX the type of all n-simplexes of X with this boundary. 

2. homdfsslen (S n) (tpair _ _ sknX phiX) (tpair _ _ sknY phiY) := total2 (homdfsslen n sknX sknY) (fun sknff:_ => forall gamma: homdfsslen n (dfskndeltam n (S n)) sknX, phiX gamma -> phiY (compdfsslen n _ sknX sknY gamma sknff)). 

3. compdfsslen (S n) (tpair _ _ sknX phiX) (tpair _ _ sknY phiY) (tpair _ _ sknZ phiZ) (tpair _ _ sknff fsn) (tpair _ _ sknfg gsn) := tpair _ _ (compdfsslen n sknff sknfg) (fun gamma: homdfsslen n (dfskndeltam n (S n)) sknX => (fun xn: phiX gamma => gsn (compdfsslen n _ sknX sknY gamma sknff) (fsn gamma xn))).  


4. dfskndeltam (S n) := fun m:nat => tpair _ _ (dfskndeltam n m) (fun gamma : homdfsslen n (dfskndeltam n (S n)) (dfskndeltam n m) => 

if n >= m then empty
if n < m and n > O then unit
if n < m and n = O then
  if gamma O < gamma 1 then unit
  if gamma O >= gamma 1 then empty.  Note, this requires us to define notations for the points of initinterval and <= and > on initinterval. 


 
match leb m n with 
true => empty |
false =>
match n with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S k => unit 
end
end.
 
*)

(*
Record test0 := ttriple { c1: nat*nat ; c2: nat*nat ; c3: match c1 with (x, y) => match c2 with (z, t) => nat end end} .
Fixpoint test (a: test0) := match a with ttriple (a1, a2) (b1, b2) x =>  S x end.  
*)

Fixpoint t1 (n:nat) : Type :=
match n with
O => (prod unit unit) |
S k => unit
end.

Fixpoint t2 (n:nat) : t1 n  :=
match n with 
O => (tt, tt) |
S k => tt
end.





Record dfssrecord : UU2 := { c1 : UU1 ; c2: forall X Y: c1, UU0 ; c3: forall X Y Z :c1, (c2 X Y) -> (c2 Y Z) -> (c2 X Z) ; c4: forall m:nat, c1 }.


Definition dfssle (n:nat) : dfssrecord. 
Proof. intro. induction n. apply ({| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c4:= fun m:nat => initinterval m |}).

set (cc1 := u1.total2 IHn.(c1) (fun sknX:_ => (IHn.(c2) (IHn.(c4) (S n)) sknX) -> UU0)).

set (cc1pair:= u1.tpair IHn.(c1) (fun sknX:_ => (IHn.(c2) (IHn.(c4) (S n)) sknX) -> UU0)).

set (cc2 := fun X: cc1  => match X with u1.tpair sknX phiX  => fun Y: cc1 =>
 match Y with u1.tpair sknY phiY =>
 total2 ((IHn).(c2) sknX sknY) (fun sknff:_ => forall gamma: (IHn).(c2) ((IHn).(c4) (S n)) sknX, phiX gamma -> phiY ((IHn).(c3) _ sknX sknY gamma sknff)) end end ).


assert (cc3: forall  X Y Z :cc1, (cc2 X Y) -> (cc2 Y Z) -> (cc2 X Z) ).

intros. destruct X.  rename t into sknX. rename x into phiX. destruct Y. rename t into sknY. rename x into phiY. destruct Z.  rename t into sknZ. rename x into phiZ. destruct X0.  rename t into sknff. rename x into fsn. destruct X1.  rename t into sknfg. rename x into gsn. simpl. split with ((IHn).(c3) _ _ _ sknff sknfg). intro. intro. rename X into xn. simpl. apply  (gsn _ (fsn gamma xn)).


set (cc3 := fun X: cc1 => match X with u1.tpair sknX phiX => fun Y: cc1 =>  match Y with u1.tpair sknY phiY => fun Z: cc1 =>  match Z with u1.tpair sknZ phiZ => fun f: cc2 (cc1pair sknX phiX) (cc1pair sknY phiY) => match f with tpair sknff fsn => fun g: cc2 Y Z  =>  match g with tpair sknfg gsn =>
   tpair  ((IHn).(c2) sknX sknZ) (fun sknfh: _ => forall gamma: (IHn).(c2) ((IHn).(c4) (S n)) sknX, phiX gamma -> phiZ ((IHn).(c3) _ sknX sknZ gamma sknfh)) ( (IHn).(c3) sknX sknY sknZ sknff sknfg) (fun gamma: (IHn).(c2) ((IHn).(c4) (S n)) sknX => (fun xn: phiX gamma => gsn ((IHn).(c3) _ sknX sknY gamma sknff) (fsn gamma xn))) end end end end end).  
  
c4:= fun m:nat => tpair _ _ ((IHn).(c4) m) (fun gamma : _ ((IHn).(c4) (S k)) ((IHn).(c4) m) => 
match leb m k with 
true => empty |
false =>
match k with     
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.





(* Fixpoint dfssle (n:nat) : dfssrecord := match n with

O => {| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c4:= fun m:nat => initinterval m |} |

S k  => {| 

c1 := u1.total2 (dfssle k).(c1) (fun sknX:_ => ((dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX) -> UU0) ; 

c2 := fun X:_  => match X with u1.tpair sknX phiX  => fun Y: _ =>
 match Y with u1.tpair sknY phiY =>
 total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) end end ; 

c3 := fun X: _ => match X with u1.tpair sknX phiX => fun Y: _ =>  match Y with u1.tpair sknY phiY => fun Z: _ =>  match Z with u1.tpair sknZ phiZ => fun f: total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) => match f with tpair sknff fsn => fun g: _  =>  match g with tpair sknfg gsn =>
   tpair _ _ ( _  sknff sknfg) (fun gamma: (dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX => (fun xn: phiX gamma => gsn ((dfssle k).(c3) _ sknX sknY gamma sknff) (fsn gamma xn))) end end end end end; 
  
c4:= fun m:nat => tpair _ _ ((dfssle k).(c4) m) (fun gamma : _ ((dfssle k).(c4) (S k)) ((dfssle k).(c4) m) => 
match leb m k with 
true => empty |
false =>
match k with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.

*)





(* Bacck-up copy:

Fixpoint dfssle (n:nat) : dfssrecord := match n with

O => {| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c4:= fun m:nat => initinterval m |} |

S k  => {| 

c1 := u1.total2 (dfssle k).(c1) (fun sknX:_ => ((dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX) -> UU0) ; 

c2 := fun X:_  => fun Y: _ =>
match X with u1.tpair sknX phiX  => match Y with u1.tpair sknY phiY =>
 total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) end end ; 

c3 := fun X: _ => fun Y: _ => fun Z: _ => fun f: _ => fun g: _  =>
match X with u1.tpair sknX phiX  => match Y with u1.tpair sknY phiY =>  match Z with u1.tpair sknZ phiZ => match f with tpair sknff fsn => match g with tpair sknfg gsn => tpair _ _ ( _  sknff sknfg) (fun gamma: (dfssle k).(c2) ((dfssle k).(c4) (S k)) sknX => (fun xn: phiX gamma => gsn ((dfssle k).(c3) _ sknX sknY gamma sknff) (fsn gamma xn))) end end end end end; 
  
c4:= fun m:nat => tpair _ _ ((dfssle k).(c4) m) (fun gamma : _ ((dfssle k).(c4) (S k)) ((dfssle k).(c4) m) => 
match leb m k with 
true => empty |
false =>
match k with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.

 *)










 


(* End of file experiments.v *)