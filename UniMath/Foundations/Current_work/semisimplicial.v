Add Rec LoadPath "..".

Require Export Foundations.hlevel2.finitesets .

Unset Automatic Introduction.


Variable Delta : forall (i j : nat) , UU . (* This should be defined as the type of order preserving injections from {0,...i} to {0,...,j}. I introduced these axiomatically to save the time. *)

Variable gamma : forall ( i j k : nat ) ( s1 : Delta i j ) (s2 : Delta j k ) , Delta i k . (* This should be defined as compositions of injections. *)

Variable rl : forall ( j k : nat )( s : Delta j k )( a : stn (j+1) ) , stn (k + 1) . (* This should be defined as the obvious function from order preserving injections to all funcions. *) 

Definition Intrec1 ( n : nat ) := total2 ( fun 

SS : UU => total2 ( fun 

mapsfromsks : forall ( X : SS ) ( m : nat ) ( c : natleh m n )  (i : nat ) , UU  => 

(* restr: *) forall ( X : SS )  ( m : nat ) ( c : natleh m n )  (i j : nat ) ( s : Delta i j ) ( f : mapsfromsks X m c j ) , mapsfromsks X m c i ) ) .

Definition SS ( n : nat ) ( XX : Intrec1 n ) := pr1 XX .

Definition mapsfromsks ( n : nat ) ( XX : Intrec1 n ) := pr1 (pr2 XX ) . 

Definition restr ( n : nat ) ( XX : Intrec1 n ) :=  pr2 ( pr2 XX ) . 


(* We are now going to attempt to construct for each n : nat an object SEMISIPL n of Intrec1 n such that:

SS n ( SEMISIMPL n ) - is the type of semi-simplicial types of dimension n.

mapsfromsks n ( SEMISIMPL n ) X m c i - the type of functions sk_m Delta^i -> X from the m-th skeleton of Delta^i into X.

restr n ( SEMISIMPL n ) X m c i j s f - the composition of sk_m (s) where s : Delta^i -> Delta^j with f : sk_m Delta^k -> X.

We will do it by induction on n . To apply induction we need to construct for each n : nat a function Intrec1 n -> Intrec1 ( S n ) . We will be construcing it in a sequence of lemmas below, constructing first a function 

SSSn n : Intrec1 n -> UU 

then a function  

mapsfromsksSn n : forall IHn : Intrec1 n , ( forall ( X : SSSn n IHn ) ( m : nat ) ( c : natleh m ( S n ) )  (i : nat ) , UU ) 

and then restrSn n.


*)


Definition SSSn ( n : nat ) ( IHn : Intrec1 n ) : UU := total2 ( fun Xn : SS n IHn => forall f : mapsfromsks n IHn Xn n (isreflnatleh n) ( S n ) , UU ) .

Definition mapsfromsksSn ( n : nat ) ( IHn : Intrec1 n ) : forall ( X : SSSn n IHn ) ( m : nat ) ( c : natleh m ( S n ) ) ( i : nat ) , UU .
Proof.  intros . set ( cc := natlehchoice2 _ _ c ) . destruct cc .
simpl in h . change (pr1 (natleh m n ) ) in h . exact ( mapsfromsks n IHn ( pr1 X ) m h i ) .   
exact ( total2 ( fun f : mapsfromsks n IHn ( pr1 X ) n ( isreflnatleh n ) i => forall s : Delta ( S n ) i , (pr2 X) (restr n IHn (pr1 X) n (isreflnatleh n) ( S n ) i s f ) ) ). Defined.

Definition SEMISIMPL ( n : nat ) : Intrec1 n .
Proof . induction n as [ | n IHn ] .

(* n=0 *)  unfold Intrec1. split with UU . split with (fun X => fun i => fun c => fun j => ( stn (j+1) -> X )) . About rl .  exact ( fun X => fun i => fun c => fun j => fun k => fun a => fun f => fun phi => f (rl j k a phi) ). 

(* n => Sn *) set ( SSn := SS n IHn ) . set (mapsfromsksn := mapsfromsks n IHn ) . set (restrn := restr n IHn ) .

set ( SSSn := total2 ( fun Xn : SSn => forall f : mapsfromsksn Xn n (isreflnatleh n) ( S n ) , UU ) ) . split with SSSn . 

split with (fun X => fun i => fun c => fun j => mapsfromsksSn n IHn X i c j ) . 

intros X i c j k . unfold mapsfromsksSn . set ( cc := natlehchoice2 _ _ c ) . destruct cc  as [ isle | iseq ] . apply restrn . 

intros s f. destruct f as [fn ff]. simpl in restrn .  change (pr1 IHn) with SSn in restrn . change (pr1 (pr2 IHn)) with mapsfromsksn in restrn.  split with (restrn (pr1 X) n (isreflnatleh n) j k s fn ).  

intros . set ( s1 := gamma ( S n ) j k s0 s ) . set ( ffint := ff s1 ) . 

set ( fs1 := restrn (pr1 X) n (isreflnatleh n) (S n) k s1 fn ) . set (fs0s := restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s0 (restrn (pr1 X) n (isreflnatleh n) j k s fn)). 

simpl in fs1 . simpl in fs0s. 

assert ( e : paths (restrn (pr1 X) n (isreflnatleh n) (S n) k s1 fn) (restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s0 (restrn (pr1 X) n (isreflnatleh n) j k s fn )) ).

(* At this point the goal is to prove a certain equality which asserts "transitivity" or "naturality" of restriction maps. This equlity will be provable as a strict equality in HTS. The proof is by induction and if attempt it for "paths" we get into problems with the need to take into acount transports of increasing complexity with each new induction step. Here we use "admit" . *) admit . 

apply ( transportf ( fun z : _ => pr2 X z ) e ) .   apply ffint . Defined. 



Definition SEMISIMPL0 : Intrec1 0.
Proof . unfold Intrec1. split with UU . split with (fun X => fun i => fun c => fun j => ( stn (j+1) -> X )) .  exact ( fun X => fun i => fun c => fun j => fun k => fun a => fun f => fun phi => f (rl j k a phi ) ). Defined.

Definition SEMISIMPL1 : Intrec1 1.
Proof.  set ( IHn := SEMISIMPL0 ) . set ( SSn := SS 0 IHn ) . set (mapsfromsksn := mapsfromsks 0 IHn ) . set (restrn := restr 0 IHn ) .

set ( SSSn := total2 ( fun Xn : SSn => forall f : mapsfromsksn Xn 0 (isreflnatleh 0) ( S 0 ) , UU ) ) . split with SSSn . 
split with (fun X => fun i => fun c => fun j => mapsfromsksSn 0 IHn X i c j ) . 

intros X i c j k.  unfold mapsfromsksSn . set ( cc := natlehchoice2 _ _ c ) . destruct cc . apply restrn . 

intros. destruct f as [fn ff]. simpl in restrn .  change (pr1 IHn) with SSn in restrn . change (pr1 (pr2 IHn)) with mapsfromsksn in restrn.  split with (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn).  

intros . set ( s1 := gamma ( S 0 ) j k s0 s ) . set ( ffint := ff s1 ) . 

set ( fs1 := restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn) . set (fs0s := restr 0 IHn (pr1 X) 0 (isreflnatleh 0) (S 0) j s0 (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn )). 

simpl in fs1 . simpl in fs0s.

assert ( e : paths (restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn) (restr 0 IHn (pr1 X) 0 (isreflnatleh 0) (S 0) j s0 (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn ) ) ).

simpl.  unfold IHn. unfold restrn. unfold restr. unfold IHn .   unfold SEMISIMPL0.  simpl . apply funextfun . intro .  apply ( maponpaths fn ) . 

Check (restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn).








(* End of the file semisimplicial.v *)


