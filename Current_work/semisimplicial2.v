Add Rec LoadPath "../Foundations/Generalities".
Add Rec LoadPath "../Foundations/hlevel1".
Add Rec LoadPath "../Foundations/hlevel2".

Require Export "../Foundations/hlevel2/finitesets" .

Unset Automatic Introduction.

Print identity_rect.

Variable Delta : forall (i j : nat) , UU . (* This should be defined as the type of order preserving injections from {0,...i} to {0,...,j}. I introduced these axiomatically to save the time. *)

Variable gamma : forall ( i j k : nat ) ( s1 : Delta i j ) (s2 : Delta j k ) , Delta i k . (* This should be defined as compositions of injections. *)

Variable rl : forall ( j k : nat )( s : Delta j k )( a : stn (j+1) ) , stn (k + 1) . (* This should be defined as the obvious function from order preserving injections to all funcions. *) 

Definition Intrec1 ( n : nat ) := total2 ( fun 

SS : UU => total2 ( fun 

mapsfromsks : forall ( X : SS ) ( m : nat ) ( c : natleh m n )  (i : nat ) , UU  => total2 ( fun 

restr: forall ( X : SS )  ( m : nat ) ( c : natleh m n )  (i j : nat ) ( s : Delta i j ) ( f : mapsfromsks X m c j ) , mapsfromsks X m c i =>

(* pbn : *) forall ( X : SS )  ( m : nat ) ( c : natleh m n ) ( i j k : nat ) ( s1 : Delta i j ) ( s2 : Delta j k ) ( f : mapsfromsks X m c k ) , paths  ( restr X m c i k ( gamma i j k s1 s2 ) f ) ( restr X m c i j s1 ( restr X m c j k s2 f ) ) ) ) ) .    

Definition SS ( n : nat ) ( XX : Intrec1 n ) := pr1 XX .

Definition mapsfromsks ( n : nat ) ( XX : Intrec1 n ) := pr1 (pr2 XX ) . 

Definition restr ( n : nat ) ( XX : Intrec1 n ) := pr1 ( pr2 ( pr2 XX ) ). 

Definition pbn ( n : nat ) ( XX : Intrec1 n ) := pr2 ( pr2 ( pr2 XX ) ) . 

(* We are now going to construct for each n : nat an object SEMISIPL n of Intrec1 n such that:

SS n ( SEMISIMPL n ) - is the type of semi-simplicial types of dimension n.

mapsfromsks n ( SEMISIMPL n ) X m c i - the type of functions sk_m Delta^i -> X from the m-th skeleton of Delta^i into X.

restr n ( SEMISIMPL n ) X m c i j s f - the composition of sk_m (s) where s : Delta^i -> Delta^j with f : sk_m Delta^k -> X.

pbn n ( SEMISIMPL n ) X m c i j k s1 s2 f - the "associativity" of the form ( ( f sk_m(s2) ) sk_m(s1) ) = f ( sk_m ( s2 s1 ) ) 

We will do it by induction on n . To apply induction we need to construct for each n : nat a function Intrec1 n -> Intrec1 ( S n ) . We will be construcing it in a sequence of lemmas below, constructing first a function 

SSSn n : Intrec1 n -> UU 

then a function  

mapsfromsksSn n : forall IHn : Intrec1 n , ( forall ( X : SSSn n IHn ) ( m : nat ) ( c : natleh m ( S n ) )  (i : nat ) , UU ) 

and then restrSn n and pbnSn n . 


*)


Definition SSSn ( n : nat ) ( IHn : Intrec1 n ) : UU := total2 ( fun Xn : SS n IHn => forall f : mapsfromsks n IHn Xn n (isreflnatleh n) ( S n ) , UU ) .

Definition mapsfromsksSn ( n : nat ) ( IHn : Intrec1 n ) : forall ( X : SSSn n IHn ) ( m : nat ) ( c : natleh m ( S n ) ) ( i : nat ) , UU .
Proof.  intros . set ( cc := natlehchoice2 _ _ c ) . destruct cc .
simpl in h . change (pr1 (natleh m n ) ) in h . exact ( mapsfromsks n IHn ( pr1 X ) m h i ) .   
exact ( total2 ( fun f : mapsfromsks n IHn ( pr1 X ) n ( isreflnatleh n ) i => forall s : Delta ( S n ) i , (pr2 X) (restr n IHn (pr1 X) n (isreflnatleh n) ( S n ) i s f ) ) ). Defined.

Definition restrSn ( n : nat ) ( IHn : Intrec1 n ) : forall ( X : SSSn n IHn ) ( m : nat ) ( c : natleh m ( S n ) )  (i j : nat ) ( s : Delta i j ) ( f : mapsfromsksSn n IHn X m c j ) , mapsfromsksSn n IHn X m c i.
Proof . intros n IHn.  

intros X m c i j. unfold mapsfromsksSn . set ( cc := natlehchoice2 _ _ c ) . destruct cc . apply ( restr n IHn ). 

intros. destruct f as [fn ff].   split with (restr n IHn (pr1 X) n (isreflnatleh n) i j s fn ).  

intros . set ( s1 := gamma ( S n ) i j s0 s ) . set ( ffint := ff s1 ) . 

set ( fs1 := restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s1 fn ) . set (fs0s := restr n IHn (pr1 X) n (isreflnatleh n) (S n) i s0 (restr n IHn (pr1 X) n (isreflnatleh n) i j s fn)). 

simpl in fs1 . simpl in fs0s.

assert ( e : paths (restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s1 fn) (restr n IHn (pr1 X) n (isreflnatleh n) (S n) i s0 (restr n IHn (pr1 X) n (isreflnatleh n) i j s fn )) ). unfold s1. apply ( pbn n IHn ) . 

change (restr n IHn (pr1 X) n (isreflnatleh n) (S n) i s0
           (restr n IHn (pr1 X) n (isreflnatleh n) i j s fn)) with fs0s in e . apply (transportf _ e ffint ) . Defined. 

(* 

Definition pbnSn ( n : nat ) ( IHn : Intrec1 n ) : forall ( X : SSSn n IHn )  ( m : nat ) ( c : natleh m ( S n ) ) ( i j k : nat ) ( s1 : Delta i j ) ( s2 : Delta j k ) ( f : mapsfromsksSn  n IHn X m c k ) , paths  ( restrSn n IHn X m c i k ( gamma i j k s1 s2 ) f ) ( restrSn n IHn X m c i j s1 ( restrSn n IHn X m c j k s2 f ) ) .
Proof .  intros n IHn X m c i j k s1 s2 . unfold mapsfromsksSn . unfold restrSn. set ( cc := natlehchoice2 _ _ c ) . destruct cc .

apply ( pbn n IHn ) . 

intro f . destruct f as [ f sf ] .  

assert ( inte1 : paths (tpair _ (restr n IHn (pr1 X) n (isreflnatleh n) i k (gamma i j k s1 s2) f) ( fun s0 : Delta (S n) i =>
            transportf (pr2 X)
              (pbn n IHn (pr1 X) n (isreflnatleh n) 
                 (S n) i k s0 (gamma i j k s1 s2) f)
              (sf (gamma (S n) i k s0 (gamma i j k s1 s2))) ) ) 
                        (tpair _ (restr n IHn (pr1 X) n (isreflnatleh n) i j s1
              (restr n IHn (pr1 X) n (isreflnatleh n) j k s2 f)) ( fun s0 : Delta ( S n ) i => 
transportf (pr2 X)
              (pbn n IHn (pr1 X) n (isreflnatleh n) 
                 (S n) i k s0 (gamma i j k s1 s2) f)
transportf (pr2 X)
              (pbn n IHn (pr1 X) n (isreflnatleh n) 
                 (S n) i k s0 (gamma i j k s1 s2) f)
              (sf (gamma (S n) i k s0 (gamma i j k s1 s2))) 


set ( P := fun g : mapsfromsks n IHn ( pr1 X ) n ( isreflnatleh n ) i =>  forall s0 : Delta ( S n ) i , pr2 X
         ( restr n IHn (pr1 X) n (isreflnatleh n) (S n) i s0 g) ) . 

(restr n IHn (pr1 X) n (isreflnatleh n) i k
               (gamma i j k s1 s2) f)


set ( e := pbn n IHn ( pr1 X ) n (isreflnatleh n) i j k s1 s2 f  : paths ( restr n IHn (pr1 X) n (isreflnatleh n) i k (gamma i j k s1 s2) f ) ( restr n IHn (pr1 X) n (isreflnatleh n) i j s1
              (restr n IHn (pr1 X) n (isreflnatleh n) j k s2 f) ) ) .  rewrite e .    

*)


Definition SEMISIMPL ( n : nat ) : Intrec1 n .
Proof . induction n .

(* n=0 *)  unfold Intrec1. split with UU . split with (fun X => fun i => fun c => fun j => ( stn (j+1) -> X )) .  exact ( fun X => fun i => fun c => fun j => fun k => fun f => fun phi => fun a => f (rl j k phi a ) ). 

(* n => Sn *) set ( SSn := SS n IHn ) . set (mapsfromsksn := mapsfromsks n IHn ) . set (restrn := restr n IHn ) .

set ( SSSn := total2 ( fun Xn : SSn => forall f : mapsfromsksn Xn n (isreflnatleh n) ( S n ) , UU ) ) . split with SSSn . 

split with (fun X => fun i => fun c => fun j => mapsfromsksSn n IHn X i c j ) . 

intro. intro. intro. intro. intro.   unfold mapsfromsksSn . set ( cc := natlehchoice2 _ _ c ) . destruct cc . apply restrn . 

intros. destruct f as [fn ff]. simpl in restrn .  change (pr1 IHn) with SSn in restrn . change (pr1 (pr2 IHn)) with mapsfromsksn in restrn.  split with (restrn (pr1 X) n (isreflnatleh n) j k s fn ).  

intros . set ( s1 := gamma ( S n ) j k s0 s ) . set ( ffint := ff s1 ) . 

set ( fs1 := restrn (pr1 X) n (isreflnatleh n) (S n) k s1 fn ) . set (fs0s := restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s0 (restrn (pr1 X) n (isreflnatleh n) j k s fn)). 

simpl in fs1 . simpl in fs0s.

assert ( e : paths (restrn (pr1 X) n (isreflnatleh n) (S n) k s1 fn) (restr n IHn (pr1 X) n (isreflnatleh n) (S n) j s0 (restrn (pr1 X) n (isreflnatleh n) j k s fn )) ).

(* At this point the remaining goal is to prove a certain equality. This equlity will hold definitionally in TS (if I am not mistaken). *)

Check (restrn (pr1 X) n (isreflnatleh n) (S n) k s1 fn).

Admitted.


Definition SEMISIMPL0 : Intrec1 0.
Proof . unfold Intrec1. split with UU . split with (fun X => fun i => fun c => fun j => ( stn (j+1) -> X )) .  exact ( fun X => fun i => fun c => fun j => fun k => fun f => fun phi => fun a => f (rl j k phi a ) ). Defined.

Definition SEMISIMPL1 : Intrec1 1.
Proof.  set ( IHn := SEMISIMPL0 ) . set ( SSn := SS 0 IHn ) . set (mapsfromsksn := mapsfromsks 0 IHn ) . set (restrn := restr 0 IHn ) .

set ( SSSn := total2 ( fun Xn : SSn => forall f : mapsfromsksn Xn 0 (isreflnatleh 0) ( S 0 ) , UU ) ) . split with SSSn . 
split with (fun X => fun i => fun c => fun j => mapsfromsksSn 0 IHn X i c j ) . 

intro. intro. intro. intro. intro.   unfold mapsfromsksSn . set ( cc := natlehchoice2 _ _ c ) . destruct cc . apply restrn . 

intros. destruct f as [fn ff]. simpl in restrn .  change (pr1 IHn) with SSn in restrn . change (pr1 (pr2 IHn)) with mapsfromsksn in restrn.  split with (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn).  

intros . set ( s1 := gamma ( S 0 ) j k s0 s ) . set ( ffint := ff s1 ) . 

set ( fs1 := restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn) . set (fs0s := restr 0 IHn (pr1 X) 0 (isreflnatleh 0) (S 0) j s0 (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn )). 

simpl in fs1 . simpl in fs0s.

assert ( e : paths (restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn) (restr 0 IHn (pr1 X) 0 (isreflnatleh 0) (S 0) j s0 (restrn (pr1 X) 0 (isreflnatleh 0) j k s fn ) ) ).

simpl.  unfold IHn. unfold restrn. unfold restr. unfold IHn .   unfold SEMISIMPL0.  simpl . apply funextfun . intro .  apply ( maponpaths fn ) . 

Check (restrn (pr1 X) 0 (isreflnatleh 0) (S 0) k s1 fn).








(* End of the file semisimplicial.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

