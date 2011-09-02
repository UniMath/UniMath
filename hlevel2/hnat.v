(** * Natural numbers and their properties. Vladimir Voevodsky . Apr. - Sep. 2011  

This file contains the formulations and proofs of general properties of natural numbers from the univalent perspecive. *)






(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Export algebra1 . 

(** To up-stream files  *)




(** ** Equality on [ nat ] *)


(** *** Basic properties of [ paths ] on [ nat ] and the proofs of [ isdeceq ] and [ isaset ] for [ nat ] .  *) 

Theorem nopathsOtoSx: forall x:nat, paths O (S x) -> empty.
Proof. intro. 
set (f:= fun n:nat => match n with 
O => true|
S m => false
end). 

apply ( negf ( @maponpaths _ _ f 0 ( S x ) ) nopathstruetofalse ) . Defined. 

Corollary nopathsSxtoO ( x : nat ) : paths (S x) O -> empty.
Proof. intros x X. apply (nopathsOtoSx x (pathsinv0  X)). Defined. 

Lemma noeqinjS ( x x':nat) :  (paths x x' -> empty) -> (paths (S x) (S x') -> empty).
Proof. set (f:= fun n:nat => match n with 
O => O|
S m => m
end). 

intro. intro. intro X. apply ( negf ( @maponpaths _ _ f ( S x ) ( S x' ) ) X ) .  Defined. 
 

Theorem isdeceqnat: isdeceq nat.
Proof. unfold isdeceq.  intro x . induction x as [ | x IHx ] . intro x' .  destruct x'. apply (ii1  (idpath O)). apply (ii2  (nopathsOtoSx x')). intro x' .  destruct x'.  apply (ii2  (nopathsSxtoO x)). destruct (IHx x') as [ p | e ].   apply (ii1  (maponpaths S  p)).  apply (ii2  (noeqinjS  _ _ e)). Defined. 

Theorem isisolatedn ( n : nat ) : isisolated _ n .
Proof. intro. unfold isisolated . intro x' . apply isdeceqnat . Defined. 

Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdeceq _ isdeceqnat). Defined. 

Definition natset : hSet := hSetpair _ isasetnat . 
Canonical Structure natset . 


Definition  eqnat ( a b : nat ) : hProp := hProppair _ ( isasetnat a b ) . 



(** *** Semi-boolean equality or [eqh] on [ nat ] . *)

Fixpoint eqbnat (n m : nat ) : bool :=
match n,m with
 | S n , S m => eqbnat n m
 | O , O => true
 | O , S m => false
 | S m , 0 => false
end.


Definition eqh ( n m : nat ) : hProp := hProppair ( paths ( eqbnat n m ) true ) ( isasetbool _ _ ) .

Lemma isdecpropeqh ( n m : nat ) : isdecprop ( eqh n m ) .
Proof. intros . apply ( isdecproppaths isdeceqbool ( eqbnat n m ) true  ) .  Defined . 


Lemma isrefleqh ( n : nat ) : eqh n n .
Proof. intro . induction n . simpl . apply idpath . simpl . assumption .  Defined . 


Definition eqhtopaths ( n m : nat ) : eqh n m -> paths n m .
Proof . intro n. induction n as [ | n IHn ] . intro m . destruct m as [ | m ] . intro . apply idpath .    intro X . simpl in X . destruct ( nopathsfalsetotrue X ) . intro m .  destruct m as [ | m ] .  intro X . simpl in X .  destruct ( nopathsfalsetotrue X ) . intro X .  set ( a := IHn m X ) .  apply ( maponpaths S a ) . Defined . 

Definition pathstoeqh ( n m : nat ) : paths n m -> eqh n m .
Proof. intros n m e . destruct e . simpl . apply isrefleqh . Defined.

Definition weqeqhtopaths ( n m : nat ) : weq ( eqh n m ) ( paths n m ) .
Proof. intros . assert ( is1 : isaprop ( eqh n m ) ) . apply ( pr22 ( eqh n m ) ) . assert ( is2 : isaprop ( paths n m ) ) . set ( a:= isasetnat n m ) .   simpl in a . assumption . 
split with ( eqhtopaths _ _ ) . apply ( isweqimplimpl ( eqhtopaths _ _ ) ( pathstoeqh _ _ ) is1 is2 ) . Defined. 

Definition neqh ( n m : nat ) : hProp :=  hProppair ( paths ( eqbnat n m ) false ) ( isasetbool _ _ ) .

Lemma neqhtonegpaths ( n m : nat ) : neqh n m -> neg ( paths n m ) .
Proof. intros n m ne . intro e .  destruct e . destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 ( isrefleqh n ) ) ne ) ) .  Defined .


(** *** [ S : nat -> nat ] is a decidable inclusion . *)

Lemma invmaponpathsS ( n m : nat ) : paths ( S n ) ( S m ) -> paths n m .
Proof. intros n m e . apply ( eqhtopaths n m ( pathstoeqh ( S n ) ( S m )  e ) ) . Defined.     

Theorem isinclS : isincl S .
Proof. apply ( isinclbetweensets S isasetnat isasetnat invmaponpathsS ) .  Defined .

Theorem isdecinclS : isdecincl S .
Proof. intro n . apply isdecpropif . apply ( isinclS n ) .  destruct n as [ | n ] .  assert ( nh : neg ( hfiber S 0 ) ) .  intro hf .  destruct hf as [ m e ] .  apply ( nopathsSxtoO _ e ) .  apply ( ii2 nh ) .  apply ( ii1 ( hfiberpair _ n ( idpath _ ) ) ) .  Defined . 






(** ** Inequalities on [ nat ] . *)


(** *** Boolean "less or equal" or [ leb ] on [ nat ] . *)

Fixpoint leb (n m : nat) : bool :=
match n,m with
 | S n , S m => leb n m
 | O, _ => true
 | _, _ => false
end.



(** *** Semi-boolean "less or equal" or [ leh ] and "greater" or [ gth ] on [ nat ] . 

 Note that due to its definition [ leh ] automatically has the property that [ leh n m <-> leh ( S n ) ( S m ) ] .  *)



Definition leh ( n m : nat ) : hProp := hProppair ( paths ( leb n m ) true ) ( isasetbool _ _ ) . 

Lemma isdecpropleh ( n m : nat ) : isdecprop ( leh n m ) .
Proof. intros . apply ( isdecproppaths isdeceqbool ( leb n m ) true  ) .  Defined . 

Lemma lehtrans ( n m k : nat ) : leh n m -> leh m k -> leh n k .
Proof. intro. induction n as [ | n IHn ] .  intros m k X X0 .  simpl.  apply idpath.
intros m k X X0. destruct m as [ | m ] .  apply (fromempty (nopathsfalsetotrue X)). destruct k as [ | k ] .  apply (fromempty (nopathsfalsetotrue X0)). simpl. simpl in X . simpl in X0 . apply (IHn m k).   assumption . assumption . Defined. 
Hint Resolve lehtrans : natarith .  

Lemma lehrefl (n:nat): leh n n .
Proof. intros. induction n as [ | n IHn ] . split .   simpl. assumption.  Defined. 
Hint Resolve lehrefl : natarith .

Definition lehpo : po nat := popair leh ( dirprodpair lehtrans lehrefl ). 



(* Lemma lehasymm ( n m : nat ) : leh n m -> leh m n -> paths n m .
Proof. intro . induction n as [ | n IHn ] . intro . induction *)


Lemma lehnsn (n:nat): leh n (S n) .
Proof. intro. induction n as [ | n IHn ] . apply ( idpath true ) .  assumption.  Defined. 
Hint Resolve lehnsn : natarith . 

Lemma neglehsnn (n:nat): neg ( leh ( S n ) n).
Proof. intro. induction n as [ | n IHn ] .  simpl.  intro X. apply (nopathsfalsetotrue X). assumption.  Defined.

Lemma lehimpllehs ( n m : nat ) : leh n m -> leh n ( S m ) .
Proof. intros n m is . apply ( lehtrans n m ( S m ) is ( lehnsn m ) ) . Defined . 

Lemma lehsimplleh ( n m : nat ) : leh ( S n ) m -> leh n m .
Proof.  intros n m is . apply ( lehtrans ( S n ) m ( S m ) is ( lehnsn m ) ) . Defined . 

Lemma leh0implis0 (n:nat) : leh n 0 -> paths n 0.
Proof.  intro. destruct n as [ | n ] . intro.   apply idpath.  intro X. apply (fromempty (nopathsfalsetotrue X)). Defined. 

Lemma neglehsn0 ( n : nat ) : neg ( leh ( S n ) 0 ) .
Proof. intros n H . set ( int := leh0implis0 ( S n ) H ) .  simpl in H .  apply ( nopathsfalsetotrue H ) . Defined . 

Lemma lehchoice ( n m : nat ) : leh n m -> coprod ( leh ( S n ) m ) ( paths n m ) .
Proof . intros n m . revert n . induction m as [ | m IHm ] . intros n l . apply ( ii2 ( leh0implis0 _ l ) ) . intros n l . destruct n as [ | n ] .  apply ( ii1 ( idpath true ) ) .  destruct ( IHm n l )  as [ l' | e ] .  apply ( ii1 l' ) . apply ( ii2 ( maponpaths S e ) ) . Defined . 


(** *** Semi-boolean "greater" or [ gth ] on [ nat ] and its properties . 

Note that due to its definition [ gth ] automatically has the property that [ gth n m <-> gth ( S n ) ( S m ) ] . *) 


Definition gth ( n m : nat ) : hProp := hProppair ( paths ( leb n m ) false ) ( isasetbool _ _ ) . 


Lemma isdecpropgth ( n m : nat ) : isdecprop ( gth n m ) .
Proof. intros . apply ( isdecproppaths isdeceqbool ( leb n m ) false  ) .  Defined .

Lemma neggthnn ( n : nat ) : neg ( gth n n ) .
Proof. intros n is . induction n as [ | n IHn ] .  apply ( nopathstruetofalse is ) . apply ( IHn is ) .  Defined .   

Lemma gthtrans ( n m k : nat ) : gth n m -> gth m k -> gth n k .
Proof. intro. induction n as [ | n IHn ] .  intros m k X X0. apply (fromempty (nopathstruetofalse X)).  intros m k X X0 .  destruct m as [ | m ] .  apply (fromempty (nopathstruetofalse X0 )).  destruct k as [ | k ] . apply ( idpath false ) . apply (IHn m k) . assumption . assumption . Defined. 

Lemma gthasymm ( n m : nat ) : gth n m -> gth m n -> empty .
Proof. intros n m is is' . apply ( neggthnn n ( gthtrans _ _ _ is is' ) ) . Defined .    

Lemma gthsnn ( n : nat ) : gth ( S n ) n .
Proof . intro n . induction n as [ | n IHn ] . apply ( idpath false ) . assumption . Defined .

Lemma gthimplgths ( n m : nat ) : gth n m -> gth ( S n ) m .
Proof. intros n m is . apply ( gthtrans ( S n ) n m ( gthsnn n ) is ) . Defined . 

Lemma neggth0n ( n : nat ) : neg ( gth 0 n ) .
Proof. intros n is . apply ( nopathstruetofalse is ) . Defined . 

Lemma gthchoice ( n m : nat ) : gth n m -> coprod ( gth n ( S m ) ) ( paths n ( S m ) ) .
Proof. intro n . induction n as [ | n IHn ] . intros m g .   destruct ( neggth0n _ g ) .  intro m .   destruct m as [ | m ] .  intro .  destruct n as [ | n ] . apply ( ii2 ( idpath _ ) ) .  apply ( ii1 ( idpath false ) ) .  intro g .  destruct ( IHn m g ) as [ g' | e ] . apply ( ii1 g' ) .    apply ( ii2 ( maponpaths S e ) ) .  Defined . 


(** *** Semi-boolean " greater or equal " or [ geh ] and " less " or [ lth] *)

Definition geh ( n m : nat ) := leh m n .

Definition lth ( n m : nat ) := gth m n .

Lemma gehtrans ( n m k : nat ) : geh n m -> geh m k -> geh n k .
Proof . intros n m k g1 g2 . apply ( lehtrans _ _ _ g2 g1 ) . Defined . 

Definition gehpo : po nat := popair geh ( dirprodpair gehtrans lehrefl ). 

Lemma lthtrans ( n m k  : nat ) : lth n m -> lth m k -> lth n k .
Proof. intros n m k l1 l2 . apply ( gthtrans _ _ _ l2 l1 ) . Defined . 

Lemma lth1implis0 ( n : nat ) : lth n 1 ->  paths n 0 .
Proof. intros n l . destruct n as [ | n ] . apply idpath . destruct ( neggth0n n l ) .  Defined .   


(** *** Lemmas including a combination of [ leh ] , [ gth ] , [ geh ] and [ lth ] . *)

Lemma neglehgth ( n m : nat ) : leh n m -> gth n m -> empty .
Proof. intros n m is is' . apply ( nopathsfalsetotrue ( pathscomp0 ( pathsinv0 is' ) is ) ) .  Defined .   

Lemma gthimplgeh ( n m : nat ) : gth n m -> geh n m .
Proof. intros n m g . simpl .  destruct ( boolchoice ( leb m n ) ) . assumption  .  destruct ( gthasymm _ _ g i ) . Defined .

Lemma gehsnimplgth ( n m : nat ) : geh n ( S m ) -> gth n m .
Proof. intro n . induction n as [ | n IHn ] .  intros m X . destruct ( neglehsn0 _ X ) .  intros m X . destruct m as [ | m ] . apply ( idpath false ) . apply ( IHn m X ) .  Defined . 

Lemma gthimplgehsn ( n m : nat ) : gth n m -> geh n ( S m ) .
Proof. intro n . induction n as [ | n IHn ] .  intros m X .  destruct ( neggth0n _ X ) . intros m X . destruct m as [ | m ] .  apply ( idpath true ) .  apply ( IHn m X ) .  Defined . 

Lemma lehsnimpllth ( n m : nat ) : leh ( S n ) m -> lth n m .
Proof.  intros n m X . apply ( gehsnimplgth m n X ) . Defined . 

Lemma lthimpllehsn ( n m : nat ) : lth n m -> leh ( S n ) m .
Proof. intros n m X . apply ( gthimplgehsn m n X ) . Defined . 

Lemma gthgehtrans ( n m k : nat ) : gth n m -> geh m k -> gth n k .
Proof. intro. induction n as [ | n IHn ] .  intros m k X X0. apply (fromempty (nopathstruetofalse X)).  intros m k X X0 .  destruct m as [ | m ] .  set ( e := leh0implis0 k X0 ) . rewrite e . apply ( idpath false ) .  destruct k as [ | k ] . apply ( idpath false ) . apply (IHn m k) . assumption . assumption . Defined. 

Lemma gehgthtrans ( n m k : nat ) : geh n m -> gth m k -> gth n k .
Proof. intro. induction n as [ | n IHn ] .  intros m k X X0. destruct m as [ | m ] .  apply (fromempty (nopathstruetofalse X0 ) ).  destruct ( neglehsn0 _ X ) .   intros m k X X0 .  destruct k as [ | k ] .   apply ( idpath false ) .  destruct m as [ | m ] .  apply (fromempty (nopathstruetofalse X0 ) ). apply (IHn m k) . assumption . assumption . Defined. 

Lemma lthlehtrans ( n m k : nat ) : lth n m -> leh m k -> lth n k .
Proof . intros n m k l1 l2 . apply ( gehgthtrans k m n l2 l1 ) . Defined . 

Lemma lehlthtrans ( n m k : nat ) : leh n m -> lth m k -> lth n k .
Proof . intros n m k l1 l2 . apply ( gthgehtrans k m n l2 l1 ) . Defined . 


(** ** Some properties of [ plus ] on [ nat ] *)


(** *** The structure of the additive ablelian unitary monoid on [ nat ] *) 


Lemma natplusl0 ( n : nat ) : paths ( 0 + n ) n .
Proof . intros . apply idpath . Defined .  

Lemma natplusr0 ( n : nat ) : paths ( n + 0 ) n .
Proof . intro . induction n as [ | n IH n ] . apply idpath .  simpl . apply ( maponpaths S IH ) . Defined .
Hint Resolve natplusr0: natarith .

Lemma plusnsm ( n m : nat ) : paths ( n + S m ) ( S n + m ) .
Proof. intro . simpl . induction n as [ | n IHn ] .  auto with natarith . simpl . intro . apply ( maponpaths S ( IHn m ) ) .  Defined . 
Hint Resolve plusnsm : natarith .

Lemma natpluscomm ( n m : nat ) : paths ( n + m ) ( m + n ) .
Proof. intro. induction n as [ | n IHn ] . intro . auto with natarith .  intro .  set ( int := IHn ( S m ) ) . set ( int2 := pathsinv0 ( plusnsm n m ) ) . set ( int3 := pathsinv0 ( plusnsm m n ) ) .  set ( int4 := pathscomp0 int2 int  ) .  apply ( pathscomp0 int4 int3 ) . Defined . 
Hint Resolve natpluscomm : natarith . 

Lemma natplusassoc ( n m k : nat ) : paths ( ( n + m ) + k ) ( n + ( m + k ) ) .
Proof . intro . induction n as [ | n IHn ] . auto with natarith . intros . simpl .  apply ( maponpaths S ( IHn m k ) ) . Defined. 
Hint Resolve natplusassoc : natarith .

Definition addabmonoidnat : abmonoid := abmonoidpair ( setwithbinoppair natset ( fun n m : nat => n + m ) ) ( dirprodpair ( dirprodpair natplusassoc ( @isunitalpair natset _ 0 ( dirprodpair natplusl0 natplusr0 ) ) ) natpluscomm ) .    


(** *** The structure of a partially ordered by [ leh ] additive abelian unitary monoid on [ nat ] *) 


Lemma lehmplusnm ( n m : nat ) : leh m ( n + m ) .
Proof. intros . induction n as [ | n IHn ] . simpl . apply lehrefl . simpl .  apply ( lehtrans _ _ _ IHn ( lehnsn _ ) ) .  Defined . 

Lemma lehnplusnm ( n m : nat ) : leh n ( n + m ) .
Proof. intros . rewrite ( natpluscomm n m ) .  apply ( lehmplusnm m n ) .  Defined . 

Lemma neggthmplusnm ( n m : nat ) : neg ( gth m ( n + m ) ) .
Proof. intros . intro g . apply ( neglehgth _ _ ( lehmplusnm n m ) g ) .  Defined . 

Lemma neggthnplusnm ( n m : nat ) : neg ( gth n ( n + m ) ) .
Proof. intros . intro g . apply ( neglehgth _ _ ( lehnplusnm n m ) g ) .  Defined . 

Lemma lehandplusl ( n m k : nat ) : leh n m -> leh ( k + n ) ( k + m ) .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  assumption .  Defined . 

Lemma lehandplusr ( n m k : nat ) : leh n m -> leh ( n + k ) ( m + k ) .
Proof. intros . rewrite ( natpluscomm n k ) . rewrite ( natpluscomm m k ) . apply lehandplusl . assumption . Defined . 

Lemma lehandpluslinv  ( n m k : nat ) : leh ( k + n ) ( k + m ) -> leh n m .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  apply ( IHk l ) . Defined .

Lemma lehandplusrinv ( n m k : nat ) :  leh ( n + k ) ( m + k ) -> leh n m . 
Proof. intros n m k l . rewrite ( natpluscomm n k ) in l . rewrite ( natpluscomm m k ) in l . apply ( lehandpluslinv _ _ _ l )  . Defined . 


 


(** *** Cancellation properties of [ plus ] on [ nat ] *)

Lemma pathsitertoplus ( n m : nat ) : paths ( iteration S n m ) ( n + m ) .
Proof. intros .  induction n as [ | n IHn ] . apply idpath . simpl .  apply ( maponpaths S IHn ) .  Defined .

Lemma isinclplusn ( n : nat ) : isincl ( fun m : nat => m + n ) .
Proof. intro . induction n as [ | n IHn ] . apply ( isofhlevelfhomot 1 _ _ ( fun m : nat => pathsinv0 ( natplusr0 m ) ) ) . apply ( isofhlevelfweq 1 ( idweq nat ) ) .  apply ( isofhlevelfhomot 1 _ _ ( fun m : nat => pathsinv0 ( plusnsm m n ) ) ) . simpl .   apply ( isofhlevelfgf 1 _ _ isinclS IHn ) .  Defined. 

Lemma iscontrhfiberplusn ( n m : nat ) ( is : geh m n ) : iscontr ( hfiber ( fun i : nat => i + n ) m ) .
Proof. intros . apply iscontraprop1 .    apply isinclplusn . induction m as [ | m IHm ] . set ( e := leh0implis0 _ is ) .   split with 0 . apply e .  destruct ( lehchoice _ _ is ) as [ l | e ] .  set ( j := IHm l ) .  destruct j as [ j e' ] . split with ( S j ) .  simpl . apply ( maponpaths S e' ) .  split with 0 . simpl .  assumption .  Defined . 

Lemma neghfiberplusn ( n m : nat ) ( is : lth m n ) : neg ( hfiber  ( fun i : nat => i + n ) m ) .
Proof. intros. intro h . destruct h as [ i e ] . rewrite ( pathsinv0 e )  in is . destruct ( neglehgth _ _ ( lehmplusnm i n ) is ) .  Defined .    

Lemma isdecinclplusn ( n : nat ) : isdecincl ( fun i : nat => i + n ) .
Proof. intros . intro m . apply isdecpropif . apply ( isinclplusn _ m ) . destruct ( boolchoice ( leb n m ) ) as [ i | ni ] . apply ( ii1 ( pr21 ( iscontrhfiberplusn n m i ) ) ) . apply ( ii2 ( neghfiberplusn n m ni ) ) .  Defined .  


(** *** Some properties of [ minus ] on [ nat ] *)

Lemma plusminusnmm ( n m : nat ) ( is : leh m n ) : paths ( ( n - m ) + m ) n .
Proof . intro n . induction n as [ | n IH n] . intro m . intro lh . simpl . apply ( leh0implis0 _ lh ) . intro m . destruct m as [ | m ] . intro .   simpl . rewrite ( natplusr0 n ) .  apply idpath .  simpl . intro lh .  rewrite ( plusnsm ( n - m ) m ) . apply ( maponpaths S ( IH m lh ) ) .  Defined . 


(** *** [ plus ] and [ gth ] *)

Lemma gthandplusl ( n m k : nat ) : gth n m -> gth ( k + n ) ( k + m ) .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  assumption .  Defined . 

Lemma gthandplusr ( n m k : nat ) : gth n m -> gth ( n + k ) ( m + k ) .
Proof. intros . rewrite ( natpluscomm n k ) . rewrite ( natpluscomm m k ) . apply gthandplusl . assumption . Defined . 

Lemma gthandpluslinv  ( n m k : nat ) : gth ( k + n ) ( k + m ) -> gth n m .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  apply ( IHk l ) . Defined .

Lemma gthandplusrinv ( n m k : nat ) :  gth ( n + k ) ( m + k ) -> gth n m . 
Proof. intros n m k l . rewrite ( natpluscomm n k ) in l . rewrite ( natpluscomm m k ) in l . apply ( gthandpluslinv _ _ _ l )  . Defined . 




(** ** Some properties of [ mult ] on [ nat ] *)

(** *** Basic algebraic properties of [ mult ] on [ nat ] *)

Lemma multn0 ( n : nat ) : paths ( n * 0 ) 0 .
Proof. intro n . induction n as [ | n IHn ] . apply idpath . simpl .   assumption .  Defined . 
Hint Resolve multn0 : natarith .

Lemma multsnm ( n m : nat ) : paths ( ( S n ) * m ) ( m + n * m ) .
Proof. intros . apply idpath . Defined .
Hint Resolve multsnm : natarith .

Lemma multnsm ( n m : nat ) : paths ( n * ( S m ) ) ( n + n * m ) .
Proof. intro n . induction n as [ | n IHn ] . intro .  simpl .  apply idpath .  intro m .  simpl . apply ( maponpaths S ) .  rewrite ( pathsinv0 ( natplusassoc n m ( n * m ) ) ) .  rewrite ( natpluscomm n m ) .  rewrite ( natplusassoc m n ( n * m ) ) .  apply ( maponpaths ( fun x : nat => m + x ) ( IHn m ) ) .  Defined . 
Hint Resolve multnsm : natarith .

Lemma natmultcomm ( n m : nat ) : paths ( n * m ) ( m * n ) .
Proof. intro . induction n as [ | n IHn ] . intro .  auto with natarith . intro m .  rewrite ( multsnm n m ) .  rewrite ( multnsm m n ) .  apply ( maponpaths ( fun x : _ => m + x ) ( IHn m ) ) .   Defined .

Lemma natrdistr ( n m k : nat ) : paths ( ( n + m ) * k ) ( n * k + m * k ) .
Proof . intro . induction n as [ | n IHn ] . auto with natarith .   simpl . intros . rewrite ( natplusassoc k ( n * k ) ( m * k ) ) .   apply ( maponpaths ( fun x : _ => k + x ) ( IHn m k ) ) .  Defined . 
  
Lemma natldistr ( n m k : nat ) : paths ( n * ( m + k ) ) ( n * m + n * k ) .
Proof . intros n m . induction m as [ | m IHm ] . simpl . intro . rewrite ( multn0 n ) . auto with natarith .  simpl . intro . rewrite ( multnsm n ( m + k ) ) . rewrite ( multnsm n m ) .  rewrite ( natplusassoc _ _ _ ) .  apply ( maponpaths ( fun x : _ => n + x ) ( IHm k ) ) . Defined .

Lemma natmultassoc ( n m k : nat ) : paths ( ( n * m ) * k ) ( n * ( m * k ) ) .
Proof. intro . induction n as [ | n IHn ] . auto with natarith . intros . simpl . rewrite ( natrdistr m ( n * m ) k ) .  apply ( maponpaths ( fun x : _ => m * k + x ) ( IHn m k ) ) .   Defined . 

Lemma natmultl1 ( n : nat ) : paths ( 1 * n ) n .
Proof. simpl .  auto with natarith . Defined . 
Hint Resolve natmultl1 : natarith .

Lemma natmultr1 ( n : nat ) : paths ( n * 1 ) n .
Proof. intro n . rewrite ( natmultcomm n 1 ) . auto with natarith . Defined . 
Hint Resolve natmultr1 : natarith . 


Definition multabmonoidnat : abmonoid :=  abmonoidpair ( setwithbinoppair natset ( fun n m : nat => n * m ) ) ( dirprodpair ( dirprodpair natmultassoc ( @isunitalpair natset _ 1 ( dirprodpair natmultl1 natmultr1 ) ) ) natmultcomm ) .    





(** *** Multiplication and comparisons ( [ leh ] [ gth ] etc . ) *)


Lemma lehandmultl ( n m k : nat ) : leh n m -> leh ( k * n ) ( k * m ) .
Proof. intros n m k l . induction k as [ | k IHk ] . auto with natarith. simpl . apply ( lehtrans _ _ _ ( lehandplusr n m ( k * n ) l ) ( lehandplusl ( k * n ) ( k * m ) m IHk ) ) .   Defined .  

Lemma lehandmultr ( n m k : nat ) : leh n m -> leh ( n * k ) ( m * k ) .
Proof . intros n m k l . rewrite ( natmultcomm n k ) . rewrite ( natmultcomm m k ) . apply ( lehandmultl n m k l ) . Defined .

Lemma lehandmultlinv ( n m k : nat ) ( is : gth k 0 ) : leh ( k * n ) ( k * m ) -> leh n m .
Proof . intro n . induction n as [ | n IHn ] . intros . apply ( idpath true ) .  intros  m k . destruct m as [ | m ] . intros g l .  rewrite ( multn0 k ) in l .   rewrite ( multnsm k n ) in l .  set ( l' := lehtrans _ _ _ ( lehnplusnm k ( k * n ) ) l ) .  destruct ( neglehgth _ _ l' g ) . intros g l .  rewrite ( multnsm k n ) in l .   rewrite ( multnsm k m ) in l .  set ( l' := lehandpluslinv _ _ _ l ) . apply ( IHn m k g l' ) .  Defined . 

Lemma lehandmultrinv ( n m k : nat ) ( is : gth k 0 ) : leh ( n * k ) ( m * k ) -> leh n m .
Proof.  intros n m k is l . rewrite ( natmultcomm n k ) in l . rewrite ( natmultcomm m k ) in l . apply ( lehandmultlinv n m k is l ) . Defined .

Lemma lthandmultl ( n m k : nat ) ( is : gth k 0 ) : lth n m -> lth ( k * n ) ( k * m ) .
Proof. intro n . induction n as [ | n IHn ] . intros m k is l . destruct m as [ | m ] .  destruct ( neggthnn _ l ) .  rewrite ( multn0 k ) .  rewrite ( multnsm k m ) . apply ( gehgthtrans _ _ _ ( lehnplusnm k ( k * m ) ) is ) . intro m .   destruct m as [ | m ] .  intros k g l . destruct ( neggth0n _ l ) .  intros k g l .  rewrite ( multnsm k n ) .  rewrite ( multnsm k m ) .  apply ( gthandplusl _ _ k ) .  apply ( IHn m k g l ) .  Defined . 

Lemma lthandmultr ( n m k : nat ) ( is : gth k 0 ) : lth n m -> lth ( n * k ) ( m * k ) .
Proof . intros n m k l . rewrite ( natmultcomm n k ) . rewrite ( natmultcomm m k ) . apply ( lthandmultl n m k l ) . Defined .

Lemma lthandmultlinv ( n m k : nat ) ( is : gth k 0 ) : lth ( k * n ) ( k * m ) -> lth n m .
Proof . intro n . induction n as [ | n IHn ] . intros m k is l . destruct m as [ | m ] .  destruct ( neggthnn _ l ) . simpl .  apply idpath .  intro m . destruct m as [ | m ] . intros k g l .  rewrite ( multn0 k ) in l .  destruct ( neggth0n _ l ) .  intros k g l .  rewrite ( multnsm k n ) in l .   rewrite ( multnsm k m ) in l .  set ( l' := gthandpluslinv _ _ _ l ) .   apply ( IHn m k g l' ) .  Defined . 

Lemma lthandmultrinv ( n m k : nat ) ( is : gth k 0 ) : lth ( n * k ) ( m * k ) -> lth n m .
Proof.  intros n m k is l . rewrite ( natmultcomm n k ) in l . rewrite ( natmultcomm m k ) in l . apply ( lthandmultlinv n m k is l ) . Defined .







(** *** Division with a remainder on [ nat ] *)


Definition natdivrem ( n m : nat ) ( is : gth m 0 ) : dirprod nat nat .
Proof. intros . induction n as [ | n IHn ] . intros . apply ( dirprodpair 0 0 ) . destruct ( leb m ( S ( pr22 IHn ) ) )  . apply ( dirprodpair ( S ( pr21 IHn ) ) 0 ) .  apply ( dirprodpair ( pr21 IHn ) ( S ( pr22 IHn ) ) ) .  Defined . 

Definition natdiv ( n m : nat ) ( is : gth m 0 ) := pr21 ( natdivrem n m is ) .
Definition natrem ( n m : nat ) ( is : gth m 0 ) := pr22 ( natdivrem n m is ) .

Lemma lthnatrem ( n m : nat ) ( is : gth m 0 ) : lth ( natrem n m is ) m .
Proof. intro . destruct n as [ | n ] . unfold natrem . simpl . intros.  assumption .  unfold natrem . unfold natdivrem . simpl . intros m is . fold ( natdivrem n m is ) .  destruct ( boolchoice ( leb m (S (pr22 (natdivrem n m is))) ) ) as [ t | nt ] . rewrite t .  simpl .  assumption .   rewrite nt . simpl . assumption .  Defined . 


Theorem natdivremrule ( n m : nat ) ( is : gth m 0 ) : paths n ( ( natrem n m is ) + ( natdiv n m is ) * m ) .
Proof. intro . induction n as [ | n IHn ] . simpl .  intros . apply idpath . intros m is . unfold natrem . unfold natdiv .  unfold natdivrem . simpl . fold  ( natdivrem n m is ) .   destruct ( boolchoice ( leb m ( S ( pr22 ( natdivrem n m is  ) ) ) ) ) as [ t | nt ] . 

rewrite t . simpl . set ( is' := lthnatrem n m is ) . destruct ( gthchoice _ _ is' ) as [ h | e ] .    destruct ( neglehgth _ _ t h ) .  fold ( natdiv n m is ) . set ( e'' := maponpaths S ( IHn m is ) ) .  change (S (natrem n m is + natdiv n m is * m) ) with (  S ( natrem n m is ) + natdiv n m is * m ) in  e'' . rewrite ( pathsinv0 e ) in e'' . apply e'' . 
 
rewrite nt . simpl . apply ( maponpaths S ( IHn m is ) ) .  Defined .  


Lemma lehmultnatdiv ( n m : nat ) ( is : gth m 0 ) :  leh ( mult ( natdiv n m is ) m ) n .
Proof . intros . set ( e := natdivremrule n m is ) . set ( int := natdiv n m is * m ) . rewrite e . unfold int  .   apply ( lehmplusnm _ _ ) .  Defined . 


Theorem natdivremunique ( m i j i' j' : nat ) ( lj : lth j m ) ( lj' : lth j' m ) ( e : paths ( j + i * m ) ( j' + i' * m ) ) : dirprod ( paths i i' ) ( paths j j' ) .
Proof. intros m i . induction i as [ | i IHi ] .

intros j i' j' lj lj' .  intro e .  simpl in e . rewrite ( natplusr0 j ) in e .  rewrite e in lj .  destruct i' . simpl in e .  rewrite ( natplusr0 j' ) in e .  apply ( dirprodpair ( idpath _ ) e ) .  simpl in lj . rewrite ( natpluscomm m ( i' * m ) ) in lj . rewrite ( pathsinv0 ( natplusassoc _ _ _ ) ) in lj .  destruct ( neggthmplusnm _ _ lj ) .

intros j i' j' lj lj' e . destruct i' as [ | i' ] .  simpl in e .  rewrite ( natplusr0 j' ) in e . rewrite ( pathsinv0 e ) in lj' .   rewrite ( natpluscomm m ( i * m ) ) in lj' .  rewrite ( pathsinv0 ( natplusassoc _ _ _ ) ) in lj' .  destruct ( neggthmplusnm _ _ lj' ) .  

simpl in e .  rewrite ( natpluscomm m ( i * m ) ) in e .  rewrite ( natpluscomm m ( i' * m ) ) in e .  rewrite ( pathsinv0 ( natplusassoc j _ _ ) ) in e .  rewrite ( pathsinv0 ( natplusassoc j' _ _ ) ) in e . set ( e' := invmaponpathsincl _ ( isinclplusn m ) _ _ e ) .  set ( ee := IHi j i' j' lj lj' e' ) .  apply ( dirprodpair ( maponpaths S ( pr21 ee ) ) ( pr22 ee )  ) .  Defined . 



(** *** Exponentiation [ natpower n m ] ( " n to the power m " ) on [ nat ] *)

Fixpoint natpower ( n m : nat ) := match m with
O => 1 |
S m' => n * ( natpower n m' ) end .


(** *** Fcatorial on [ nat ] *)

Fixpoint factorial ( n : nat ) := match n with
0 => 1 |
S n' => ( S n' ) * ( factorial n' ) end .  





(** ** The order-preserving functions [ di i : nat -> nat ] whose image is the complement to one element [ i ] . *)

Definition di ( i : nat ) ( x : nat ) : nat :=
match leb i x with 
false => x |
true => S x 
end .

Lemma lehdinsn ( i n : nat ) : leh ( di i n ) ( S n ) .
Proof . intros . unfold di . destruct ( leb i n ) . apply lehrefl . apply lehnsn . Defined . 

Lemma gehdinn ( i n : nat ) : geh ( di i n ) n .
Proof. intros . unfold di . destruct ( leb i n ) .  apply lehnsn . apply lehrefl .   Defined . 


Lemma isincldi ( i : nat ) : isincl ( di i ) .
Proof. intro .   apply ( isinclbetweensets ( di i ) isasetnat isasetnat ) . intros x x' . unfold di . intro e. destruct  ( boolchoice ( leb i x ) )  as [ nel | l ] . rewrite nel in e .    destruct  ( boolchoice ( leb i x' ) )  as [ nel' | l' ] . rewrite nel' in e . apply ( invmaponpathsS _ _ e ) .  rewrite l' in e . destruct e . set ( e' := gthimplgths _ _ l' ) . simpl in e' .   destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 nel ) e' ) ) .  rewrite l in e . destruct  ( boolchoice ( leb i x' ) )  as [ nel' | l' ] .  rewrite nel' in e . rewrite e in l .  set ( e' := gthimplgths _ _  l ) . simpl in e' .  destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 nel' ) e' ) ) .  rewrite l' in e .  assumption .  Defined . 


Lemma neghfiberdi ( i : nat ) : neg ( hfiber ( di i ) i ) .
Proof. intros i hf . unfold di in hf . destruct hf as [ j e ] .  destruct ( boolchoice ( leb i j ) ) as [ l | g ] . rewrite l in e .    destruct e . apply ( neglehsnn j l ) . rewrite g in e .  destruct e . assert ( e : paths ( leb ( S j ) ( S j ) ) true ) . apply lehrefl .  apply ( nopathstruetofalse ( pathscomp0 ( pathsinv0 e ) g ) ) .  Defined. 

Lemma iscontrhfiberdi ( i j : nat ) ( ne : neg ( paths i j ) ) : iscontr ( hfiber ( di i ) j ) .
Proof. intros . apply iscontraprop1 .   apply ( isincldi i j ) . destruct ( boolchoice ( leb i j ) ) as [ nel | l ]  . destruct j as [ | j ] . destruct i as [ | i ] . destruct ( ne ( idpath _ ) ) .  simpl in nel . destruct ( nopathsfalsetotrue nel ) .  split with j .  unfold di .   destruct ( boolchoice ( leb i j ) ) as [ nel' | l' ]  .  rewrite nel' .  apply idpath .  destruct ( gthchoice _ _ l' ) as [ h | h ] .  destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 nel ) h ) ) .  destruct ( ne h ) . split with j . unfold di .  rewrite l .  apply idpath .   Defined . 
 
Lemma isdecincldi ( i : nat ) : isdecincl ( di i ) .
Proof. intro i . intro j . apply isdecpropif .   apply ( isincldi i j ) .  destruct ( boolchoice ( eqbnat i j ) ) as [ eq | neq ] . assert  ( e := eqhtopaths _ _ eq ) .   destruct e .  apply ( ii2 ( neghfiberdi i ) ) . apply ( ii1 ( pr21 ( iscontrhfiberdi i j ( neqhtonegpaths _ _ neq ) ) ) ) .   Defined .











(** ** Inductive types [ le ] with values in [ Type ] . 

This part is included for illustration purposes only . In practice it is easier to work with [ leh ] than with [ le ] . 

*)

(** *** A generalization of [ le ] and its properties . *)

Inductive leF { T : Type } ( F : T -> T ) ( t : T ) : T -> Type := leF_O : leF F t t | leF_S : forall t' : T , leF F t t' -> leF F t ( F t' ) .



Lemma leFiter { T : UU } ( F : T -> T ) ( t : T ) ( n : nat ) : leF F t ( iteration F n t ) .
Proof. intros .   induction n as [ | n IHn ] . apply leF_O . simpl . unfold funcomp . apply leF_S .  assumption .  Defined . 

Lemma leFtototal2withnat { T : UU } ( F : T -> T ) ( t t' : T ) ( a : leF F t t' ) : total2 ( fun n : nat => paths ( iteration F n t ) t' ) .
Proof. intros. induction a as [ | b H0 IH0 ] . split with O . apply idpath .  split with  ( S ( pr21 IH0 ) ) . simpl . apply ( @maponpaths _ _ F ( iteration F ( pr21 IH0 ) t ) b ) . apply ( pr22 IH0 ) .  Defined. 
Lemma total2withnattoleF { T : UU } ( F : T -> T ) ( t t' : T ) ( a : total2 ( fun n : nat => paths ( iteration F n t ) t' ) ) : leF F t t' .
Proof. intros .  destruct a as [ n e ] .  destruct e .  apply leFiter.  Defined . 


Lemma leFtototal2withnat_l0 { T : UU } ( F : T -> T ) ( t : T ) ( n : nat ) : paths ( leFtototal2withnat F t _ (leFiter F t n)) ( tpair _  n ( idpath (iteration F n t) ) ) . 
Proof . intros . induction n as [ | n IHn ] .   apply idpath . simpl .  
set ( h := fun ne :  total2 ( fun n0 : nat => paths ( iteration F n0 t ) ( iteration F n t ) ) => tpair  ( fun n0 : nat => paths ( iteration F n0 t ) ( iteration F ( S n ) t ) ) ( S ( pr21 ne ) ) ( maponpaths F ( pr22 ne ) ) ) . apply ( @maponpaths _ _ h  _ _ IHn ) . Defined. 


Lemma isweqleFtototal2withnat { T : UU } ( F : T -> T ) ( t t' : T ) : isweq ( leFtototal2withnat F t t' ) .
Proof . intros .  set ( f := leFtototal2withnat F t t' ) . set ( g :=  total2withnattoleF  F t t' ) . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x .  induction x as [ | y H0 IHH0 ] . apply idpath . simpl . simpl in IHH0 .  destruct (leFtototal2withnat F t y H0 ) as [ m e ] .   destruct e .  simpl .   simpl in IHH0.  apply (  @maponpaths _ _ ( leF_S F t (iteration F m t) ) _ _ IHH0 ) .
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x .  destruct x as [ n e ] .  destruct e . simpl .  apply  leFtototal2withnat_l0 . 
apply ( gradth _ _ egf efg ) . Defined.

Definition weqleFtototalwithnat { T : UU } ( F : T -> T ) ( t t' : T ) : weq ( leF F t t' ) (  total2 ( fun n : nat => paths ( iteration F n t ) t' ) ) := weqpair _ ( isweqleFtototal2withnat F t t' ) .


(** *** Inductive types [ le ] with values in [ Type ] are in [ hProp ] *)

Definition le ( n : nat ) : nat -> Type := leF S n .
Definition le_n := leF_O S .
Definition le_S := leF_S S . 



Theorem isaprople ( n m : nat ) : isaprop ( le n m ) .
Proof. intros .  apply ( isofhlevelweqb 1 ( weqleFtototalwithnat S n m ) ) . apply invproofirrelevance .  intros x x' .  set ( i := @pr21 _ (fun n0 : nat => paths (iteration S n0 n) m) ) . assert ( is : isincl i ) . apply ( isinclpr21 _ ( fun n0 : nat => isasetnat (iteration S n0 n) m ) ) . apply ( invmaponpathsincl _  is ) .  destruct x as [ n1 e1 ] . destruct x' as [ n2 e2 ] . simpl .   set ( int1 := pathsinv0 ( pathsitertoplus n1 n ) ) . set ( int2 := pathsinv0 (pathsitertoplus n2 n ) ) . set ( ee1 := pathscomp0 int1 e1 ) . set ( ee2 := pathscomp0 int2 e2 ) . set ( e := pathscomp0 ee1 ( pathsinv0 ee2 ) ) .   apply ( invmaponpathsincl _ ( isinclplusn n ) n1 n2 e ) .    Defined . 

(** *** Comparison between [ le ] with values in [ Type ] and [ leh ] . *)


Lemma letoleh ( n m : nat ) : le n m -> leh n m .
Proof .  intros n m H . induction H as [ | m H0 IHH0 ] . apply lehrefl .  apply lehimpllehs .  assumption .  Defined . 

Lemma lehtole ( n m : nat ) : leh n m ->  le n m .
Proof. intros n m H .  induction m .  assert ( int := leh0implis0 n H ) .   clear H . destruct int . apply le_n . 
 set ( int2 := lehchoice n ( S m ) H ) .  destruct int2 as [ isleh | iseq ] . apply ( le_S n m ( IHm isleh ) ) . destruct iseq .   apply le_n . Defined .

Lemma isweqletoleh ( n m : nat ) : isweq ( letoleh n m ) .
Proof. intros . set ( is1 := isaprople n m ) . set ( is2 := isasetbool ( leb n m ) true ) . apply ( isweqimplimpl ( letoleh n m ) ( lehtole n m ) is1 is2 ) .  Defined . 

Definition weqletoleh ( n m : nat ) := weqpair _ ( isweqletoleh n m ) .

Corollary isdecprople ( n m : nat ) : isdecprop ( le n m ) .
Proof. intros . apply ( isdecpropweqb ( weqletoleh n m ) ( isdecpropleh n m ) ) . Defined . 





(* (** Some properties of [ le ] . *)


Lemma le0m ( m : nat ) : le 0 m .
Proof. intro. induction m as [ | m IHm ] . apply  le_n . apply ( le_S _ _ ) . assumption . Defined. 

Lemma negleSn0 ( n : nat ) : neg ( le ( S n ) 0 ) .
Proof. intros n H . set ( int := letoleh _ _ H ) . apply ( neglehsn0 _ int ) . Defined .

Lemma len0topaths ( n : nat ) : le n 0 -> paths n 0 .
Proof. intros n H . set ( int :=letoleh n 0 H ) .    apply ( leh0implis0 n int ) .  Defined . 



(** Some properties of [ minus ] on [ nat ] *)

Lemma is0nminusn ( n : nat ) : paths 0 ( n - n ) .
Proof. intro . induction n as [ | n IHn ] . apply idpath .  simpl .  assumption .  Defined . *)







(* End of the file hnat.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)