Require Export Foundations.Current_work.to_upstream_files .

Unset Automatic Introduction.


Definition pseudotower_a (n : nat ) : total2 ( fun PT : UU => PT -> UU ) . 
Proof. intro n . induction n as [ | n IHn ] .

exact ( tpair _ UU ( idfun UU ) ) . 

split with ( total2 ( fun ft : pr1 IHn => ( ( pr2 IHn ) ft ) -> UU ) ) . 
exact ( fun ftfam => total2 ( fun x : ( pr2 IHn ) ( pr1 ftfam ) => ( pr2 ftfam ) x ) ) .    

Defined.

Definition pseudotower ( n : nat ) : UU := pr1 ( pseudotower_a n ) . 

Definition tot { n : nat } ( PT : pseudotower n ) : UU := pr2 ( pseudotower_a n ) PT . 

Definition pseudotfun_a { n : nat } ( PT1 PT2 : pseudotower n ) :
 total2 ( fun funspace : UU => ( funspace -> ( tot PT1 ) -> ( tot PT2 ) ) )  .
Proof .   intro n . induction n as [ | n IHn ] . 

exact ( fun X Y => 
( tpair ( fun funspace : UU => ( funspace -> ( tot X ) -> ( tot Y ) ) ) ( X -> Y ) ( fun f : X -> Y => fun x : X => f x ) ) )  . 

unfold pseudotower. simpl . 

intros ftfam1 ftfam2 . refine ( tpair _ ( total2 _ ) _ )  .  

exact ( pr1 ( IHn ( pr1 ftfam1 ) ( pr1 ftfam2 ) ) ) . 

intro ftf . exact ( forall ( x : tot ( pr1 ftfam1 ) ) , ( pr2 ftfam1 x ) -> 
( pr2 ftfam2 ( pr2 ( IHn ( pr1 ftfam1 ) ( pr1 ftfam2 ) ) ftf x ) ) ) . 

intro f .  

unfold tot . simpl .  intro tbasefib.  set ( ftf := pr1 f ) . set ( ffam := pr2 f ) .  
set ( ff := pr2 ( (IHn (pr1 ftfam1) (pr1 ftfam2)) ) ftf ) .  split with ( ff ( pr1 tbasefib ) ) .  
simpl in ffam . exact ( ffam ( pr1 tbasefib ) ( pr2 tbasefib ) ) . 

Defined. 

Definition pseudotfun { n : nat } ( PT1 PT2 : pseudotower n ) := pr1 ( pseudotfun_a PT1 PT2 ) . 

Definition pseudotfuntot { n : nat } { PT1 PT2 : pseudotower n } ( f : pseudotfun PT1 PT2 ) : tot PT1 -> tot PT2 := 
pr2 ( pseudotfun_a PT1 PT2 ) f .  


Definition pseudotfunid_a { n : nat } ( PT : pseudotower n ) : ( total2 ( fun idf : pseudotfun PT PT => paths ( pseudotfuntot idf ) ( idfun ( tot PT ) ) ) ) .
Proof . intro n . induction n as [ | n IHn ] . 

exact ( fun PT => ( tpair _ ( idfun PT ) ( idpath _ )  ) )  . 

intro PT . destruct PT as [ ft fam ] .  refine ( tpair _ _ _ ) .

 change ( tot ft -> UU ) in fam .  change ( pseudotower n ) in ft . unfold pseudotfun .  
 simpl . 
split with ( pr1 ( IHn ft ) ) .  intro x . intro xfib . change ( fam ( pseudotfuntot ( pr1 ( IHn ft ) ) x ) )  . 

assert ( ef := pr2 ( IHn ft ) ) . 
simpl in ef . 

{ set ( e := app1 ef x ) . simpl in e . apply ( transportb fam e ) .  exact xfib . } 

simpl . unfold pseudotfuntot . simpl . 

change ( pr2 (pseudotower_a n) ) with ( @tot n ) . 
set ( f := pr2 (pseudotfun_a ft ft) (pr1 (IHn ft)) ) . 
change ( pr2 (pseudotfun_a ft ft) (pr1 (IHn ft))  ) with f . 
set ( alpha := (pr2 (IHn ft)) ) . 
change (pr2 (IHn ft)) with alpha .

simpl in alpha . change (pseudotfuntot (pr1 (IHn ft))) with f in alpha . 

rewrite ( alpha ) .  simpl . unfold transportb . simpl . unfold transportf . unfold constr1 . simpl . unfold idfun . simpl .  apply funextsec . intro t .  destruct t .  apply idpath . Defined .  


(* End of the file pseudo_towers.v *)