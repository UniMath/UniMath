Require Export Foundations.Current_work.bsystem.

Unset Automatic Introduction.


(** *** Equivalence between towers and pre-towers *)



(** Towers from pre-towers *)



CoFixpoint tfrompt ( pT : pretower )  : tower := towerconstr ( pT 0 ) ( fun t => tfrompt ( pretfib pT t ) ) .

CoFixpoint tfromptfun { pT pT' : pretower } ( f : pretowerfun pT pT' ) : 
towerfun ( tfrompt pT ) ( tfrompt pT' ) := towerfunconstr ( tfrompt pT ) ( tfrompt pT' )  
( f 0 ) ( fun t0 => @tfromptfun ( pretfib pT t0 ) ( pretfib pT' ( f 0 t0 ) ) ( pretfibfunct f t0 ) ) . 

Definition tfib_tfrompt ( pT: pretower ) ( t : pT O ) :
 paths ( tfrompt ( pretfib pT t ) ) ( tfib ( tfrompt pT ) t ) . 
Proof. intros .   apply idpath . Defined .

Lemma oneshift_tfrompt_to ( pT : pretower ) :
 towerfun ( tfrompt ( pretoweroneshift pT ) ) ( oneshift ( tfrompt pT ) ) . 
Proof. intro .

refine ( towerfunconstr _ _ _ _ ) . 

{ exact ( tohfpcocone ( pretowerpn pT 0 ) ) . }

{ intro t1 .  

set (tinhfpfiber := pr2 ( tohfpcocone ( pretowerpn pT O ) t1 )  :
 hfpfiber ( pretowerpn pT 0 ) ( pretowerpn pT 0 t1 ) ) . 
change (tfib ( oneshift ( tfrompt pT ) ) (tohfpcocone (pretowerpn pT 0) t1 ) ) with 
(tfib ( tfrompt ( pretfib pT ( pretowerpn pT 0 t1 ) ) )  tinhfpfiber ) .  
change (tfib (tfrompt (pretoweroneshift pT)) t1) with 
( tfrompt ( pretfib ( pretoweroneshift pT ) t1 ) ) .  
change (tfib (tfrompt (pretfib _ (pretowerpn pT 0 t1))) tinhfpfiber) with 
( tfrompt ( pretfib ( pretfib _ ( pretowerpn pT 0 t1 ) ) tinhfpfiber ) ) . 

apply tfromptfun . apply pretfibofpretoweroneshift . }

Defined. 

Lemma oneshift_tfrompt_from ( pT : pretower ) : 
towerfun ( oneshift ( tfrompt pT ) ) ( tfrompt ( pretoweroneshift pT ) ) . 
Proof. intro . cofix. 

refine ( towerfunconstr _ _ _ _ ) . 

{ exact ( fromhfpcocone ( pretowerpn pT 0 ) ) . }

{ intro t1 . 

change (tfib (tfrompt (pretoweroneshift pT)) (fromhfpcocone (pretowerpn pT 0) t1)) with 
( tfrompt ( pretfib ( pretoweroneshift pT ) (fromhfpcocone (pretowerpn pT 0) t1)) ) . 

change (tfib ( oneshift ( tfrompt pT ) ) t1 ) with 
( tfib ( tfrompt ( pretfib _ ( pr1 t1 ) ) ) ( pr2 t1 ) )  . 

change (tfib (tfrompt (pretfib _ ( pr1 t1 ))) (pr2 t1)) with 
( tfrompt ( pretfib ( pretfib _ ( pr1 t1 ) ) (pr2 t1))) . 

apply tfromptfun .  change (fromhfpcocone (pretowerpn pT 0) t1) with ( pr2 ( pr1 ( pr2 t1 ) ) ) .  

set ( ptf := pretowerfunoneshift ( pretowerpbpr pT ( fromunit ( pr1 t1 ) ) ) :
 pretowerfun (pretfib pT (pr1 t1)) ( pretoweroneshift pT ) ) . 

exact ( pretfibfunct ptf (pr2 t1) ) . } Defined . 






(** Pre-towers from towers *)


Lemma TSn ( T :tower ) ( n : nat ) : paths ( T ( S n ) ) ( total2 ( fun t : T n => pr0 ( tfib _ t ) ) ) .  
Proof. intros . apply idpath . Defined. 

Definition pn ( T : tower ) ( n : nat ) : T ( S n ) -> T n := @pr1 _ ( fun t : pr0 ( nshift n T ) => pr0 ( tfib _ t ) ) . 

Definition ptfromt ( T : tower ) : pretower := pretowerpair ( fun n => T n ) ( fun n => pn T n ) . 

Definition ptfromtfunct { T T' : tower } ( f : towerfun T T' ) : pretowerfun ( ptfromt T ) ( ptfromt T' ) .
Proof. intros .  refine ( tpair _ _ _ ) . 

exact ( Tnfunct f ) . 

{intro n . apply idhomot . } Defined.








(** Pre-towers from towers from pre-towers *)

Definition ptfromtfrompt_a ( pT : pretower ) ( n : nat ) ( x : Tn ( tfrompt pT ) n ) : pT n .
Proof. intros pT n .  generalize pT . clear pT .  induction n as [ | n IHn ] . 

intros . exact x .

intros . apply ( IHn ( pretoweroneshift pT ) ) .  unfold Tn in x . rewrite ( snshift n _ ) in x .  
exact ( Tnfunct ( oneshift_tfrompt_from pT ) n x ) . 

Defined. 


(* To be done:

Definition ptfromtfrompt ( pT : pretower ) : pretowerfun ( ptfromt ( tfrompt pT ) ) pT .
Proof. intro. split with ( ptfromtfrompt_a pT ) . 

intro n . destruct n as [ | n ] . 

intro x . exact ( pr2 ( pr2 x ) ) .

simpl . ???



Definition isweqptfromtfrompt ( pT : pretower ) ( n : nat ) : isweq( ptfromtfrompt_a pT n ) .  
Proof. intros . ???

*)


(* End of the file towers_from_pretowers.v *)