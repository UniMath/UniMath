(** * Generalities on the type of integers and integer arithmetic. Vladimir Voevodsky . Aug. - Sep. 2011.

In this file we introduce the type [ hz ] of integers defined as the quotient set of [ dirprod nat nat ] by the standard equivalence relation and develop the main notions of the integer arithmetic using this definition . 


*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hnat .


(** Upstream *)

Definition booleq { X : UU } ( is : isdeceq X ) ( x x' : X ) : bool .
Proof . intros . destruct ( is x x' ) . apply true . apply false . Defined .    




(** ** The abelian group [ hz ] of integres *)

(** *** General definitions *)

Definition abgrhz : abgr := abgrfrac addabmonoidnat .
Definition hz : hSet := pr21 ( pr21 abgrhz ) .  
Definition natnattohz : nat -> nat -> hz := prabgrfrac addabmonoidnat .
(* Definition nattohz : nat -> hz := prabgrfrac1 addabmonoidnat . *)

Definition hzplus : hz -> hz -> hz := @op abgrhz.
Definition hzsign : hz -> hz := grinv abgrhz .
Definition hzminus : hz -> hz -> hz := fun x y => hzplus x ( hzsign y ) .
Definition hzzero : hz := unel abgrhz .

Bind Scope hz_scope with hz . 
Notation " x + y " := ( hzplus x y ) : hz_scope .
Notation " 0 " := hzzero : hz_scope .
Notation " - x " := ( hzsign x ) : hz_scope . 
Notation " x - y " := ( hzminus x y ) : hz_scope .   


(** *** Properties of equlaity on [ hz ] *)

Theorem isdeceqhz : isdeceq hz .
Proof . change ( isdeceq abgrhz ) . apply isdeceqabgrfrac . apply isinclplusn .  apply isdeceqnat .  Defined . 

Definition eqbhz := booleq isdeceqhz . 


Lemma isasethz : isaset hz .
Proof . apply ( setproperty abgrhz ) . Defined . 

Definition eqhz ( x y : hz ) : hProp := hProppair _ ( isasethz x y ) .  


(** *** Properties of addition and subtraction on [ hz ] *) 

Open Local Scope hz_scope . 

Lemma hzplusr0 ( x : hz ) : paths ( x + 0 ) x .
Proof . intro . apply ( runax abgrhz x ) .  Defined . 

Lemma hzplusl0 ( x : hz ) : paths ( 0 + x ) x .
Proof . intro . apply ( lunax abgrhz x ) . Defined . 

Lemma hzplusassoc ( x y z : hz ) : paths ( ( x + y ) + z ) ( x + ( y + z ) ) .
Proof . intros . apply ( assocax abgrhz x y z ) . Defined .   

Lemma hzpluscomm ( x y : hz ) : eqhz ( x + y ) ( y + x ) .
Proof . intros .  apply ( commax abgrhz x y ) . Defined .


(** *** Addition and subtraction on [ nat ] and [ hz ] *)



(** ** Absolute value on [ hz ] *)

Definition absvalhzint : ( dirprod nat nat ) -> nat .
Proof . intro nm . destruct nm as [ n m ] .  destruct ( leb n m ) . apply ( minus m n ) . apply ( minus n m ) . Defined .
       
Lemma absvalhzintcomp : iscomprelfun ( hrelabgrfrac addabmonoidnat )  absvalhzint .
Proof . unfold iscomprelfun .  intros x x' . unfold hrelabgrfrac . simpl . apply ( @hinhuniv _ ( hProppair _ ( isasetnat (absvalhzint x) (absvalhzint x') ) ) ) .    intro tt0 . simpl .   destruct tt0 as [ x0 eq ] . destruct x as [ n m ] . destruct x' as [ n' m' ] . simpl in eq .  set ( e' := invmaponpathsincl _ ( isinclplusn x0 ) _ _ eq ) .  simpl . destruct ( boolchoice ( leb n m ) ) as [ isle | isgt ] . 

rewrite isle . destruct ( boolchoice ( leb n' m' ) ) as [ isle' | isgt' ] . 

rewrite isle' . apply ( invmaponpathsincl _ ( isinclplusn ( n + n' ) ) ) . destruct ( natplusassoc ( m - n )  n n' ) . destruct ( natpluscomm n' n ) .  destruct ( natplusassoc ( m' - n' ) n' n ) .  rewrite ( plusminusnmm m n isle ) . rewrite ( plusminusnmm m' n' isle' ) .  simpl .  destruct ( natpluscomm m' n ) .  destruct ( natpluscomm m n'  ) .  apply ( pathsinv0 e' ) . 

rewrite isgt' . destruct ( natpluscomm m n' ) . set ( e'' := lehandplusr n m m' isle ) .  set ( e''' :=  gthandplusl n' m' m isgt' )  .  set ( e'''' := lehlthtrans _ _ _ e'' e''' ) .  rewrite e' in e'''' . destruct ( neggthnn _ e'''' ) .  

rewrite isgt . destruct ( boolchoice ( leb n' m' ) ) as [ isle' | isgt' ] . 

rewrite isle' . destruct ( natpluscomm m n' ) . set ( e'' := lehandplusl n' m' n isle' ) .  set ( e''' :=  gthandplusr n m n' isgt )  .  set ( e'''' := lthlehtrans _ _ _ e''' e'' ) .  rewrite e' in e'''' . destruct ( neggthnn _ e'''' ) . 

rewrite isgt' . apply ( invmaponpathsincl _ ( isinclplusn ( m + m' ) ) ) . destruct ( natplusassoc ( n - m )  m m' ) . destruct ( natpluscomm m' m ) .  destruct ( natplusassoc ( n' - m' ) m' m ) .  rewrite ( plusminusnmm n m ( gthimplgeh _ _ isgt ) ) . rewrite ( plusminusnmm n' m' ( gthimplgeh _ _ isgt' ) ) . apply e' .  Defined .  
   

Definition absvalhz : hz -> nat := setquotuniv _ natset absvalhzint absvalhzintcomp . 

Eval lazy in ( eqbhz ( natnattohz 3 4 ) ( natnattohz 17 18 ) ) . 
Eval lazy in ( eqbhz ( natnattohz 3 4 ) ( natnattohz 17 19 ) ) . 

Eval lazy in ( absvalhz ( natnattohz 58 332 ) ) .  
Eval lazy in ( absvalhz ( hzplus ( natnattohz 2 3 ) ( natnattohz 3 2 ) ) ) . 
Eval lazy in ( absvalhz ( hzminus ( natnattohz 2 3 ) ( natnattohz 3 2 ) ) ) . 




   







(* End of the file hz.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)