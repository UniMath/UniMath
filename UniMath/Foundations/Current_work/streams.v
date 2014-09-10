Require Export Foundations.Current_work.to_upstream_files .
Require Export Foundations.Proof_of_Extensionality.funextfun . 

Unset Automatic Introduction.


CoInductive stream ( T : UU ) := streamconstr : forall ( t : T ) ( s : stream T ) , stream T . 

Definition firstof { T : UU } ( s : stream T ) : T .
Proof. intros . destruct s as [ f r ] . exact f . Defined . 

Definition restof { T : UU } ( s : stream T ) : stream T .
Proof. intros . destruct s as [ f r ] . exact r . Defined . 

Definition streamfunct { T1 T2 : UU } ( f : T1 -> T2 ) ( s1 : stream T1 ) : stream T2 . 
Proof. intros . cofix. destruct s1 as [ s1f s1r ] . exact ( streamconstr T2 ( f s1f ) streamfunct ) . Defined . 

Lemma streamfunctid { T : UU } ( s : stream T ) : paths ( streamfunct ( idfun T ) s ) s .
Proof.  intros .  destruct s as [ sf sr ] .  ???



CoInductive bisim { T : UU } ( s1 s2 : stream T ) := 
bisimconstr : forall ( ef : paths ( firstof s1 ) ( firstof s2 ) ) ( er : bisim ( restof s1 ) ( restof s2 ) ) , bisim s1 s2 . 





 

Lemma bisimext_a { T : UU } { s1 s2 : stream T } ( be : bisim s1 s2 ) : stream ( pathsspace T ) . 
Proof. intros . cofix . destruct be as [ bef ber ] . 

refine ( streamconstr _ _ _ ) . 

exact ( pathsspacetriple T bef ) . 

exact bisimext_a . 

Defined . 

Lemma bsimext_as { T : UU } ( s1 s2 : stream T ) ( be : bisim s1 s2 ) : paths ( streamfunct ( fun xye : pathsspace T => pr1 xye ) ( bisimext_a be ) ) s1 .  
Proof . intros . destruct be as [ bef ber ] . simpl . ???







Theorem bisimext { T : UU } ( s1 s2 : stream T ) ( be : bisim s1 s2 ) : paths s1 s2 . 
Proof. intros . destruct be as [ bef ber ] . simpl . ???



(* End of the file streams.v *)