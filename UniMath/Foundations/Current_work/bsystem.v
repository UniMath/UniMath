Require Export Foundations.Current_work.towers

Unset Automatic Introduction.






(* The type of carriers of B-systems - towers together with a one step ramification at each floor except for the ground floor. In 
existing examples the ground floor of a B-system is always the unit type which corresponds to the fact that there is only one empty
 context. *)


Definition bsyscar := total2 ( fun T : tower => forall ( n : nat ) ( GT : T ( S n )  ) , UU ) . 
Definition bsyscarpair ( T : tower ) ( btilde : forall ( n : nat ) ( GT : T ( S n )  ) , UU ) : bsyscar := tpair _ T btilde . 

(* Note: the following is possibly an alternative definition of bsyscar:
CoInductive bsyscar' := bsyscar'constr : forall ( T : UU ) ( P : T -> UU ) , ( T -> bsyscar' ) -> bsyscar' .  *)

Definition bsyscartotower ( B : bsyscar ) := pr1 B .
Coercion bsyscartotower : bsyscar >-> tower.

Definition obj { n : nat } { B : bsyscar } ( GT : B ( S n ) ) : UU := ( pr2 B ) n GT . 

Definition ft { n : nat } { B : bsyscar } ( GT : B ( S n ) ) : B n := pr1 GT . 

Definition bsyscarover { n : nat } { B : bsyscar } ( G : B n ) : bsyscar :=
 bsyscarpair ( tfibplus G ) 
( fun m : nat => fun DT : ( tfibplus G ) ( S m )  => 
@obj ( ( m + n ) ) B ( ( mnshiftfun ( S m ) n B ) 0 ( ( fromtfibplus G ) ( S m ) DT ) ) ) . 

Definition tocarover { n : nat } { B : bsyscar } ( GT : B ( S n ) ) : bsyscarover ( ft GT ) 1 := @fiberfloortotowerfloor 0 ( tfibplus ( ft GT ) ) tt ( pr2 GT ) . 










(** Functions between B-system carriers *)

Definition bsyscarfun ( B B' : bsyscar ) : UU := 
total2 ( fun f : towerfun B B' => forall ( n : nat ) ( GT : B ( S n ) ) , obj GT -> obj ( f ( S n ) GT ) ) .
   
Definition bsyscarfuntotowerfun ( B B' : bsyscar ) : bsyscarfun B B' -> towerfun B B' := pr1 .
Coercion bsyscarfuntotowerfun : bsyscarfun >-> towerfun .

Definition objfun { n : nat } { B B' : bsyscar } ( f : bsyscarfun B B' ) { GT : B (S n ) } ( t : obj GT ) :
 obj ( f ( S n ) GT ) := ( pr2 f ) n GT t .

Definition bsyscaridfun ( B : bsyscar ) : bsyscarfun B B := tpair _ ( toweridfun B ) ( fun n => fun GT => idfun ( obj GT ) ) . 






(** Structures on bsystemcarriers which together form the data of a B-system. *)

(* Operations 

T : ( Gamma, x:T |- ) => ( Gamma , Delta |- ) => ( Gamma, x:T, Delta |- ) 

and

Ttilde : ( Gamma, x:T |- ) => ( Gamma , Delta |- s : S ) => ( Gamma, x:T, Delta |- s : S ) 

combined into a function of B-system carriers from the carrier over (Gamma) to the carrier over (Gamma,T) .*)

Definition Tops ( B : bsyscar ) := 
forall ( n : nat ) ( GT : B ( S n ) ) , bsyscarfun ( bsyscarover ( ft GT ) ) ( bsyscarover GT ) . 


(* Operations

S : ( Gamma |- s : S ) => ( Gamma , x:S, Delta |- ) => ( Gamma, Delta[s/x] |- ) 

and

Stilde : ( Gamma |- s : S ) => ( Gamma , x:S, Delta |- r : R ) => ( Gamma, Delta[s/x] |- r[s/x]:R[s/x]) 

combined into a function of B-system carriers from the carrier over (Gamma, S) to the carrier over (Gamma). *)


Definition Sops ( B : bsyscar ) := 
forall ( n : nat ) ( GS : B ( S n ) ) ( s : obj GS ) , bsyscarfun ( bsyscarover GS ) ( bsyscarover ( ft GS ) ) . 



(* Operations

Dops : ( Gamma, x:T |- ) => ( Gamma, x : T |- x : T ) *)

Definition Dops ( B : bsyscar ) ( T : Tops B ) := 
forall ( n : nat ) ( GT : B ( S n ) ) , obj ( T n GT 1 ( tocarover GT ) ) . 



(** The data for a B-system *)

Definition bsysdata : UU := total2 ( fun B : bsyscar => total2 ( fun SS : Sops B => total2 ( fun T : Tops B => Dops B T )  ) ) . 

Definition bsysdata_to_bsyscar : bsysdata -> bsyscar := pr1 . 
Coercion bsysdata_to_bsyscar : bsysdata >-> bsyscar .

Definition SS { B : bsysdata } { m n : nat } { GS : B ( S n ) } ( s : obj GS ) ( GD : bsyscarover GS m ) :
 bsyscarover ( ft GS ) m := ( pr1 ( pr2 B ) ) n GS s m GD .

Definition SSt { B : bsysdata } { m n : nat } { GS : B ( S n ) } ( s : obj GS ) { GSDR : bsyscarover GS ( S m ) } ( r : obj GSDR ) : obj ( SS s GSDR ) := objfun ( ( pr1 ( pr2 B ) ) n GS s ) r . 
 
Definition TT { B : bsysdata } { m n : nat } ( GT : B ( S n ) ) ( GD : bsyscarover ( ft GT ) m ) :
 bsyscarover GT m := ( pr1 ( pr2 ( pr2 B ) ) ) n GT m GD . 

Definition TTt { B : bsysdata } { m n : nat } ( GT : B ( S n ) ) { GDS : bsyscarover ( ft GT ) ( S m ) } ( s : obj GDS ) : obj ( TT GT GDS ) := objfun ( ( pr1 ( pr2 ( pr2 B ) ) ) n GT ) s . 

Definition DD { B : bsysdata } { n : nat } ( GT : B ( S n ) ) : obj ( TT GT ( tocarover GT ) ) := ( pr2 ( pr2 ( pr2 B ) ) ) n GT .


(** Iterated operations *)

(** Operation 

ft j : ( Gamma, Gamma' ) => ( Gamma )  *)

Definition ftj ( j : nat ) { n : nat } { T : tower } ( GG' : T ( j + n ) ) : T n .
Proof. intros j n T . induction j as [ | j IHj ] . intro GG' .  exact GG' . intro GG' . exact ( IHj ( pr1 GG' ) ) .  Defined. 


(* Operations 

T : ( Gamma, Gamma' |- ) => ( Gamma , Delta |- ) => ( Gamma, Gamma' , Delta |- ) 

and

Ttilde : ( Gamma, Gamma' |- ) => ( Gamma , Delta |- s : S ) => ( Gamma, Gamma' , Delta |- s : S ) 

combined into a function of B-system carriers from the carrier over (Gamma) to the carrier over (Gamma,Gamma') .*)



Definition TTj { j n : nat } { B : bsysdata } ( GG' : B ( j + n ) ) : bsyscarfun ( bsyscarover ( ftj j GG' ) ) ( bsyscarover GG' ) . 
Proof. intro j . induction j as [| j IHj]. intros . exact bsyscaridfun . 






(* To be removed:

Definition pretfib_Tn_jn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : total2 ( fun pretfibn : UU => pretfibn -> pT ( S n ) ) .
Proof . intros . induction n .  

split with (hfiber ( pretowerpn pT O ) t ) .  exact pr1 . 

split with ( hfp ( pr2 IHn ) ( pretowerpn pT ( S n ) ) ) . exact ( hfppru ( pr2 IHn ) ( pretowerpn pT ( S n ) ) ) . Defined. 

Definition pretfib_Tn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : UU  := pr1 ( pretfib_Tn_jn pT t n ) . 

Definition pretfib_jn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : pretfib_Tn pT t n -> pT ( S n ) := pr2 (  pretfib_Tn_jn pT t n ) . 

Definition pretfib_pn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : pretfib_Tn pT t ( S n ) -> pretfib_Tn pT t n .
Proof. intros pT t n .  exact ( hfpprl ( pr2 ( pretfib_Tn_jn pT t n ) ) ( pretowerpn pT ( S n ) ) ) . Defined. 

Definition pretfib { pT : pretower } ( t : pT 0 ) : pretower := pretowerpair ( pretfib_Tn pT t ) ( pretfib_pn pT t ) . 

Lemma pr0pretfib ( pT : pretower ) ( t : pT 0 ) : paths ( pretfib _ t  0 ) ( hfiber ( pretowerpn pT O ) t ) . 
Proof. intros. apply idpath .  Defined. 

Definition pretowerfuntfib_a { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( t : pT 0 ) ( n : nat ) : total2 ( fun funtfibn : ( pretfib _ t n ) -> ( pretfib _ ( f 0 t ) n ) => commsqstr ( f ( S n ) ) ( pretfibj ( f 0 t ) n ) ( pretfibj t n ) funtfibn ) .
Proof. intros pT pT' f t n . induction n as [ | n IHn ] .  

split with ( hfibersgtof' ( f 0 ) ( pretowerpn pT' 0 ) ( pretowerpn pT 0 ) ( f 1 ) ( prehn f 0 ) t ) . intro . About commsqstr .  apply idpath . ???


split with ( hfpcube ( f ( S n ) ) ( pretowerpn pT ( S n ) ) ( pretowerpn pT' ( S n ) ) ( f ( S ( S n ) ) )  ( pretfibj pT t n ) ( pretfibj pT' ( f 0 t ) n ) ( pr1 IHn ) ( prehn f ( S n ) ) ( pr2 IHn ) ) .  intro. apply idpath .  Defined. 

*)

(* To be erased 

Definition freefunctions : UU := total2 ( fun XY : dirprod UU UU => ( pr1 XY -> pr2 XY ) ) . 

Definition freefunctionstriple { X Y : UU } ( f : X -> Y ) : freefunctions := tpair ( fun XY : dirprod UU UU => ( pr1 XY -> pr2 XY ) ) ( dirprodpair X Y ) f . 

Definition ptsteps ( pT : pretower ) ( n : nat ) : freefunctions := freefunctionstriple ( pretowerpn pT n ) . 

(* *)

*)


(* End of the file bsystem.v *)