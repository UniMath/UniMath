Require Export Foundations.Current_work.pretowers.

Unset Automatic Introduction.




(** *** Towers of types - the coinductive definition. *)


(** Towers and shifts of towers *)

CoInductive tower := towerconstr : forall T0 : UU, ( T0 -> tower ) -> tower .

Definition pr0 ( T : tower ) : UU .
Proof. intro . destruct T as [ T' S' ] . exact T' . Defined. 

Definition tfib ( T : tower ) ( t : pr0 T ) : tower .
Proof. intro. destruct T as [ T' S' ] . exact S' . Defined. 

Definition oneshift ( T : tower ) : tower := 
towerconstr ( total2 ( fun t : pr0 T => pr0 ( tfib T t ) ) ) ( fun tf => tfib _ ( pr2 tf ) ) .

Definition nshift ( n : nat ) ( T : tower ) : tower .
Proof. intros . induction n as [| n IHn] . exact T . exact (oneshift IHn). Defined. 

Lemma snshift ( n : nat ) ( T : tower ) : paths ( nshift ( S n ) T ) ( nshift n ( oneshift T ) ) .
Proof .  intro n . induction n as [|n IHn]. apply idhomot. intro T . simpl. exact ( maponpaths _ ( IHn T ) ) .  Defined.

(*

Definition nshift' ( n : nat ) ( T : tower ) : tower.
Proof. intro n. induction n as [|n IHn]. intro T. exact T. intro T. exact ( IHn ( oneshift T ) ) . Defined . 

Lemma snshifts ( n : nat ) ( T : tower ) : paths ( nshift ( S n ) T ) ( nshift' ( S n ) T ) .
Proof. intro n . induction n as [|n IHn]. apply idhomot. intro T. simpl. simpl in IHn . rewrite ( IHn T ) .  

*)









(** Functions of towers *)


(* Coq with the type-in-type patch gives the universe inconsistency message here! *) 

CoInductive towerfun : forall ( T T' : tower ) , Type := towerfunconstr : forall ( T T' : tower ) ( f0 : pr0 T -> pr0 T' ) 
( ff : forall t0 : pr0 T , towerfun ( tfib _ t0 ) ( tfib _ ( f0 t0 ) ) ) , towerfun T T' . 

Definition towerfunpr0 { T T' : tower } ( f : towerfun T T' ) : pr0 T -> pr0 T' .
Proof. intros T1 T2 f G . destruct f as [ T T' f0 ff ] .  exact ( f0 G ) . Defined. 

Definition towerfuntfib { T T' : tower } ( f : towerfun T T' ) ( t : pr0 T ) : 
towerfun ( tfib _ t ) ( tfib _ ( towerfunpr0 f t ) ) .
Proof. intros. destruct f as [ T T' f0 ff ] . exact ( ff t ).  Defined.

CoFixpoint toweridfun ( T : tower ) : towerfun T T := towerfunconstr T T ( fun x => x ) ( fun t0 => toweridfun ( tfib _ t0 ) ) .

CoFixpoint towerfuncomp { T T' T'' : tower } ( f : towerfun T T' ) ( g : towerfun T' T'' ) : towerfun T T'' := 
towerfunconstr T T'' ( fun x => towerfunpr0 g ( towerfunpr0 f x ) ) ( fun x : pr0 T => @towerfuncomp ( tfib _ x ) 
( tfib _ ( towerfunpr0 f x ) ) ( tfib _ ( towerfunpr0 g ( towerfunpr0 f x ) ) ) 
( towerfuntfib f x ) ( towerfuntfib g ( towerfunpr0 f x ) ) )  . 

Definition oneshiftfunct { T T' : tower } ( f : towerfun T T' ) : towerfun ( oneshift T ) ( oneshift T' ) . 
Proof. intros .  refine ( towerfunconstr _ _ _ _ ) . 

{exact ( fun xf => tpair _ ( towerfunpr0 f ( pr1 xf ) ) ( towerfunpr0 ( towerfuntfib f ( pr1 xf ) ) ( pr2 xf ) ) ) . }

{intro t0. exact ( towerfuntfib ( towerfuntfib f ( pr1 t0 ) ) ( pr2 t0 ) ) . } Defined . 


Definition nshiftfunct ( n : nat ) { T T' : tower } ( f : towerfun T T' ) : towerfun ( nshift n T ) ( nshift n T' ) . 
Proof.  intro n . induction n as [|n IHn]. intros T T' f .  exact f .  intros T T' f . simpl . 
exact ( oneshiftfunct ( IHn _ _ f ) ) . 
Defined.





(** Floors of towers *)

Definition Tn ( T : tower ) ( n : nat ) : UU := pr0 ( nshift n T ) .
Coercion Tn : tower >-> Funclass . 

Definition Tnfunct { T T' : tower } ( f : towerfun T T' ) ( n : nat ) : T n -> T' n := towerfunpr0 ( nshiftfunct n f ) . 
Coercion Tnfunct : towerfun >-> Funclass . 

Definition fiberfloor { n : nat } { T : tower } ( tn : T n ) := pr0 ( tfib _ tn ) . 

(* Useful formulas:

towerfloor (1+n) T := total2 ( fun G : towerfoloor n T => fiberfloor G ) 

tfib (1+n) T ( tpair _ G G' ) := tfib (tfib _ G) G'

*) 

Definition fiberfloortotowerfloor { n : nat } { T : tower } ( tn : T n ) ( t' : fiberfloor tn ) : T ( S n ) := tpair _ tn t' .
Coercion fiberfloortotowerfloor : fiberfloor >-> Tn . 














(** *** The type of functions berween towers *)


Definition towerfunfiberfloor { T T' : tower } ( f : towerfun T T' ) { G : T 0 } :
 @fiberfloor 0 _ G -> @fiberfloor 0 _ ( f 0 G ) := ( towerfuntfib f G ) 0 .

Definition towerfunontowersovers  { n : nat } { T T' : tower } ( f : towerfun T T' ) ( G : T n ) :
 towerfun ( tfib _ G ) ( tfib _ ( f n G ) ) := towerfuntfib ( nshiftfunct n f ) G .


(** An example of a function between towers *)


CoFixpoint towerstrmap ( T : tower ) ( t0 : pr0 T ) : towerfun ( tfib _ t0 ) T :=
 towerfunconstr _ _ ( fun x => t0 ) ( fun t1 => towerstrmap ( tfib _ t0 ) t1 ) .   
 

(** *** The type of homotopies between functions of towers *)















(** Some constructions related to tower shifts *)


Definition mnshiftfun ( m n : nat ) ( T : tower ) : towerfun ( nshift m ( nshift n T ) ) ( nshift ( m + n ) T ) .
Proof. intros . induction m . 

apply toweridfun . 

set ( onfloors := ( fun G' => tpair _ (towerfunpr0 IHm (pr1 G')) (towerfunfiberfloor IHm  (pr2 G' ) ) )  :
  (nshift n T) (S m) -> T (S (m + n))) .   

split with onfloors . intro G .  apply ( towerfuntfib ( towerfuntfib IHm (pr1 G) ) (pr2 G) ) . Defined. 

Definition mnfloorfun { m n : nat } { T : tower } ( G : ( nshift n T ) m  ) : T ( m + n )  :=
 towerfunpr0 ( mnshiftfun m n T ) G . 


Definition tfibtotop { n : nat } { T : tower } ( G : T n  ) : towerfun ( tfib _ G ) ( nshift  ( S n ) T ).
Proof. intros. 

split with ( fun G' : pr0 ( tfib _ G ) => tpair ( fun G : T n  => pr0 ( tfib _ G ) ) G G' ) .  

intro G' . apply toweridfun . Defined. 

Definition fiberfloortofloor { n m : nat } { T : tower } ( G : T n  ) ( G' : ( tfib _ G ) m  ) : T ( m + ( S n ) )  . 
Proof. intros. apply ( mnfloorfun ( ( tfibtotop G ) m G' ) ) . Defined. 


(** Extending a tower with a unit type *)

Definition towerunitext ( T : tower ) : tower := towerconstr unit ( fun x : unit => T ) . 

(** Extended tower over a node G : T n *)

Definition tfibplus { n : nat } { T : tower } ( G : T n ) := towerconstr unit ( fun x => tfib _ G ) . 

Definition fromtfibplus { n : nat } { T : tower } ( G : T n ) : towerfun ( tfibplus G ) ( nshift n T ) .
Proof .  intros .  split with ( fun x => G ) . intro . apply ( toweridfun (tfib _ G) ) .  Defined. 

Definition fromtfibplusfloor { m n : nat } { T : tower } ( G : T n ) ( D : tfibplus G m ) : T ( m + n ) :=
towerfunpr0 ( mnshiftfun m n T ) ( ( fromtfibplus G ) m D ) .
 











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


(* End of the file bsystems.v *)