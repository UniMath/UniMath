Require Export Foundations.Current_work.to_upstream_files .

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


(** Homotopies between functions of towers *)

Definition  towerfunhomot_a { T T' : tower } ( f g : towerfun T T' ) ( h0 : homot ( towerfunpr0 f ) ( towerfunpr0 g ) ) ( x : pr0 T ) : towerfun ( tfib T x ) ( tfib T' ( towerfunpr0 f x ) ) . 
Proof . intros .  destruct ( pathsinv0 ( h0 x ) ) . exact ( towerfuntfib g x ) . Defined .  


CoInductive towerfunhomot : forall ( T T' : tower ) ( f g : towerfun T T' ) , Type := tfhomotconstr : forall ( T T' : tower ) ( f g : towerfun T T' )  ( h0 : homot ( towerfunpr0 f ) ( towerfunpr0 g ) ) ( hfib : forall x : pr0 T , towerfunhomot _ _ ( towerfuntfib f x ) ( towerfunhomot_a f g h0 x ) ) , towerfunhomot T T' f g  . 

Arguments towerfunhomot [ T T' ] f g . 


(* Unfinished:

Definition oneshiftidfun ( T : tower ) : towerfunhomot( oneshiftfunct ( toweridfun T ) ) ( toweridfun ( oneshift T ) ) . 
Proof. intro . refine ( tfhomotconstr _ _ _ _ _ _ ) .  

intro x .  destruct x . exact ( idpath _ ) . 

simpl . intro . destruct x .  simpl .  ???

*)






(** Floors of towers *)

Definition Tn ( T : tower ) ( n : nat ) : UU := pr0 ( nshift n T ) .
Coercion Tn : tower >-> Funclass . 

Definition Tnfunct { T T' : tower } ( f : towerfun T T' ) ( n : nat ) : T n -> T' n := towerfunpr0 ( nshiftfunct n f ) . 
Coercion Tnfunct : towerfun >-> Funclass .

(* Unfinished:

Definition Tnid ( n : nat ) ( T : tower ) : paths ( ( toweridfun T ) n ) ( idfun ( T n ) )  . 
Proof. intros . induction n as [ | n IHn ] . 

apply idpath .  

unfold Tnfunct . simpl . unfold oneshiftfunct . simpl . destruct T as [ T0 Tfib ] .  simpl . ??? *)
 

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
 




(* End of the file towers.v *)

