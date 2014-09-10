Require Export Foundations.Current_work.to_upstream_files.

Unset Automatic Introduction.




(** ** Pre-towers and towers of types 

A tower of types can be viewed either as an infinite sequence of functions ... -> T_{n+1} -> T_n -> ... -> T_0 or as a
 coinductive object as in [tower] below.
We call such infinite sequences of functions pre-towers and coinductive opbjects towers. 
In its coinductive version a tower is essentially a rooted tree of infinite (countable) depth with the collection of
 branches leaving each node parametrized by a  arbitrary type. 


*)

(** *** Pre-towers of types - the sequence of functions definition. *)




Definition pretowerfam := ( fun T : nat -> UU => forall n : nat , T ( S n ) -> T n ) .

Definition pretower := total2 pretowerfam . 

Definition pretowerpair ( T : nat -> UU ) ( p : forall n : nat , T ( S n ) -> T n ) : pretower :=
 tpair ( fun T : nat -> UU => forall n : nat , T ( S n ) -> T n ) T p . 

Definition preTn ( pT : pretower ) ( n : nat ) : UU := pr1 pT n .

Coercion preTn : pretower >-> Funclass .  

Definition pretowerpn ( pT : pretower ) ( n : nat ) : pT ( S n ) -> pT n := pr2 pT n . 








(** Equalities of pre-towers *)


Definition ptintpaths ( pT pT' : pretower ) : UU := 
total2 ( fun e : forall n : nat , paths ( pT n ) ( pT' n ) =>
 forall n : nat , paths ( funcomp ( pathstofun ( pathsinv0 ( e ( S n ) ) ) ) 
( funcomp ( pretowerpn pT n ) ( pathstofun ( e n ) ) ) ) ( pretowerpn pT' n ) ) .


Definition ptintpathstopaths_a ( pT : pretower ) ( ppT' : nat -> UU ) ( e : paths ( pr1 pT ) ppT' ) :
 paths ( transportf pretowerfam e ( pr2 pT ) ) 
( fun n : nat => 
funcomp ( funcomp ( pathstofun ( pathsinv0 ( app1 e ( S n ) ) ) ) ( pretowerpn pT n  ) ) ( pathstofun ( app1 e n ) ) )  . 
Proof. intros. destruct e . apply idpath . Defined. 


Definition ptintpathstopaths ( pT pT' : pretower ) ( eneen : ptintpaths pT pT' ) : paths pT pT' . 
Proof.  intros . set ( int := funextfun _ _ ( pr1 eneen ) ) .  set ( int2 := pr2 eneen ) .  
refine ( topathsintotal2 pretowerfam _ _ _ _ ).

apply int . 

apply ( pathscomp0 (ptintpathstopaths_a pT ( pr1 pT' ) int ) ) . 

apply funextsec .  intro n . 

set ( es1 := ( app1 int n ) ) . assert ( e1 : paths es1 ( pr1 eneen n ) ) .  apply ( happ1funextsec _ ( pr1 eneen ) n ) . 

set ( es2 := ( pathsinv0 ( app1 int ( S n ) ) ) ) . assert ( e2 : paths es2 ( pathsinv0 ( pr1 eneen ( S n ) ) ) )  .  
apply ( maponpaths ( fun e => pathsinv0 e ) ) . apply ( happ1funextsec _ ( pr1 eneen ) ( S n ) ) .

change  (paths
     (fun x' : pr1 pT' (S n) =>
      pathstofun es1
        (pretowerpn pT n (pathstofun es2 x')))
     (pr2 pT' n)) . rewrite e1 . rewrite e2 . 

apply ( pr2 eneen ) .  Defined . 






(** Pre-tower functions. *)

Definition pretowerfun ( pT pT' : pretower ) : UU := total2 ( fun fn : forall n : nat , pT n -> pT' n => 
forall n : nat , homot ( funcomp ( fn ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( fn n ) ) ) . 

Definition pretowerfunconstr ( pT pT' : pretower ) ( fn : forall n : nat , pT n -> pT' n ) 
( hn : forall n : nat , homot ( funcomp ( fn ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( fn n ) ) ) :
 pretowerfun pT pT' := tpair _ fn hn . 

Definition prefn { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( n : nat ) : pT n -> pT' n := pr1 f n . 

Coercion prefn : pretowerfun >-> Funclass .  

Definition prehn { pT pT' : pretower }  ( f : pretowerfun pT pT' ) ( n : nat ) :
 homot ( funcomp ( prefn f ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( prefn f n ) ) := pr2 f n . 

Definition pretowerweq ( pT pT' : pretower ) : UU := total2 ( fun f : pretowerfun pT pT' => forall n : nat , isweq ( prefn f n ) ) . 

Definition pretoweridfun ( T : pretower ) : pretowerfun T T := 
pretowerfunconstr T T ( fun n => idfun _ ) ( fun n => fun z => idpath _ ) .

Definition pretowerfuncomp { T T' T'' : pretower } ( f : pretowerfun T T' ) ( g : pretowerfun T' T'' ) :
 pretowerfun T T'' := pretowerfunconstr T T'' ( fun n => funcomp ( f n ) ( g n ) ) 
( fun n => fun z => pathscomp0 ( prehn g n ( f ( S n ) z ) ) ( maponpaths ( g n ) ( prehn f n z ) ) ) . 









(** Pre-tower shifts *)

Definition pretoweroneshift ( pT : pretower )  : pretower := 
pretowerpair ( fun n => pT ( n + 1 ) ) ( fun n => pretowerpn pT ( n + 1 ) ) .   

Definition pretowerfunoneshift { pT pT' : pretower } ( f : pretowerfun pT pT' ) :
 pretowerfun ( pretoweroneshift pT ) ( pretoweroneshift pT' ) := 
pretowerfunconstr   ( pretoweroneshift pT ) ( pretoweroneshift pT' ) ( fun n => f ( n + 1 ) ) ( fun n => prehn f ( n + 1 ) ) . 

Definition pretoweroneshiftfunct { pT pT' : pretower } ( f : pretowerfun pT pT' ) : pretowerfun ( pretoweroneshift pT ) ( pretoweroneshift pT' ) .
Proof .  


intros.  refine ( tpair _ _ _ ) . 

intro n . exact ( pr1 f ( n + 1 ) ) . 

intro n . exact ( pr2 f ( n + 1 ) ) .  Defined.


Definition pretowernshift ( m : nat ) ( pT : pretower ) : pretower := pretowerpair ( fun n => pT ( n + m ) ) ( fun n => pretowerpn pT ( n + m ) ) . 










(** Pre-tower pull-backs *) 


Definition pretowerpb_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) :
 total2 ( fun pretowerpbsn : UU => pretowerpbsn -> pT n ) . 
Proof . intros . induction n .

split with X . exact f . 

split with ( hfp ( pr2 IHn ) ( pretowerpn pT n ) ) . exact ( hfppru ( pr2 IHn ) ( pretowerpn pT n ) ) .  Defined. 

Definition pretowerpb ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) : pretower := 
pretowerpair ( fun n => pr1 ( pretowerpb_a pT f n ) ) ( fun n => hfpprl ( pr2 ( pretowerpb_a pT f n ) ) ( pretowerpn pT n ) ) .

Definition pretowerpbpr ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) :
 pretowerfun ( pretowerpb pT f ) pT := pretowerfunconstr ( pretowerpb pT f ) pT ( fun n => pr2 ( pretowerpb_a pT f n ) ) 
( fun n => commhfp ( pr2 ( pretowerpb_a pT f n ) ) ( pretowerpn pT n ) ) . 



Definition pretowerfunct_a { pT' pT : pretower } { X X' : UU } ( g' : X' -> pT' 0 ) ( f' : pretowerfun pT' pT ) ( g : X' -> X ) 
( f : X -> pT 0 ) ( h : commsqstr g f g' ( f' 0 ) ) ( n : nat ) :
 total2 ( fun fto : pretowerpb pT' g' n -> pretowerpb pT f n => 
commsqstr  fto ( pretowerpbpr pT f n ) ( pretowerpbpr pT' g' n ) ( f' n ) ) .  
Proof. intros. induction n as [ | n IHn ] . 

refine ( tpair _ _ _ ) .  { exact g . } { exact h . }

refine ( tpair _ _ _ ) . 

{ exact ( hfpcube ( f' n ) ( pretowerpn pT' n ) ( pretowerpn pT n ) ( f' ( S n ) ) ( pretowerpbpr pT' g' n ) 
( pretowerpbpr pT f n ) ( pr1 IHn ) ( prehn f' n ) ( pr2 IHn ) ) . } 

{ exact ( fun z => idpath _ ) . } Defined. 


Definition pretowerpbfunct { pT' pT : pretower } { X' X : UU } ( g' : X' -> pT' 0 ) ( f' : pretowerfun pT' pT ) ( g : X' -> X ) 
( f : X -> pT 0 ) ( h : commsqstr g f g' ( f' 0 ) ) : pretowerfun ( pretowerpb pT' g' ) ( pretowerpb pT f ) . 
Proof. intros . split with ( fun n => pr1 ( pretowerfunct_a g' f' g f h n ) ) . intro n . intro xze . apply idpath . Defined. 


Definition pretowerpbfunct1 { pT' pT : pretower } { X' : UU } ( g' : X' -> pT' 0 ) ( f' : pretowerfun pT' pT ) :
 pretowerfun ( pretowerpb pT' g' ) ( pretowerpb pT ( funcomp g' ( f' 0 ) ) ) := 
pretowerpbfunct g' f' ( idfun X' ) ( funcomp g' ( f' 0 ) ) ( fun x => idpath _ ) . 


Definition doublepretowerpb_from ( pT : pretower ) { X X' : UU } ( g : X' -> X ) ( f : X -> pT 0 ) : 
pretowerfun ( pretowerpb ( pretowerpb pT f ) g ) ( pretowerpb pT ( funcomp g f ) ) := 
@pretowerpbfunct ( pretowerpb pT f ) pT X' X' g ( pretowerpbpr pT f ) ( idfun X' ) ( funcomp g f ) 
( fun x' : X' => idpath ( f ( g x' ) ) ) .  


Definition doublepretowerpb_to_a ( pT : pretower ) { X X' : UU } ( g : X' -> X ) ( f : X -> pT 0 ) ( n : nat ) :
 total2 ( fun fto : pretowerpb pT ( funcomp g f ) n -> pretowerpb ( pretowerpb pT f ) g n => 
homot ( pretowerpbpr pT ( funcomp g f ) n ) ( funcomp ( funcomp fto ( pretowerpbpr ( pretowerpb pT f ) g n ) ) 
( pretowerpbpr pT f n ) ) ) .
Proof. intros .  induction n as [ | n IHn ] .

{ split with ( fun x => x ) . intro . apply idpath . }

{ set ( fn := pretowerpbpr pT f n ) . set ( gn := pretowerpbpr ( pretowerpb pT f ) g n ) . set ( pn := pretowerpn pT n ) . 
refine ( tpair _ _ _ ) .  

  { intro xze .  set ( xze' := hfplhomot ( pr2 IHn )  ( pretowerpn pT n ) xze : 
hfp ( funcomp ( funcomp ( pr1 IHn ) gn ) fn ) pn  ) .  unfold  pretowerpb . unfold pretowerpb .  simpl . 
change ( hfp gn ( hfpprl fn pn ) ) . apply doublehfp_to . 
 apply ( hfppru ( pr1 IHn ) ( hfpprl ( funcomp gn fn ) pn ) ) .  apply doublehfp_to . apply xze' . }

  { intro xze . destruct xze as [ [ x z ] e ] . apply idpath . }} 

Defined . 


Definition doublepretowerpb_to ( pT : pretower ) { X X' : UU } ( g : X' -> X ) ( f : X -> pT 0 ) :
 pretowerfun ( pretowerpb pT ( funcomp g f ) ) ( pretowerpb ( pretowerpb pT f ) g ) . 
Proof. intros . refine ( pretowerfunconstr _ _ _ _ ) . 

{ intro n .  exact ( pr1 ( doublepretowerpb_to_a pT g f n ) ) . } 

{ intro n .  intro xze . destruct xze as [ [ x z ] e ] . simpl .  apply idpath . } 

Defined. 















(** Pre-tower pull-backs and pre-tower shift *)




Definition pretowerbponeshift_to_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) : 
total2 ( fun en : ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) -> 
( pr1 ( pretowerpb_a pT f ( n + 1 ) ) ) => homot ( funcomp en ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) ) ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) )  . 
Proof. intros .  induction n as [ | n IHn ] . 

split with ( idfun _ ) . apply idhomot . 

refine ( tpair _ _ _ ) . 

{refine ( hfpcube _ _ _ _ _ _ _ _ _ ) . 

exact ( idfun _ ) . 
exact ( idfun _ ) . 
exact ( pr1 IHn ) . 
exact ( idhomot _ ) . 
exact ( pr2 IHn ) . }

{refine ( hfpcube_h_down  _ _ _ _ _ _ _ _ _ ) . } Defined. 


Definition pretowerbpnshift_to_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( m n : nat ) : 
total2 ( fun en : ( pr1 ( pretowerpb_a ( pretowernshift pT m ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) -> 
( pr1 ( pretowerpb_a pT f ( n + 1 ) ) ) => homot ( funcomp en ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) ) ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) )  . 
Proof. intros .  induction n as [ | n IHn ] . 

split with ( idfun _ ) . apply idhomot . 

refine ( tpair _ _ _ ) . 

{refine ( hfpcube _ _ _ _ _ _ _ _ _ ) . 

exact ( idfun _ ) . 
exact ( idfun _ ) . 
exact ( pr1 IHn ) . 
exact ( idhomot _ ) . 
exact ( pr2 IHn ) . }

{refine ( hfpcube_h_down  _ _ _ _ _ _ _ _ _ ) . } Defined. 








Definition pretowerpboneshift_to ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) : 
pretowerfun ( pretowerpb ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ) ( pretoweroneshift ( pretowerpb pT f ) ) .
Proof. intros. refine ( tpair _ _ _ ) . 

exact ( fun n => pr1 ( pretowerbponeshift_to_a pT f n ) ) . 

intro n . refine ( hfpcube_h_front  _ _ _ _ _ _ _ _ _  ) .  Defined. 

Definition pretowerbponeshift_from_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) : 
total2 ( fun en : ( pr1 ( pretowerpb_a pT f ( n + 1 ) ) ) -> ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) )
 => homot ( funcomp en ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) ) ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) )  )  . 
Proof. intros .  induction n as [ | n IHn ] . 

split with ( idfun _ ) . apply idhomot . 

refine ( tpair _ _ _ ) . 

{refine ( hfpcube _ _ _ _ _ _ _ _ _ ) . 

exact ( idfun _ ) . 
exact ( idfun _ ) . 
exact ( pr1 IHn ) . 
exact ( idhomot _ ) . 
exact ( pr2 IHn ) . }

{refine ( hfpcube_h_down  _ _ _ _ _ _ _ _ _ ) . } Defined. 


Definition pretowerpboneshift_from ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) : 
pretowerfun ( pretoweroneshift ( pretowerpb pT f ) ) ( pretowerpb ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ) .
Proof. intros. refine ( tpair _ _ _ ) . 

exact ( fun n => pr1 ( pretowerbponeshift_from_a pT f n ) ) . 

intro n . refine ( hfpcube_h_front  _ _ _ _ _ _ _ _ _  ) .  Defined. 


(** Step lemma *)

Lemma pretowerstep { Y X : UU } ( pT : pretower ) ( f : X -> pT 0 ) ( g : Y -> ( pretowerpb pT f ) 1 ) : 
pretowerfun ( pretowerpb ( pretoweroneshift pT ) ( funcomp g ( hfppru f ( pretowerpn pT 0 ) ) ) ) 
( pretowerpb ( pretoweroneshift ( pretowerpb pT f ) ) g ) . 
Proof. intros .  refine ( pretowerfuncomp ( doublepretowerpb_to _ _ _ ) _ ) . refine ( pretowerpbfunct _ _ _ _ _ ) .  

{refine ( pretowerpboneshift_to _ _ ) . }

{exact ( idfun _ ) . }

{exact ( idhomot _ ) . }

Defined.  







(** Pre-tower fibers *)



Definition pretfib ( pT : pretower ) ( t : pT 0 ) : pretower := pretoweroneshift ( pretowerpb pT ( fromunit t ) ) . 

Definition pretfibj { pT : pretower } ( t : pT 0 ) : pretowerfun ( pretfib _ t ) ( pretoweroneshift pT ) := 
pretowerfunoneshift ( pretowerpbpr pT ( fromunit t ) ) . 


Definition pretfibfunct { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( t : pT 0 ) : 
pretowerfun ( pretfib _ t ) ( pretfib _ ( f 0 t ) ) .
Proof. intros.  apply pretowerfunoneshift.  
exact ( pretowerpbfunct ( fromunit t ) f ( idfun unit ) ( fromunit ( f 0 t ) ) ( fun _ : _ => idpath _ ) ) .  Defined. 


Definition pretfibtopretoweroneshift ( pT : pretower ) ( t0 : pT 0 ) : pretowerfun ( pretfib _ t0 ) ( pretoweroneshift pT ) := 
pretowerfunoneshift ( pretowerpbpr pT ( fromunit t0 ) ) . 


Definition pretfibofpretoweroneshift ( pT : pretower ) ( t1 : pT 1 ) : 
pretowerfun ( @pretfib ( pretoweroneshift pT ) t1 ) ( @pretfib ( @pretfib pT ( pretowerpn pT 0 t1 ) ) 
( tohfpfiber ( pretowerpn pT 0 ) t1 ) ) .
Proof.   intros . apply pretoweroneshiftfunct .  unfold pretfib . 

exact ( pretowerstep pT ( fromunit ( pretowerpn pT 0 t1 ) ) (fromunit (tohfpfiber (pretowerpn pT 0) t1)) ) . Defined.









(** An equality version of the relation between pretowerpb and pretoweroneshift.

Strict (substitutional) equality would simplify the proof of pretowerpboneshift considerably since the equality which we are
 trying to prove is a strict one and after showing that the first components of the dependent pairs are equal it would be easy to 
show that the second components are equal as well. 

Note also that the equality 
path which we have constructed can not be computed with due, at least in part, to the use of function extensionality in its 
cosntruction. 
*)


Definition pretowerbponeshift_aa { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> Y ) ( e : paths X' X ) 
( h : paths f' ( funcomp ( pathstofun e ) f ) ) : 
total2 ( fun esn : paths ( hfp f' g ) ( hfp f g ) => 
dirprod ( paths ( hfppru f' g ) ( funcomp ( pathstofun esn ) ( hfppru f g ) ) ) 
( paths ( funcomp ( pathstofun ( pathsinv0 esn ) ) ( funcomp ( hfpprl f' g ) ( pathstofun e ) ) ) ( hfpprl f g ) ) )  . 
Proof. intros . destruct e . simpl . change ( paths f' f ) in h . destruct h . split with ( idpath _ ) .  split with ( idpath _ ) . 
apply idpath . Defined. 


Definition pretowerbponeshift_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) : 
total2 ( fun en : paths ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pr1 ( pretowerpb_a pT f ( n + 1 ) ) ) => 
total2 ( fun h : paths ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( funcomp ( pathstofun en )  ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) ) => 
paths ( fun xx : ( hfp ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) ( pretowerpn pT ( n + 1 ) ) ) => 
( pathstofun en ) ( ( hfpprl ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( n + 1 ) ) ) 
( pathstofun ( pathsinv0 ( pr1 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) )  ( pretowerpn pT ( n + 1 ) ) en h ) ) ) xx ) ) )

( hfpprl ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) ( pretowerpn pT ( n + 1 ) ) ) ) ) . 
Proof. intros . induction n as [| n IHn]. 

split with ( idpath _ ) . split with ( idpath _ ) .  apply idpath . 



set (esn := pr1 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( n + 1 ) ) ( pr1 IHn ) ( pr1 ( pr2 IHn ) ) ) ) . 

set (hsn := pr1 (pr2 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( n + 1 ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( n + 1 ) ) ( pr1 IHn ) ( pr1 ( pr2 IHn ) ) ) ) ). 

set ( int := pr2 ( pr2 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( S ( n + 1 ) ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ( S n ) ) ) 
( pretowerpn pT ( S ( n + 1 ) ) ) esn hsn ) ) ) . 

split with esn. 
split with hsn.  
apply int.
Defined. 



Definition pretowerpboneshift ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) : 
paths ( pretowerpb ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ) ( pretoweroneshift ( pretowerpb pT f ) ) .  
Proof. intros .   apply ptintpathstopaths . split with (fun n => pr1 ( pretowerbponeshift_a pT f n ) ) .  intro n . 
 exact ( pr2 ( pr2 ( pretowerbponeshift_a pT f n ) ) ) .  Defined. 




(* End of the file pretowers.v *)