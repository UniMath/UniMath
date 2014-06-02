Require Export Foundations.Generalities.uu0.

Unset Automatic Introduction.


(** ** To ustream files of the library *)

Notation hfppru := hfpg' .

Notation hfpprl := hfpg . 

Notation fromunit := termfun .


(** To homotopies *)

Definition idhomot { X Y : UU } ( f : X -> Y ) : homot f f := fun x => idpath ( f x ) . 


(** To hfiber. *)


Definition tohfiber { X Y : UU } ( f : X -> Y ) ( x : X ) : hfiber f ( f x ) := hfiberpair f x ( idpath _ ) . 

(** To hfp *)

Definition hfptriple { X X' Y:UU} (f:X -> Y) (f':X' -> Y) ( x : X ) ( x' : X' ) ( h : paths ( f' x' ) ( f x ) ) : 
hfp f f' := tpair ( fun xx' : dirprod X X'  => paths ( f' ( pr2 xx' ) ) ( f ( pr1 xx' ) ) )  ( dirprodpair x x' ) h .

Definition tohfpfiber { X Y : UU } ( f : X -> Y ) ( x : X ) : hfp ( fromunit ( f x ) ) f := 
hfptriple ( fromunit ( f x ) )  f tt x ( idpath ( f x ) ) . 

(* The coconus of a function f : X -> Y is the total space of the family of hfibers of f. Since we use hfpfiber f y := 
hfp ( fromunit y ) f we need some basic facts about hfpcocones defiend as the total spaces of the family of hfpfibers. *)

Definition hfpfiber { X Y : UU } ( f : X -> Y ) ( y : Y ) := hfp ( fromunit y ) f . 

Definition hfpcocone { X Y : UU } ( f : X -> Y ) := total2 ( hfpfiber f ) .  

Definition tohfpcocone { X Y : UU } ( f : X -> Y ) : X -> hfpcocone f := fun x => tpair ( hfpfiber f ) ( f x ) ( hfptriple ( fromunit ( f x ) )  f tt x ( idpath _ ) ) . 

Definition fromhfpcocone { X Y : UU } ( f : X -> Y ) : hfpcocone f -> X := fun ytxe => ( pr2 ( pr1 ( pr2 ytxe ) ) ) . 
 

(** Functoriality of hfp. *)

Lemma hfplhomot { X Y Z : UU } { fl1 fl2 : X -> Y } ( h : homot fl1 fl2 ) ( gr : Z -> Y ) 
: weq ( hfp fl1 gr ) ( hfp fl2 gr ) .
Proof . intros . refine ( weqgradth _ _ _ _ ) .  

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 e (h (pr1 xz))) . }

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 e ( pathsinv0 (h (pr1 xz)))) . }

{ intro xze . destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) .  destruct ( h ( pr1 xz ) ) . 
destruct e . apply idpath . } 

{  intro xze .  destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) . destruct (h (pr1 xz)) . 
destruct e . apply idpath . }

Defined . 

Lemma hfprhomot { X Y Z : UU } ( fl : X -> Y ) { gr1 gr2 : Z -> Y } ( h : homot gr1 gr2 ) :
 weq ( hfp fl gr1 ) ( hfp fl gr2 ) .
Proof . intros . refine ( weqgradth _ _ _ _ ) .  

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 ( pathsinv0 (h (pr2 xz))) e) . }

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 (h (pr2 xz)) e) . }

{ intro xze . destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) .  destruct ( h ( pr2 xz ) ) . 
destruct e . apply idpath . } 

{  intro xze .  destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) . destruct (h (pr2 xz)) . 
destruct e . apply idpath . }

Defined . 


Lemma hfpcube { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) 
( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_back : commsqstr g' f' g f ) ( h_up : commsqstr gt' ft' gt f ) ( x : hfp gt g ) :
 hfp ft' f' . 
Proof . intros .  split with ( dirprodpair ( gt' ( pr1 ( pr1 x ) ) ) ( g' ( pr2 ( pr1 x ) ) ) ) . destruct x as [ x e ] . simpl . 
 destruct x as [ zt z ] . 
 simpl .  simpl in e .  destruct ( pathsinv0 ( h_back z ) ) . destruct ( pathsinv0 ( h_up zt ) ) . exact ( maponpaths f e ) .
 Defined.

Lemma hfpcube_h_front { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) 
( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_back : commsqstr g' f' g f ) ( h_up : commsqstr gt' ft' gt f ) :
 commsqstr ( hfpcube f g f' g' gt ft' gt' h_back h_up ) ( hfpprl ft' f' ) ( hfpprl gt g ) gt'  . 
Proof. intros .  intro z . apply idpath . Defined.


Lemma hfpcube_h_down { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) 
( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_back : commsqstr g' f' g f ) ( h_up : commsqstr gt' ft' gt f ) :
 commsqstr ( hfpcube f g f' g' gt ft' gt' h_back h_up )  ( hfppru ft' f' ) ( hfppru gt g ) g' . 
Proof. intros .  intro z . apply idpath . Defined.







(** Double pull-backs  ( cf. two_pullbacks_isequiv in hott-limits ) . *)

Definition doublehfp_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) 
( xyh' : hfp f'l ( hfpprl fl gr ) ) : hfp ( funcomp f'l fl ) gr . 
Proof. intros . destruct xyh' as [ [ x' [ [ x y ] h ] ] h' ] . set ( hflh' :=  pathscomp0 h ( maponpaths fl h' ) ) .
 exact ( hfptriple ( funcomp f'l fl ) gr x' y hflh' ) . Defined. 

 
Definition doublehfp_to { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr )  
( x'yh' : hfp ( funcomp f'l fl ) gr ) : hfp f'l ( hfpprl fl gr ) . 
Proof. intros . destruct x'yh' as [ [ x' y ] h' ] . exact ( hfptriple f'l ( hfpprl fl gr ) x' ( hfptriple fl gr ( f'l x' ) y h' ) 
( idpath _ ) ) . Defined. 


Definition doublehfp_to_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) :
 homot ( funcomp ( doublehfp_to f'l fl gr ) ( doublehfp_from f'l fl gr ) ) ( idfun ( hfp ( funcomp f'l fl ) gr ) ). 
Proof. intros . intro xyh . destruct xyh as [ [ x y ] h ] .  unfold doublehfp_to . unfold doublehfp_from. unfold funcomp . 
unfold hfppru. unfold hfpprl . unfold idfun .  simpl .  simpl in h . rewrite ( @pathscomp0rid _ _ (fl (f'l x)) h ) . 
 apply idpath . Defined . 

Lemma doublehfp_from_to_l1 { Tll Tlr Tur } ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) ( x0 : Tll ) ( z : hfiber ( hfpprl fl gr ) x0 ) :
 hfiber ( hfpprl fl gr ) x0 .
Proof . intros .  destruct z as [ [ [ x y ] h ] h0 ] . 
 exact ( tohfiber ( hfpprl fl gr ) ( hfptriple fl gr x0 y ( pathscomp0 h ( maponpaths fl h0 ) ) ) ) . Defined.  

Lemma doublehfp_from_to_l2 { Tll Tlr Tur } ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) ( x0 : Tll ) :
 homot ( doublehfp_from_to_l1 fl gr x0 ) ( idfun _ ) . 
Proof. intros . intro z .  destruct z as [ [ [ x y ] h ] h0 ] . destruct h0 . unfold idfun . simpl .  unfold hfpprl .    simpl .
 rewrite ( @pathscomp0rid _ ( gr y ) ( fl x ) h ) . apply idpath . Defined . 

Definition doublehfp_from_to { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) :
 homot ( funcomp  ( doublehfp_from f'l fl gr ) ( doublehfp_to f'l fl gr ) ) ( idfun ( hfp f'l ( hfpprl fl gr ) ) ).
Proof. intros .  intro x'yh' . destruct x'yh' as [ [ x' xyh ] h' ] .  simpl in h'. unfold hfpprl in h' .   simpl in h'.  
unfold idfun . unfold funcomp. unfold doublehfp_to. unfold doublehfp_from. unfold hfpprl . unfold hfppru .   simpl . 
  set ( x0 := f'l x' ) .  set ( e := doublehfp_from_to_l2 fl gr x0 ( hfiberpair ( hfpprl fl gr ) xyh h' ) ) .  
set ( phi := fun xyhh' : hfiber ( hfpprl fl gr ) x0 => hfptriple f'l ( hfpprl fl gr ) x' ( pr1 xyhh') ( pr2 xyhh' ) ) . 
destruct xyh as [ [ x y ] h ] .   exact ( maponpaths phi e ) .   Defined.       
 

Lemma isweq_doublehfp_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) :
 isweq ( doublehfp_from f'l fl gr ) . 
Proof . intros . apply gradth with ( doublehfp_to f'l fl gr ) .  exact ( doublehfp_from_to f'l fl gr ) .
 exact ( doublehfp_to_from f'l fl gr ) . Defined. 


(** Note: change these in uu0.v *)
 
Definition hfibersgtof'  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) 
( h : commsqstr g' f' g f ) ( x : X ) ( ze : hfiber g x ) : hfiber f' ( f x )  .
Proof. intros . split with ( g' ( pr1 ze ) ) .    apply ( pathscomp0  ( h ( pr1 ze ) )  ( maponpaths f ( pr2 ze ) )  ) . Defined . 

Definition hfibersg'tof  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) 
( h : commsqstr g' f' g f ) ( x' : X' ) ( ze : hfiber g' x' ) : hfiber f ( f' x' )  .
Proof. intros . split with ( g ( pr1 ze ) ) .    apply ( pathscomp0 ( pathsinv0 ( h ( pr1 ze ) ) ) ( maponpaths f' ( pr2 ze ) ) ) .
 Defined . 

(** To uu0.v *)

Definition pathstofun { X Y : UU } ( e : paths X Y ) : X -> Y .
Proof. intros X Y e x. destruct e . apply x .  Defined.  

Notation app1 := toforallpaths. 

Implicit Arguments app1 [ T P f g ] . 

(** To uu0.v after funextsec *)

Definition hfunextsecapp1 { T : UU } ( P : T -> UU ) { s1 s2 : forall t:T, P t} ( e : paths s1 s2 ) :
 paths ( funextsec P s1 s2 ( fun t => app1 e t ) ) e . 
Proof.  intros . apply ( homotweqinvweq ( weqfunextsec P s1 s2 ) e ) . Defined. 


Definition happ1funextsec { T : UU } ( P : T -> UU ) { s1 s2 : forall t:T, P t } ( e : forall t:T, paths (s1 t) (s2 t) ) ( t : T ) :
 paths ( app1 ( funextsec P s1 s2 e ) t ) ( e t ) . 
Proof.  intros . set ( int := homotinvweqweq ( weqfunextsec P s1 s2 ) e ) .  apply ( app1 int t ) .  Defined . 


(** Paths in total2 *)

Definition topathsintotal2 { X : UU } ( P : X -> UU ) ( x1 x2 : total2 P ) ( e : paths ( pr1 x1 ) ( pr1 x2 ) ) 
( ee : paths ( transportf P e ( pr2 x1 ) ) ( pr2 x2 ) ) : paths x1 x2 .
Proof. intros. destruct x1 as [ x11 x12 ]. destruct x2 as [ x21 x22 ]. set (int := pr1 ( pr2 ( constr1 P e ) ) x12 ). 
 apply ( pathscomp0 int ( maponpaths ( fun p => tpair P x21 p ) ee ) ) . Defined.






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
pretowerpair ( fun n => pT ( S n ) ) ( fun n => pretowerpn pT ( S n ) ) .   

Definition pretowerfunoneshift { pT pT' : pretower } ( f : pretowerfun pT pT' ) :
 pretowerfun ( pretoweroneshift pT ) ( pretoweroneshift pT' ) := 
pretowerfunconstr   ( pretoweroneshift pT ) ( pretoweroneshift pT' ) ( fun n => f ( S n ) ) ( fun n => prehn f ( S n ) ) . 

Definition pretoweroneshiftfunct { pT pT' : pretower } ( f : pretowerfun pT pT' ) : pretowerfun ( pretoweroneshift pT ) ( pretoweroneshift pT' ) .
Proof . intros.  refine ( tpair _ _ _ ) . 

intro n . exact ( pr1 f ( S n ) ) . 

intro n . exact ( pr2 f ( S n ) ) .  Defined.


Definition pretowernshift ( n : nat ) ( pT : pretower ) : pretower .
Proof. intros . induction n as [| n IHn] . exact pT . exact ( pretoweroneshift IHn ). Defined. 











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


(* Strict (substitutional) equality would simplify the proof of pretowerpboneshift considerably since the equality which we are
 trying to prove is a strict one and after showing that the first components of the dependent pairs are equal it would be easy to 
show that the second components are equal as well. *)


Definition pretowerbponeshift_aa { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> Y ) ( e : paths X' X ) 
( h : paths f' ( funcomp ( pathstofun e ) f ) ) : 
total2 ( fun esn : paths ( hfp f' g ) ( hfp f g ) => 
dirprod ( paths ( hfppru f' g ) ( funcomp ( pathstofun esn ) ( hfppru f g ) ) ) 
( paths ( funcomp ( pathstofun ( pathsinv0 esn ) ) ( funcomp ( hfpprl f' g ) ( pathstofun e ) ) ) ( hfpprl f g ) ) )  . 
Proof. intros . destruct e . simpl . change ( paths f' f ) in h . destruct h . split with ( idpath _ ) .  split with ( idpath _ ) . 
apply idpath . Defined. 


Definition pretowerbponeshift_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) : 
total2 ( fun en : paths ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pr1 ( pretowerpb_a pT f ( S n ) ) ) => 
total2 ( fun h : paths ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( funcomp ( pathstofun en )  ( pr2 ( pretowerpb_a pT f ( S n ) ) ) ) => 
paths ( fun xx : ( hfp ( pr2 ( pretowerpb_a pT f ( S n ) ) ) ( pretowerpn pT ( S n ) ) ) => 
( pathstofun en ) ( ( hfpprl ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( S n ) ) ) 
( pathstofun ( pathsinv0 ( pr1 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( S n ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) )  ( pretowerpn pT ( S n ) ) en h ) ) ) xx ) ) )

( hfpprl ( pr2 ( pretowerpb_a pT f ( S n ) ) ) ( pretowerpn pT ( S n ) ) ) ) ) . 
Proof. intros . induction n as [| n IHn]. 

split with ( idpath _ ) . split with ( idpath _ ) .  apply idpath . 



set (esn := pr1 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( S n ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( S n ) ) ( pr1 IHn ) ( pr1 ( pr2 IHn ) ) ) ) . 

set (hsn := pr1 (pr2 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( S n ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) 
( pretowerpn pT ( S n ) ) ( pr1 IHn ) ( pr1 ( pr2 IHn ) ) ) ) ). 

set ( int := pr2 ( pr2 ( pretowerbponeshift_aa ( pr2 ( pretowerpb_a pT f ( S ( S n ) ) ) ) 
( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ( S n ) ) ) 
( pretowerpn pT ( S ( S n ) ) ) esn hsn ) ) ) . 

split with esn. 
split with hsn.  
apply int.
Defined. 



Definition pretowerpboneshift ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) : 
paths ( pretowerpb ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) ) ( pretoweroneshift ( pretowerpb pT f ) ) .  
Proof. intros .   apply ptintpathstopaths . split with (fun n => pr1 ( pretowerbponeshift_a pT f n ) ) .  intro n . 
 exact ( pr2 ( pr2 ( pretowerbponeshift_a pT f n ) ) ) .  Defined. 

(* In the following we have to construct functions between the pretowers which we have shown to be "equal" anew because the equality 
path which we have constructed can not be computed with due, at least in part, to the use of function extensionality in its 
cosntruction. *) 

Definition pretowerbponeshift_to_a ( pT : pretower ) { X : UU } ( f : X -> pT 0 ) ( n : nat ) : 
total2 ( fun en : ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) -> 
( pr1 ( pretowerpb_a pT f ( S n ) ) ) => homot ( funcomp en ( pr2 ( pretowerpb_a pT f ( S n ) ) ) ) ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) )  . 
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
total2 ( fun en : ( pr1 ( pretowerpb_a pT f ( S n ) ) ) -> ( pr1 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) )
 => homot ( funcomp en ( pr2 ( pretowerpb_a ( pretoweroneshift pT ) ( hfppru f ( pretowerpn pT 0 ) ) n ) ) ) ( pr2 ( pretowerpb_a pT f ( S n ) ) )  )  . 
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

set ( e := pretowerpboneshift pT ( fromunit ( pretowerpn pT 0 t1 ) ) ) . 

exact ( pretowerstep pT ( fromunit ( pretowerpn pT 0 t1 ) ) (fromunit (tohfpfiber (pretowerpn pT 0) t1)) ) . Defined.






(* End of the file pretowers.v *)