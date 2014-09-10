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


(* End of the file to_upstream_files.v *)