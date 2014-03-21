Require Export Foundations.Generalities.uu0.

Unset Automatic Introduction.


(** ** To ustream files of the library *)

Notation hfppru := hfpg' .

Notation hfpprl := hfpg . 

Notation fromunit := termfun .


(** To hfiber. *)


Definition tohfiber { X Y : UU } ( f : X -> Y ) ( x : X ) : hfiber f ( f x ) := hfiberpair f x ( idpath _ ) . 

(** To hfp *)

Definition hfptriple { X X' Y:UU} (f:X -> Y) (f':X' -> Y) ( x : X ) ( x' : X' ) ( h : paths ( f' x' ) ( f x ) ) : hfp f f' := tpair ( fun xx' : dirprod X X'  => paths ( f' ( pr2 xx' ) ) ( f ( pr1 xx' ) ) )  ( dirprodpair x x' ) h . 

(** Functoriality of hfp. *)

Lemma hfplhomot { X Y Z : UU } { fl1 fl2 : X -> Y } ( h : homot fl1 fl2 ) ( gr : Z -> Y ) : weq ( hfp fl1 gr ) ( hfp fl2 gr ) .
Proof . intros . refine ( weqgradth _ _ _ _ ) .  

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 e (h (pr1 xz))) . }

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 e ( pathsinv0 (h (pr1 xz)))) . }

{ intro xze . destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) .  destruct ( h ( pr1 xz ) ) . destruct e . apply idpath . } 

{  intro xze .  destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) . destruct (h (pr1 xz)) . destruct e . apply idpath . }

Defined . 

Lemma hfprhomot { X Y Z : UU } ( fl : X -> Y ) { gr1 gr2 : Z -> Y } ( h : homot gr1 gr2 ) : weq ( hfp fl gr1 ) ( hfp fl gr2 ) .
Proof . intros . refine ( weqgradth _ _ _ _ ) .  

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 ( pathsinv0 (h (pr2 xz))) e) . }

{ intro xze . destruct xze as [ xz e ] . split with xz .  exact (pathscomp0 (h (pr2 xz)) e) . }

{ intro xze . destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) .  destruct ( h ( pr2 xz ) ) . destruct e . apply idpath . } 

{  intro xze .  destruct xze as [ xz e ] . apply ( maponpaths ( fun ee => tpair _ xz ee ) ) . destruct (h (pr2 xz)) . destruct e . apply idpath . }

Defined . 


Lemma hfpfunct { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) ( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_front : commsqstr g' f' g f ) ( h_down : commsqstr gt' ft' gt f ) ( x : hfp gt g ) : hfp ft' f' . 
Proof . intros .  split with ( dirprodpair ( gt' ( pr1 ( pr1 x ) ) ) ( g' ( pr2 ( pr1 x ) ) ) ) . destruct x as [ x e ] . simpl .  destruct x as [ zt z ] . 
 simpl .  simpl in e .  destruct ( pathsinv0 ( h_front z ) ) . destruct ( pathsinv0 ( h_down zt ) ) . exact ( maponpaths f e ) . Defined.

Lemma hfpfunct_h_back { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) ( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_front : commsqstr g' f' g f ) ( h_down : commsqstr gt' ft' gt f ) : commsqstr ( hfpfunct f g f' g' gt ft' gt' h_front h_down ) ( hfpprl ft' f' ) ( hfpprl gt g ) gt'  . 
Proof. intros .  intro z . apply idpath . Defined.


Lemma hfpfunct_h_up { X X' Y Z Zt Xt' : UU } ( f : X -> Y ) ( g : Z -> X ) ( f' : X' -> Y ) ( g' : Z -> X' ) ( gt : Zt -> X ) ( ft' : Xt' -> Y ) ( gt' : Zt -> Xt' ) ( h_front : commsqstr g' f' g f ) ( h_down : commsqstr gt' ft' gt f ) : commsqstr ( hfpfunct f g f' g' gt ft' gt' h_front h_down )  ( hfppru ft' f' ) ( hfppru gt g ) g' . 
Proof. intros .  intro z . apply idpath . Defined.


(** Double pull-backs  ( cf. two_pullbacks_isequiv in hott-limits ) . *)

Definition doublehfp_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) ( xyh' : hfp f'l ( hfpprl fl gr ) ) : hfp ( funcomp f'l fl ) gr . 
Proof. intros . destruct xyh' as [ [ x' [ [ x y ] h ] ] h' ] . set ( hflh' :=  pathscomp0 h ( maponpaths fl h' ) ) . exact ( hfptriple ( funcomp f'l fl ) gr x' y hflh' ) . Defined. 

 
Definition doublehfp_to { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr )  ( x'yh' : hfp ( funcomp f'l fl ) gr ) : hfp f'l ( hfpprl fl gr ) . 
Proof. intros . destruct x'yh' as [ [ x' y ] h' ] . exact ( hfptriple f'l ( hfpprl fl gr ) x' ( hfptriple fl gr ( f'l x' ) y h' ) ( idpath _ ) ) . Defined. 


Definition doublehfp_to_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr )  : homot ( funcomp ( doublehfp_to f'l fl gr ) ( doublehfp_from f'l fl gr ) ) ( idfun ( hfp ( funcomp f'l fl ) gr ) ). 
Proof. intros . intro xyh . destruct xyh as [ [ x y ] h ] .  unfold doublehfp_to . unfold doublehfp_from. unfold funcomp . unfold hfppru. unfold hfpprl . unfold idfun .  simpl .  simpl in h . rewrite ( @pathscomp0rid _ _ (fl (f'l x)) h ) .  apply idpath . Defined . 

Lemma doublehfp_from_to_l1 { Tll Tlr Tur } ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) ( x0 : Tll ) ( z : hfiber ( hfpprl fl gr ) x0 ) : hfiber ( hfpprl fl gr ) x0 .
Proof . intros .  destruct z as [ [ [ x y ] h ] h0 ] .  exact ( tohfiber ( hfpprl fl gr ) ( hfptriple fl gr x0 y ( pathscomp0 h ( maponpaths fl h0 ) ) ) ) . Defined.  

Lemma doublehfp_from_to_l2 { Tll Tlr Tur } ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) ( x0 : Tll ) : homot ( doublehfp_from_to_l1 fl gr x0 ) ( idfun _ ) . 
Proof. intros . intro z .  destruct z as [ [ [ x y ] h ] h0 ] . destruct h0 . unfold idfun . simpl .  unfold hfpprl .    simpl . rewrite ( @pathscomp0rid _ ( gr y ) ( fl x ) h ) . apply idpath . Defined . 

Definition doublehfp_from_to { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr )  : homot ( funcomp  ( doublehfp_from f'l fl gr ) ( doublehfp_to f'l fl gr ) ) ( idfun ( hfp f'l ( hfpprl fl gr ) ) ).
Proof. intros .  intro x'yh' . destruct x'yh' as [ [ x' xyh ] h' ] .  simpl in h'. unfold hfpprl in h' .   simpl in h'.  unfold idfun . unfold funcomp. unfold doublehfp_to. unfold doublehfp_from. unfold hfpprl . unfold hfppru .   simpl . 
  set ( x0 := f'l x' ) .  set ( e := doublehfp_from_to_l2 fl gr x0 ( hfiberpair ( hfpprl fl gr ) xyh h' ) ) .  set ( phi := fun xyhh' : hfiber ( hfpprl fl gr ) x0 => hfptriple f'l ( hfpprl fl gr ) x' ( pr1 xyhh') ( pr2 xyhh' ) ) . destruct xyh as [ [ x y ] h ] .   exact ( maponpaths phi e ) .   Defined.       
 

Lemma isweq_doublehfp_from { Tll' Tll Tlr Tur } ( f'l : Tll' -> Tll ) ( fl : Tll -> Tlr ) ( gr : Tur -> Tlr ) : isweq ( doublehfp_from f'l fl gr ) . 
Proof . intros . apply gradth with ( doublehfp_to f'l fl gr ) .  exact ( doublehfp_from_to f'l fl gr ) . exact ( doublehfp_to_from f'l fl gr ) . Defined. 


(** Note: change these in uu0.v *)
 
Definition hfibersgtof'  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr g' f' g f ) ( x : X ) ( ze : hfiber g x ) : hfiber f' ( f x )  .
Proof. intros . split with ( g' ( pr1 ze ) ) .    apply ( pathscomp0  ( h ( pr1 ze ) )  ( maponpaths f ( pr2 ze ) )  ) . Defined . 

Definition hfibersg'tof  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr g' f' g f ) ( x' : X' ) ( ze : hfiber g' x' ) : hfiber f ( f' x' )  .
Proof. intros . split with ( g ( pr1 ze ) ) .    apply ( pathscomp0 ( pathsinv0 ( h ( pr1 ze ) ) ) ( maponpaths f' ( pr2 ze ) ) ) . Defined . 




(** ** Pre-towers and towers of types 

A tower of types can be viewed either as an infinite sequence of functions ... -> T_{n+1} -> T_n -> ... -> T_0 or as a coinductive object as in [tower] below.
We call such infinite sequences of functions pre-towers and coinductive opbjects towers. 
In its coinductive version a tower is essentially a rooted tree of infinite (countable) depth with the collection of branches leaving each node parametrized by a  arbitrary type. 


*)

(** *** Pre-towers of types - the sequence of functions definition. *)

Definition pretower := total2 ( fun T : nat -> Type => forall n : nat , T ( S n ) -> T n ) . 

Definition pretowerpair ( T : nat -> Type ) ( p : forall n : nat , T ( S n ) -> T n ) : pretower := tpair ( fun T : nat -> Type => forall n : nat , T ( S n ) -> T n ) T p . 

Definition preTn ( pT : pretower ) ( n : nat ) : Type := pr1 pT n .

Coercion preTn : pretower >-> Funclass .  

Definition pretowerpn ( pT : pretower ) ( n : nat ) : pT ( S n ) -> pT n := pr2 pT n . 


(** Pre-tower functions. *)

Definition pretowerfun ( pT pT' : pretower ) : Type := total2 ( fun fn : forall n : nat , pT n -> pT' n => forall n : nat , homot ( funcomp ( fn ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( fn n ) ) ) . 

Definition pretowerfunconstr ( pT pT' : pretower ) ( fn : forall n : nat , pT n -> pT' n ) ( hn : forall n : nat , homot ( funcomp ( fn ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( fn n ) ) ) : pretowerfun pT pT' := tpair _ fn hn . 

Definition prefn { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( n : nat ) : pT n -> pT' n := pr1 f n . 

Coercion prefn : pretowerfun >-> Funclass .  

Definition prehn { pT pT' : pretower }  ( f : pretowerfun pT pT' ) ( n : nat ) : homot ( funcomp ( prefn f ( S n ) ) ( pretowerpn pT' n ) ) ( funcomp ( pretowerpn pT n ) ( prefn f n ) ) := pr2 f n . 

Definition pretowerweq ( pT pT' : pretower ) : Type := total2 ( fun f : pretowerfun pT pT' => forall n : nat , isweq ( prefn f n ) ) . 

Definition pretoweridfun ( T : pretower ) : pretowerfun T T := pretowerfunconstr T T ( fun n => idfun _ ) ( fun n => fun z => idpath _ ) .

Definition pretowerfuncomp { T T' T'' : pretower } ( f : pretowerfun T T' ) ( g : pretowerfun T' T'' ) : pretowerfun T T'' := pretowerfunconstr T T'' ( fun n => funcomp ( f n ) ( g n ) ) ( fun n => fun z => pathscomp0 ( prehn g n ( f ( S n ) z ) ) ( maponpaths ( g n ) ( prehn f n z ) ) ) . 


(** Pre-tower shifts *)

Definition pretoweroneshift ( pT : pretower )  : pretower := pretowerpair ( fun n => pT ( S n ) ) ( fun n => pretowerpn pT ( S n ) ) .   

Definition pretowerfunoneshift { pT pT' : pretower } ( f : pretowerfun pT pT' ) : pretowerfun ( pretoweroneshift pT ) ( pretoweroneshift pT' ) := pretowerfunconstr   ( pretoweroneshift pT ) ( pretoweroneshift pT' ) ( fun n => f ( S n ) ) ( fun n => prehn f ( S n ) ) . 

(** Pre-tower pull-backs *) 


Definition pretowerpb_a ( pT : pretower ) { X : Type } ( f : X -> pT 0 ) ( n : nat ) : total2 ( fun pretowerpbsn : Type => pretowerpbsn -> pT n ) . 
Proof . intros . induction n .

split with X . exact f . 

split with ( hfp ( pr2 IHn ) ( pretowerpn pT n ) ) . exact ( hfppru ( pr2 IHn ) ( pretowerpn pT n ) ) .  Defined. 

Definition pretowerpb ( pT : pretower ) { X : Type } ( f : X -> pT 0 ) : pretower := pretowerpair ( fun n => pr1 ( pretowerpb_a pT f n ) ) ( fun n => hfpprl ( pr2 ( pretowerpb_a pT f n ) ) ( pretowerpn pT n ) ) .

Definition pretowerpbpr ( pT : pretower ) { X : Type } ( f : X -> pT 0 ) : pretowerfun ( pretowerpb pT f ) pT := pretowerfunconstr ( pretowerpb pT f ) pT ( fun n => pr2 ( pretowerpb_a pT f n ) ) ( fun n => commhfp ( pr2 ( pretowerpb_a pT f n ) ) ( pretowerpn pT n ) ) . 



Definition pretowerfunct_a { pT' pT : pretower } { X X' : Type } ( g' : X' -> pT' 0 ) ( f' : pretowerfun pT' pT ) ( g : X' -> X ) ( f : X -> pT 0 ) ( h : commsqstr g f g' ( f' 0 ) ) ( n : nat ) : total2 ( fun fto : pretowerpb pT' g' n -> pretowerpb pT f n => commsqstr  fto ( pretowerpbpr pT f n ) ( pretowerpbpr pT' g' n ) ( f' n ) ) .  
Proof. intros. induction n as [ | n IHn ] . 

refine ( tpair _ _ _ ) .  { exact g . } { exact h . }

destruct IHn as [ fto hn ] . refine ( tpair _ _ _ ) . 

{ exact ( hfpfunct ( f' n ) ( pretowerpn pT' n ) ( pretowerpn pT n ) ( f' ( S n ) ) ( pretowerpbpr pT' g' n ) ( pretowerpbpr pT f n ) fto ( prehn f' n ) hn ) . } 

{ exact ( fun z => idpath _ ) . } Defined. 


 
Definition pretowerpbfunct { pT' pT : pretower } { X X' : Type } ( g' : X' -> pT' 0 ) ( f' : pretowerfun pT' pT ) ( g : X' -> X ) ( f : X -> pT 0 ) ( h : commsqstr g f g' ( f' 0 ) ) : pretowerfun ( pretowerpb pT' g' ) ( pretowerpb pT f ) . 
Proof. intros . split with ( fun n => pr1 ( pretowerfunct_a g' f' g f h n ) ) . intro n . intro xze . destruct xze as [ [ x z ] e ] . apply idpath . exact ( hfpfunct_h_back  ( f' n ) ( pretowerpn pT' n ) ( pretowerpn pT n ) ( f' ( S n ) ) ( pretowerpbpr pT' g' n ) ( pretowerpbpr pT f n ) ( pr1 ( pretowerfunct_a g' f' g f h n ) ) ( prehn f' n ) ( pr2 ( pretowerfunct_a g' f' g f h n ) ) n ) . 







Definition doublepretowerpb_from_a ( pT : pretower ) { X X' : Type } ( g : X' -> X ) ( f : X -> pT 0 ) ( n : nat ) : total2 ( fun fto : pretowerpb pT ( funcomp g f ) n -> pretowerpb ( pretowerpb pT f ) g n => homot ( pretowerpbpr pT ( funcomp g f ) n ) ( funcomp ( funcomp fto ( pretowerpbpr ( pretowerpb pT f ) g n ) ) ( pretowerpbpr pT f n ) ) ) .
Proof. intros .  induction n as [ | n IHn ] .

{ split with ( fun x => x ) . intro . apply idpath . }

{ set ( fn := pretowerpbpr pT f n ) . set ( gn := pretowerpbpr ( pretowerpb pT f ) g n ) . set ( pn := pretowerpn pT n ) . destruct IHn as [ fto en ] . refine ( tpair _ _ _ ) .  

  { intro xze .  set ( xze' := hfplhomot en ( pretowerpn pT n ) xze : hfp ( funcomp ( funcomp fto gn ) fn ) pn  ) .  unfold  pretowerpb . unfold pretowerpb .  simpl . change ( hfp gn ( hfpprl fn pn ) ) . apply doublehfp_to . 
 apply ( hfppru fto ( hfpprl ( funcomp gn fn ) pn ) ) .  apply doublehfp_to . apply xze' . }

  { intro xze .  destruct xze as [ [ x z ] e ] . apply idpath . }} 

Defined . 


Definition doublepretowerpb_from ( pT : pretower ) { X X' : Type } ( g : X' -> X ) ( f : X -> pT 0 ) : pretowerfun ( pretowerpb pT ( funcomp g f ) ) ( pretowerpb ( pretowerpb pT f ) g ) . 
Proof. intros . refine ( pretowerfunconstr _ _ _ _ ) . 

{ intro n .  exact ( pr1 ( pretowerpb_trans_a pT g f n ) ) . } 

{ intro n .  intro xze . destruct xze as [ [ x z ] e ] . simpl .  destruct ( pretowerpb_trans_a pT g f n ) . apply idpath . } 

Defined. 


(** Pre-tower fibers *)



Definition pretfib { pT : pretower } ( t : pT 0 ) : pretower := pretoweroneshift ( pretowerpb pT ( fromunit t ) ) . 

Definition pretfibj { pT : pretower } ( t : pT 0 ) : pretowerfun ( pretfib t ) ( pretoweroneshift pT ) := pretowerfunoneshift ( pretowerpbpr pT ( fromunit t ) ) . 


(* To be removed:

Definition pretfib_Tn_jn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : total2 ( fun pretfibn : Type => pretfibn -> pT ( S n ) ) .
Proof . intros . induction n .  

split with (hfiber ( pretowerpn pT O ) t ) .  exact pr1 . 

split with ( hfp ( pr2 IHn ) ( pretowerpn pT ( S n ) ) ) . exact ( hfppru ( pr2 IHn ) ( pretowerpn pT ( S n ) ) ) . Defined. 

Definition pretfib_Tn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : Type := pr1 ( pretfib_Tn_jn pT t n ) . 

Definition pretfib_jn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : pretfib_Tn pT t n -> pT ( S n ) := pr2 (  pretfib_Tn_jn pT t n ) . 

Definition pretfib_pn ( pT : pretower ) ( t : pT 0 ) ( n : nat ) : pretfib_Tn pT t ( S n ) -> pretfib_Tn pT t n .
Proof. intros pT t n .  exact ( hfpprl ( pr2 ( pretfib_Tn_jn pT t n ) ) ( pretowerpn pT ( S n ) ) ) . Defined. 

Definition pretfib { pT : pretower } ( t : pT 0 ) : pretower := pretowerpair ( pretfib_Tn pT t ) ( pretfib_pn pT t ) . 

Lemma pr0pretfib ( pT : pretower ) ( t : pT 0 ) : paths ( pretfib t  0 ) ( hfiber ( pretowerpn pT O ) t ) . 
Proof. intros. apply idpath .  Defined. 

Definition pretowerfuntfib_a { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( t : pT 0 ) ( n : nat ) : total2 ( fun funtfibn : ( pretfib t n ) -> ( pretfib ( f 0 t ) n ) => commsqstr ( f ( S n ) ) ( pretfibj ( f 0 t ) n ) ( pretfibj t n ) funtfibn ) .
Proof. intros pT pT' f t n . induction n as [ | n IHn ] .  

split with ( hfibersgtof' ( f 0 ) ( pretowerpn pT' 0 ) ( pretowerpn pT 0 ) ( f 1 ) ( prehn f 0 ) t ) . intro . About commsqstr .  apply idpath . ???


split with ( hfpfunct ( f ( S n ) ) ( pretowerpn pT ( S n ) ) ( pretowerpn pT' ( S n ) ) ( f ( S ( S n ) ) )  ( pretfibj pT t n ) ( pretfibj pT' ( f 0 t ) n ) ( pr1 IHn ) ( prehn f ( S n ) ) ( pr2 IHn ) ) .  intro. apply idpath .  Defined. 

*)

Definition pretowerfuntfib { pT pT' : pretower } ( f : pretowerfun pT pT' ) ( t : pT 0 ) : pretowerfun ( pretfib t ) ( pretfib ( f 0 t ) ) .
Proof. intros.  apply pretowerfunoneshift.  apply ( pretowerpb_trans pT ( fromunit t ) ???? . 


Definition pretfibtopretoweroneshift ( pT : pretower ) ( t0 : pT 0 ) : pretowerfun ( pretfib t0 ) ( pretoweroneshift pT ) := pretowerfunconstr ( pretfib t0 ) ( pretoweroneshift pT ) ( pretfibj pT t0 ) ( fun n => fun z => ( pr2 z ) ) .  

Definition pretfibofpretoweroneshift_a ( pT : pretower ) ( t1 : pT 1 ) ( n : nat ) ( t : @pretfib ( pretoweroneshift pT ) t1 n ) : @pretfib ( @pretfib pT ( pretowerpn pT 0 t1 ) ) ( tohfiber ( pretowerpn pT 0 ) t1 ) n . 
Proof. intros .  induction n .  ???

Definition pretfibofpretoweroneshift ( pT : pretower ) ( t1 : pT 1 ) : pretowerfun ( @pretfib ( pretoweroneshift pT ) t1 ) ( @pretfib ( @pretfib pT ( pretowerpn pT 0 t1 ) ) ( tohfiber ( pretowerpn pT 0 ) t1 ) ) .
Proof.   intros . ???





Definition prenshift ( n : nat ) ( pT : pretower ) : pretower .
Proof. intros . induction n as [| n IHn] . exact pT . exact ( pretoweroneshift IHn ). Defined. 








(** *** Towers of types - the coinductive definition. *)

CoInductive tower := towerconstr : forall T0 : Type, ( T0 -> tower ) -> tower .

Definition pr0 ( T : tower ) : Type .
Proof. intro . destruct T as [ T' S' ] . exact T' . Defined. 

Definition tfib { T : tower } ( t : pr0 T ) : tower .
Proof. intro. destruct T as [ T' S' ] . exact S' . Defined. 

Definition oneshift ( T : tower ) : tower := towerconstr ( total2 ( fun t : pr0 T => pr0 ( tfib t ) ) ) ( fun tf => tfib ( pr2 tf ) ) .

Definition nshift ( n : nat ) ( T : tower ) : tower .
Proof. intros . induction n as [| n IHn] . exact T . exact (oneshift IHn). Defined. 



CoInductive towerfun : forall ( T T' : tower ) , Type := towerfunconstr : forall ( T T' : tower ) ( f0 : pr0 T -> pr0 T' ) ( ff : forall t0 : pr0 T , towerfun ( tfib t0 ) ( tfib ( f0 t0 ) ) ) , towerfun T T' . 

Definition towerfunpr0 { T T' : tower } ( f : towerfun T T' ) : pr0 T -> pr0 T' .
Proof. intros T1 T2 f G . destruct f as [ T T' f0 ff ] .  exact ( f0 G ) . Defined. 

Definition towerfuntfib { T T' : tower } ( f : towerfun T T' ) ( t : pr0 T ) : towerfun ( tfib t ) ( tfib ( towerfunpr0 f t ) ) .
Proof. intros. destruct f as [ T T' f0 ff ] . exact ( ff t ).  Defined.

CoFixpoint toweridfun ( T : tower ) : towerfun T T := towerfunconstr T T ( fun x => x ) ( fun t0 => toweridfun ( tfib t0 ) ) .

CoFixpoint towerfuncomp { T T' T'' : tower } ( f : towerfun T T' ) ( g : towerfun T' T'' ) : towerfun T T'' := towerfunconstr T T'' ( fun x => towerfunpr0 g ( towerfunpr0 f x ) ) ( fun x : pr0 T => @towerfuncomp ( tfib x ) ( tfib ( towerfunpr0 f x ) ) ( tfib ( towerfunpr0 g ( towerfunpr0 f x ) ) ) ( towerfuntfib f x ) ( towerfuntfib g ( towerfunpr0 f x ) ) )  . 






(** *** Equivalence between towers and pre-towers *)

(** Towers from pre-towers *)



CoFixpoint towerfrompretower ( pT : pretower )  : tower := towerconstr ( prepr0 pT ) ( fun t => towerfrompretower ( @pretfib pT t ) ) .

CoFixpoint towerfrompretowerfun { pT pT' : pretower } ( f : pretowerfun pT pT' ) : towerfun ( towerfrompretower pT ) ( towerfrompretower pT' ) := towerfunconstr ( towerfrompretower pT ) ( towerfrompretower pT' )  ( f 0 ) ( fun t0 => @towerfrompretowerfun ( @pretfib pT t0 ) ( @pretfib pT' ( f 0 t0 ) ) ( pretowerfuntfib f t0 ) ) . 
Definition tfib_t_from_pt ( pT: pretower ) ( t : pT O ) : paths ( towerfrompretower ( @pretfib pT t ) ) ( @tfib ( towerfrompretower pT ) t ) . 
Proof. intros .   apply idpath . Defined .

Lemma oneshift_t_from_pt_to ( pT : pretower ) : towerfun ( towerfrompretower ( pretoweroneshift pT ) ) ( oneshift ( towerfrompretower pT ) ) . 
Proof. intro . cofix. split with ( tococonusf ( pretowerpn pT O ) ) .  intro t1 .  

set (tinhfiber := pr2 ( tococonusf ( pretowerpn pT O ) t1 )  : hfiber ( pretowerpn pT 0 ) ( pretowerpn pT 0 t1 ) ) . change (@tfib ( oneshift ( towerfrompretower pT ) ) (tococonusf (pretowerpn pT 0) t1 ) ) with (@tfib ( towerfrompretower ( @pretfib pT ( pretowerpn pT 0 t1 ) ) )  tinhfiber ) . 

apply ( fun f => @towerfuntfib ( towerfrompretower ( pretoweroneshift pT ) ) ( towerfrompretower (  @pretfib pT ( pretowerpn pT 0 t1 ) ) ) f t1 ) .   . simpl . 


  Defined. 


(** Pre-towers from towers *)

Definition Tn ( T : tower ) ( n : nat ) : Type := pr0 (nshift n T).

Coercion Tn : tower >-> Funclass . 

Lemma TSn ( T :tower ) ( n : nat ) : paths ( T ( S n ) ) ( total2 ( fun t : T n => pr0 ( tfib t ) ) ) .  
Proof. intros . apply idpath . Defined. 


Definition pn ( T : tower ) ( n : nat ) : T ( S n ) -> T n := @pr1 _ ( fun t : pr0 ( nshift n T ) => pr0 ( tfib t ) ) . 

Definition pretowerfromtower ( T : tower ) : pretower := pretowerpair ( fun n => T n ) ( fun n => pn T n ) . 


(** Pre-towers from towers from pre-towers *)

Definition TnpretopreTn ( pT : pretower ) ( n : nat ) : Tn ( towerfrompretower pT ) n  -> preTn pT n .
Proof. intros pT n .  induction n . 

intro x . exact x .

intro x . unfold towerfrompretower in x . unfold Tn in x .  simpl in x .  




Definition weqTnpre ( pT : pretower ) ( n : nat ) : weq ( towerfrompretower pT n ) ( preTn pT n ) . 
Proof. intros . 

assert   



Lemma pttpt_to_id_fun ( pT : pretower ) : pretowerfun ( pretowerfromtower ( towerfrompretower pT ) ) pT .
Proof. intro. 








Definition fiberfloor { n : nat } { T : tower } ( tn : T n ) := pr0 ( tfib tn ) . 

(* Useful formulas:

towerfloor (1+n) T := total2 ( fun G : towerfoloor n T => fiberfloor G ) 

@tfib (1+n) T ( tpair _ G G' ) := @tfib (tfib G) G'

*) 

Definition fiberfloortotowerfloor { n : nat } { T : tower } ( tn : T n ) ( t' : fiberfloor tn ) : T ( S n ) := tpair _ tn t' .



(** *** The type of functions berween towers *)




Definition towerfunfiberfloor { T T' : tower } ( f : towerfun T T' ) { G : pr0 T } : @fiberfloor 0 _ G -> @fiberfloor 0 _ ( towerfunpr0 f G ) := towerfunpr0 ( towerfuntfib f G ) .

Definition towerfunnshift { T T' : tower } ( n : nat ) ( f : towerfun T T' ) : towerfun ( nshift n T ) ( nshift n T' ) .
Proof.  intros . induction n as [ | n IHn ] .  exact f .  apply towerfunconstr with ( fun tf => tpair _ ( towerfunpr0 IHn (pr1 tf) ) ( towerfunfiberfloor IHn (pr2 tf) ) ) .  intro t0 . apply ( towerfuntfib ( towerfuntfib IHn ( pr1 t0 ) ) ( pr2 t0 ) ) . Defined. 

Definition towerfunonfloors { n : nat } { T T' : tower } ( f : towerfun T T' ) :  T n -> T' n := towerfunpr0 ( towerfunnshift n f ) . 

Definition towerfunontowersovers  { n : nat } { T T' : tower } ( f : towerfun T T' ) ( G : T n ) : towerfun ( tfib G ) ( tfib ( towerfunonfloors f G ) ) := towerfuntfib ( towerfunnshift n f ) G .


(** An example of a function between towers *)


CoFixpoint towerstrmap ( T : tower ) ( t0 : pr0 T ) : towerfun ( tfib t0 ) T := towerfunconstr _ _ ( fun x => t0 ) ( fun t1 => towerstrmap ( tfib t0 ) t1 ) .   
 

(** *** The type of homotopies between functions of towers *)















(* Some constructions related to tower shifts *)


Definition mnshiftfun ( m n : nat ) ( T : tower ) : towerfun ( nshift m ( nshift n T ) ) ( nshift ( m + n ) T ) .
Proof. intros . induction m . 

apply toweridfun . 

set ( onfloors := ( fun G' => tpair _ (towerfunpr0 IHm (pr1 G')) (towerfunfiberfloor IHm  (pr2 G' ) ) )  :  (nshift n T) (S m) -> T (S (m + n))) .   

split with onfloors . intro G .  apply ( towerfuntfib ( towerfuntfib IHm (pr1 G) ) (pr2 G) ) . Defined. 

Definition mnfloorfun { m n : nat } { T : tower } ( G : ( nshift n T ) m  ) : T ( m + n )  := towerfunpr0 ( mnshiftfun m n T ) G . 


Definition tfibtotop { n : nat } { T : tower } ( G : T n  ) : towerfun ( tfib G ) ( nshift  ( S n ) T ).
Proof. intros. 

split with ( fun G' : pr0 ( tfib G ) => tpair ( fun G : T n  => pr0 ( tfib G ) ) G G' ) .  

intro G' . apply toweridfun . Defined. 

Definition fiberfloortofloor { n m : nat } { T : tower } ( G : T n  ) ( G' : ( tfib G ) m  ) : T ( m + ( S n ) )  . 
Proof. intros. apply ( mnfloorfun ( towerfunonfloors ( tfibtotop G ) G' ) ) . Defined. 


(* Extending a tower with a unit type *)

Definition towerunitext ( T : tower ) : tower := towerconstr unit ( fun x : unit => T ) . 

(* Extended tower over a node G : T n *)

Definition tfibplus { n : nat } { T : tower } ( G : T n ) := towerconstr unit ( fun x => tfib G ) . 

Definition fromtfibplus { n : nat } { T : tower } ( G : T n ) : towerfun ( tfibplus G ) ( nshift n T ) .
Proof .  intros .  split with ( fun x => G ) . intro . apply ( toweridfun (tfib G) ) .  Defined. 



(* The type of carriers of B-systems - towers together with a one step ramification at each floor except for the ground floor. *)


Definition bsyscar := total2 ( fun T : tower => forall ( n : nat ) ( GT : T ( S n )  ) , Type ) . 
Definition bsyscarpair ( T : tower ) ( btilde : forall ( n : nat ) ( GT : T ( S n )  ) , Type ) : bsyscar := tpair _ T btilde . 

Definition bsyscartotower ( B : bsyscar ) := pr1 B .

Coercion bsyscartotower : bsyscar >-> tower.


Definition Btilde { n : nat } { B : bsyscar } ( GT : B ( S n ) ) : Type := pr2 B n GT . 

Definition bsyscarover { n : nat } { B : bsyscar } ( G : B n ) : bsyscar := bsyscarpair ( tfibplus G ) ( fun m : nat => fun DT : ( tfibplus G ) ( S m )  => @Btilde ( ( m + n ) ) B ( towerfunpr0 ( mnshiftfun ( S m ) n B ) ( towerfunonfloors ( fromtfibplus G ) DT ) ) ) .    




(* The type of functions between bsystemcarrier's *)

Definition bsyscarfun ( B B' : bsyscar ) := total2 ( fun f : towerfun B B' => forall ( n : nat ) ( GT : B ( S n ) ) , Btilde GT -> Btilde ( @towerfunonfloors (S n) _ _ f GT ) ) . 

Definition bsyscarfuntotowerfun ( B B' : bsyscar ) : bsyscarfun B B' -> towerfun B B' := pr1 .
Coercion bsyscarfuntotowerfun : bsyscarfun >-> towerfun .

Definition Bnfun { n : nat } { B B' : bsyscar } ( f : bsyscarfun B B' ) ( G : B n ) : B' n := @towerfunonfloors n _ _ f G .

Definition Btildefun { n : nat } { B B' : bsyscar } ( f : bsyscarfun B B' ) { GT : B (S n ) } ( t : Btilde GT ) : Btilde ( Bnfun f GT ) := pr2 f n GT t .

(* Structures on bsystemcarriers which together form the data of a B-system. *)

(* Operation Tops : ( Gamma, x:T |- ) => ( Gamma , Delta |- ) => ( Gamma, x:T, Delta |- ) *)

Definition Tops ( B : bsyscar ) := forall ( n : nat ) ( G : B n ) ( GT : pr0 ( tfib G ) ) , towerfun ( tfib G ) ( tfib GT ) .

(* Operation Ttildeops : ( Gamma, x:T |- ) => ( Gamma , Delta |- s : S ) => ( Gamma, x:T, Delta |- s : S ) *)

Definition Ttildeops ( B : bsyscar ) ( Top : Tops B ) := forall ( n m : nat ) ( G : towerfloor n B ) ( GT : tfib G ) ( GDS : towerfloor ( S m ) ( tfib G ) ) ( s : BT ( fiberfloortofloor ( pr1 GT ) GDS ) ) , BT ( fiberfloortofloor GT ( towerfunonfloors ( Top _ GT ) GDS ) ) .  

(* note - B for bsyscar, G : towerfloor n B , T : tfib G *)


(* Operation Sops : ( Gamma |- s : S ) => ( Gamma , x:S, Delta |- ) => ( Gamma, Delta[s/x] |- ) *)

Definition Sops ( B : bsyscar ) := forall ( n : nat ) ( G : towerfloor ( S n ) B ) ( s : BT G ) , towerfun ( @tfib (nshift (S n) B ) G ) ( @tfib (nshift n B ) ( pr1 G ) ) . 

(* Operation Stildeops : ( Gamma |- s : S ) => ( Gamma , x:S, Delta |- r : R ) => ( Gamma, Delta[s/x] |- r[s/x]:R[s/x]) *)

Definition Stildeops ( B : bsyscar ) ( Sop : Sops B ) := forall ( n m : nat ) ( GS : pr0 ( nshift ( S n ) B ) ) ( s : BT GS ) ( GSDR : towerfloor ( S m ) ( tfib GS ) ) ( r : BT ( fiberfloortofloor GS GSDR ) ) , BT ( fiberfloortofloor ( pr1 GS ) ( towerfunonfloors ( Sop _ _ s ) GSDR ) ) .  

(* Operation deltaops : ( Gamma, x:T |- ) => ( Gamma, x : T |- x : T ) *)

Definition deltaops ( B : bsyscar ) ( Top : Tops B ) := forall ( n : nat ) ( GT : towerfloor ( S n ) B ) , BT ( fiberfloortotowerfloor GT ( towerfunpr0 ( Top n GT ) ( pr2 GT )  ) ) .   


(* End of the file bsystems.v *)