Unset Automatic Introduction.

Require Export Foundations.hlevel2.finitesets.

(* Standard finite posets and order preserving functions between them. *)  

Notation " 'stnel' ( i , j ) " := ( stnpair _ _  ( ctlong natlth isdecrelnatlth j i ( idpath true ) ) ) ( at level 70 ) .

Definition stnposet ( i : nat ) : Poset .
Proof. intro. unfold Poset . split with ( hSetpair ( stn i ) ( isasetstn i ) ) . unfold po. split with ( fun j1 j2 : stn i => natleh j1 j2 ) . split with ( fun j1 j2 j3 : stn i => istransnatleh j1 j2 j3 ) . exact ( fun j : stn i => isreflnatleh j ) . Defined. 

Definition issmaller { X : Poset } ( x1 x2 : X ) := dirprod ( pr2 X x1 x2 ) ( neg ( paths x1 x2 ) ) . 

Definition ndchains ( i : nat ) ( X : Poset ) := total2 ( fun ndccar: forall j : stn i , X => forall ( j1 j2 : stn i ) ( is : natlth j1 j2 ) , issmaller (ndccar j1 ) (ndccar j2 ) ) . 

Definition ndchainstosequences ( i : nat ) ( X : Poset ) : ndchains i X -> ( stn i ) -> X := fun xstar => fun k => ( pr1 xstar ) k . 
Coercion ndchainstosequences : ndchains >-> Funclass .

Lemma natlthinndchainstn { i j : nat } ( ch : ndchains j ( stnposet i ) ) { j1 j2 : stn j } ( is : natlth j1 j2 ) : natlth ( stntonat _ ( ch j1 ) ) ( stntonat _ ( ch j2 ) ) .
Proof .  intros . 
assert ( is10 : natleh ( stntonat _ ( ch j1 ) ) ( stntonat _ ( ch j2 ) ) ) . apply ( pr1 ( pr2 ch j1 j2 is ) ) . 
assert ( is110 : neg ( paths ( ch j1 ) ( ch j2 ) ) ) . apply ( pr2 ( pr2 ch j1 j2 is ) ) .  
assert ( is11 : natneq ( stntonat _ ( ch j1 ) ) ( stntonat _ ( ch j2 ) ) ) .  apply ( negf ( invmaponpathsincl ( stntonat _ ) ( isinclstntonat _ ) (ch j1 ) ( ch j2 )  ) is110 ) .  
destruct ( natlehchoice _ _ is10 ) as [ l | e ].  apply l . destruct ( is11 e ) .  Defined. 


Definition ndchainsrestr { i j : nat } { X : Poset } ( chs : ndchains j ( stnposet i ) ) ( chX : ndchains i X ) : ndchains j X .
Proof . intros .  split with ( fun k : stn j =>  chX ( chs k ) ) .  intros j1 j2 . intro is . apply ( pr2 chX _ _ ( natlthinndchainstn chs is ) ) . Defined.      


















Definition Ind_tuple ( i : nat ) : total2 ( fun 

FSkXtoUUcat : forall ( X : Poset ) , UU (* FSkXtoUUcat X := sk_i(N(X)) -> N(UU_cat) *)

=> total2 ( fun XtoT : total2 ( fun 

FSkXtoT : forall ( X : Poset ) ( T : UU ) , UU (* FSkXtoT X T := sk_i(N(X)) -> N(T) *)

=>

forall ( X : Poset ) ( T : UU ) ( F : T -> UU ) , FSkXtoT X T -> FSkXtoUUcat X 

)

=> dirprod 

( forall a : FSkXtoUUcat ( stnposet  ( S ( S i ) ) ) , UU ) (* a : sk_i(Delta^{i+1}) -> N(UU_cat) => the type of extensions of a to Delta^{i+1}->N(UU_cat) *)

( total2 ( fun 

Phi :forall ( j : nat ) ( is : natgeh j i ) ( X : Poset ) ( xstar : ndchains ( S j ) X ) ( d : FSkXtoUUcat X )  , FSkXtoUUcat ( stnposet ( S j ) ) 

=> 

forall ( j : nat ) ( is : natgeh j ( S i ) ) ( X : Poset ) ( xstar : ndchains ( S j ) X ) ( di : FSkXtoUUcat X )  ( xstar0 : ndchains ( S ( S i ) ) ( stnposet ( S j ) ) ) ,  paths ( (Phi (S i) (natgehsnn i) (stnposet (S j)) xstar0 (Phi j (istransnatgeh j (S i) i is (natgehsnn i)) X xstar di))) ( Phi (S i) (natgehsnn i) X (ndchainsrestr xstar0 xstar) di )  

)))) .
Proof. intros .   induction i as [ | i IHi].  

(* i=0 *)

split with ( fun X : Poset => ( X -> UU ) ) .
split . 
split with ( fun X => fun T => ( X -> T ) ) .  
exact ( fun X => fun T => fun F => ( fun d => fun x => F ( d x ) ) ) . 
split with ( fun f : stnposet 2 -> UU  => ( f ( stnel(2,0) ) -> f ( stnel(2,1) ) ) ) . 
split with  ( fun j => fun is => fun X => fun xstar => fun d => fun k => d ( xstar k ) ) . 

intros . apply idpath.  

(* i+1 *)

set ( FSkXtoUUcat := pr1 IHi ) . set ( FSkXtoT := pr1 ( pr1 ( pr2 IHi ) ) ) . set ( FSkXtoTcomp := pr2 ( pr1 ( pr2 IHi ) ) ) . set ( FDT := pr1 ( pr2 ( pr2 IHi ) ) ) . set ( Phi := pr1 ( pr2 ( pr2 ( pr2 IHi ) ) ) ) . set ( h := pr2 ( pr2 ( pr2 ( pr2 IHi ) ) ) ) .  simpl in Phi .  simpl in FSkXtoT . simpl in FDT.  simpl in h . 

(*

FSkXtoUUcat X = Hom ( sk_i(N(X)) , N(UU_cat) ) 

FSkXtoT X T := Hom ( sk_i(N(X)) , N(T) )

FSkXtoTcomp X T F := fun d : sk_i(N(X)) -> N(T) => F \circ d 

FDT d = the type of extensions of d : sk_i(Delta^{i+1}) -> N(UU_cat) to functions Delta^{i+1} -> N(UU_cat) 

Phi j is X xstar = restriction map Hom ( sk_i(N(X)) , N(UU_cat) ) -> Hom ( sk_i(Delta^j), N(UU_cat) ) defined by the map xstar:Delta^j -> N(X)

*)

(* First split with Hom ( sk_{i+1}(N(X)), N(UU_cat) ) *)

split with ( fun X => total2 ( fun d : FSkXtoUUcat X => forall xstar : ndchains ( S ( S i ) ) X , FDT ( Phi ( S i ) ( natgehsnn i ) X xstar d ) ) )  . 

split. 

(* we need to define for a poset X and a type T the type of functions sk_{i+1}(N(X)) -> N(T) . We try the following definition. *)

split with ( fun X => fun T => total2 ( fun d : FSkXtoT X T => forall F : T -> UU, forall xstar : ndchains ( S ( S i ) ) X , FDT ( Phi ( S i ) ( natgehsnn i ) X xstar ( FSkXtoTcomp X T F d ) ) ) ) . 

(* now we need the composition map d : sk_i(N(X)) -> N(T) => F \circ d where F : T -> UU *)

intros X T F dsi . destruct dsi as [ d dall ] .  split with ( FSkXtoTcomp X T F d ) .  apply ( dall F ) .  


split.

(* now we need to define for any dsi : sk_{i+1}(Delta^{i+2})-> N(UU_cat) the type of the extensions of dsi to a "functor" Delta^{i+2} -> N(UU_cat) *)

intro dsi . destruct dsi as [ d dfill ] .  

admit. 

assert ( Phi0 : forall j : nat,
               natgeh j (S i) ->
               forall X : Poset,
               ndchains (S j) X ->
               total2
                 (fun d : FSkXtoUUcat X =>
                  forall xstar0 : ndchains (S (S i)) X,
                  FDT (Phi (S i) (natgehsnn i) X xstar0 d)) ->
               total2
                 (fun d0 : FSkXtoUUcat (stnposet (S j)) =>
                  forall xstar0 : ndchains (S (S i)) (stnposet (S j)),
                  FDT (Phi (S i) (natgehsnn i) (stnposet (S j)) xstar0 d0)) ).


intros j is X xstar. 

(* Now we need to define for all j >= i+1 the restriction maps Hom ( sk_{i+1}(N(X)) , N(UU_cat) ) -> Hom ( sk_{i+1}(Delta^j), N(UU_cat) ) defined by
xstar : Delta^j -> N(X) *)

intro d . destruct d as [ di dfdt ] . split with ( Phi j (istransnatgeh _ _ _ is (natgehsnn i)) X xstar di ) . 

intro xstar0.

set ( xstar1 := ndchainsrestr xstar0 xstar ) . 

(* Now we have xstar0 : Delta^{i+1} -> Delta^j , xstar : Delta^j -> N(X) and di : sk_i(N(X)) -> N(UU_cat) and need to define an extension to Delta^{i+1} of the map sk_i(Delta^{i+1}) -> ( sk_i(Delta^{j}) -> sk_i(N(X)) -> N(UU_cat) ) . The idea is that this map equals to the map
sk_i(Delta^{i+1}->Delta^j->N(X)) -> N(UU_cat) for which we have an extesnion  dfdt xstar1 *)

simpl in h . rewrite h . apply ( dfdt xstar1 ) . 

split with Phi0 . 

intros . 