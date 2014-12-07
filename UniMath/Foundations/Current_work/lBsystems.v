(** * Definition of B-systems using the length function.

Vladimir Voevodsky. 

Started December 3, 2014. 

A companion code to the paper "B-systems". 

*)


Unset Automatic Introduction.

Require Export Foundations.hlevel2.finitesets.



(** ** Non-unital pre-l-B-systems *)

(** *** l-B-system carriers. *)

Definition lBsystem_carrier := total2 ( fun BB : total2 ( fun BtildeB : dirprod UU UU =>
                                          dirprod ( pr1 BtildeB -> pr1 BtildeB )
                                                  ( pr2 BtildeB -> pr1 BtildeB ) ) =>
                                          pr1 ( pr1 BB ) -> nat ) .

Definition Btype : lBsystem_carrier -> UU := fun BB => pr1 ( pr1 ( pr1 BB ) ) . 
Coercion Btype : lBsystem_carrier >-> UU .

Definition Tilde : lBsystem_carrier -> UU := fun BB => pr2 ( pr1 ( pr1 BB ) ) .

Definition ft { BB : lBsystem_carrier } : BB -> BB := pr1 ( pr2 ( pr1 BB ) ) .

Definition fti { BB : lBsystem_carrier } ( i : nat ) : BB -> BB := iteration ( @ft BB ) i . 

Definition dd { BB : lBsystem_carrier } : Tilde BB -> BB := pr2 ( pr2 ( pr1 BB ) ) .

Definition ll { BB : lBsystem_carrier } : BB -> nat := pr2 BB .


(** *** l-B-sytems operations T, Tt, S, St.

Since we have to work with operations that are not everywhere defined we start by 
naming their domains of definitions and then defining operations as total operations
on the domeains of definition. This has the advantage that when we need to state and
prove results that involve compositions of operations we can conveniently package 
the proofs that the compositive operations are defined in definition of functions 
such as the function ??? below. 

*)


(** **** Operation(s) T  *)

Definition T_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) :=
  total2 ( fun gts : dirprod ( ll X1 > 0 ) ( ll X2 >= ll X1 ) =>
             ft X1 = fti ( 1 + ( ll X2 - ll X1 ) ) X2 ) . 

Definition T_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) ,
    total2 ( fun R : BB => ( ll R ) = 1 + ( ll X2 ) ) .

Definition Ti { BB : lBsystem_carrier } ( T_op : T_ops_type BB ) { X1 X2 : BB }
           ( inn : T_dom X1 X2 ) : BB :=
  pr1 ( T_op X1 X2 inn ) .


(** **** Operation(s) Tt  *)

Definition Tt_dom { BB : lBsystem_carrier } ( X : BB ) ( s : Tilde BB ) :=
  total2 ( fun gts : dirprod ( ll X > 0 ) ( ll ( dd s ) >= ll X ) =>
             ft X = fti ( 1 + ( ll ( dd s ) - ll X ) ) ( dd s ) ) . 
            
Definition Tt_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) ,
    total2 ( fun R : Tilde BB => ( ll ( dd R ) ) = ( 1 + ll ( dd s ) ) ) .



(* **** Operation(s) S  *)


Definition S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :=
  total2 ( fun gts : ll Y >= ll ( dd r ) =>
             dd r = fti ( 1 + ( ll Y - ll ( dd r ) ) ) Y ) .
    

Definition S_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ,
    total2 ( fun R : BB => ( ll R ) = ( ll Y ) - 1 ) .


(** **** Operation(s) St  *)


Definition St_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( s : Tilde BB ) :=
  total2 ( fun gts : ll ( dd s ) >= ll ( dd r ) =>
             dd r = fti ( 1 + ( ll ( dd s ) - ll ( dd r ) ) ) ( dd s ) ) .
    

Definition St_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) ,
    total2 ( fun R : Tilde BB => ( ll ( dd R ) ) = ( ll ( dd s ) ) - 1 ) .



(** *** Non-unital pre-l-Bsystems, definition. *)

Definition nu_pre_lBsystem :=
  total2 ( fun BB : lBsystem_carrier =>
             dirprod ( dirprod ( T_ops_type BB ) ( Tt_ops_type BB ) )
                     ( dirprod ( S_ops_type BB ) ( St_ops_type BB ) ) ) .


Definition nu_pre_lBsystem_to_lBsystem_carrier : nu_pre_lBsystem -> lBsystem_carrier := pr1 .
Coercion nu_pre_lBsystem_to_lBsystem_carrier : nu_pre_lBsystem >-> lBsystem_carrier .


Definition T { BB : nu_pre_lBsystem } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  BB := pr1 ( ( pr1 ( pr1 ( pr2 BB ) ) ) X1 X2 inn ) .

Definition Tt { BB : nu_pre_lBsystem } { X : BB } { s : Tilde BB } ( inn : Tt_dom X s ) :
  Tilde BB := pr1 ( ( pr2 ( pr1 ( pr2 BB ) ) ) X s inn ) .

Definition Si { BB : nu_pre_lBsystem } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  BB := pr1 ( ( pr1 ( pr2 ( pr2 BB ) ) ) r Y inn ) .
    
Definition Sti { BB : nu_pre_lBsystem } { r : Tilde BB } { s : Tilde BB } ( inn : St_dom r s ) :
  Tilde BB := pr1 ( ( pr2 ( pr2 ( pr2 BB ) ) ) r s inn ) .



(* ** Non-unital l-B0-systems. *) 


Definition Ti_ax0_a { BB : ne_pre_lBsystem } := forall ( i : nat ) ( gti : i > 0 ) ( X1 X2 : BB )
                                                     ( gtX1 : ll X1 > 0 ) ( gtX2 : ll X2 > 0 )
                                                     ( iseq : ft X1 = fti ( 1 + i ) X2 ) ,
                                                  ft ( Ti i gtX1 gtX2 iseq ) = ...








(* End of the file lBsystems.v *)


