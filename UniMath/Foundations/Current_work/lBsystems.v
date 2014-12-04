(* * Definition of B-systems using the length function.

Vladimir Voevodsky. 

Started December 3, 2014. 

A companion code to the paper "B-systems". 

*)


Unset Automatic Introduction.

Require Export Foundations.hlevel2.finitesets.



(* ** Non-unital pre-l-B-systems *)


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

Definition Ti_type { BB : lBsystem_carrier } :=
  forall ( i : nat ) ( Y X : BB ) ( gtY : natgth ( ll Y ) 0 )  ( gtX : natgth ( ll X ) i )
         ( iseq : ft Y = fti ( 1 + i ) X ) , BB .

Definition Tti_type { BB : lBsystem_carrier } :=
  forall ( i : nat ) ( Y : BB ) ( r : Tilde BB ) ( gtY : natgth ( ll Y ) 0 )
         ( gtX : natgth ( ll ( dd r ) ) i ) ( iseq : ft Y = fti ( 1 + i ) ( dd r ) ) , Tilde BB .

Definition Si_type { BB : lBsystem_carrier } :=
  forall ( i : nat ) ( s : Tilde BB ) ( X : BB ) ( iseq : dd s = fti ( 1 + i ) X ) , BB .

Definition Sti_type { BB : lBsystem_carrier } :=
  forall ( i : nat ) ( s : Tilde BB ) ( r : Tilde BB ) ( iseq : dd s = fti ( 1 + i ) ( dd r ) ) ,
    BB .



    








(* End of the file lBsystems.v *)


