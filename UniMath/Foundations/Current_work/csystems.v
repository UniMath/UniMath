Require Export Foundations.hlevel2.hnat .
Require Export RezkCompletion.precategories.

Import uu0.PathNotations.

Unset Automatic Introduction.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g)(at level 50).

(* *)

Definition ft_data ( C :  precategory_ob_mor ) := total2 ( fun ftd : C -> C => forall X : C , X --> ftd X ) .  

Definition ftX ( C : precategory_ob_mor ) ( ftd : ft_data C ) : C -> C := pr1 ftd . 
Coercion ftX : ft_data >-> Funclass . 

Definition pX { C : precategory_ob_mor } ( ftd : ft_data C ) ( X : C ) : X --> ftd X := pr2 ftd X .

(* *)

Definition q_data { C : precategory_ob_mor } ( ftd : ft_data C ) ( l : C -> nat ) := 
 forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , total2 ( fun fstarX : C => fstarX --> X ) .   

Definition fstar { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } (qd : q_data ftd l ) 
 { X : C } { Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) := 
 pr1 ( qd X Y is f ) . 

Definition qof { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l )
 { X Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) : 
 fstar qd is f --> X := pr2 ( qd X Y is f ) . 

(* 

A problem arises with the following definition since one of the morphisms f or ( pX ftd ( fstar qd is f ) ) need to be transported along the equality fteq in order for the composition  ( pX ftd ( fstar qd is f ) ) ;; f to be defined. 

Definition C0sysax5 { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l ) :=
 forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , total2 ( fun fteq : ftd ( fstar qd is f ) = Y => ( pX ftd ( fstar qd is f ) ) ;; f == ( qof qd is f ) ;; ( pX ftd X ) ) . 

*)

(* 

Note: continue checking the definition of a C-system as a category with attributes together with additional data.

Then check the connection with categories with families of Peter Dybjer. *)




(* Let's try the definition of a category with attributes instead. 

Definition atr_data_1 ( C : precategory_ob_mor ) := total2 ( fun 

*)





 



(* End of the file csystem.v *)