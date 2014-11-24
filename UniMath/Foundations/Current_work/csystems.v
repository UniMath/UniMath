Require Export Foundations.hlevel2.hnat .
Require Export RezkCompletion.precategories.

(* Import uu0.PathNotations.*)

Unset Automatic Introduction.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g)(at level 50). 

(* To precategories? *)


Definition weakcomp { C : precategory_data } { X Y Y' Z : C } ( f : X --> Y ) ( g : Y' --> Z ) ( e : Y = Y' ) : 
X --> Z := ( transportf ( fun A : C => ( X --> A ) ) e f ) ;; g  . 


(* *)

Definition ft_data ( C :  precategory_ob_mor ) := total2 ( fun ftd : C -> C => forall X : C , X --> ftd X ) .  

Definition ftX ( C : precategory_ob_mor ) ( ftd : ft_data C ) : C -> C := pr1 ftd . 
Coercion ftX : ft_data >-> Funclass . 

Definition pX { C : precategory_ob_mor } { ftd : ft_data C } ( X : C ) : X --> ftd X := pr2 ftd X .

(* *)

Definition q_data { C : precategory_ob_mor } ( ftd : ft_data C ) ( l : C -> nat ) := 
 forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , total2 ( fun fstarX : C => fstarX --> X ) .   

Definition fstar { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } (qd : q_data ftd l ) 
 { X : C } { Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) := 
 pr1 ( qd X Y is f ) . 

Definition qof { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l )
 { X Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) : 
  fstar qd is f --> X := pr2 ( qd X Y is f ) . 

Definition weakq { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l ) 
           { X : C } { X' Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> X' ) ( e : X' = ftd X ) : 
  total2 ( fun fstarX => fstarX --> X ) := qd X Y is ( transportf ( fun A : C => ( Y --> A ) ) e f ) . 


           

(* 

A problem arises with the following definition since one of the morphisms f or ( pX ftd ( fstar qd is f ) ) 
need to be transported along the equality fteq in order for the composition  ( pX ftd ( fstar qd is f ) ) ;; f 
to be defined. Therefore we have to use weakcomp  *) 


Definition C0sysax5a { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l ) :=
  forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , natgth ( l ( fstar qd is f ) ) 0  .

Definition C0sysax5b { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } ( qd : q_data ftd l ) :=
  forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , ftd ( fstar qd is f ) = Y .

Definition C0sysax5c { C : precategory_data } { ftd : ft_data C } { l : C -> nat } { qd : q_data ftd l }
  ( ax : C0sysax5b qd ) := 
  forall ( X Y : C ) ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) , 
               ( weakcomp ( pX ( fstar qd is f ) ) f ( ax X Y is f ) ) = ( qof qd is f ) ;; ( pX X ) . 




Definition C0sysax2 { C : precategory_ob_mor } ( l : C -> nat ) ( ftd : ft_data C ) := 
  forall ( X : C ) , l ( ftd X ) = l X - 1 . 

(* Lemma loffstar { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } { qd : q_data ftd l }
      ( ax2 : C0sysax2 l ftd ) ( ax5a : C0sysax5a qd ) { X : C } { Y : C } ( is : natgth ( l X ) 0 ) ( f : Y --> ftd X ) : 
  l ( fstar qd is f ) = 1 + l Y . 
Proof. intros .  admit . Qed . *)
  

Definition C0sysax1 { C : UU } ( l : C -> nat ) := iscontr ( total2 ( fun X : C => l X = 0 ) ) . 
Definition C0pt { C : UU } { l : C -> nat } ( ax : C0sysax1 l ) : C := pr1 ( pr1  ax ) . 

Definition C0sysax3 { C : precategory_ob_mor } { ftd : ft_data C } { l : C -> nat } { ax : C0sysax1 l } :=
  ftd ( C0pt ax ) = C0pt ax . 

(* Here it might be better to use the standard definition of being a final object *)

Definition C0sysax4 { C : precategory_ob_mor } { l : C -> nat } { ax : C0sysax1 l } := 
  forall X : C , iscontr ( X --> C0pt ax ) . 

Definition C0sysax6 { C : precategory_data } { ftd : ft_data C } { l : C -> nat } { qd : q_data ftd l } :=
  forall ( X : C ) ( is : natgth ( l X ) 0 ) , qd _ _ is ( identity ( ftd X ) ) = tpair _ X ( identity X ) . 

Definition C0sysax7 { C : precategory_data } { ftd : ft_data C } { l : C -> nat } { qd : q_data ftd l } 
  ( ax5a : C0sysax5a qd ) ( ax5b : C0sysax5b qd ) :=
  forall ( X Y Z : C ) ( is : natgth ( l X ) 0 ) ( g : Z --> Y ) ( f : Y --> ftd X ) , 
    qd _ _ is ( g ;; f ) = 
     let is' := ax5a _ _ is f   in tpair _ ( pr1 ( weakq qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) 
          ( ( pr2 ( weakq qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) ;; qof qd is f  ) . 








(* 

Note: continue checking the definition of a C-system as a category with attributes together with additional data.

Then check the connection with categories with families of Peter Dybjer. *)




(* Let's try the definition of a category with attributes instead. 

Definition atr_data_1 ( C : precategory_ob_mor ) := total2 ( fun 

*)





 



(* End of the file csystem.v *)