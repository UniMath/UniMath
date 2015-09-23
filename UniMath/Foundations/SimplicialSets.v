(** * Homotopy theory of simplicial sets.

Vladimir Voevodsky

started on Nov. 22, 2014 (with Alexander Vishik) 

*)

Unset Automatic Introduction.

(* Preamble *)

Require Export Foundations.finitesets.
Require Export CategoryTheory.precategories. 
Require Export CategoryTheory.category_hset.
Require Export CategoryTheory.functor_categories.


(* To upstream files *)



(* The pre-category data for the category Delta *)


Definition monfunstn ( n m : nat ) : UU := total2 ( fun f : stn n -> stn m =>
                                                       forall ( x y : stn n ) ( is : x < y ) ,
                                                         f x < f y ) .
Definition monfunstnpair { n m : nat } := tpair ( fun f : stn n -> stn m =>
                                                       forall ( x y : stn n ) ( is : x < y ) ,
                                                         f x < f y ) .
           

Definition monfunstnpr1 ( n m : nat ) : monfunstn n m  -> ( stn n -> stn m ) := pr1 .
Coercion monfunstnpr1 : monfunstn >-> Funclass .

Lemma isasetmonfunstn ( n m : nat ) : isaset ( monfunstn n m ) .
Proof.
  intros . apply ( isofhleveltotal2 2 ) .
  apply impred . 
  intro . apply isasetstn . 
  intro f . apply impred .  intro .  apply impred . intro . apply impred . intro . 
  apply isasetaprop. 
  exact ( pr2 ( f t < f t0 ) ) . 
Defined.

  
Definition monfunstncomp { n m k : nat } ( f : monfunstn n m ) ( g : monfunstn m k ) :
  monfunstn n k .
Proof.
  intros . split with ( funcomp f g ) . intros . unfold funcomp . apply ( pr2 g ) .
  apply ( pr2 f ) . apply is .
Defined.

Lemma monfunstncompassoc { n m k l } ( f : monfunstn n m ) ( g : monfunstn m k )
      ( h : monfunstn k l ) :  ( monfunstncomp f ( monfunstncomp g h ) ) =
                               ( monfunstncomp ( monfunstncomp f g ) h ) .
Proof.
  intros . apply idpath . 
Defined.

Definition monfunstnid ( n : nat ) : monfunstn n n :=
  monfunstnpair ( idfun ( stn n ) ) ( fun x : stn n => fun y : stn n => fun is : x < y => is ) . 

Lemma monfunstncompidr { n m : nat } ( f : monfunstn n m ) : ( monfunstncomp f ( monfunstnid m ) )
                                                             = f .
Proof.
  intros .  unfold monfunstnid . unfold monfunstncomp.  unfold funcomp . simpl . 
  induction f as [ f isf ] . apply idpath .
Defined.

Lemma monfunstncompidl { n m : nat } ( f : monfunstn n m ) : ( monfunstncomp ( monfunstnid n ) f )
                                                             = f .
Proof.
  intros .  unfold monfunstnid . unfold monfunstncomp.  unfold funcomp . simpl . 
  induction f as [ f isf ] . apply idpath .
Defined.


Definition precatDelta : precategory .
Proof.
  refine ( tpair _ _ _ ) . 
  refine ( tpair _ _ _ ) .
  refine ( tpair _ _ _ ) . 
  exact nat . 
  intros n m . (* split with ( monfunstn n m ) . apply isasetmonfunstn . 
  refine ( tpair _ _ _ ) . 
  intros . simpl in * .  apply monfunstnid . 
  intros ? ? ? f g .  simpl in * . apply ( monfunstncomp f g ) . 
  simpl . 
  refine ( tpair _ _ _ ) . 
  refine ( tpair _ _ _ ) .
  intros . simpl in * .  apply monfunstncompidl . 
  intros . simpl in * .  apply monfunstncompidr . 
  intros . simpl in * .  apply monfunstncompassoc .
Defined. *)
Admitted.               



  
(* Definition of a simplicial hset *)

Definition sSet := [ precatDelta , HSET, pr2 is_category_HSET ] . 

(* V.V. with Sasha Vishik, Nov. 23, 2014 *)









                   


(* End of the file sSet.v *)
