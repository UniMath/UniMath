(** * Generalities on [ hSet ] .

In this file we introduce the type [ hSet ] of h-sets i.e. of types of h-level 2 as well as a number of constructions such as type of (monic) subtypes, images, surjectivity etc. which, while they formally apply to functions between arbitrary types actually only depend on the behavior of the function on the sets of connected componenets of these types. The set of connected componenets itself, being an example of a quotient set of a type is introduced in a separate file. 

While it is possible to write a part of this file in a form which does not require RA1 it seems like a waste of effort since it would require to repeat a lot of things twice. Accordingly we assume RA1 from the start in dealing with sets. The drawback is that all the subsequent files will not compile at the moment without the Type in Type patch.


*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)


Require Export hProp_r.


(** ** The type of monic sybtypes of a type (subsets of the set of connected components) *)


Definition hsubtype ( X : UU0 ) := ( X -> hProp ).
Definition carrier { X : UU0 } ( A : hsubtype X ) := total2 A.
Coercion carrier : hsubtype >-> Sortclass. 
Definition carrierpair { X : UU0 } (A:hsubtype X):= tpair A.


Definition aux1 ( X : UU0 ) ( A : hsubtype X ) := X.
Definition carrierincl { X:UU0 } ( A : hsubtype X ) := ( @pr21 _ _ ) : carrier A -> aux1 X A.
Coercion carrierincl : carrier >-> aux1.



(** A single element subtype of a set is an h-prop. *)


Lemma isaprophsubtype ( X : hSet ) ( A : hsubtype X ) ( is : forall ( x1 x2 : X ) , A x1 -> A x2 -> paths x1 x2 ) : isaprop ( carrier A ) . 
Proof. intros.  apply invproofirrelevance. intros x x' .  
assert ( isincl ( @pr21 _ A )).  apply isinclpr21. intro x0. apply ( pr22 ( A x0 )).  
apply ( invmaponpathsincl ( @pr21 _ A ) X0 ). destruct x as [ x0 is0 ]. destruct x' as [ x0' is0' ] . simpl. apply is. assumption. assumption. Defined. 




(** *** Relations on types (or equivalently relations on the sets of connected components) *)


Definition hrel ( X : UU0 ) := X -> X -> hProp.

Definition isrefl { X : UU0 } ( R : hrel X ) := forall x:X, R x x.

Definition issymm { X : UU0 } ( R : hrel X ) := forall x1 x2 : X, R x1 x2 -> R x2 x1.

Definition istrans { X : UU0 } ( R : hrel X ) := forall x1 x2 x3 : X, forall (f1: R  x1 x2) (f2: R x2 x3), R x1 x3.


(** *** Partial orderings and associated types . *)


Definition ispo { X : UU0 } ( R : hrel X ) := dirprod ( istrans R ) ( isrefl R ) .

Definition po ( X : UU0 ) := total2 ( fun R : hrel X => ispo R ) .
Definition popair ( X : UU0 ) := tpair ( fun R : hrel X => ispo R ) .
Definition carrierofpo ( X : UU0 ) :  po X  -> hrel X :=  @pr21 _ ( fun R : hrel X => ispo R ) .
Coercion carrierofpo : po >-> hrel . 

Definition Poset := total2 ( fun X : hSet => po X ) .
Definition Posetpair := tpair ( fun X : hSet => po X ) .
Definition carrierofposet : Poset -> hSet := @pr21 _ _ .
Coercion carrierofposet : Poset >-> hSet . 

Definition isaposetmorphism { X Y : Poset } ( f : X -> Y ) := forall x x' : X , ( pr21 ( pr22 X ) x x' ) -> ( pr21 ( pr22 Y ) ( f x ) ( f x' ) ) .
Definition posetmorphism ( X Y : Poset ) := total2 ( fun f : X -> Y => isaposetmorphism f ) .
Definition posetmorphismpair ( X Y : Poset ) := tpair ( fun f : X -> Y => isaposetmorphism f ) .
Definition carrierofposetmorphism ( X Y : Poset ) : posetmorphism X Y -> ( X -> Y ) := @pr21 _ _ .
Coercion  carrierofposetmorphism : posetmorphism >-> Funclass . 

(** *** Eqivalence relations and associated types . *)

Definition iseqrel { X : UU0 } ( R : hrel X ) := dirprod (ispo R) (issymm R) .

Definition eqrel ( X : UU0 ) := total2 ( fun R : hrel X => iseqrel R ) .
Definition carrierofeqrel ( X : UU0 ) : eqrel X -> hrel X := @pr21 _ _ .
Coercion carrierofeqrel : eqrel >-> hrel . 


(** *** Monic subtypes of a type which are equivalence classes with respect to a given relation *)



Definition iseqclass { X : UU0 } ( R : hrel X ) ( A : hsubtype X ) := dirprod (ishinh (carrier A)) (dirprod (forall x1 x2 : X , (R x1 x2) -> (A x1) -> (A x2)) (forall x1 x2 : X, (A x1) ->  (A x2) ->  (R x1 x2))).



Definition eqax0 { X : UU0 } ( R : hrel X ) ( A : hsubtype X ) := ( fun is : iseqclass R A =>  pr21 is ) : iseqclass R A -> (ishinh (carrier A)).
Definition eqax1 (X:UU0)(R:hrel X)(A:hsubtype X):= (fun is: iseqclass R A => pr21 (pr22 is)): iseqclass R A ->  (forall x1 x2 : X,  (R x1 x2) ->  (A x1) -> (A x2)).
Definition eqax2 (X:UU0)(R:hrel X)(A:hsubtype X):= (fun is: iseqclass R A => pr22 (pr22 is)): iseqclass R A ->  (forall x1 x2 : X,  (A x1) -> (A x2) ->  (R x1 x2)).



Lemma isapropiseqclass  { X : UU0 } (R:hrel X)(A:hsubtype X): isaprop ( iseqclass R A ).
Proof. intros.
unfold iseqclass. apply isofhleveldirprod. apply (isapropishinh (carrier A)).     apply isofhleveldirprod. apply impredtwice. intros t t' . apply impred. intro. apply impred.  intro.  apply (pr22 (A t')). 
apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr22 (R t t')).  Defined. 


(**  *** Images and surjectivity for functions between types (both depend on on the behavior of the corresponding function between the sets of connected components) **)

Definition image { X Y : UU0 } (f:X -> Y):= total2 (fun y:Y => ishinh (hfiber f y)).
Definition imagepair { X Y : UU0 } (f: X -> Y) := tpair (fun y:Y => ishinh (hfiber f y)).

Definition imageincl { X Y : UU0 } (f:X -> Y) : image f -> Y := @pr21 _ _.

Definition prtoimage { X Y : UU0 } (f : X -> Y) : X -> image f.
Proof. intros X Y f X0. apply (imagepair _ (f X0) (hinhpr _ (hfiberpair f X0 (idpath _ )))). Defined. 

Definition issurjective { X Y : UU0 } (f : X -> Y ) := forall y:Y, ishinh (hfiber f y). 



Lemma isapropissurjective { X Y : UU0 } ( f : X -> Y) : isaprop (issurjective f).
Proof. intros.  apply impred. intro t. apply  (pr22 (ishinh_hprop (hfiber f t))). Defined. 


Lemma isinclimageincl { X Y : UU0 } (f:X -> Y): isincl (imageincl f).
Proof. intros. apply isofhlevelfpr21. intro. apply isapropishinh. Defined.


Lemma issurjprtoimage { X Y : UU0 } ( f : X -> Y) : issurjective (prtoimage f ).
Proof. intros. intro z.  set (f' := prtoimage f ). set (g:= imageincl f ). set (gf':= fun x:_ => g ( f' x )).
assert (e: paths f gf'). apply etacorrection .  
assert (ff: hfiber gf' (pr21 z) -> hfiber f' z).   apply ( invweq ( samehfibers _ _ ( isinclimageincl f ) z ) ) .  
assert (is2: ishinh (hfiber gf' (pr21 z))). destruct e.  apply (pr22 z). 
apply (hinhfunct ff is2). Defined. 




(** *** Surjections to sets are epimorphisms  *)

Theorem surjectionisepitosets { X Y Z : UU0 } ( f : X -> Y )( g1 g2 : Y -> Z )( is1 : issurjective f)(is2: isaset Z): (forall x:X, paths (g1 (f x)) (g2 (f x))) -> (forall y:Y, paths (g1 y) (g2 y)).
Proof. intros X Y Z f g1 g2 is1 is2 X0 y. set (P1:= hProppair (paths (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber f y)-> paths (g1 y) (g2 y)). intro X1. destruct X1 as [t x ]. induction x. apply (X0 t). 
assert (s2: ishinh (paths (g1 y) (g2 y))). apply (hinhfunct s1 (is1 y)).  
set (is3:= is2 (g1 y) (g2 y)). simpl in is3. apply (@hinhuniv (paths (g1 y) (g2 y)) (hProppair _ is3)). intro X1.  assumption. assumption. Defined. 













(* End of the file hSet_r.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)