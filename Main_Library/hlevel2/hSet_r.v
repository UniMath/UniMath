(** * Generalities on [ hSet ] .

In this file we introduce the type [ hSet ] of h-sets i.e. of types of h-level 2 as well as a number of constructions such as type of (monic) subtypes, images, surjectivity etc. which, while they formally apply to functions between arbitrary types actually only depend on the behavior of the function on the sets of connected componenets of these types. The set of connected componenets itself, being an example of a quotient set of a type is introduced in a separate file. 

While it is possible to write a part of this file in a form which does not require RA1 it seems like a waste of effort since it would require to repeat a lot of things twice. Accordingly we assume RA1 from the start in dealing with sets. The drawback is that all the subsequent files will not compile at the moment without the Type in Type patch.


*)



(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp_r.





(** *** The type of sets i.e.  types of h-level 2 in [ UU0 ] *) 


Definition hSet:= (uu1.total2 UU0 (fun X:UU0 => isaset X)).
Definition hSetpair := (uu1.tpair UU0 (fun X:UU0 => isaset X)).
Definition hSettoUU:= uu1.pr21 UU0 (fun X:UU0 => isaset X) : hSet -> Type.
Coercion hSettoUU: hSet >-> Sortclass. 

(** *** The canonical structure of an h-property on paths in an h-set. *)

Definition paths_hprop ( X : hSet ) ( x y : X ) : hProp := hProppair ( paths _ x y ) ( uu1.pr22 _ _ X x y ) .
Canonical Structure paths_hprop. 
 


(** *** Canonical hSet structures on standard sets. *)

Definition nat_set := hSetpair nat isasetnat.
Canonical Structure nat_set . 




(** *** Types of monic sybtypes of a type (subsets of the set of connected components) *)



Definition hsubtypes (X:UU0) := (X -> hProp).


Definition carrier (X:UU0)(A:hsubtypes X):= total2 X (fun x:X => A x).

Coercion carrier : hsubtypes >-> Sortclass. 

Definition carrierpair (X:UU0)(A:hsubtypes X):= tpair X (fun x:X => A x).


Definition aux1 (X:UU0)( A : hsubtypes X ) := X.

Definition carrierincl (X:UU0)(A:hsubtypes X):= (pr21 _ _) : carrier X A -> aux1 X A.

Coercion carrierincl : carrier >-> aux1.



(** A single element of a set is a prop. *)


Lemma isaprophsubtype ( X : hSet ) ( A : hsubtypes X ) ( is : forall ( x1 x2 : X ) , A x1 -> A x2 -> paths _ x1 x2 ) : isaprop ( total2 X A ) . 
Proof. intros.  apply invproofirrelevance. intros x x' .  
assert ( isincl _ _ ( pr21 _ _ : total2 X A -> X )).  apply isinclpr21. intro x0. apply ( uu1.pr22 _ _ ( A x0 )).  
apply ( invmaponpathsincl _ X ( pr21 _ _ ) X0 ). destruct x as [ x0 is0 ]. destruct x' as [ x0' is0' ] . simpl. apply is. assumption. assumption. Defined. 





(** *** Relations on types (or equivalently relations on the sets of connected components) *)


Definition hrel (X:UU0) := forall x1 x2 : X, hProp.

Definition isrefl (X:UU0)(R:hrel X) := forall x:X, R x x.

Definition issymm (X:UU0)(R:hrel X):= forall x1 x2 : X, R x1 x2 -> R x2 x1.

Definition istrans (X:UU0) (R: hrel X):= forall x1 x2 x3 : X, forall (f1: R  x1 x2) (f2: R x2 x3), R x1 x3.

Definition iseqrel (X:UU0)(R:hrel X):= dirprod (isrefl _ R) (dirprod (issymm _ R) (istrans _ R)).

Lemma isapropiseqrel  (X:UU0)(R:hrel X): isaprop (iseqrel _ R).
Proof. intros.
unfold iseqrel. apply isofhleveldirprod. apply impred. intro. apply (uu1.pr22 _ _ (R t t)).  apply isofhleveldirprod. apply impredtwice. intros. apply impred. intro. apply (uu1.pr22 _ _ (R t' t)). apply impred.  intro. apply impred. intro. apply impred.  intro. apply impred. intro. apply impred.  intro.  apply (uu1.pr22 _ _ (R t t1)).  Defined. 




(** *** Monic subtypes of a type which are equivalence classes with respect to a given relation *)



Definition iseqclass (X:UU0)(R:hrel X)(A: hsubtypes X):= dirprod (ishinh (carrier X A)) (dirprod (forall (x1 x2 : X), (R x1 x2) -> (A x1) -> (A x2)) (forall x1 x2:X, (A x1) ->  (A x2) ->  (R x1 x2))).



Definition eqax0 (X:UU0)(R:hrel X)(A:hsubtypes X):= pr21 _ _ : iseqclass X R A -> (ishinh (carrier X A)).
Definition eqax1 (X:UU0)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr21 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall (x1 x2 : X),  (R x1 x2) ->  (A x1) -> (A x2)).
Definition eqax2 (X:UU0)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr22 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall x1 x2:X,  (A x1) -> (A x2) ->  (R x1 x2)).



Lemma isapropiseqclass  (X:UU0)(R:hrel X)(A:hsubtypes X): isaprop ( iseqclass X R A ).
Proof. intros.
unfold iseqclass. apply isofhleveldirprod. apply (isapropishinh (carrier X A)).     apply isofhleveldirprod. apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (uu1.pr22 _ _ (A t')). 
 apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (uu1.pr22 _ _ (R t t')).  Defined. 


(**  *** Images and surjectivity for functions between types (both depend on on the behavior of the corresponding function between the sets of connected components) **)

Definition image (X Y:UU0)(f:X -> Y):= total2 Y (fun y:Y => ishinh (hfiber _ _ f y)).
Definition imagepair (X Y : UU0)(f: X -> Y) := tpair Y (fun y:Y => ishinh (hfiber _ _ f y)).

Definition imageincl (X Y:UU0)(f:X -> Y): image _ _ f -> Y := pr21 _ _.

Definition prtoimage (X Y : UU0) (F : X -> Y) : X -> image _ _ F.
Proof. intros X Y F X0. apply (imagepair _ _ _ (F X0) (hinhpr _ (hfiberpair _ _ F (F X0) X0 (idpath _ _ )))). Defined. 

Definition issurjective (X Y:UU0)(f:X -> Y):= forall y:Y, ishinh (hfiber _ _ f y). 



Lemma isapropissurjective (X Y:UU0)(f: X -> Y) : isaprop (issurjective _ _ f).
Proof. intros.  apply impred. intro. apply  (uu1.pr22 _ _ (ishinh_hprop (hfiber X Y f t))). Defined. 


Lemma isinclimageincl (X Y:UU0)(f:X -> Y): isincl _ _ (imageincl _ _ f).
Proof. intros. apply isofhlevelfpr21. intro. apply isapropishinh. Defined.


Lemma issurjprtoimage (X Y : UU0) (F : X -> Y) : issurjective _ _ (prtoimage X Y F).
Proof. intros. intro z.  set (f := prtoimage X Y F). set (g:= imageincl X Y F). set (gf:= fun x:_ => g ( f x )).
assert (e: paths _ F gf). apply etacorrection .  
assert (ff: hfiber _ _ gf (pr21 _ _ z) -> hfiber _ _ f z).  set (hz:= hfiberpair _ _ g (g z) z (idpath _ _ )).  set (u:= (hfibersftogf _ _ _ f g (g z) hz)). 
assert (is : isweq _ _ u). apply samehfibers.  apply isinclimageincl.  apply weqinv.  split with u.  assumption.  
assert (is2: ishinh (hfiber X Y gf (pr21 Y (fun y : Y => ishinh (hfiber X Y F y)) z))). destruct e.  apply (pr22 _ _ z). 
apply (hinhfunct _ _ ff is2). Defined. 




(** *** Surjections to sets are epimorphisms  *)

Theorem surjectionisepitosets (X Y Z:UU0)(f:X -> Y)(g1 g2: Y -> Z)(is1:issurjective _ _ f)(is2: isaset Z): (forall x:X, paths _ (g1 (f x)) (g2 (f x))) -> (forall y:Y, paths _ (g1 y) (g2 y)).
Proof. intros X Y Z f g1 g2 is1 is2 X0 y. set (P1:= hProppair (paths _ (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber X Y f y)-> paths _ (g1 y) (g2 y)). intro X1. destruct X1 as [t x ]. induction x. apply (X0 t). 
assert (s2: ishinh (paths Z (g1 y) (g2 y))). apply (hinhfunct _ _ s1 (is1 y)).  
set (is3:= is2 (g1 y) (g2 y)). simpl in is3. apply (hinhuniv (paths Z (g1 y) (g2 y)) (hProppair _ is3)). intro X1.  assumption. assumption. Defined. 













(* End of the file hSet_r.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)