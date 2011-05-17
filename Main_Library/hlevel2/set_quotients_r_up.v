(** * Set quotients of types. 

In this file we study the set quotients of types by equivalence relations. While the general notion of a quotient of a type by a relation is complicated due to the existence of different kinds of quotients (e.g. homotopy quotients or categorical quotients in the homotopy category which are usually different from each other) there is one particular class of quotients which is both very important for applications and semantically straightforward. These quotients are the universal functions from a type to an hset which respect a given relation. Some of the proofs in this section depend on the proerties of the hinhabited construction and some also depend on the univalence axiom for [ hProp ] which allows us to prove that the type of monic subtypes of a type is a set. 

Our main construction is analogous to the usual construction of quotient as a set of equivalence classes. Another construction of [ setquot ] is considered in a separate file. Both have generalizations to the "higher" quotients (i.e. groupoid quotients etc.) which will be considered separately. In particular, the quotients the next h-level appear to be closely related to the localizations of categories and will be considered in the section about types of h-level 3.  


*)



(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hSet_r_up.





(** ** Setquotient defined in terms of equivalence classes *)


Definition setquot (X:UU0)(R : hrel X):= total2 (hsubtypes X) (fun A:_=> iseqclass X R A).
Definition setquotpair ( X : UU0 ) ( R : hrel X ) := tpair  (hsubtypes X) (fun A:_=> iseqclass X R A).


Definition setquottouu0 ( X : UU0 ) ( R : hrel X ) : setquot X R -> UU0 := fun a : setquot X R => carrier _ (pr21 (hsubtypes X) (fun A:_=> iseqclass X R A) a ).
Coercion setquottouu0 : setquot >-> UU0.


Theorem isasetseqtquot ( X : UU0 ) ( R : hrel X ) : isaset ( setquot X R ) .
Proof. intros.  apply (isasetsubset _ (hsubtypes X) (pr21 (hsubtypes X) (fun A:_=> iseqclass X R A)) (isasethsubtypes X)). apply isinclpr21.  intro.  apply isapropiseqclass.  Defined. 


Theorem setquoteqrelpr (X:UU0)(R: hrel X)(is:iseqrel _ R): X -> setquot X R.
Proof. intros X R is X0. set (rax:= pr21 _ _ is). set (sax:= pr21 _ _ (pr22 _ _ is)). set (tax:= pr22 _ _ (pr22 _ _ is)). split with (fun x:X =>R X0 x). split with (hinhpr _ (tpair _ _ X0 (rax X0))).  
assert (a1: (forall x1 x2 : X, R x1 x2 -> R X0 x1 -> R X0 x2)). intros x1 x2 X1 X2.  apply (tax X0 x1 x2 X2 X1). split with a1.
assert (a2: (forall x1 x2 : X, R X0 x1 -> R X0 x2 -> R x1 x2)). intros x1 x2 X1 X2. apply (tax x1 X0 x2 (sax X0 x1 X1) X2). 
assumption. Defined. 

Theorem issurjsetquoteqrelpr (X:UU0)(R: hrel X)(is:iseqrel X R): issurjective _ _ (setquoteqrelpr X R is).
Proof. intros. unfold issurjective. intro C. 
assert ( s : C -> (hfiber X (setquot X R) (setquoteqrelpr X R is) C ) ). intro xe.  destruct xe as [ x e ].  split with x. 
set (st := pr21 _ _ C). set ( is1 := pr22 _ _ C).
assert ( e1 : paths _ (pr21 _ _ (setquoteqrelpr X R is x)) st ). simpl. apply funextfun.  intro x0. 
assert ( f1 : R x  x0 -> st x0 ). intro r. apply ( pr21 _ _ ( pr22 _ _ is1 ) x x0 r e ).  
assert ( f2 : st x0 -> R x x0 ). intro x1. apply ( pr22 _ _ ( pr22 _ _ is1 ) x x0 e x1 ).  
apply u1pathstou0paths. apply uahp. assumption. assumption. 
assert ( is2 : isincl (setquot X R ) _ ( pr21 _ _ )). apply isinclpr21.  intro x0. apply isapropiseqclass.  apply ( invmaponpathsincl _ _ _ is2 _ _ e1).  
apply hinhuniv2 with C. intro x0.  apply ( hinhpr _ (s x0) ). apply (pr21 _ _ (pr22 _ _ C)). Defined. 



Lemma isapropimeqclass  (X:UU0)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2)) (C: setquot X R): isaprop (image _ _ (fun a: C => f (pr21 _ _ a))).
Proof. intros.  destruct C as [ t x ]. destruct x as [ t0 x ]. destruct x as [ t1 x ]. rename t into A.
set (ImA:=  (total2 Y (fun y:_ => ishinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y)))). unfold isaprop.  intros.  simpl. intros.   
assert (is3: isincl _ _ ((pr21 _ _): ImA -> Y)). apply isofhlevelfpr21. intro. apply (isapropishinh (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) x1)).  
assert (is4: isweq _ _ (maponpaths _ _ ((pr21 _ _):ImA -> Y) x0 x') ). apply isweqonpathsincl. assumption. 
apply (iscontrxifiscontry _ _ _ is4). simpl. destruct x0 as [ t x1 ]. destruct x' as [ t2 x2 ].    simpl. 
assert (p1: (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t) -> (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t2) -> (paths _ t t2)). intros X0 X1.  destruct X0 as [ t3 x3 ]. destruct X1 as [ t4 x4 ]. assert (e1: R (pr21 _ _ t3) (pr21 _ _ t4)). apply x. apply (pr22 _ _ t3). apply (pr22 _ _ t4). assert (e2: paths _ (f (pr21 X (fun x : X => A x) t3)) (f (pr21 X (fun x : X => A x) t4))). apply is. apply e1. apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ x3) e2) x4). 
assert (isi: ishinh (paths _ t t2)). apply (hinhfunct2 _ _ _ p1 x1 x2). 
assert (cn: paths _ t t2). apply (hinhunivcor1 (hProppair _ ((uu1.pr22 _ _ Y) t t2)) isi). 
apply (iscontraprop1 _ ((uu1.pr22 _ _ Y) t t2) cn). Defined. 


Theorem setquotuniv  (X:UU0)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2))(C:setquot X R): Y.
Proof. intros. set (A:= pr21 _ _ C).
set (ImA:= total2 Y (fun y:_ => ishinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y))).
set (fA:= (fun a:A => tpair _ _  (f (pr21 _ _ a)) (hinhpr _ (hfiberpair A Y (fun a:A => f (pr21 _ _ a)) (f (pr21 _ _ a)) a (idpath _ _ )))):A -> ImA).  
set (is2:=(isapropimeqclass X R Y f is C):isaprop ImA).  
apply (pr21 _ _ (hinhuniv _ (hProppair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))). Defined. 

(** Note: the axioms rax, sax and trans are not used in the proof of setquotuniv. If we consider a relation which is not an equivalence relation then setquot will still be the set of subsets which are equivalence classes. Now however such subsets need not to cover all of the type. In fact their set can be empty. Nevertheless setquotuniv will apply. *)

Lemma setquotl1 (X:UU0)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2))(C: setquot X R)(x: X)(inC: (pr21 _ _ C x)): paths _ (f x) (setquotuniv X R Y f is C).
Proof. intros. set (A:= pr21 _ _ C).
set (ImA:= total2 Y (fun y:_ => ishinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y))).
set (fA:= (fun a:A => tpair _ _  (f (pr21 _ _ a)) (hinhpr _ (hfiberpair A Y (fun a:A => f (pr21 _ _ a)) (f (pr21 _ _ a)) a (idpath _ _ )))):A -> ImA).  
set (is2:=(isapropimeqclass X R Y f is C):isaprop ImA). change (setquotuniv X R Y f is C) with (pr21 _ _ (hinhuniv _ (hProppair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))). change (f x) with (pr21 _ _ (fA (carrierpair _ _ x inC))). 

assert (e: paths _ (fA (carrierpair _ _ x inC)) (hinhuniv _ (hProppair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))).  apply isapropimeqclass. assumption.  apply (maponpaths _ _ (pr21 _ _) _ _ e). Defined. 


Theorem setquotunivcomm  (X:UU0)(R: hrel X)(is0:iseqrel X R)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2)) : forall x:X, paths _ (f x) (setquotuniv X R Y f is (setquoteqrelpr X R is0  x)).
Proof. intros. set (C:= (setquoteqrelpr X R is0 x)). set (s:= pr21 _ _ C x).  simpl in s. set (inC:= (pr21 _ _ is0) x). apply setquotl1.  simpl. assumption.  Defined.

Lemma iscompsetquoteqrelpr (X : UU0) (R : hrel X) (is: iseqrel _ R) ( x x' : X) (a: R x x') : paths _ (setquoteqrelpr _ R is x) (setquoteqrelpr _ R is x').
Proof. intros. 
assert (e: uu1.paths _  (pr21 _ _ (setquoteqrelpr _ R is x)) (pr21 _ _ (setquoteqrelpr _ R is x'))). simpl. apply uu1.funextsec.  intro.  
set (is1:= pr21 _ _ (pr22 _ _ (pr22 _ _ (setquoteqrelpr _ R is t)))). simpl in is1. 
set (r1:= pr21 _ _ (pr22 _ _ is)). unfold issymm in r1. 
set (ax := is1 x x' a). set (ax' := is1 x' x (r1 _ _ a)). 
set (f:= fun u: R x t => (r1 _ _ (ax (r1 _ _ u)))). set (g:= fun u: R x' t => (r1 _ _ (ax' (r1 _ _ u)))). 
apply (uahp _ _ f g). 
set (is2:= isofhlevelfpr21 (S O) _ _ (fun A: hsubtypes X =>  (isapropiseqclass X R A))).  
apply (invmaponpathsincl _ _ _ is2 _ _ e). Defined. (* Uses univalence for hProp *)







(** *** The set of connected components of type. *)



Definition pathconnected (X:UU0):= fun (x x':X) =>  (ishinh_hprop (paths _ x x')).
Definition isreflpathconnected (X:UU0): isrefl X (pathconnected X):= fun x:_ =>  (hinhpr _ (idpath _ x)).
Definition issymmpathconnected (X:UU0): issymm _ (pathconnected X):= fun x x':_ => fun a:_ => ((hinhfunct _ _ (fun e:paths _ x x' => pathsinv0 _ _ _ e) a)). 
Definition istranspathconnected (X:UU0): istrans _ (pathconnected X):= fun x x' x'':_ => fun a:_ => fun b:_ =>  ((hinhfunct2 _ _ _ (fun e1: paths _ x x' => fun e2: paths _ x' x'' => pathscomp0 _ _ _ _ e1 e2)  a  b)).
Definition iseqrelpathconnected (X:UU0): iseqrel _ (pathconnected X):= dirprodpair _ _ (isreflpathconnected  _ ) (dirprodpair _ _ (issymmpathconnected _ ) (istranspathconnected  _ )).

Definition pi0 (X:UU0):= setquot X (pathconnected X). 
Definition pi0pr (X:UU0):= setquoteqrelpr X (pathconnected X) (iseqrelpathconnected X).



(** *** Homotopy sets of a pointed type. I. *)





















(* End of the file set_quotients_UU0.v *)




(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)