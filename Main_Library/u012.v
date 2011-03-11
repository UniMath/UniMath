(* It is at the moment an experimental file. It's first part is about set-quotients of types as well as about the related material. In the second type the definitions related to finite sets from u0.v are re-written with the different version of "inhabited" construction which is introduced in this file. Since manipulations with this construction require the use of the axioms which stimulate the global impredicativity of hProp these definitions do not let Coq to compute things - the test computations which work on u0.v hang for these definitions. Evemtually instead of real axioms one should use a resizing axiom which will not creatre cproblems with the computation. 


At the very end of the file are some experiments which are a part of my attempts to define a "weakly commutative simplex" in Coq. 

*)




Require Export u12 u01.

Unset Automatic Introduction. 



(**  **)





(** * Inhabited construction *)

Definition isinhtech (X:UU1):= forall P:hProp, (X -> P) -> P.

Theorem isapropisinhtech (X:UU1): isaprop (isinhtech X).
Proof. intro. unfold isinhtech.
assert (s1: forall P:hProp, isaprop ((X -> P) -> P)). intro. apply impredfun. apply (pr22 _ _ P).    
apply impred. assumption. Defined. 

Definition isinh (X:UU1) := hProp1pair (isinhtech X) (isapropisinhtech X) :hProp1.

Definition isinhpr (X:UU1):= (fun x:X => fun P:_ => fun f:X -> P => f x): X -> isinh X. 


Definition isinhuniv (X:UU1)(P:hProp): (X -> P) -> ((isinh X) -> P) := fun f: X -> P => fun a: isinh X => a P f.

Definition isinhunivcor (P:hProp): isinh P -> P := isinhuniv P P (fun p:P => p).

Theorem isinhand (X Y:UU1): dirprod (isinh X) (isinh Y) -> isinh (dirprod X Y).
Proof. intros. destruct X0. intro. apply (ddualand X Y P (t P) (x P)). Defined. 

Definition isinhfunct (X Y:UU1): (X -> Y) -> ((isinh X) -> (isinh Y)) := fun f:_ => fun a:isinh X => (fun P:_ => fun g: Y -> P => a P (fun x:X => g (f x))).  

Theorem isinhfunct2 (X Y Z:UU1):(X -> Y -> Z) -> ((isinh X) -> (isinh Y) -> (isinh Z)).
Proof. intros. apply (isinhfunct _ _ (fun xy: dirprod X Y => X0 (pr21 _ _ xy) (pr22 _ _ xy)) (isinhand _ _ (dirprodpair _ _ X1 X2))).  Defined.


(** A group of constructions simulating global impredicativity of hProp and their basic corollaries. **)

Axiom hp1toUU0 : hProp1 -> UU0.


(* Axiom hp1tohp:hProp1 -> hProp. *)
(* Coercion hp1tohp:hProp1 >-> hProp. *)

(* Axiom hp1tohptoid : forall P:hProp1, hp1tohp P -> P.

Axiom idtohp1tohp : forall P:hProp1, P -> hp1tohp P. *)





Axiom idforce : forall P : hProp1 , u2.paths UU1 (hp1toUU0 P) P.




Definition hp1tohp : hProp1 -> hProp.
Proof. intro. split with (hp1toUU0 X). set (e := u2.pathsinv0 _ _ _ (idforce X)).  destruct e.  apply (u2.pr22 _ _ X).  Defined.


Definition hp1tohptoid : forall P:hProp1, hp1tohp P -> P.
Proof. intros. set (e := idforce P).  destruct e. assumption. Defined.

Definition idtohp1tohp : forall P:hProp1, P -> hp1tohp P. 
Proof. intros.  set (e := idforce P).  destruct e.  simpl.  assumption.  Defined. 

Definition isinhuniv1 (X:UU1)(P:hProp1): (X -> P) -> ((isinh X) -> P).
Proof. intros.  set (e := idforce P).  destruct e. apply (isinhuniv _ (hp1tohp P) X0). assumption. Defined. 


Definition isinhunivcor1 (P:hProp1): isinh P -> P := isinhuniv1 P P (fun p:P => p).




(**  * Images and surjectivity **)

Definition image (X Y:UU1)(f:X -> Y):= total2 Y (fun y:Y => isinh (hfiber _ _ f y)).

Definition imageincl (X Y:UU1)(f:X -> Y): image _ _ f -> Y := pr21 _ _.

Definition issurjective (X Y:UU1)(f:X -> Y):= forall y:Y, isinh (hfiber _ _ f y). 

Lemma isapropissurjective (X Y:UU1)(f: X -> Y) : isaprop (issurjective _ _ f).
Proof. intros.  apply impred. intro. apply  (u2.pr22 _ _ (isinh (hfiber X Y f t))). Defined. 

Lemma isinclimageincl (X Y:UU1)(f:X -> Y): isincl _ _ (imageincl _ _ f).
Proof. intros. apply isofhlevelfpr21. intro. apply (isapropisinhtech (hfiber X Y f x)). Defined.



(** ** Set quotients of types *)

(** ** Surjections are epimorphisms to sets *)

Theorem surjectionisepitosets (X Y Z:UU1)(f:X -> Y)(g1 g2: Y -> Z)(is1:issurjective _ _ f)(is2: isaset Z): (forall x:X, paths _ (g1 (f x)) (g2 (f x))) -> (forall y:Y, paths _ (g1 y) (g2 y)).
Proof. intros. set (P1:= hProp1pair (paths _ (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber X Y f y)-> paths _ (g1 y) (g2 y)). intro. destruct X1. induction x. apply (X0 t). 
assert (s2: isinh (paths Z (g1 y) (g2 y))). apply (isinhfunct _ _ s1 (is1 y)).  apply (isinhunivcor1 P1). assumption. Defined. 


(** ** Equivalence classes *)


Definition iseqclass (X:UU1)(R:hrel X)(A:hsubtypes X):= dirprod (isinh A) (dirprod (forall (x1 x2 : X), (R x1 x2) -> (A x1) -> (A x2)) (forall x1 x2:X, (A x1) ->  (A x2) ->  (R x1 x2))).
Definition eqax0 (X:UU1)(R:hrel X)(A:hsubtypes X):= pr21 _ _ : iseqclass X R A -> (isinh A).
Definition eqax1 (X:UU1)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr21 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall (x1 x2 : X),  (R x1 x2) ->  (A x1) -> (A x2)).
Definition eqax2 (X:UU1)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr22 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall x1 x2:X,  (A x1) -> (A x2) ->  (R x1 x2)).

Lemma isapropiseqclass  (X:UU1)(R:hrel X)(A:hsubtypes X): isaprop(iseqclass X R A).
Proof. intros.
unfold iseqclass. apply isofhleveldirprod. apply (isapropisinhtech A).     apply isofhleveldirprod. apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr22 _ _ (A t')). 
 apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr22 _ _ (R t t')).  Defined. 



(** ** Setquotient *)

Definition setquot (X:UU1)(R : hrel X):= total2 (hsubtypes X) (fun A:_=> iseqclass X R A).


Theorem setquoteqrelpr (X:UU1)(R: hrel X)(is:iseqrel _ R): X -> setquot X R.
Proof. intros. set (rax:= pr21 _ _ is). set (sax:= pr21 _ _ (pr22 _ _ is)). set (tax:= pr22 _ _ (pr22 _ _ is)). split with (fun x:X =>R X0 x). split with (isinhpr _ (tpair _ _ X0 (rax X0))).  
assert (a1: (forall x1 x2 : X, R x1 x2 -> R X0 x1 -> R X0 x2)). intros.  apply (tax X0 x1 x2 X2 X1). split with a1.
assert (a2: (forall x1 x2 : X, R X0 x1 -> R X0 x2 -> R x1 x2)). intros. apply (tax x1 X0 x2 (sax X0 x1 X1) X2). 
assumption. Defined. 

(* Theorem issurjsetquoteqrelpr (X:UU1)(R: hrel X)(is:iseqrel X R): issurjective _ _ (setquoteqrelpr X R is).
Proof. intros. unfold issurjective. intro. destruct y. 
assert (s:t -> hfiber X (setquot X R) (setquoteqrelpr X R is)
        (tpair (hsubtypes X) (fun A : hsubtypes X => iseqclass X R A) t x)). intro. destruct X0. split with t0. unfold setquoteqrelpr. 
assert (e: paths _ (fun x1 : X => R t0 x1) t).  apply funextsec.  intro. *)

Lemma isapropimeqclass  (X:UU1)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2)) (C: setquot X R): isaprop (image _ _ (fun a: pr21 _ _ C => f (pr21 _ _ a))).
Proof. intros.  destruct C. destruct x. destruct x. rename t into A.
set (ImA:=  (total2 Y (fun y:_ => isinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y)))). unfold isaprop.  intros.  simpl. intros.   
assert (is3: isincl _ _ ((pr21 _ _): ImA -> Y)). apply isofhlevelfpr21. intro. apply (isapropisinhtech (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) x1)).  
assert (is4: isweq _ _ (maponpaths _ _ ((pr21 _ _):ImA -> Y) x0 x') ). apply isweqonpathsincl. assumption. 
apply (iscontrxifiscontry _ _ _ is4). simpl. destruct x0. destruct x'.    simpl. 
assert (p1: (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t) -> (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t2) -> (paths _ t t2)). intros.  destruct X0. destruct X1. assert (e1: R (pr21 _ _ t3) (pr21 _ _ t4)). apply x. apply (pr22 _ _ t3). apply (pr22 _ _ t4). assert (e2: paths _ (f (pr21 X (fun x : X => A x) t3)) (f (pr21 X (fun x : X => A x) t4))). apply is. apply e1. apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ x2) e2) x3). 
assert (isi: isinh (paths _ t t2)). apply (isinhfunct2 _ _ _ p1 x0 x1). 
assert (cn: paths _ t t2). apply (isinhunivcor1 (hProp1pair _ ((u2.pr22 _ _ Y) t t2)) isi). 
apply (iscontraprop1 _ ((u2.pr22 _ _ Y) t t2) cn). Defined. 



Theorem setquotuniv  (X:UU1)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2))(C:setquot X R): Y.
Proof. intros. set (A:= pr21 _ _ C).
set (ImA:= total2 Y (fun y:_ => isinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y))).
set (fA:= (fun a:A => tpair _ _  (f (pr21 _ _ a)) (isinhpr _ (hfiberpair A Y (fun a:A => f (pr21 _ _ a)) (f (pr21 _ _ a)) a (idpath _ _ )))):A -> ImA).  
set (is2:=(isapropimeqclass X R Y f is C):isaprop ImA).  
apply (pr21 _ _ (isinhuniv1 _ (hProp1pair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))). Defined. 

(** Note: the axioms rax, sax and trans are not used in the proof of setquotuniv. If we consider a relation which is not an equivalence relation then setquot will still be the set of subsets which are equivalence classes. Now however such subsets need not to cover all of the type. In fact their set can be empty. Nevertheless setquotuniv will apply. **)

Lemma setquotl1 (X:UU1)(R: hrel X)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2))(C: setquot X R)(x: X)(inC: (pr21 _ _ C x)): paths _ (f x) (setquotuniv X R Y f is C).
Proof. intros. set (A:= pr21 _ _ C).
set (ImA:= total2 Y (fun y:_ => isinh (hfiber A Y (fun a:A => f (pr21 _ _ a)) y))).
set (fA:= (fun a:A => tpair _ _  (f (pr21 _ _ a)) (isinhpr _ (hfiberpair A Y (fun a:A => f (pr21 _ _ a)) (f (pr21 _ _ a)) a (idpath _ _ )))):A -> ImA).  
set (is2:=(isapropimeqclass X R Y f is C):isaprop ImA). change (setquotuniv X R Y f is C) with (pr21 _ _ (isinhuniv1 _ (hProp1pair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))). change (f x) with (pr21 _ _ (fA (carrierpair _ _ x inC))). 

assert (e: paths _ (fA (carrierpair _ _ x inC)) (isinhuniv1 _ (hProp1pair ImA is2) fA (pr21 _ _ (pr22 _ _ C)))).  apply isapropimeqclass. assumption.  apply (maponpaths _ _ (pr21 _ _) _ _ e). Defined. 


Theorem setquotunivcomm  (X:UU1)(R: hrel X)(is0:iseqrel X R)(Y:hSet)(f:X -> Y)(is:forall x1 x2 : X, (R x1 x2) -> paths _ (f x1) (f x2)) : forall x:X, paths _ (f x) (setquotuniv X R Y f is (setquoteqrelpr X R is0  x)).
Proof. intros. set (C:= (setquoteqrelpr X R is0 x)). set (s:= pr21 _ _ C x).  simpl in s. set (inC:= (pr21 _ _ is0) x). apply setquotl1.  simpl. assumption.  Defined. 


(** The set of connected components of type. *)

Definition pathconnected (X:UU1):= fun (x x':X) => (hp1tohp (isinh (paths _ x x'))).
Definition isreflpathconnected (X:UU1): isrefl X (pathconnected X):= fun x:_ => (idtohp1tohp _ (isinhpr _ (idpath _ x))).
Definition issymmpathconnected (X:UU1): issymm _ (pathconnected X):= fun x x':_ => fun a:_ => ((idtohp1tohp _ (isinhfunct _ _ (fun e:paths _ x x' => pathsinv0 _ _ _ e) (hp1tohptoid _ a)))). 
Definition istranspathconnected (X:UU1): istrans _ (pathconnected X):= fun x x' x'':_ => fun a:_ => fun b:_ =>  ((idtohp1tohp _ (isinhfunct2 _ _ _ (fun e1: paths _ x x' => fun e2: paths _ x' x'' => pathscomp0 _ _ _ _ e1 e2)  (hp1tohptoid _ a)  (hp1tohptoid _ b)))).
Definition iseqrelpathconnected (X:UU1): iseqrel _ (pathconnected X):= dirprodpair _ _ (isreflpathconnected  _ ) (dirprodpair _ _ (issymmpathconnected _ ) (istranspathconnected  _ )).

Definition pizero (X:UU1):= setquot X (pathconnected X). 
Definition pizeropr (X:UU1):= setquoteqrelpr X (pathconnected X)  (iseqrelpathconnected X).

(** Homotopy sets of a type. I. *)










(** * Univalence axiom for hProp *)

(** At the moment I do not see how to prove directly that setquot X is a set or that setquoteqrelpr is a surjection even in the case of [pizero] and [pizeropr]. The problem lies in the fact that we do not know that [hProp] is a set. We do not even know that [paths UU0 unit unit] is contractible. To deal with this problem we introduce at this stage the weakest form of the univalence axiom - the univalence axiom for hProp which is equivalent to the second part of the extensionality axiom in Church simple type theory. *)


Axiom uahp : forall P P':hProp,  (P -> P') -> (P' -> P) -> paths hProp P P'.


(** This axiom is easily shown to be equivalent to its version with [paths UU0 P P'] as a target and to weqtopathshProp (see below) and to the version of weqtopathshProp with [paths UU0 P P'] as a target. **)


Definition eqweqmaphProp (P P':hProp) : paths hProp P P' -> weq P P'.
Proof. intros. destruct  X. apply idweq.  Defined.

Definition  weqtopathshProp (P P':hProp)(w: weq P P'): paths hProp P P' := uahp P P' w (weqinv _ _ w).

Definition weqpathsweqhProp (P P':hProp)(w: weq P P'): paths _ (eqweqmaphProp _ _ (weqtopathshProp _ _ w)) w.
Proof. intros. apply (proofirrelevance). apply (isapropweq P P' (pr22 _ _ P')). Defined.

(** The proof of the following theorem is modeled on the proof of [univfromtwoaxioms] in univ01.v *)

Theorem univfromtwoaxiomshProp (P P':hProp): isweq (paths hProp P P') (weq P P') (eqweqmaphProp P P').
Proof. intros. set (P1:= fun XY: dirprod hProp hProp => (match XY with tpair X Y =>  paths hProp X Y end)). set (P2:= fun XY:  dirprod hProp hProp => match XY with  tpair X Y => weq X Y end). set (Z1:=  total2 _ P1). set (Z2:=  total2 _ P2). set (f:= ( totalfun _ _ _ (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => eqweqmaphProp X Y end))): Z1 -> Z2). set (g:=  ( totalfun _ _ _ (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => weqtopathshProp X Y end))): Z2 -> Z1). set (s1:= (fun X Y :hProp => fun w: weq X Y =>  tpair _ P2 ( dirprodpair _ _ X Y) w)). set (efg:= (fun a:_ => match a as a' return ( paths _ (f (g a')) a') with  tpair ( tpair X Y) w => ( maponpaths _ _ (s1 X Y) _ _ (weqpathsweqhProp X Y w)) end)). 

set (h:= fun a1:Z1 => ( pr21 _ _ ( pr21 _ _ a1))).
assert (egf0: forall a1:Z1,  paths ( dirprod hProp hProp) ( pr21 _ _ (g (f a1))) ( pr21 _ _ a1)). intro. apply  idpath.  
assert (egf1: forall a1 a1':Z1,  paths _ ( pr21 _ _ a1') ( pr21 _ _ a1) ->  paths _ a1' a1). intros.  set (X':=  maponpaths _ _ ( pr21 _ _ ) _ _ X). 
assert (is:  isweq _ _ h).  apply ( isweqpr21pr21). apply ( pathsweq2 _ _ h is _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:= gradth _ _ _ _ egf efg). 
apply ( isweqtotaltofib _ P1 P2  (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => eqweqmaphProp X Y end)) is2 ( dirprodpair _ _ P P')). Defined. 




Corollary isasethProp : isaset hProp.
Proof. unfold isaset.  simpl. intro. intro. apply (isofhlevelweqb (S O) _ _ _ (univfromtwoaxiomshProp x x') (isapropweq x x' (pr22 _ _ x'))). Defined.


Corollary isasethsubtypes (X:UU1): isaset (hsubtypes X).
Proof. unfold isaset. intro.  apply impred. intro. apply isasethProp. Defined.




(** Setquotients of types cont. *)



Theorem isasetsetquot (X:UU1)(R: hrel X) : isaset (setquot X R).
Proof. intros. assert (is1: isincl (setquot X R) (hsubtypes X) (pr21 _ _)). apply (isinclpr21 _ _ (fun A: hsubtypes X => isapropiseqclass X R A)).  apply (isofhlevelsourceofincl (S O) _ _ (pr21 _ _ ) is1 (isasethsubtypes X)).  Defined.


(*Theorem issurjsetquoteqrelpr (X:UU1)(R: hrel X)(is: iseqrel X R): issurjective _ _ (setquoteqrelpr X R is).
Proof. intros. *)










(** * Finite sets. *)



(** ** Standard finite sets. *)



Fixpoint stn (n:nat):UU1:= match n with
O => empty|
S m => coprod (stn m) unit
end.

 

Lemma isisolatedinstn (n:nat): forall x: stn n, isisolated _ x.
Proof. intro.   induction n. intro. apply (initmap _ x). intro.  simpl in x.  destruct x. apply (isolatedtoisolatedii1 _ _ s (IHn s)). destruct u. 
apply disjointl1.  Defined. 



Corollary isdeceqstn (n:nat): isdeceq (stn n).
Proof. intro.  unfold isdeceq. apply (isisolatedinstn n). Defined. 


Lemma stnsnegl1 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ X lp). Defined.

Lemma stnsnegl2 (n:nat): neg (weq (stn O) (stn (S n))).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ (weqinv _ _ X) lp). Defined.


Lemma stnsposl0 (n:nat): weq (stn n) (complement (stn (S n)) (ii2 _ _ tt)).
Proof. intros. split with (tocompltodisjoint (stn n)). apply isweqtocompltodisjoint. Defined.

Lemma stnsposl1 (n:nat)(x: stn (S n)): weq (stn n) (complement (stn (S n)) x).
Proof. intro. induction n. intros. simpl in x.  destruct x.  apply (initmap _ e). simpl. destruct u. apply (stnsposl0 O). intro. simpl in x. destruct x. set  (g:=tocompltoii1x _ unit c).  set (f:= coprodf _ _ _ _ (pr21 _ _ (IHn c)) (fun t:unit => t)).  split with (fun x:_ => g (f x)). 
assert (is1:isweq _ _ f). apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ (IHn c)) (idisweq unit)). 
assert (is2: isweq _ _ g). apply (isweqtocompltoii1x _ unit c). 
apply (twooutof3c _ _ _ f g is1 is2). 
destruct u. split with (tocompltodisjoint _). apply (isweqtocompltodisjoint _).  Defined.






Lemma stnsposl2 (n n':nat): weq (stn (S n)) (stn (S n')) -> weq (stn n) (stn n').
Proof. intros. destruct X. rename t into ff. rename x into is.    simpl in ff. set (int1:= complement (stn (S n')) (ff (ii2 _ _ tt))).
set (f1:= tocompltodisjoint (stn n)).  
set (f2:= maponcomplementsweq _ _ ff is (ii2 _ _ tt)).
set (f3:= invmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
assert (is1: isweq _ _ f1). apply isweqtocompltodisjoint. 
assert (is2: isweq _ _ f2). apply isweqmaponcomplements.
assert (is3: isweq _ _ f3). apply (isweqinvmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
set (gg:= fun xx:_ => (f3 (f2 (f1 xx)))). split with gg.
apply (twooutof3c _ _ _ _ _ (twooutof3c _ _ _ _ _ is1 is2) is3). Defined.



Theorem stnsweqtoeq (n n':nat): (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intro. induction n. intro. induction n'.  intros. apply idpath. intro. apply (initmap _ (stnsnegl2  n' X)).  
 intro. induction n'. intros. set (int:= isdeceqnat O (S n)).  destruct int.  assumption. apply (initmap _ (stnsnegl1 n X)).  intro. 
set (e:= IHn n' (stnsposl2 n n' X)). apply (maponpaths _ _ S _ _ e). Defined. 

Corollary stnsdnegweqtoeq (n n':nat): dneg (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intros. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf _ _ (stnsweqtoeq n n') X)). Defined. 






(** ** Sets with fixed number of elements. *)



Definition nelstruct (n:nat)(X:UU1):= weq (stn n) X. 
Definition isofnel (n:nat)(X:UU1) := isinh (weq (stn n) X). 

Definition isofnelstn (n:nat): isofnel n (stn n) := isinhpr _ (idweq (stn n)).

Lemma isofnelimpl (n:nat)(X:UU1)(isx: isofnel n X)(P: hProp1): ((weq (stn n) X) -> P) -> (isofnel n X -> P).
Proof. intros.  apply isinhuniv1 with (weq (stn n) X). assumption. unfold isofnel in X1. assumption.  Defined. 



Lemma isof0ela (X:UU1): isofnel O X -> neg X.
Proof. intros. intro. apply (isofnelimpl O X X0 (hProp1pair empty  isapropempty)). intro.  apply (invmap _ _ _ (pr22 _ _ X2) X1). assumption.  Defined. 


Lemma isof0elb (X:UU1): neg X -> isofnel O X.
Proof. intros. apply (isinhpr _ (weqinv _ _ (weqpair _ _ _ (isweqtoempty _ X0)))). Defined. 


Corollary isof0elempty: isofnel O empty.
Proof. apply (isof0elb empty (fun x:_ => x)). Defined. 

Lemma isof1ela (X:UU1): isofnel (S O) X -> iscontr X.
Proof. intros.  apply (isofnelimpl (S O) X X0 (hProp1pair (iscontr X)  (isapropiscontr X))).  set (w2:= (weqinv _ _ (weqfromcoprodwithempty unit))). intro.  set (w3:= weqcomp _ _ _ w2 X1). apply (iscontrifweqtounit _ (weqinv _ _ w3)). assumption. Defined.  

Lemma isof1elb (X:UU1): (iscontr X) -> isofnel (S O) X.
Proof. intros. set (w1:= weqpair _ _ _ (isweqcontrtounit _ X0)). set (w2:= weqfromcoprodwithempty unit).  set (w:= weqcomp _ _ _ w2 (weqinv _ _ w1)). apply (isinhpr _ w). Defined. 


Lemma isof1elunit: isofnel (S O) unit.
Proof. apply (isinhpr _ (weqfromcoprodwithempty unit)). Defined. 


Lemma isofsnel (n:nat)(X:UU1): isofnel n X -> isofnel (S n) (coprod X unit).
Proof. intros. 
assert (f: weq (stn n) X -> weq (stn (S n)) (coprod X unit)).  intro.  split with (coprodf _ _ _ _ (pr21 _ _ X1) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X1) (idisweq unit)). apply (isinhfunct _ _ f X0). Defined.


Lemma isofnelweqf (n:nat)(X Y:UU1)(f:X -> Y)(is: isweq _ _ f): isofnel n X -> isofnel n Y.
Proof. intros.  set (ff:= fun u:weq (stn n) X => weqcomp _ _ _ u (weqpair _ _ f is)). apply (isinhfunct _ _ ff X0). Defined.


Lemma isof2elbool : isofnel (S (S O)) bool.
Proof. apply (isofnelweqf _ _ _ _ (pr22 _ _ boolascoprod) (isofsnel (S O) unit isof1elunit)). Defined. 



(** ** Finite subsets of nat. *)

Fixpoint leb (n m : nat) : bool :=
match n,m with
 | S n , S m => leb n m
 | 0, _ => true
 | _, _ => false
end.


Lemma isreflleb (n:nat): paths _ (leb n n) true.
Proof. intros. induction n. apply idpath.  simpl. assumption.  Defined. 

Lemma islebnsn (n:nat): paths _ (leb n (S n)) true.
Proof. intro. induction n.  apply idpath. simpl.  assumption.  Defined. 

Lemma neglebsnn (n:nat): neg (paths _ (leb (S n) n) true).
Proof. intro. induction n.  simpl.  intro. apply (nopathsfalsetotrue X). assumption.  Defined.


Lemma istransleb (k m n : nat): paths _ (leb k m) true -> paths _ (leb m n) true -> paths _ (leb k n) true.
Proof. intro. induction k.  intros.  simpl. apply idpath. intro. destruct m.  intros.   simpl in X.   apply (initmap _ (nopathsfalsetotrue X)). intro. destruct n.  intros.  apply (initmap _ (nopathsfalsetotrue X0)). simpl. apply (IHk m n).  Defined. 


Lemma is0leb0 (n:nat) : paths _ (leb n 0) true -> paths _ n 0.
Proof.  intro. destruct n. intro.   apply idpath.  intro. apply (initmap _ (nopathsfalsetotrue X)). Defined. 

Lemma lebsnchoice0 (x n:nat): paths _ (leb x (S n)) true -> (neg (paths _ x (S n))) -> paths _ (leb x n) true.
Proof. intro. induction x.  intros. apply idpath.  intro. destruct n.  intros.  simpl in X.  destruct x.  apply (initmap _ (X0 (idpath _ _))). simpl in X.  apply (initmap _ (nopathsfalsetotrue X)). intros. simpl in X.  set (a:= IHx n X (negf _ _ (maponpaths _ _ S _ _) X0)).  assumption.  Defined. 

Lemma lebsnchoice (x n:nat) : paths _ (leb x (S n)) true -> coprod (paths _ (leb x n) true) (paths _ x (S n)).
Proof. intros. set (s:= isdeceqnat (S n) x).  destruct s.  apply (ii2 _ _ p).
apply (ii1 _ _ (lebsnchoice0 x n X e)).  Defined. 


Definition initinterval (n:nat) := total2 nat (fun x:nat => paths _ (leb x n) true).
Definition initintervalpair (n:nat):= tpair  nat (fun x:nat => paths _ (leb x n) true).
Definition initintervaltonat (n:nat): initinterval n -> nat := pr21 _ _. 

Lemma isinclinitintervaltonat (n:nat) : isincl _ _ (initintervaltonat n).
Proof. intro.  apply isofhlevelfpr21. intro. intro.  intro. apply (isasetbool (leb x n) true). Defined. 

Definition initintervalsincl (m n:nat)(isle: paths _ (leb m n) true) : initinterval m -> initinterval n.
Proof. intros. destruct X.  split with t.  simpl. apply (istransleb t m n x isle).  Defined. 
 

Lemma iscontrinitinterval0 : iscontr (initinterval O).
Proof. split with (initintervalpair O O (isreflleb O)).  intro. destruct t.  assert (e: paths _ O t). apply (pathsinv0 _ _ _ (is0leb0 t x)).  destruct e. simpl.  apply (invmaponpathsincl _ _ _ (isinclinitintervaltonat O) (tpair nat (fun x0 : nat => paths bool (leb x0 O) true) O x)
     (initintervalpair O O (idpath bool true)) (idpath _ O)). Defined. 


Definition toinitintervalsn (n:nat):  (coprod (initinterval n) unit) -> (initinterval (S n)) := sumofmaps ( initintervalsincl n (S n) (islebnsn n)) (fun t:unit => initintervalpair (S n) (S n) (isreflleb (S n))).

Definition frominitintervalsn (n:nat): initinterval (S n) -> coprod (initinterval n) unit.
Proof. intros.   destruct X.  destruct (isdeceqnat (S n) t).  apply (ii2 _ _ tt).  apply (ii1 _ _ (initintervalpair n t (lebsnchoice0 t n x e))).   Defined. 


Definition weqtoinitintervalsn  (n:nat) : weq  (coprod (initinterval n) unit) (initinterval (S n)).
Proof. intro. set (f:= toinitintervalsn n). set (g:= frominitintervalsn n). split with f. 
set (u:= coprodf _ _ _ _ (initintervaltonat n) (fun t:unit => t)).   assert (is: isincl _ _ u). apply (isofhlevelfcoprodf (S O) _ _ _ _ _ _ (isinclinitintervaltonat n) (isofhlevelfweq (S O) _ _ _ (idisweq unit))).  
assert (egf: forall x:_, paths _ (g (f x)) x).  intro. 
assert (egf0: paths _ (u (g (f x))) (u x)).  destruct x. simpl. destruct i. destruct t.   simpl.  apply idpath. simpl. destruct (isdeceqnat n t).    simpl. induction p. apply (initmap _ (neglebsnn t x)).  simpl.  apply idpath.  destruct u0. destruct n.  apply idpath. simpl.  destruct (isdeceqnat n n). apply idpath.  apply (initmap _ (e (idpath _ _))). apply (invmaponpathsincl _ _ _ is _ _ egf0). 
assert (efg: forall x:_, paths _ (f (g x)) x). intro. 
assert (efg0: paths _ (initintervaltonat (S n) (f (g x))) (initintervaltonat (S n) x)).  destruct x. simpl.  destruct t. apply idpath. destruct (isdeceqnat n t).  simpl. apply (pathsinv0 _ _ _ (maponpaths _ _ S _ _ p)).  simpl.  apply idpath.  apply  (invmaponpathsincl _ _ _ (isinclinitintervaltonat _)  _ _ efg0). 
apply (gradth _ _ _ _ egf efg). Defined.  



Theorem weqstntoinitinterval (n:nat): weq (stn (S n)) (initinterval n).
Proof. intro. induction n. set (w1:= weqfromcoprodwithempty unit). set (w2:= weqinv _ _ (weqpair _ _ _ (isweqcontrtounit _ (iscontrinitinterval0)))).     apply (weqcomp _ _ _ w1 w2).  apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ IHn (idweq unit)) (weqtoinitintervalsn n)). Defined. 





(** ** General finite sets. *)



Definition finitestruct (X:UU1):= total2 nat (fun n:nat => weq (stn n) X).
Definition finitestructpair (X:UU1) := tpair nat (fun n:nat => weq (stn n) X).
Definition isfinite (X:UU1):= isinh (finitestruct X).
Definition isfiniteimpl (X:UU1)(P: hProp1): (forall n:nat, forall w: weq (stn n) X, P) -> isfinite X -> P.
Proof. intros. set (f0:= fun xx:(total2 nat (fun n:_ => weq (stn n) X)) => (X0 (pr21 _ _ xx) (pr22 _ _ xx))).  apply (isinhuniv1 (total2 nat (fun n:nat => weq (stn n) X)) P f0 X1). Defined. 


Definition isfiniteifofnel (n:nat)(X:UU1): isofnel n X -> isfinite X.
Proof. intros.  apply (isinhfunct _ _ (fun w:weq (stn n) X => finitestructpair _ n w) X0).  Defined.



Definition isofnel0 (n:nat)(X:UU1):= dneg (weq (stn n) X).
Definition isfinite0 (X:UU1):= total2 nat (fun n:_ => isofnel0 n X).



Lemma isapropisfinite0 (X:UU1): isaprop (isfinite0 X).
Proof. intros. assert (is1: (isfinite0 X) -> (iscontr (isfinite0 X))).  intro. unfold iscontr. split with X0.  intro. destruct X0.  destruct t.
assert (c1: coprod (paths _ t t0) (neg (paths _ t t0))). apply isdeceqnat. destruct c1.  apply (invmaponpathsincl (isfinite0 X) nat (pr21 _ _) (isofhlevelfpr21 (S O) _ _  (fun n:nat => isapropdneg (weq (stn n) X))) (tpair nat (fun n : nat => isofnel0 n X) t x0) (tpair nat (fun n : nat => isofnel0 n X) t0 x) p).  
assert (is1: dneg (dirprod (weq (stn t0) X) (weq (stn t) X))). apply (dneganddnegimpldneg _ _ x x0). 
assert (is2: dneg (weq (stn t0) (stn t))). apply (dnegf _ _ (fun fg: dirprod (weq (stn t0) X) (weq (stn t) X) => weqcomp _ _ _ (pr21 _ _ fg) (weqinv _ _ (pr22 _ _ fg))) is1).   apply (initmap _ (dnegf _ _ (fun ee:_ => pathsinv0 _ _ _ (stnsweqtoeq t0 t ee)) is2 n)). apply (iscontraprop1inv _ is1). Defined. 


Lemma isfiniteimplisfinite0 (X:UU1): isfinite X -> isfinite0 X.
Proof. intros. 
assert (nw: forall n:nat, forall w: weq (stn n) X, isfinite0 X). intros. split with n. apply (todneg _  w).  
apply (isfiniteimpl X (hProp1pair (isfinite0 X) (isapropisfinite0 X)) nw X0). Defined.


Definition card (X:UU1)(is: isfinite X): nat:= pr21 _ _ (isfiniteimplisfinite0 X is).

Definition preweq (X:UU1)(is: isfinite X): isofnel (card X is) X.
Proof. intros.  set (c:= card X is). set (dnw:= pr22 _ _ (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr21 nat (fun n : nat => isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw. 

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intros. destruct X0.  destruct t. 
assert (dw: dneg (weq (stn t) (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr21 _ _ ab) (weqinv _ _ (pr22 _ _ ab))).  apply (dnegf _ _ ff (isinhdnegand _ _ (todneg _ x0) x)). 
assert (e:paths _ t c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel. 
apply (isinhfunct _ _ f (isinhand (finitestruct X) _ (dirprodpair _ _ is (isinhpr _ dnw)))). Defined. 





(* To be completed 


Lemma finiteprops (X:UU1)(is1: isaprop X)(is2: isfinite X): coprod X  (neg X).
Proof. intros. 
assert (is: isaprop (coprod X (neg X))). apply isapropisdec. assumption. 
assert (f: (total2 nat (fun n:nat => weq (stn n) X)) -> coprod X (neg X)).  intros. destruct X0.  


*)


Definition finitestructstn (n:nat):= finitestructpair _ n (idweq _).
Definition isfinitestn (n:nat): isfinite (stn n) := isinhpr _ (finitestructstn n). 

Definition finitestructempty := finitestructpair _ O (idweq _).
Definition isfiniteempty : isfinite empty := isinhpr _ finitestructempty.

Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).
Definition isfiniteunit : isfinite unit := isinhpr _ finitestructunit. 

Definition finitestructbool := finitestructpair _ (S (S O)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (weqfromcoprodwithempty unit) (idweq unit)) boolascoprod).
Definition isfinitebool : isfinite bool  := isinhpr _ finitestructbool.

Definition finitestructinitinterval (n:nat) := finitestructpair _ (S n) (weqstntoinitinterval n).
Definition isfiniteinitinterval (n:nat):= isinhpr _ (finitestructinitinterval n).


Theorem finitestructweqf (X Y:UU1)(f:X -> Y)(is:isweq _ _ f) : finitestruct X -> finitestruct Y.
Proof. intros.   destruct X0. split with t. apply (weqcomp _ _ _ x (weqpair _ _ f is)). Defined. 

Theorem isfiniteweqf (X Y:UU1)(f:X -> Y)(is:isweq _ _ f) : isfinite X -> isfinite Y.
Proof. intros. apply (isinhfunct _ _ (finitestructweqf _ _ f is) X0). Defined. 


(* to be completed 

Theorem cardweqf (X Y:UU1)(f: X -> Y)(isw:isweq _ _ f)(isx: isfinite X): paths _ (card _ isx) (card _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *) 


Lemma finitestructcoprodwithunit  (X:UU1): finitestruct X -> finitestruct (coprod X unit).
Proof. intros.  destruct X0. split with (S t).  
assert (f: weq (stn t) X -> weq (stn (S t)) (coprod X unit)).  intro.  split with (coprodf _ _ _ _ (pr21 _ _ X0) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X0) (idisweq unit)). apply (f x). Defined. 

Lemma isfinitecoprodwithunit (X:UU1): isfinite X -> isfinite (coprod X unit).
Proof. intros. apply (isinhfunct _ _ (finitestructcoprodwithunit _) X0). Defined. 


Theorem finitestructcoprod (X Y:UU1) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (coprod X Y).
Proof. intros. destruct isy. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx.  split with t. apply (weqcomp _ _ _ (weqcomp _ _ _ (weqinv _ _ (weqfromcoprodwithempty (stn t))) (weqcoprodcomm empty (stn t))) (weqcoprodf _ _ _ _ x0 x)).  

intros.  set (st0t:= IHt (stn t) (coprod X unit) (finitestructcoprodwithunit _ isx) (idweq _ )). 
assert (w: weq (coprod (coprod X unit) (stn t)) (coprod X Y)). apply (weqcomp _ _ _ (weqcoprodasstor X unit (stn t)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq X) (weqcoprodcomm unit (stn t))) (weqcoprodf _ _ _ _ (idweq X) x))). 
apply (finitestructweqf _ _ _ (pr22 _ _ w) st0t). Defined.

Theorem isfinitecoprod (X Y:UU1) (isx: isfinite X)(isy: isfinite Y): isfinite (coprod X Y).
Proof. intros. apply (isinhfunct2 _ _ _ (finitestructcoprod X Y) isx isy). Defined.



Theorem finitestructdirprod (X Y:UU1) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (dirprod X Y).
Proof. intros. destruct isy. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx. split with O.  set (f:= fun xy:dirprod X Y => pr21 _ _ (weqinv _ _ x) (pr22 _ _ xy)). set (is:= isweqtoempty _ f). apply (weqinv _ _ (weqpair _ _ _ is)). 

intros. set (w:= weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq (dirprod X (stn t))) (weqtodirprodwithunit X)) (weqcomp _ _ _ (weqrdistrtoprod X (stn t) unit) (weqdirprodf _ _ _ _ (idweq X) x))). apply (finitestructweqf _ _ _ (pr22 _ _ w) (finitestructcoprod _ _ (IHt (stn t) X isx (idweq _)) isx)). Defined. 

Theorem isfinitedirprod (X Y:UU1)(isx: isfinite X)(isy: isfinite Y): isfinite (dirprod X Y).
Proof. intros. apply  (isinhfunct2 _ _ _ (finitestructdirprod X Y) isx isy). Defined.



Theorem finitestructcomplement (X:UU1)(x:X)(is:finitestruct X): finitestruct (complement X x).
Proof. intros.  destruct is.   destruct t.   apply (initmap _ (invmap _ _ _ (pr22 _ _ x0) x)).

set (w:= weqcomp _ _ _ (stnsposl1 t _ ) (weqinv _ _ (weqoncomplements _ _ x (weqinv _ _ x0)))). 
split with t. assumption.  Defined.  


Theorem  isfinitecomplement (X:UU1)(x:X)(is:isfinite X): isfinite (complement X x).
Proof. intros. apply (isinhfunct _ _ (finitestructcomplement X x) is). Defined. 


Theorem finitestructfromcomplement (X:UU1)(x:X)(is:isisolated _ x): finitestruct (complement X x) -> finitestruct X.
Proof. intros. destruct X0.  split with (S t). 
assert (w1: weq (coprod (complement X x) unit) X). apply (weqpair _ _ _ (isweqrecompl X x is)). apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ x0 (idweq _)) w1). Defined.


Theorem isfiniteifcomplement (X:UU1)(x:X)(is: isisolated _ x): isfinite (complement X x) -> isfinite X.
Proof. intros. apply (isinhfunct _ _ (finitestructfromcomplement X x is) X0). Defined. 


Theorem finitestructsummand (X Y:UU1)(is: finitestruct (coprod X Y)): finitestruct X.
Proof. intros. destruct is.  generalize X Y x.  clear X Y x. induction t.  intros.  split with O. assert (w: weq X empty). apply (weqpair _ _ _ (isweqtoempty _ (fun x0:X => invmap _ _ _ (pr22 _ _ x) (ii1 _ _ x0)))). apply (weqinv _ _ w).  

intros. set (xy:= pr21 _ _ x (ii2 _ _ tt)). 
assert (is: isisolated _ xy). apply (isolatedtoisolated _ _ _ (pr22 _ _ x) (ii2 _ _ tt) (isisolatedinstn (S t) (ii2 _ _ tt))). 
assert (w1: weq (stn t) (complement _ xy)).  apply (weqcomp _ _ _ (stnsposl0 t) (weqoncomplements _ _ (ii2 _ _ tt) x)). destruct xy. 
assert (w2: weq (complement (coprod X Y) (ii1 X Y x0)) (coprod (complement X x0) Y)). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii1x _ _ x0))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)).

assert (isx: isisolated _ x0). apply (isolatedifisolatedii1 _ _ _ is). apply (finitestructfromcomplement _ _ isx is1). 

assert (w2: weq (complement (coprod X Y) (ii2 X Y y)) (coprod X (complement Y y))). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii2y _ _ y))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)). assumption.  Defined. 

Theorem isfinitesummand (X Y:UU1)(is:isfinite (coprod X Y)): isfinite X.
Proof. intros.  apply (isinhfunct _ _ (finitestructsummand X Y) is). Defined. 


Theorem finitestructsubset (X:UU1)(f:X -> bool): finitestruct X -> finitestruct (hfiber _ _ f true).
Proof. intros. 
assert (w: weq (coprod (hfiber _ _ f true) (hfiber _ _ f false)) X). apply weqsubsetsplit. apply (finitestructsummand _ _ (finitestructweqf _ _ _ (pr22 _ _ (weqinv _ _ w)) X0)).   Defined. 


Theorem isfinitesubset  (X:UU1)(f:X -> bool): isfinite X -> isfinite (hfiber _ _ f true).
Proof. intros. apply  (isinhfunct _ _ (finitestructsubset X f) X0). Defined. 


















(** ** Test computations. *)



(*Eval compute in card _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O))))).*)

Eval lazy in card _ (isfiniteempty).

Eval compute in card _ (isfiniteunit).

Eval lazy in card _  (isfinitebool).




(*Eval lazy in   (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).*)
 



Eval lazy in card _ (isfinitecomplement _ true isfinitebool).

Eval compute in card _ (isfinitedirprod _ _ isfinitebool isfinitebool).

Eval compute in card _ (isfinitedirprod _ _ isfinitebool (isfinitedirprod _ _ isfinitebool isfinitebool)).

Eval compute in card _ (isfinitecoprod _ _ (isfinitebool) (isfinitecomplement _ (ii1 _ _ (ii2 _ _ tt)) (isfinitestn (S (S (S O)))))).

Eval lazy in card _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).

(*Eval compute in  card _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).*)

(*Eval compute in card _ (isfinitecomplement _ (dirprodpair _ _ tt tt) (isfinitedirprod _ _ isfiniteunit isfiniteunit)).*)


(*Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).*)

Eval lazy in (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).
 


Eval lazy in card _ (isfinitecomplement _ (dirprodpair _ _ true (dirprodpair _ _ true false)) (isfinitedirprod _ _ (isfinitebool) (isfinitedirprod _ _ (isfinitebool) (isfinitebool)))).



  






(** * Composable sequences of functions. *) 


Fixpoint seqplus (n:nat) : u2.total2 UU1 (fun T:UU1 => (T -> UU0)) := match n with 
O =>  u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) UU0 (fun X:_ => X) |
S m => u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) ( total2 (u2.pr21 _ _ (seqplus m)) (fun D:_ =>  total2 UU0 (fun Y:_ => ((u2.pr22 _ _ (seqplus m) D) -> Y)))) (fun E:_ =>  pr21 _ _ ( pr22 _ _ E))
end. 

Definition seq (n:nat): UU1 := u2.pr21 _ _ (seqplus n). (** The type of composable sequences of functions of length n. *)

Definition lasttype (n:nat) (s:seq n): UU0 := u2.pr22 _ _ (seqplus n) s. (** The last type in the sequence of functions s. *)



(** To univ.v *)

Definition d0:= initintervalpair 1 O (idpath _ _).

Definition d1:= initintervalpair 1 1 (idpath _ _).


(** ** Simplicial objects without degeneracies.


We define inductively, for any n:nat, the following objects:

1. dfsslen n : UU1.  - the type of degeneracy free simplicial objects of dimension less or equal to n in UU0.

2. homdfsslen n: forall X Y : dfsslen n, UU0.  - the type of morphisms from X to Y.

3. compdfsslen n: forall X Y Z: dfsslen n, homdfsslen n X Y -> homdfsslen n Y Z -> homdfsslen n X Z. - the composition opf morphisms which will be strictly associative. 

4. associativity.


5. dfskndeltam n : forall m:nat, dfsslen n. - the degeneracy free part of the n-th skeleton of the simplex of dimension m. The morphisms from it to a simplicial object X in the category of degeneracy free objects are the same as morphisms from the complete n-skeleton of m-dimensional simplex to X in the category of simplicial sets. 

For (n =) O we define these ingredients as follows:

1. dfsslen O := UU0.

2. homdfsslen O := fun X Y : dfsslen O => (X -> Y).

3. compdfsslen O := fun X Y Z : dfsslen O => fun  f: X -> Y => fun g Y -> Z =>  fun x:X => (g (f x)).

4. idpath.

5. dfskndeltam O := fun m:nat => initinterval m.




For S n  as follows:

1. dfsslen (S n) := u1.total2 (dfsslen n) (fun sknX:_ => (homdfsslen n (dfskndeltam n (S n)) sknX) -> UU0).  In words, a d.f. simplicial object X of dimension (S n) is a pair which consists of a d.f. simplicial object sknX of dimension n together with a mapping which assigns to each morphism from the boundary of n-dimensional simplex to sknX the type of all n-simplexes of X with this boundary. 

2. homdfsslen (S n) (tpair _ _ sknX phiX) (tpair _ _ sknY phiY) := total2 (homdfsslen n sknX sknY) (fun sknff:_ => forall gamma: homdfsslen n (dfskndeltam n (S n)) sknX, phiX gamma -> phiY (compdfsslen n _ sknX sknY gamma sknff)). 

3. compdfsslen (S n) (tpair _ _ sknX phiX) (tpair _ _ sknY phiY) (tpair _ _ sknZ phiZ) (tpair _ _ sknff fsn) (tpair _ _ sknfg gsn) := tpair _ _ (compdfsslen n sknff sknfg) (fun gamma: homdfsslen n (dfskndeltam n (S n)) sknX => (fun xn: phiX gamma => gsn (compdfsslen n _ sknX sknY gamma sknff) (fsn gamma xn))).  

4. ...

5. dfskndeltam (S n) := fun m:nat => tpair _ _ (dfskndeltam n m) (fun gamma : homdfsslen n (dfskndeltam n (S n)) (dfskndeltam n m) => 

if n >= m then empty
if n < m and n > O then unit
if n < m and n = O then
  if gamma O < gamma 1 then unit
  if gamma O >= gamma 1 then empty.)  Note, this requires us to define notations for the points of initinterval and <= and > on initinterval. 


 
match leb m n with 
true => empty |
false =>
match n with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S k => unit 
end
end.
 
*)

Fixpoint t1 (n:nat) : Type :=
match n with
O => (prod unit unit) |
S k => unit
end.

Fixpoint t2 (n:nat) : t1 n  :=
match n with 
O => (tt, tt) |
S k => tt
end.





Record dfssrecord : UU2 := { 
c1 : UU1 ; 
c2: forall X Y: c1, UU0 ; 
c3: forall X Y Z :c1, (c2 X Y) -> (c2 Y Z) -> (c2 X Z) ; 
c4: forall (X Y Z T:c1)(f: c2 X Y)(g: c2 Y Z)(h: c2 Z T), paths _  (c3 _ _ _ (c3 _ _ _ f g) h) (c3 _ _ _ f (c3 _ _ _ g h)); 
c5: forall m:nat, c1 }.



Definition dfssleO: dfssrecord := {| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c4:= fun (X Y Z T: UU0) (f: X -> Y)(g:Y -> Z)(h: Z -> T) => idpath _ _ ;
c5:= fun m:nat => initinterval m |}.


Definition c1next (n:nat)(IH: dfssrecord):= u1.total2 IH.(c1) (fun sknX:_ => (IH.(c2) (IH.(c5) (S n)) sknX) -> UU0).


Definition c2next (n:nat)(IH: dfssrecord):= fun X: c1next n IH => match X with u1.tpair sknX phiX  => fun Y: c1next n IH  =>
 match Y with u1.tpair sknY phiY =>
 total2 ((IH).(c2) sknX sknY) (fun sknff:_ => forall gamma: (IH).(c2) ((IH).(c5) (S n)) sknX, phiX gamma -> phiY ((IH).(c3) _ sknX sknY gamma sknff)) end end.


Definition c3next (n:nat)(IH: dfssrecord): forall (X Y Z: c1next n IH), (c2next n IH) X Y -> (c2next n IH) Y Z -> (c2next n IH) X Z.
Proof. intros. destruct X.  rename t into sknX. rename x into phiX. destruct Y. rename t into sknY. rename x into phiY. destruct Z.  rename t into sknZ. rename x into phiZ. destruct X0.  rename t into sknff. rename x into fsn. destruct X1.  rename t into sknfg. rename x into gsn. simpl. split with ((IH).(c3) _ _ _ sknff sknfg). intro. intro. rename X into xn. simpl. set   (int:=gsn _ (fsn gamma xn)). apply (transportf _ _ _ _ ((IH).(c4) _ _ _ _ gamma sknff sknfg) int). Defined. 



Definition c4next (n:nat)(IH: dfssrecord): forall (X Y Z T:c1next n IH)(f: (c2next n IH) X Y)(g: (c2next n IH) Y Z)(h: (c2next n IH) Z T), paths _  ((c3next n IH) _ _ _ ((c3next n IH) _ _ _ f g) h) ((c3next n IH) _ _ _ f ((c3next n IH) _ _ _ g h)).
Proof. intros. destruct X. destruct Y. destruct Z. destruct T.    destruct f. destruct g. destruct h. simpl.  


Definition dfssle (n:nat) : dfssrecord. 
Proof. intro. induction n. apply dfssleO.

set (cc1 := u1.total2 IHn.(c1) (fun sknX:_ => (IHn.(c2) (IHn.(c5) (S n)) sknX) -> UU0)).

set (cc1pair:= u1.tpair IHn.(c1) (fun sknX:_ => (IHn.(c2) (IHn.(c5) (S n)) sknX) -> UU0)).

set (cc2 := fun X: cc1  => match X with u1.tpair sknX phiX  => fun Y: cc1 =>
 match Y with u1.tpair sknY phiY =>
 total2 ((IHn).(c2) sknX sknY) (fun sknff:_ => forall gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX, phiX gamma -> phiY ((IHn).(c3) _ sknX sknY gamma sknff)) end end ).





assert  (cc3: forall  X Y Z :cc1, (cc2 X Y) -> (cc2 Y Z) -> (cc2 X Z)).

intros. destruct X.  rename t into sknX. rename x into phiX. destruct Y. rename t into sknY. rename x into phiY. destruct Z.  rename t into sknZ. rename x into phiZ. destruct X0.  rename t into sknff. rename x into fsn. destruct X1.  rename t into sknfg. rename x into gsn. simpl. split with ((IHn).(c3) _ _ _ sknff sknfg). intro. intro. rename X into xn. simpl. set   (int:=gsn _ (fsn gamma xn)). apply (transportf _ _ _ _ ((IHn).(c4) _ _ _ _ gamma sknff sknfg) int).

unfold cc3.


assert (cc4: forall (X Y Z T:cc1)(f: cc2 X Y)(g: cc2 Y Z)(h: cc2 Z T), paths _  (cc3 _ _ _ (cc3 _ _ _ f g) h) (cc3 _ _ _ f (cc3 _ _ _ g h))). intros. 





set (cc3 := fun X: cc1 => match X with u1.tpair sknX phiX => fun Y: cc1 =>  match Y with u1.tpair sknY phiY => fun Z: cc1 =>  match Z with u1.tpair sknZ phiZ => fun f: total2 ((IHn).(c2) sknX sknY) (fun sknff:_ => forall gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX, phiX gamma -> phiY ((IHn).(c3) _ sknX sknY gamma sknff)) => match f with tpair sknff fsn => fun g: _  =>  match g with tpair sknfg gsn =>
   tpair  ((IHn).(c2) sknX sknZ) (fun sknfh: _ => forall gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX, phiX gamma -> phiZ ((IHn).(c3) _ sknX sknZ gamma sknfh)) ((IHn).(c3) sknX sknY sknZ sknff sknfg) (fun gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX => (fun xn: phiX gamma => (transportf _ _ _ _ ((IHn).(c4) ((IHn).(c5) (S n)) sknX sknY sknZ gamma sknff sknfg) (gsn _ (fsn gamma xn))))) end end end end end).  



set (cc3 := fun X: cc1 => match X with u1.tpair sknX phiX => fun Y: cc1 =>  match Y with u1.tpair sknY phiY => fun Z: cc1 =>  match Z with u1.tpair sknZ phiZ => fun f: cc2 (cc1pair sknX phiX) (cc1pair sknY phiY) => match f with tpair sknff fsn => fun g: cc2 Y Z  =>  match g with tpair sknfg gsn =>
   tpair  ((IHn).(c2) sknX sknZ) (fun sknfh: _ => forall gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX, phiX gamma -> phiZ ((IHn).(c3) _ sknX sknZ gamma sknfh)) ( (IHn).(c3) sknX sknY sknZ sknff sknfg) (fun gamma: (IHn).(c2) ((IHn).(c5) (S n)) sknX => (fun xn: phiX gamma => (transportf _ _ _ _ ((IHn).(c4) _ _ _ _ gamma sknff sknfg) (gsn ((IHn).(c3) _ sknX sknY gamma sknff) (fsn gamma xn)))) end end end end end).  
  
c5:= fun m:nat => tpair _ _ ((IHn).(c5) m) (fun gamma : _ ((IHn).(c5) (S k)) ((IHn).(c5) m) => 
match leb m k with 
true => empty |
false =>
match k with     
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.





(* Fixpoint dfssle (n:nat) : dfssrecord := match n with

O => {| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c5:= fun m:nat => initinterval m |} |

S k  => {| 

c1 := u1.total2 (dfssle k).(c1) (fun sknX:_ => ((dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX) -> UU0) ; 

c2 := fun X:_  => match X with u1.tpair sknX phiX  => fun Y: _ =>
 match Y with u1.tpair sknY phiY =>
 total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) end end ; 

c3 := fun X: _ => match X with u1.tpair sknX phiX => fun Y: _ =>  match Y with u1.tpair sknY phiY => fun Z: _ =>  match Z with u1.tpair sknZ phiZ => fun f: total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) => match f with tpair sknff fsn => fun g: _  =>  match g with tpair sknfg gsn =>
   tpair _ _ ( _  sknff sknfg) (fun gamma: (dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX => (fun xn: phiX gamma => gsn ((dfssle k).(c3) _ sknX sknY gamma sknff) (fsn gamma xn))) end end end end end; 
  
c5:= fun m:nat => tpair _ _ ((dfssle k).(c5) m) (fun gamma : _ ((dfssle k).(c5) (S k)) ((dfssle k).(c5) m) => 
match leb m k with 
true => empty |
false =>
match k with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.

*)





(* Bacck-up copy:

Fixpoint dfssle (n:nat) : dfssrecord := match n with

O => {| 
c1 := UU0  ;
c2 := fun X Y: UU0 => (X -> Y) ; 
c3 := fun X Y Z : UU0 => fun f:X -> Y => fun g: Y -> Z => fun x:X => (g (f x)) ; 
c5:= fun m:nat => initinterval m |} |

S k  => {| 

c1 := u1.total2 (dfssle k).(c1) (fun sknX:_ => ((dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX) -> UU0) ; 

c2 := fun X:_  => fun Y: _ =>
match X with u1.tpair sknX phiX  => match Y with u1.tpair sknY phiY =>
 total2 ((dfssle k).(c2) sknX sknY) (fun sknff:_ => forall gamma: (dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX, phiX gamma -> phiY ((dfssle k).(c3) _ sknX sknY gamma sknff)) end end ; 

c3 := fun X: _ => fun Y: _ => fun Z: _ => fun f: _ => fun g: _  =>
match X with u1.tpair sknX phiX  => match Y with u1.tpair sknY phiY =>  match Z with u1.tpair sknZ phiZ => match f with tpair sknff fsn => match g with tpair sknfg gsn => tpair _ _ ( _  sknff sknfg) (fun gamma: (dfssle k).(c2) ((dfssle k).(c5) (S k)) sknX => (fun xn: phiX gamma => gsn ((dfssle k).(c3) _ sknX sknY gamma sknff) (fsn gamma xn))) end end end end end; 
  
c5:= fun m:nat => tpair _ _ ((dfssle k).(c5) m) (fun gamma : _ ((dfssle k).(c5) (S k)) ((dfssle k).(c5) m) => 
match leb m k with 
true => empty |
false =>
match k with 
O => 
match leb (initintervaltonat (gamma d1)) (initintervaltonat (gamma d0)) with
true => empty |
false => unit
end | 
S l => unit 
end
end)
|} 
end.

 *)










 


(* End of file experiments.v *)