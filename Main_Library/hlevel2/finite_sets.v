(** * Finite sets. 

This file contains the definition and main properties of finite sets. At the end of the file there are several elementary examples which are used as test cases to check that our constructions do not prevent Coq from normalizing terms of type nat to numerals. This file has not been updated from the previous version.

*)









(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp.




(** ** Standard finite sets. *)



Fixpoint stn (n:nat):UU0:= match n with
O => empty|
S m => coprod (stn m) unit
end.

 

Lemma isisolatedinstn (n:nat): forall x: stn n, isisolated _ x.
Proof. intro.   induction n. intro. apply (initmap _ x). intro.  simpl in x.  destruct x. apply (isolatedtoisolatedii1 _ _ s (IHn s)). destruct u. 
apply disjointl1.  Defined. 



Corollary isdeceqstn (n:nat): isdeceq (stn n).
Proof. intro.  unfold isdeceq. apply (isisolatedinstn n). Defined. 


Lemma stnsnegl1 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro X.  apply (pr21 _ _ X lp). Defined.

Lemma stnsnegl2 (n:nat): neg (weq (stn O) (stn (S n))).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro X.  apply (pr21 _ _ (weqinv _ _ X) lp). Defined.


Lemma stnsposl0 (n:nat): weq (stn n) (complement (stn (S n)) (ii2 _ _ tt)).
Proof. intros. split with (tocompltodisjoint (stn n)). apply isweqtocompltodisjoint. Defined.

Lemma stnsposl1 (n:nat)(x: stn (S n)): weq (stn n) (complement (stn (S n)) x).
Proof. intro. induction n. intros. simpl in x.  destruct x.  apply (initmap _ e). simpl. destruct u. apply (stnsposl0 O). intro. simpl in x. destruct x. set  (g:=tocompltoii1x _ unit c).  set (f:= coprodf _ _ _ _ (pr21 _ _ (IHn c)) (fun t:unit => t)).  split with (fun x:_ => g (f x)). 
assert (is1:isweq _ _ f). apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ (IHn c)) (idisweq unit)). 
assert (is2: isweq _ _ g). apply (isweqtocompltoii1x _ unit c). 
apply (twooutof3c _ _ _ f g is1 is2). 
destruct u. split with (tocompltodisjoint _). apply (isweqtocompltodisjoint _).  Defined.



Lemma stnsposl2 (n n':nat): weq (stn (S n)) (stn (S n')) -> weq (stn n) (stn n').
Proof. intros n n' X. destruct X as [ff is] .    simpl in ff. set (int1:= complement (stn (S n')) (ff (ii2 _ _ tt))).
set (f1:= tocompltodisjoint (stn n)).  
set (f2:= maponcomplementsweq _ _ ff is (ii2 _ _ tt)).
set (f3:= invmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
assert (is1: isweq _ _ f1). apply isweqtocompltodisjoint. 
assert (is2: isweq _ _ f2). apply isweqmaponcomplements.
assert (is3: isweq _ _ f3). apply (isweqinvmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
set (gg:= fun xx:_ => (f3 (f2 (f1 xx)))). split with gg.
apply (twooutof3c _ _ _ _ _ (twooutof3c _ _ _ _ _ is1 is2) is3). Defined.



Theorem stnsweqtoeq (n n':nat): (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intro. induction n. intro. induction n'.  intros. apply idpath. intro X. apply (initmap _ (stnsnegl2  n' X)).  
 intro. induction n'. intro X. set (int:= isdeceqnat O (S n)).  destruct int.  assumption. apply (initmap _ (stnsnegl1 n X)).  intro X. 
set (e:= IHn n' (stnsposl2 n n' X)). apply (maponpaths _ _ S _ _ e). Defined. 

Corollary stnsdnegweqtoeq (n n':nat): dneg (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intros n n' X. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf _ _ (stnsweqtoeq n n') X)). Defined. 






(** ** Sets with fixed number of elements. *)



Definition nelstruct (n:nat)(X:UU0):= weq (stn n) X. 
Definition isofnel (n:nat)(X:UU0) := ishinh (weq (stn n) X). 

Definition isofnelstn (n:nat): isofnel n (stn n) := hinhpr _ (idweq (stn n)).

Lemma isofnelimpl (n:nat)(X:UU0)(isx: isofnel n X)(P: hProp): ((weq (stn n) X) -> P) -> (isofnel n X -> P).
Proof. intros.  apply hinhuniv with (weq (stn n) X). assumption. assumption. Defined. 



Lemma isof0ela (X:UU0): isofnel O X -> neg X.
Proof. intros X X0. intro X1. apply (isofnelimpl O X X0 hfalse). intro X2.  apply (invmap _ _ _ (pr22 _ _ X2) X1). assumption.  Defined. 


Lemma isof0elb (X:UU0): neg X -> isofnel O X.
Proof. intros X X0. apply (hinhpr _ (weqinv _ _ (weqpair _ _ _ (isweqtoempty _ X0)))). Defined. 


Corollary isof0elempty: isofnel O empty.
Proof. apply (isof0elb empty (fun x:_ => x)). Defined. 

Lemma isof1ela (X:UU0): isofnel (S O) X -> iscontr X.
Proof. intros X X0.  apply (isofnelimpl (S O) X X0 (iscontr_hprop X)).  set (w2:= (weqinv _ _ (weqfromcoprodwithempty unit))). intro X1.  set (w3:= weqcomp _ _ _ w2 X1). apply (iscontrifweqtounit _ (weqinv _ _ w3)). assumption. Defined.  

Lemma isof1elb (X:UU0): (iscontr X) -> isofnel (S O) X.
Proof. intros X X0. set (w1:= weqpair _ _ _ (isweqcontrtounit _ X0)). set (w2:= weqfromcoprodwithempty unit).  set (w:= weqcomp _ _ _ w2 (weqinv _ _ w1)). apply (hinhpr _ w). Defined. 


Lemma isof1elunit: isofnel (S O) unit.
Proof. apply (hinhpr _ (weqfromcoprodwithempty unit)). Defined. 


Lemma isofsnel (n:nat)(X:UU0): isofnel n X -> isofnel (S n) (coprod X unit).
Proof. intros n X X0. 
assert (f: weq (stn n) X -> weq (stn (S n)) (coprod X unit)).  intro X1.  split with (coprodf _ _ _ _ (pr21 _ _ X1) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X1) (idisweq unit)). apply (hinhfunct _ _ f X0). Defined.


Lemma isofnelweqf (n:nat)(X Y:UU0)(f:X -> Y)(is: isweq _ _ f): isofnel n X -> isofnel n Y.
Proof. intros n X Y f is X0.  set (ff:= fun u:weq (stn n) X => weqcomp _ _ _ u (weqpair _ _ f is)). apply (hinhfunct _ _ ff X0). Defined.


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
Proof. intro. induction n.  simpl.  intro X. apply (nopathsfalsetotrue X). assumption.  Defined.


Lemma istransleb (k m n : nat): paths _ (leb k m) true -> paths _ (leb m n) true -> paths _ (leb k n) true.
Proof. intro. induction k.  intros.  simpl. apply idpath. intro. destruct m.  intros n X X0.   simpl in X.   apply (initmap _ (nopathsfalsetotrue X)). intro. destruct n.  intros X X0.  apply (initmap _ (nopathsfalsetotrue X0)). simpl. apply (IHk m n).  Defined. 


Lemma is0leb0 (n:nat) : paths _ (leb n 0) true -> paths _ n 0.
Proof.  intro. destruct n. intro.   apply idpath.  intro X. apply (initmap _ (nopathsfalsetotrue X)). Defined. 

Lemma lebsnchoice0 (x n:nat): paths _ (leb x (S n)) true -> (neg (paths _ x (S n))) -> paths _ (leb x n) true.
Proof. intro. induction x.  intros. apply idpath.  intro. destruct n.  intros X X0.  simpl in X.  destruct x.  apply (initmap _ (X0 (idpath _ _))). simpl in X.  apply (initmap _ (nopathsfalsetotrue X)). intros X X0. simpl in X.  set (a:= IHx n X (negf _ _ (maponpaths _ _ S _ _) X0)).  assumption.  Defined. 

Lemma lebsnchoice (x n:nat) : paths _ (leb x (S n)) true -> coprod (paths _ (leb x n) true) (paths _ x (S n)).
Proof. intros x n X. set (s:= isdeceqnat (S n) x).  destruct s.  apply (ii2 _ _ p).
apply (ii1 _ _ (lebsnchoice0 x n X e)).  Defined. 


Definition initinterval (n:nat) := total2 nat (fun x:nat => paths _ (leb x n) true).
Definition initintervalpair (n:nat):= tpair  nat (fun x:nat => paths _ (leb x n) true).
Definition initintervaltonat (n:nat): initinterval n -> nat := pr21 _ _. 

Lemma isinclinitintervaltonat (n:nat) : isincl _ _ (initintervaltonat n).
Proof. intro.  apply isofhlevelfpr21. intro. intro.  intro. apply (isasetbool (leb x n) true). Defined. 

Definition initintervalsincl (m n:nat)(isle: paths _ (leb m n) true) : initinterval m -> initinterval n.
Proof. intros m n isle X. destruct X as [ t x ].  split with t.  simpl. apply (istransleb t m n x isle).  Defined. 
 

Lemma iscontrinitinterval0 : iscontr (initinterval O).
Proof. split with (initintervalpair O O (isreflleb O)).  intro. destruct t as [ t x ].  assert (e: paths _ O t). apply (pathsinv0 _ _ _ (is0leb0 t x)).  destruct e. simpl.  apply (invmaponpathsincl _ _ _ (isinclinitintervaltonat O) (tpair nat (fun x0 : nat => paths bool (leb x0 O) true) O x)
     (initintervalpair O O (idpath bool true)) (idpath _ O)). Defined. 


Definition toinitintervalsn (n:nat):  (coprod (initinterval n) unit) -> (initinterval (S n)) := sumofmaps ( initintervalsincl n (S n) (islebnsn n)) (fun t:unit => initintervalpair (S n) (S n) (isreflleb (S n))).

Definition frominitintervalsn (n:nat): initinterval (S n) -> coprod (initinterval n) unit.
Proof. intros n X.   destruct X as [ t x ].  destruct (isdeceqnat (S n) t).  apply (ii2 _ _ tt).  apply (ii1 _ _ (initintervalpair n t (lebsnchoice0 t n x e))).   Defined. 


Definition weqtoinitintervalsn  (n:nat) : weq  (coprod (initinterval n) unit) (initinterval (S n)).
Proof. intro. set (f:= toinitintervalsn n). set (g:= frominitintervalsn n). split with f. 
set (u:= coprodf _ _ _ _ (initintervaltonat n) (fun t:unit => t)).   assert (is: isincl _ _ u). apply (isofhlevelfcoprodf (S O) _ _ _ _ _ _ (isinclinitintervaltonat n) (isofhlevelfweq (S O) _ _ _ (idisweq unit))).  
assert (egf: forall x:_, paths _ (g (f x)) x).  intro. 
assert (egf0: paths _ (u (g (f x))) (u x)).  destruct x. simpl. destruct i as [ t x ]. destruct t.   simpl.  apply idpath. simpl. destruct (isdeceqnat n t).    simpl. induction p. apply (initmap _ (neglebsnn t x)).  simpl.  apply idpath.  destruct u0. destruct n.  apply idpath. simpl.  destruct (isdeceqnat n n). apply idpath.  apply (initmap _ (e (idpath _ _))). apply (invmaponpathsincl _ _ _ is _ _ egf0). 
assert (efg: forall x:_, paths _ (f (g x)) x). intro. 
assert (efg0: paths _ (initintervaltonat (S n) (f (g x))) (initintervaltonat (S n) x)).  destruct x as [ t x ]. simpl.  destruct t. apply idpath. destruct (isdeceqnat n t).  simpl. apply (pathsinv0 _ _ _ (maponpaths _ _ S _ _ p)).  simpl.  apply idpath.  apply  (invmaponpathsincl _ _ _ (isinclinitintervaltonat _)  _ _ efg0). 
apply (gradth _ _ _ _ egf efg). Defined.  



Theorem weqstntoinitinterval (n:nat): weq (stn (S n)) (initinterval n).
Proof. intro. induction n. set (w1:= weqfromcoprodwithempty unit). set (w2:= weqinv _ _ (weqpair _ _ _ (isweqcontrtounit _ (iscontrinitinterval0)))).     apply (weqcomp _ _ _ w1 w2).  apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ IHn (idweq unit)) (weqtoinitintervalsn n)). Defined. 





(** ** General finite sets. *)



Definition finitestruct (X:UU0):= total2 nat (fun n:nat => weq (stn n) X).
Definition finitestructpair (X:UU0) := tpair nat (fun n:nat => weq (stn n) X).
Definition isfinite (X:UU0):= ishinh (finitestruct X).
Definition isfiniteimpl (X:UU0)(P: hProp): (forall n:nat, forall w: weq (stn n) X, P) -> isfinite X -> P.
Proof. intros X P X0 X1. set (f0:= fun xx:(total2 nat (fun n:_ => weq (stn n) X)) => (X0 (pr21 _ _ xx) (pr22 _ _ xx))).  apply (hinhuniv (total2 nat (fun n:nat => weq (stn n) X)) P f0 X1). Defined. 


Definition isfiniteifofnel (n:nat)(X:UU0): isofnel n X -> isfinite X.
Proof. intros n X X0.  apply (hinhfunct _ _ (fun w:weq (stn n) X => finitestructpair _ n w) X0).  Defined.



Definition isofnel0 (n:nat)(X:UU0):= dneg (weq (stn n) X).
Definition isfinite0 (X:UU0):= total2 nat (fun n:_ => isofnel0 n X).



Lemma isapropisfinite0 (X:UU0): isaprop (isfinite0 X).
Proof. intros. assert (is1: (isfinite0 X) -> (iscontr (isfinite0 X))).  intro X0. unfold iscontr. split with X0.  intro. destruct X0 as [ t0 x ].  destruct t as [ t x0 ].
assert (c1: coprod (paths _ t t0) (neg (paths _ t t0))). apply isdeceqnat. destruct c1.  apply (invmaponpathsincl (isfinite0 X) nat (pr21 _ _) (isofhlevelfpr21 (S O) _ _  (fun n:nat => isapropdneg (weq (stn n) X))) (tpair nat (fun n : nat => isofnel0 n X) t x0) (tpair nat (fun n : nat => isofnel0 n X) t0 x) p).  
assert (is1: dneg (dirprod (weq (stn t0) X) (weq (stn t) X))). apply (dneganddnegimpldneg _ _ x x0). 
assert (is2: dneg (weq (stn t0) (stn t))). apply (dnegf _ _ (fun fg: dirprod (weq (stn t0) X) (weq (stn t) X) => weqcomp _ _ _ (pr21 _ _ fg) (weqinv _ _ (pr22 _ _ fg))) is1).   apply (initmap _ (dnegf _ _ (fun ee:_ => pathsinv0 _ _ _ (stnsweqtoeq t0 t ee)) is2 n)). apply (iscontraprop1inv _ is1). Defined. 


Definition isfinite0_hprop (X : UU0) := hProppair (isfinite0 X) (isapropisfinite0 X).


Lemma isfiniteimplisfinite0 (X:UU0): isfinite X -> isfinite0 X.
Proof. intros X X0. 
assert (nw: forall n:nat, forall w: weq (stn n) X, isfinite0 X). intros. split with n. apply (todneg _  w).  
apply (isfiniteimpl X (isfinite0_hprop X) nw X0). Defined.




(* To be completed 


Lemma finiteprops (X:UU0)(is1: isaprop X)(is2: isfinite X): coprod X  (neg X).
Proof. intros. 
assert (is: isaprop (coprod X (neg X))). apply isapropisdec. assumption. 
assert (f: (total2 nat (fun n:nat => weq (stn n) X)) -> coprod X (neg X)).  intros. destruct X0.  


*)


Definition finitestructstn (n:nat):= finitestructpair _ n (idweq _).
Definition isfinitestn (n:nat): isfinite (stn n) := hinhpr _ (finitestructstn n). 

Definition finitestructempty := finitestructpair _ O (idweq _).
Definition isfiniteempty : isfinite empty := hinhpr _ finitestructempty.

Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).
Definition isfiniteunit : isfinite unit := hinhpr _ finitestructunit. 

Definition finitestructbool := finitestructpair _ (S (S O)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (weqfromcoprodwithempty unit) (idweq unit)) boolascoprod).
Definition isfinitebool : isfinite bool  := hinhpr _ finitestructbool.

Definition finitestructinitinterval (n:nat) := finitestructpair _ (S n) (weqstntoinitinterval n).
Definition isfiniteinitinterval (n:nat):= hinhpr _ (finitestructinitinterval n).


Theorem finitestructweqf (X Y:UU0)(f:X -> Y)(is:isweq _ _ f) : finitestruct X -> finitestruct Y.
Proof. intros X Y f is X0.   destruct X0 as [ t x ]. split with t. apply (weqcomp _ _ _ x (weqpair _ _ f is)). Defined. 

Theorem isfiniteweqf (X Y:UU0)(f:X -> Y)(is:isweq _ _ f) : isfinite X -> isfinite Y.
Proof. intros X Y f is X0. apply (hinhfunct _ _ (finitestructweqf _ _ f is) X0). Defined. 


Lemma finitestructcoprodwithunit  (X:UU0): finitestruct X -> finitestruct (coprod X unit).
Proof. intros X X0.  destruct X0 as [ t x ]. split with (S t).  
assert (f: weq (stn t) X -> weq (stn (S t)) (coprod X unit)).  intro X0.  split with (coprodf _ _ _ _ (pr21 _ _ X0) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X0) (idisweq unit)). apply (f x). Defined. 

Lemma isfinitecoprodwithunit (X:UU0): isfinite X -> isfinite (coprod X unit).
Proof. intros X X0. apply (hinhfunct _ _ (finitestructcoprodwithunit _) X0). Defined. 


Theorem finitestructcoprod (X Y:UU0) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (coprod X Y).
Proof. intros. destruct isy as [ t x ]. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx as [ t x0 ].  split with t. apply (weqcomp _ _ _ (weqcomp _ _ _ (weqinv _ _ (weqfromcoprodwithempty (stn t))) (weqcoprodcomm empty (stn t))) (weqcoprodf _ _ _ _ x0 x)).  

intros.  set (st0t:= IHt (stn t) (coprod X unit) (finitestructcoprodwithunit _ isx) (idweq _ )). 
assert (w: weq (coprod (coprod X unit) (stn t)) (coprod X Y)). apply (weqcomp _ _ _ (weqcoprodasstor X unit (stn t)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq X) (weqcoprodcomm unit (stn t))) (weqcoprodf _ _ _ _ (idweq X) x))). 
apply (finitestructweqf _ _ _ (pr22 _ _ w) st0t). Defined.

Theorem isfinitecoprod (X Y:UU0) (isx: isfinite X)(isy: isfinite Y): isfinite (coprod X Y).
Proof. intros. apply (hinhfunct2 _ _ _ (finitestructcoprod X Y) isx isy). Defined.



Theorem finitestructdirprod (X Y:UU0) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (dirprod X Y).
Proof. intros. destruct isy as [ t x ]. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx as [ t x0 ]. split with O.  set (f:= fun xy:dirprod X Y => pr21 _ _ (weqinv _ _ x) (pr22 _ _ xy)). set (is:= isweqtoempty _ f). apply (weqinv _ _ (weqpair _ _ _ is)). 

intros. set (w:= weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq (dirprod X (stn t))) (weqtodirprodwithunit X)) (weqcomp _ _ _ (weqrdistrtoprod X (stn t) unit) (weqdirprodf _ _ _ _ (idweq X) x))). apply (finitestructweqf _ _ _ (pr22 _ _ w) (finitestructcoprod _ _ (IHt (stn t) X isx (idweq _)) isx)). Defined. 

Theorem isfinitedirprod (X Y:UU0)(isx: isfinite X)(isy: isfinite Y): isfinite (dirprod X Y).
Proof. intros. apply  (hinhfunct2 _ _ _ (finitestructdirprod X Y) isx isy). Defined.



Theorem finitestructcomplement (X:UU0)(x:X)(is:finitestruct X): finitestruct (complement X x).
Proof. intros.  destruct is as [ t x0 ].   destruct t.   apply (initmap _ (invmap _ _ _ (pr22 _ _ x0) x)).

set (w:= weqcomp _ _ _ (stnsposl1 t _ ) (weqinv _ _ (weqoncomplements _ _ x (weqinv _ _ x0)))). 
split with t. assumption.  Defined.  


Theorem  isfinitecomplement (X:UU0)(x:X)(is:isfinite X): isfinite (complement X x).
Proof. intros. apply (hinhfunct _ _ (finitestructcomplement X x) is). Defined. 


Theorem finitestructfromcomplement (X:UU0)(x:X)(is:isisolated _ x): finitestruct (complement X x) -> finitestruct X.
Proof. intros X x is X0. destruct X0 as [ t x0 ].  split with (S t). 
assert (w1: weq (coprod (complement X  x) unit) X). apply (weqpair _ _ _ (isweqrecompl X x is)). apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ x0 (idweq _)) w1). Defined.


Theorem isfiniteifcomplement (X:UU0)(x:X)(is: isisolated _ x): isfinite (complement X x) -> isfinite X.
Proof. intros X x is X0. apply (hinhfunct _ _ (finitestructfromcomplement X x is) X0). Defined. 


Theorem finitestructsummand (X Y:UU0)(is: finitestruct (coprod X Y)): finitestruct X.
Proof. intros. destruct is as [ t x ].  generalize X Y x.  clear X Y x. induction t.  intros.  split with O. assert (w: weq X empty). apply (weqpair _ _ _ (isweqtoempty _ (fun x0:X => invmap _ _ _ (pr22 _ _ x) (ii1 _ _ x0)))). apply (weqinv _ _ w).  

intros. set (xy:= pr21 _ _ x (ii2 _ _ tt)). 
assert (is: isisolated _ xy). apply (isolatedtoisolated _ _ _ (pr22 _ _ x) (ii2 _ _ tt) (isisolatedinstn (S t) (ii2 _ _ tt))). 
assert (w1: weq (stn t) (complement _ xy)).  apply (weqcomp _ _ _ (stnsposl0 t) (weqoncomplements _ _ (ii2 _ _ tt) x)). destruct xy. 
assert (w2: weq (complement (coprod X Y) (ii1 X Y x0)) (coprod (complement X x0) Y)). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii1x _ _ x0))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)).

assert (isx: isisolated _ x0). apply (isolatedifisolatedii1 _ _ _ is). apply (finitestructfromcomplement _ _ isx is1). 

assert (w2: weq (complement (coprod X Y) (ii2 X Y y)) (coprod X (complement Y y))). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii2y _ _ y))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)). assumption.  Defined. 

Theorem isfinitesummand (X Y:UU0)(is:isfinite (coprod X Y)): isfinite X.
Proof. intros.  apply (hinhfunct _ _ (finitestructsummand X Y) is). Defined. 


Theorem finitestructsubset (X:UU0)(f:X -> bool): finitestruct X -> finitestruct (hfiber _ _ f true).
Proof. intros X f X0. 
assert (w: weq (coprod (hfiber _ _ f true) (hfiber _ _ f false)) X). apply weqsubsetsplit. apply (finitestructsummand _ _ (finitestructweqf _ _ _ (pr22 _ _ (weqinv _ _ w)) X0)).   Defined. 


Theorem isfinitesubset  (X:UU0)(f:X -> bool): isfinite X -> isfinite (hfiber _ _ f true).
Proof. intros X f X0. apply  (hinhfunct _ _ (finitestructsubset X f) X0). Defined. 
















(* The cardinality of finite sets using double negation and decidability of equality in nat. *)

Definition carddneg (X:UU0)(is: isfinite X): nat:= pr21 _ _ (isfiniteimplisfinite0 X is).

Definition preweq (X:UU0)(is: isfinite X): isofnel (carddneg X is) X.
Proof. intros X is X0.  set (c:= carddneg X is). set (dnw:= pr22 _ _ (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr21 nat (fun n : nat => isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw. 

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intro H. destruct H as [ t x ].  destruct t as [ t x0 ]. 
assert (dw: dneg (weq (stn t) (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr21 _ _ ab) (weqinv _ _ (pr22 _ _ ab))).  apply (dnegf _ _ ff (inhdnegand _ _ (todneg _ x0) x)). 
assert (e:paths _ t c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel. 
apply (hinhfunct _ _ f (hinhand (finitestruct X) _ is (hinhpr _ dnw))). Defined. 


(* to be completed 

Theorem carddnegweqf (X Y:UU0)(f: X -> Y)(isw:isweq _ _ f)(isx: isfinite X): paths _ (carddneg _ isx) (carddneg _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *) 

(* The cardinality of finite sets defined using the "impredicative" ishinh *)



(** ** Test computations. *)



(*Eval compute in carddneg _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O))))).*)

Eval compute in carddneg _ (isfiniteempty).

Eval compute in carddneg _ (isfiniteunit).

Eval lazy in carddneg _  (isfinitebool).




(*Eval lazy in   (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).*)
 



Eval lazy in carddneg _ (isfinitecomplement _ true isfinitebool).

Eval compute in carddneg _ (isfinitedirprod _ _ isfinitebool isfinitebool).

Eval compute in carddneg _ (isfinitedirprod _ _ isfinitebool (isfinitedirprod _ _ isfinitebool isfinitebool)).

Eval compute in carddneg _ (isfinitecoprod _ _ (isfinitebool) (isfinitecomplement _ (ii1 _ _ (ii2 _ _ tt)) (isfinitestn (S (S (S O)))))).

Eval lazy in carddneg _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).

(*Eval compute in  carddneg _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).*)

(*Eval compute in carddneg _ (isfinitecomplement _ (dirprodpair _ _ tt tt) (isfinitedirprod _ _ isfiniteunit isfiniteunit)).*)


(*Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).*)

Eval lazy in (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).
 


Eval lazy in carddneg _ (isfinitecomplement _ (dirprodpair _ _ true (dirprodpair _ _ true false)) (isfinitedirprod _ _ (isfinitebool) (isfinitedirprod _ _ (isfinitebool) (isfinitebool)))).









(*

Eval compute in (pr21 _ _ (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O)))))).


Print empty_rect. 

Lemma isof1elfrom0el (X Y:UU0): isofnel O X -> isofnel (S O) (X -> Y).
Proof. intros. unfold isofnel. intro.   simpl. 

Theorem isfinitefunctions (X Y:UU0)(isx: isfinite X)(isy: isfinite Y): isfinite (X -> Y).
Proof. intros. destruct isx.  generalize Y isy X x. clear isy Y x X.  induction t.  intros. split with (S O). 



*)















(* End of the file finite_sets.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)