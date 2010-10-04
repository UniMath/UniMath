(* The work on the file started on  Feb. 16, 2010 *)

  
(* The files u0.v, u1.v, u2.v, u01.v, u12.v and u012.v contain the definitions and theorems which form the "basics" of the foundations and a new approach to the type-theoretic formalization of mathematics. These foundations are inspired by the univalent model of type theory which interprets types as homotopy types (objects of the homotopy category which is defined using the standard set theory), Martin-Lof equality as paths spaces and universes as bases of universal ("univalent") fibrations.

The need to use several files and the distribution of the material among the files are dictated by the current situation with universe management in Coq. As of now there is no intended mechanism for an explicit control over the type universes by the user.  When the identifier "Type" is used the system creates a new universe connected to the previously created ones by a set of constraints which are automatically determined based on the context in which this particular instance of "Type" appears. If the resulting system of constraints becomes incompatible the system produces "Universe Inconsistency" message and does not allow further development. Since a new type universe is introduced essentially every time the identifier "Type" is used it soon becomes very difficult, in the case of a "Universe Inconsistency" situation, to analyze where the problem is and how to resolve it. 

In this version of the foundations we use a trick which allows us to avoid the prolifiration of type universes and the corresponding constrains. The current proofs require us in some places (actually in one place only - theorem funcontr) to use the hierarchy which cocnists of three levels of universes Type0, Type1 and Type2 with the condition that Type0:Type1,  Type1:Type2 and Type0 is a subtype of Type1 which is a subtype of Type2.

The files u0, u1, u2 contain the results which require only one universe level. These three files are identical. The universe in each of them is called UU. 

The files u01 and u12 contain the results which require a two-levels universe hierarchy. The file u01 uses universes Type0:=u0.UU and Type1:=u1.UU while u12 uses universes Type1:=u1.UU and Type2:=u2.UU. In all other ways the files u01 and u12 are identical.

The file u012 contains the results which require a three-levels universe hierarchy.   

I tried to keep the notations such that the names of types which are (expected to be) a property in the sense of being of level 1 start with "is" but I have not been very consistent about it. After functional extensionality is proved there follows a series of theorems which assert that different types of the form "is..." (iscontr, isweq etc.) are actuallly properties.


*)

(* IMPORTANT: for those who may want to add to these files. There are some rules which have to be followed in creating new definitions and theorems which at the moment are not tracked by the proof checker.

1. The current system of Coq is not completely compatible with the univalent semantics. The problem (the only one as far as I know) lies in the way the universe levels (u-levels) are assigned to the objects defined by the inductive definitions of the form

Inductive Ind (...)...(...): A -> Type := ...


The current u-level assignemet takes into account the u-levels of the constructors but not the u-level of A. To ensure compatibility with the univalent model the u-level of Ind should be no less than the u-level of A. The u-levels of the parameters (the types appearing in (...)...(...) ) do not matter. 

A particular case of this problem is the "singleton elimination" rule which provides a good example of this incompatibility. The inductive definition of the identity types which uses one of the points as a parametr has A=:T (the underlying type) but since no mention of T appears in the constructor the system considers that there are no u-level restrictions on the resulting object and in particular that it can be placed in Prop while still having the full Ind_rect elimninator (see elimination, singleton elimination in the Index to the Refernce Manual). 

Since in the present approach the universe management is made explicit as explained above the one has:

RULE 1 Do not use inductive definitions of the form 

Inductive Ind (...)...(...): A -> UU := ...

where the u-level of UU (which at the moment can be UU0, UU1 or UU2) is lower than the level of the universe to which A types.


2. While it does not lead directly to any contradictions the shape of the foundations suggests very strongly that we should completely avoid the use of the universes Prop and Set. Instead we should use the the conditions isaprop and isaset which are applicable to the types of any of the type universes.  


*)






Require Export u12 u01.

Definition UU2:=u2.UU.



(* Theorem saying that if all members of a family are contractible then the space of sections of the family is contractible. *)

Theorem funcontr (T:UU0) (P: T -> UU0) (is: forall t:T, iscontr (P t)): iscontr (forall t:T, P t).
Proof. intros. assert (e: u1.paths _ P (fun t:T => unit)). apply (u12.funextfun _ _ P (fun t:T => unit) (fun t:T => ifcontrthenunit _ (is t))). assert (e': u1.paths _ (forall t:T, P t) (forall t:T, unit)). apply (u1.maponpaths _ _ (fun Q:T->UU0 => forall t:T, Q t) _ _ e).
assert (int: iscontr (forall t:T, unit)). apply iscontrtounit. induction e'. assumption. Defined. 




(* Proof of the fact that the funextmap from paths _ s1 s2 to forall t:T, paths _ (s1 t) (s2 t) is q weak equivalence - a strong form 
of functional extensionality for sections of general families. *)


Definition funextmap (T:UU0) (P:T -> UU0) (f:forall t:T, P t)( g: forall t:T, P t): (paths (forall t:T, P t) f g) -> (forall t:T, paths (P t) (f t) (g t)).
Proof. intros. induction X. apply idpath. Defined. 


Lemma funextweql1 (T:UU0)(P:T -> UU0)(g: forall t:T, P t): iscontr (total2 _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t))).
Proof. intros. set (X:= forall t:T, coconustot (P t) (g t)). assert (is1: iscontr X). apply (funcontr  _ (fun t:T => coconustot (P t) (g t)) (fun t:T => iscontrcoconustot (P t) (g t))).  set (Y:= total2 _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t))). set (p:= fun z: X => tpair _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t)) (fun t:T => pr21 _ _ (z t)) (fun t:T => pr22 _ _ (z t))).  set (s:= fun u:Y => (fun t:T => coconustotpair (P t) (g t) ((pr21 _ _ u) t) ((pr22 _ _ u) t))).  set (etap:= fun u: Y => tpair _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t)) (fun t:T => ((pr21 _ _ u) t)) (pr22 _ _ u)).

assert (eps: forall u:Y, paths _ (p (s u)) (etap u)).  intro.  destruct u. unfold p. unfold s. unfold etap.   simpl. assert (ex: paths _ x (fun t0:T => x t0)). apply etacorrection.  induction ex. apply idpath. 

assert (eetap: forall u:Y, paths _ (etap u) u). intro. unfold etap. destruct u. simpl.


set (ff:= fun fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))) => tpair _ (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0)) (fun t0:T => (pr21 _ _ fe) t0) (pr22 _ _ fe)). 

assert (isweqff: isweq _ _ ff). apply (isweqfp (forall t:T, P t) (forall t:T, P t) (fun f:forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => forall t:T, paths (P t) (f t) (g t)) (isweqetacorrection T P)). 

assert (ee: forall fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))), paths _ (ff (ff fe)) (ff fe)). intro. apply idpath.  assert (eee: forall fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))), paths _ (ff  fe) fe). intro. apply (pathsweq2 _ _ ff isweqff _ _ (ee fe)).  

apply (eee (tpair _ _ t x)). assert (eps0: forall u: Y, paths _ (p (s u)) u). intro. apply (pathscomp0 _ _ _ _ (eps u) (eetap u)). 
 
apply (contrl1' X Y p s eps0). assumption. Defined. 





Theorem isweqfunextmap(T:UU0)(P:T -> UU0)(f: forall t:T, P t) (g: forall t:T, P t): isweq _ _ (funextmap T P f g). 
Proof. intros. set (tmap:= fun ff: total2 _ (fun f0: forall t:T, P t, paths _ f0 g) => tpair _ (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)) (pr21 _ _ ff) (funextmap _ P (pr21 _ _ ff) g (pr22 _ _ ff))). assert (is1: iscontr (total2 _ (fun f0: forall t:T, P t, paths _ f0 g))). apply (iscontrcoconustot _ g).   assert (is2:iscontr (total2 _ (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)))). apply funextweql1.  
assert (isweq _ _ tmap).  apply (ifcontrcontrthenweq _ _ tmap is1 is2).  apply (isweqtotaltofib _ (fun f0: forall t:T, P t, paths _ f0 g) (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)) (fun f0:forall t:T, P t =>  (funextmap _ P f0 g)) X f).  Defined. 


Definition funextsec (T:UU0) (P: T-> UU0) (s1: forall t:T, P t)(s2: forall t:T, P t): (forall t:T, paths _ (s1 t) (s2 t)) -> paths _ s1 s2 := invmap _ _ (funextmap _ _ s1 s2) (isweqfunextmap _ _ s1 s2).


Theorem isweqfunextsec(T:UU0)(P:T -> UU0)(f: forall t:T, P t) (g: forall t:T, P t): isweq _ _ (funextsec T P f g).
Proof. intros. apply (isweqinvmap _ _ (funextmap _ _ f g) (isweqfunextmap _ _ f g)). Defined. 


(* The following definitions introduce the particular cases the preceeding results in the case of functions i.e. section of constsnant families. It is probably possible to prove these results directly in u**. *)


Definition funextmapfun (X:UU0)(Y:UU0)(f:X->Y)(g:X->Y): (paths _ f g) -> (forall x:X, paths _ (f x) (g x)) := funextmap X (fun x:X => Y) f g.  

Definition  isweqfunextmapfun (X:UU0)(Y:UU0)(f:X->Y)(g:X->Y): isweq _ _ (funextmapfun _ _ f g) := isweqfunextmap X (fun x:X => Y) f g.

Definition funextsecfun (X:UU0)(Y:UU0)(f:X->Y)(g:X->Y):  (forall x:X, paths _ (f x) (g x)) -> (paths _ f g) := funextsec X (fun x:X => Y) f g. 














(*  Sections of "double fibration" P: T -> UU, PP: forall t:T, P t -> UU and pairs of sections (cont. from u0). *)

Definition foralltototaltoforall(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss: forall x:X, total2 (P x) (PP x)): paths _ (totaltoforall _ _ _ (foralltototal _ _ _ ss)) ss.
Proof. intros. unfold foralltototal. unfold totaltoforall.  simpl. assert (ee: forall x:X, paths _ (tpair (P x) (PP x) (pr21 (P x) (PP x) (ss x)) (pr22 (P x) (PP x) (ss x))) (ss x)).  intro. apply (pathsinv0 _ _ _ (tppr (P x) (PP x) (ss x))).  apply (funextsec). assumption. Defined.

Theorem isweqforalltototal (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (foralltototal X P PP).
Proof. intros.  apply (gradth _ _ (foralltototal X P PP) (totaltoforall X P PP) (foralltototaltoforall  X P PP) (totaltoforalltototal X P PP)). Defined. 

Theorem isweqtotaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (totaltoforall X P PP).
Proof. intros.  apply (gradth _ _  (totaltoforall X P PP) (foralltototal X P PP)  (totaltoforalltototal X P PP) (foralltototaltoforall  X P PP)). Defined. 




(* Description of the homotopy fibers of the map between section spaces defined by forall x:X, P x -> Q x. *) 


Definition hfibertoforall (X:UU0)(P:X -> UU0)(Q:X -> UU0)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): hfiber _ _ (maponsec _ _ _ f) s -> forall x:X, hfiber _ _ (f x) (s x).
Proof. intro. intro. intro. intro. intro.  unfold hfiber. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).  

set (themap := fun a:_ => map2 (map1 a)). assumption. Defined. 



Definition foralltohfiber  (X:UU0)(P:X -> UU0)(Q:X -> UU0)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): (forall x:X, hfiber _ _ (f x) (s x)) -> hfiber _ _ (maponsec _ _ _ f) s.
Proof.  intro. intro. intro. intro.   intro. unfold hfiber. 

set (map2inv := foralltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).
set (map1inv :=  totalfun (forall x : X, P x)  (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s)).
set (themap := fun a:_=> map1inv (map2inv a)). assumption. Defined. 


Theorem isweqhfibertoforall  (X:UU0)(P:X -> UU0)(Q:X -> UU0)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (hfibertoforall _ _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).  

assert (is1: isweq _ _ map1). apply (isweqfibtototal _ _ _ (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => (isweqfunextmap _ _ (fun x : X => f x (pointover x)) s))).

assert (is2: isweq _ _ map2). apply isweqtotaltoforall.

apply (twooutof3c _ _ _ map1 map2 is1 is2). Defined.


Theorem isweqforalltohfiber  (X:UU0)(P:X -> UU0)(Q:X -> UU0)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (foralltohfiber _ _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map2inv := foralltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).

assert (is2: isweq _ _ map2inv). apply (isweqforalltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).

set (map1inv :=  totalfun (forall x : X, P x)  (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s)).

assert (is1: isweq _ _ map1inv). apply (isweqfibtototal _ _ _ (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => (isweqfunextsec _ _ (fun x : X => f x (pointover x)) s))).

apply (twooutof3c _ _ _ map2inv map1inv is2 is1). Defined. 



(* The map between section spaces (dependent products) defined by a family of maps P x -> Q x is a weak equivalence if all maps P x -> Q x are weak equivalences. *)


Corollary isweqmaponsec (X:UU0)(P:X-> UU0)(Q:X -> UU0)(f: forall x:X, P x -> Q x)(isx: forall x:X, isweq _ _ (f x)): isweq _ _ (maponsec _ _ _ f). 
Proof. intros. unfold isweq.  intro.
assert (is1: iscontr (forall x:X, hfiber _ _ (f x) (y x))). assert (is2: forall x:X, iscontr (hfiber _ _ (f x) (y x))). unfold isweq in isx. intro. apply (isx x (y x)). apply funcontr. assumption. 
apply (iscontrxifiscontry _ _ (hfibertoforall _ P Q f y) (isweqhfibertoforall _ P Q f y) is1). Defined. 

(* The map between section spaces (dependent products) defined by a weak equivalence f: Y -> X of the bases is a weak equivalence. *)

Definition maponsec1l0 (X:UU0)(P:X -> UU0)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x): (forall x:X, P x) := (fun x:X => transportf X P _ _ (h x) (s (f x))).

Lemma maponsec1l1  (X:UU0)(P:X -> UU0)(x:X)(s:forall x:X, P x): paths _ (maponsec1l0 _ P (fun x:X => x) (fun x:X => idpath _ x) s x) (s x). 
Proof. intros. unfold maponsec1l0.   apply idpath. Defined. 


Lemma maponsec1l2 (X:UU0)(P:X -> UU0)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x)(x:X): paths _ (maponsec1l0 _ P f h s x) (s x).
Proof. intro. intro. intro. intro. intros.  

set (map:= fun ff: total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x) => maponsec1l0 X P (pr21 _ _ ff) (pr22 _ _ ff) s x).
assert (is1: iscontr (total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x))). apply funextweql1. assert (e: paths _ (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) f h) (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) (fun x0:X => x0) (fun x0:X => idpath _ x0))). apply ifcontrthenconnected.  assumption.  apply (maponpaths _ _ map _ _ e). Defined. 


Theorem isweqmaponsec1 (X:UU0)(Y:UU0)(P:Y -> UU0)(f:X-> Y)(is:isweq _ _ f):isweq _ _ (maponsec1 _ _ P f).
Proof. intros.
 
set (map:= maponsec1 _ _ P f).
set (invf:= invmap _ _ f is). set (e1:= weqfg _ _ f is). set (e2:= weqgf _ _ f is).
set (im1:= fun sx: forall x:X, P (f x) => (fun y:Y => sx (invf y))).
set (im2:= fun sy': forall y:Y, P (f (invf y)) => (fun y:Y => transportf _ _ _ _ (weqfg _ _ _ is y) (sy' y))).
set (invmap := (fun sx: forall x:X, P (f x) => im2 (im1 sx))). 

assert (efg0: forall sx: (forall x:X, P (f x)), forall x:X, paths _ ((map (invmap sx)) x) (sx x)).  intro. intro. unfold map. unfold invmap. unfold im1. unfold im2. unfold maponsec1.  simpl. fold invf.  set (ee:=e2 x).  fold invf in ee.

set (e3x:= fun x0:X => pathsweq2 _ _ f is (invf (f x0)) x0 (weqfg X Y f is (f x0))). set (e3:=e3x x). assert (e4: paths _ (weqfg X Y f is (f x)) (maponpaths _ _ f _ _ e3)). apply (pathsinv0 _ _ _ (pathsweq4 _ _ f is (invf (f x)) x _)).

assert  (e5:paths _ (transportf Y P (f (invf (f x))) (f x) (weqfg X Y f is (f x)) (sx (invf (f x)))) (transportf Y P (f (invf (f x))) (f x) (maponpaths _ _ f _ _ e3) (sx (invf (f x))))). apply (maponpaths _ _ (fun e40:_ => (transportf Y P (f (invf (f x))) (f x) e40 (sx (invf (f x))))) _ _ e4).

assert (e6: paths _ (transportf Y P (f (invf (f x))) (f x) (maponpaths X Y f (invf (f x)) x e3) (sx (invf (f x)))) (transportf X (fun x:X => P (f x)) _ _ e3 (sx (invf (f x))))). apply (pathsinv0 _ _ _ (functtransportf _ _ f P _ _ e3 (sx (invf (f x))))).

set (ff:= fun x:X => invf (f x)).
assert (e7: paths _ (transportf X (fun x : X => P (f x)) (invf (f x)) x e3 (sx (invf (f x)))) (sx x)). apply (maponsec1l2 _ (fun x:X => P (f x))ff e3x sx x).  apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e5 e6) e7).

assert (efg: forall sx: (forall x:X, P (f x)), paths _  (map (invmap sx)) sx). intro. apply (funextsec _ _ _ _ (efg0 sx)).

assert (egf0: forall sy: (forall y:Y, P y), forall y:Y, paths _ ((invmap (map sy)) y) (sy y)). intros. unfold invmap. unfold map.  unfold im1. unfold im2. unfold maponsec1. 

set (ff:= fun y:Y => f (invf y)). fold invf. apply (maponsec1l2 Y P ff (weqfg X Y f is) sy y). 
assert (egf: forall sy: (forall y:Y, P y), paths _  (invmap (map sy)) sy). intro. apply (funextsec _ _ _ _ (egf0 sy)). 

apply (gradth _ _ map invmap egf efg). Defined. 







(* More theorems about h-levels. *)

(* Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

Theorem impred (n:nat)(T:UU0)(P:T -> UU0): (forall t:T, isofhlevel n (P t)) -> (isofhlevel n (forall t:T, P t)).
Proof. intro. induction n. intros.  apply (funcontr T P X). intros. unfold isofhlevel in X.  unfold isofhlevel. intros. 

assert (is: forall t:T, isofhlevel n (paths _ (x t) (x' t))).  intro. apply (X t (x t) (x' t)).  
assert (is2: isofhlevel n (forall t:T, paths _ (x t) (x' t))). apply (IHn _ (fun t0:T => paths _ (x t0) (x' t0)) is).
set (u:=funextmap _ P x x').  assert (is3:isweq _ _ u). apply isweqfunextmap.  set (v:= invmap _ _ u is3). assert (is4: isweq _ _ v). apply isweqinvmap. apply (hlevelweqf n _ _ v is4). assumption. Defined.



(* Theorems saying that  (iscontr T) and (isweq f) are of h-level 1 (i.e. isaprop). *)



Lemma unitl5: iscontr (iscontr unit).
Proof. set (c:=unitiscontr). split with c. intro. induction t. unfold c. unfold unitiscontr. set (y:= (fun x0 : unit => unit_rect (fun x1 : unit => paths unit x1 tt) (idpath unit tt) x0)).  simpl in y. induction t.   assert (e: forall u: unit, paths _ (x u) (y u)). intro.  induction u. simpl. apply unitl3. assert (ee: paths _ x y). apply (funextsec _ (fun u:unit => paths _ u tt) x y e).  induction ee. 

assert (ee: paths _ x (fun x0 : unit =>
         unit_rect (fun x1 : unit => paths unit x1 tt) (idpath unit tt) x0)).  assert (eee: forall t:unit, paths _ (x t) ( (fun x0 : unit =>
         unit_rect (fun x1 : unit => paths unit x1 tt) (idpath unit tt) x0) t)). intro.  induction t. assert (e1:paths (paths unit tt tt) (x tt) (idpath _ tt)). apply unitl3. assert (e2: paths (paths unit tt tt)
     (unit_rect (fun x1 : unit => paths unit x1 tt) (idpath unit tt) tt) (idpath _ tt)).  apply unitl3. induction e1. apply pathsinv0. assumption. apply funextsec. assumption.  induction ee.  apply idpath.  Defined. 


Theorem iscontriscontr: forall T:UU0, iscontr(T)->iscontr(iscontr(T)).
Proof. intros. apply ifcontrthenunit in X. assert (is: iscontr (iscontr unit)). apply unitl5. induction X.  assumption. Defined. 



Theorem isapropiscontr (T:UU0): isaprop (iscontr T).
Proof. intros.  unfold isaprop.  unfold isofhlevel. intros. assert (is: iscontr(iscontr T)). apply iscontriscontr. apply x. assert (is2: isaprop (iscontr T)). apply (ifcontrthenaprop _ is). apply (is2 x x'). Defined.  



Theorem isapropisweq (X:UU0)(Y:UU0)(f:X-> Y) : isaprop (isweq _ _ f).
Proof. intros. unfold isweq.  apply (impred (S O) _ (fun y:Y => iscontr (hfiber X Y f y)) (fun y:Y => isapropiscontr (hfiber X Y f y))).  Defined. 


Theorem isapropisofhlevel (n:nat)(X:UU0): isaprop (isofhlevel n X).
Proof. intro.  unfold isofhlevel.    induction n. apply isapropiscontr.  intro. 
assert (forall (x x':X), isaprop  ((fix isofhlevel (n0 : nat) (X0 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X0
         | S m => forall x0 x'0 : X0, isofhlevel m (paths X0 x0 x'0)
         end) n (paths X x x'))). intros. apply (IHn (paths _ x x')). 
assert (is1: 
     (forall x:X, isaprop (forall  x' : X,
      (fix isofhlevel (n0 : nat) (X1 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X1
         | S m => forall x0 x'0 : X1, isofhlevel m (paths X1 x0 x'0)
         end) n (paths X x x')))). intro.  apply (impred (S O) _ _ (X0 x)). apply (impred (S O) _ _ is1). Defined. 









(****

Here we start the study of structures. The most fundamental structure is a "pointed type" and we begin with theorems about the space of pointed types. This is closely related to the study of so called "heterogenious equality".

****)







Definition ptype:UU1 := u1.total2 _ (fun T:UU0 => T).

Definition ptypepair:= u1.tpair _ (fun T:UU0 => T).
Definition el (X: ptype):= u1.pr21 _ _ X.

 
Definition dp (X: ptype):= u1.pr22 _ _ X. 

Definition pfun (X: ptype)(Y: ptype): UU0 := total2 (el X -> el Y) (fun f: el X -> el Y => paths _ (f (dp X)) (dp Y)). 
Definition pfunpair (X: ptype)(Y: ptype):= tpair _ (fun f: el X -> el Y => paths _ (f (dp X)) (dp Y)).

Definition idpfun (X:ptype): pfun X X := pfunpair _ _ (fun x:(el X) => x) (idpath _ (dp X)). 




Definition ispweq (X: ptype)(Y:ptype) (f: pfun X Y):= isweq _ _ (pr21 _ _ f).
Definition pweq (X: ptype)(Y: ptype): UU0 := total2 _ (fun f: pfun X Y => ispweq _ _ f).


Definition pweqpair  (X: ptype)(Y: ptype):= tpair _ (fun f: pfun X Y => ispweq _ _ f).


Definition pidisweq (X: ptype): ispweq _ _ (idpfun X) := idisweq (el X). 

Definition idpweq (X: ptype):pweq X X:= pweqpair _ _ (idpfun X) (pidisweq X).

Definition peqweqmap (X:ptype)(Y:ptype): u1.paths _ X Y -> pweq X Y.
Proof. intros.  induction X0. apply idpweq. Defined. 



(*

Theorem peqth (X:ptype)(Y:ptype): isweq _ _ (peqweqmap X Y).
Proof. intros. unfold isweq. intro.  


Definition ismonic (T1:Type) (T2:Type) (f:T1 -> T2) : Type := forall t1:T1, iscontr(hfiber T1 T2 f (f t1)).

Definition newprop : Type := total2 Type (fun T:Type =>  isaprop T).



(***** Prop is used from this point on ****)



Inductive Isnonempty (T:Type):Prop := wtn:T->(Isnonempty T).

Axiom contractiblechoice: forall T:Type, (iscontr T) -> (isweq T (Isnonempty T) (wtn T)). 

Definition Issurjective (T1:Type) (T2:Type) (f:T1 -> T2) : Prop := forall t2:T2, exists t1, (f t1)= t2.

Definition Isinjective (T1:Type) (T2:Type) (f:T1-> T2): Prop := forall t11:T1, forall t12:T1, ((f t11)=(f t12) -> (t11=t12)).

Definition Isbijective (T1:Type) (T2:Type) (f:T1-> T2) : Prop := (Issurjective T1 T2 f)/\(Isinjective T1 T2 f).





(* CONJECTURES *)



(***)







Conjecture boolisaset: isaset (bool).

Conjecture nataset: isaset (nat).




Definition Rel:= total2 Type (fun T:Type => (T -> T -> Prop)).
Definition relpair (T:Type) (R:T->T->Prop) : Rel := tpair Type (fun T:Type => (T -> T -> Prop)) T R.

Conjecture Releq: forall X:Type, forall Y:Type, forall Rx:X->X->Prop, forall Ry:Y->Y->Prop, forall f:X->Y, forall is1:isweq _ _ f, forall is2: (forall x1:X, forall x2:X, Rx x1 x2 <-> Ry (f x1) (f x2)), paths Rel (relpair X Rx) (relpair Y Ry).

    

Conjecture bijisweq: forall T1:Type, forall T2:Type, forall f:T1 -> T2, forall s1: isaset T1, forall s2: isaset T2,
Isbijective T1 T2 f  -> isweq T1 T2 f.



*)




