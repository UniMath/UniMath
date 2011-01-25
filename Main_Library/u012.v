
Require Export u12 u01.

Unset Automatic Introduction. 



(**  **)


(** A group of constructions simulating global impredicativity of hProp. **)
 
Axiom hp1tohp:hProp1 -> hProp.
Coercion hp1tohp:hProp1 >-> hProp.

Definition hp1touu0:= (fun P:hProp1 => hptouu0 (hp1tohp P)) : hProp1 -> Type.
Axiom hp1touu0toid : forall P:hProp1, hp1touu0 P -> hp1touu1 P.
Coercion hp1touu0toid: hp1touu0 >-> hp1touu1.


Axiom idtohp1touu0 : forall P:hProp1, (hp1touu1 P) -> hp1touu0 P.
Coercion idtohp1touu0: hp1touu1 >-> hp1touu0.



(** * Inhabited construction *)

Definition isinhtech (X:UU1):= forall P:hProp, (X -> P) -> P.

Theorem isapropisinhtech (X:UU1): isaprop (isinhtech X).
Proof. intro. unfold isinhtech.
assert (s1: forall P:hProp, isaprop ((X -> P) -> P)). intro. apply impredfun. apply (pr22 _ _ P).    
apply impred. assumption. Defined. 

Definition isinhinhp1 (X:UU1) := hProp1pair (isinhtech X) (isapropisinhtech X) :hProp1.

Definition isinh (X:UU1) := hp1tohp (isinhinhp1 X):hProp.

Definition isapropisinh (X:UU1): isaprop (isinh X):=  (pr22 _ _ (isinh X)).

Definition isinhtoisinhinhp1 (X:UU1): isinh X -> isinhinhp1 X := fun a:_ => hp1touu0toid _  a .

Definition isinhinhp1toisinh (X:UU1): isinhinhp1 X -> isinh X := fun a: hp1touu1 (isinhinhp1 X) =>  idtohp1touu0 _ a .

Definition isinhpr (X:UU1):= (fun x:X => isinhinhp1toisinh X (fun P:_ => fun f:X -> P => f x)): X -> isinh X. 


Definition isinhuniv (X:UU1)(P:hProp): (X -> P) -> ((isinh X) -> P) := fun f: X -> P => fun a: isinh X => (hp1touu0toid _ a) P f.

Definition isinhuniv1 (X:UU1)(P:hProp1): (X -> P) -> ((isinh X) -> P) := fun f: X -> P => fun a: isinh X => (hp1touu0toid P ((hp1touu0toid _ a) (hp1tohp P) (fun x:X => (idtohp1touu0 P (f x))))).



Definition isinhunivcor (P:hProp1): isinh P -> P := fun a:_ =>  hp1touu0toid _ (isinhuniv P (hp1tohp P) (idtohp1touu0 P) a).


Theorem isinhand (X Y:UU1): dirprod (isinh X) (isinh Y) -> isinh (dirprod X Y).
Proof. intros. destruct X0. apply isinhinhp1toisinh. intro. intro.  apply (ddualand X Y P ((hp1touu0toid _ t) P) ((hp1touu0toid _ x) P) X0). Defined. 

Definition isinhfunct (X Y:UU1): (X -> Y) -> ((isinh X) -> (isinh Y)) := fun f:_ => fun a:isinh X => (isinhinhp1toisinh _ (fun P:_ => fun g: Y -> P => (hp1touu0toid _ a) P (fun x:X => g (f x)))).  

Theorem isinhfunct2 (X Y Z:UU1):(X -> Y -> Z) -> ((isinh X) -> (isinh Y) -> (isinh Z)).
Proof. intros. apply (isinhfunct _ _ (fun xy: dirprod X Y => X0 (pr21 _ _ xy) (pr22 _ _ xy)) (isinhand _ _ (dirprodpair _ _ X1 X2))).  Defined.




(**  * Images and surjectivity **)

Definition image (X Y:UU1)(f:X -> Y):= total2 Y (fun y:Y => isinh (hfiber _ _ f y)).

Definition imageincl (X Y:UU1)(f:X -> Y): image _ _ f -> Y := pr21 _ _.

Definition issurjective (X Y:UU1)(f:X -> Y):= forall y:Y, isinh (hfiber _ _ f y). 

Lemma isapropissurjective (X Y:UU1)(f: X -> Y) : isaprop (issurjective _ _ f).
Proof. intros.  apply impred. intro. apply  (pr22 _ _ (isinh (hfiber X Y f t))). Defined. 

Lemma isinclimageincl (X Y:UU1)(f:X -> Y): isincl _ _ (imageincl _ _ f).
Proof. intros. apply isofhlevelfpr21. intro. apply isapropisinh. Defined.



(** ** Set quotients of types *)

(** ** Surjections are epimorphisms to sets *)

Theorem surjectionisepitosets (X Y Z:UU1)(f:X -> Y)(g1 g2: Y -> Z)(is1:issurjective _ _ f)(is2: isaset Z): (forall x:X, paths _ (g1 (f x)) (g2 (f x))) -> (forall y:Y, paths _ (g1 y) (g2 y)).
Proof. intros. set (P1:= hProp1pair (paths _ (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber X Y f y)-> paths _ (g1 y) (g2 y)). intro. destruct X1. induction x. apply (X0 t). 
assert (s2: isinh (paths Z (g1 y) (g2 y))). apply (isinhfunct _ _ s1 (is1 y)).  apply (isinhunivcor P1). assumption. Defined. 


(** ** Equivalence classes *)


Definition iseqclass (X:UU1)(R:hrel X)(A:hsubtypes X):= dirprod (isinh A) (dirprod (forall (x1 x2 : X), (R x1 x2) -> (A x1) -> (A x2)) (forall x1 x2:X, (A x1) ->  (A x2) ->  (R x1 x2))).
Definition eqax0 (X:UU1)(R:hrel X)(A:hsubtypes X):= pr21 _ _ : iseqclass X R A -> (isinh A).
Definition eqax1 (X:UU1)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr21 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall (x1 x2 : X),  (R x1 x2) ->  (A x1) -> (A x2)).
Definition eqax2 (X:UU1)(R:hrel X)(A:hsubtypes X):= (fun is: iseqclass X R A => pr22 _ _ (pr22 _ _ is)): iseqclass X R A ->  (forall x1 x2:X,  (A x1) -> (A x2) ->  (R x1 x2)).

Lemma isapropiseqclass  (X:UU1)(R:hrel X)(A:hsubtypes X): isaprop(iseqclass X R A).
Proof. intros.
unfold iseqclass. apply isofhleveldirprod. apply isapropisinh.     apply isofhleveldirprod. apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr22 _ _ (A t')). 
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
assert (is3: isincl _ _ ((pr21 _ _): ImA -> Y)). apply isofhlevelfpr21. intro. apply isapropisinh. 
assert (is4: isweq _ _ (maponpaths _ _ ((pr21 _ _):ImA -> Y) x0 x') ). apply isweqonpathsincl. assumption. 
apply (iscontrxifiscontry _ _ _ is4). simpl. destruct x0. destruct x'.    simpl. 
assert (p1: (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t) -> (hfiber A Y (fun a : A => f (pr21 X (fun x : X => A x) a)) t2) -> (paths _ t t2)). intros.  destruct X0. destruct X1. assert (e1: R (pr21 _ _ t3) (pr21 _ _ t4)). apply x. apply (pr22 _ _ t3). apply (pr22 _ _ t4). assert (e2: paths _ (f (pr21 X (fun x : X => A x) t3)) (f (pr21 X (fun x : X => A x) t4))). apply is. apply e1. apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ x2) e2) x3). 
assert (isi: isinh (paths _ t t2)). apply (isinhfunct2 _ _ _ p1 x0 x1). 
assert (cn: paths _ t t2). apply (isinhunivcor (hProp1pair _ ((u2.pr22 _ _ Y) t t2)) isi). 
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

Definition pathconnected (X:UU1):= fun (x x':X) => isinh (paths _ x x').
Definition isreflpathconnected (X:UU1): isrefl _ (pathconnected X):= fun x:_ => isinhpr _ (idpath _ x).
Definition issymmpathconnected (X:UU1): issymm _ (pathconnected X):= fun x x':_ => fun a:_ => isinhfunct _ _ (fun e:paths _ x x' => pathsinv0 _ _ _ e) a. 
Definition istranspathconnected (X:UU1): istrans _ (pathconnected X):= fun x x' x'':_ => fun a:_ => fun b:_ => isinhfunct2 _ _ _ (fun e1: paths _ x x' => fun e2: paths _ x' x'' => pathscomp0 _ _ _ _ e1 e2) a b.
Definition iseqrelpathconnected (X:UU1): iseqrel _ (pathconnected X):= dirprodpair _ _ (isreflpathconnected  _ ) (dirprodpair _ _ (issymmpathconnected _ ) (istranspathconnected  _ )).

Definition pizero (X:UU1):= setquot X (pathconnected X). 
Definition pizeropr (X:UU1):= setquoteqrelpr X (pathconnected X)  (iseqrelpathconnected X).

(** Homotopy sets of a type. I. *)










(** * Univalence axiom for hProp *)

(** At the moment I do not see how to prove directly that setquot X is a set or that setquoteqrelpr is a surjection even in the case of [pizero] and [pizeropr]. The problem lies in the fact that we do not know that [hProp] is a set. We do not even know that [paths UU0 unit unit] is contractible. To deal with this problem we introduce at this stage the weakest form of the univalence axiom - the univalence axiom for hProp which is equivalent to the combination of the second part of the extensionality axiom in Church simple type theory with the axiom saying that [paths _ unit unit] is contractible. *)


Axiom uahp : forall P P':hProp,  (P -> P') -> (P' -> P) -> paths UU0 P P'. 








(** * Composable sequences of functions. *) 


Fixpoint seqplus (n:nat) : u2.total2 UU1 (fun T:UU1 => (T -> UU0)) := match n with 
O =>  u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) UU0 (fun X:_ => X) |
S m => u2.tpair  UU1 (fun T:UU1 => (T -> UU0)) (u1.total2 (u2.pr21 _ _ (seqplus m)) (fun D:_ => u1.total2 UU0 (fun Y:_ => ((u2.pr22 _ _ (seqplus m) D) -> Y)))) (fun E:_ => u1.pr21 _ _ (u1.pr22 _ _ E))
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