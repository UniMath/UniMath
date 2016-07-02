(** * Univalent Basics. Vladimir Voevodsky. Feb. 2010 - Sep. 2011. Port to coq trunk (8.4-8.5) in
 March 2014. The second part of the original uu0 file, created on Dec. 3, 2014.

This file starts with the definition of h-levels. No axioms are used. Only one universe is used
and only once as a type in the definition of the family isofhlevel : nat -> UU as a fixpoint with
values in UU. *)


(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with
Coq8.2 *)

(** Imports *)

Require Export UniMath.Foundations.Basics.PartA.



(** ** Basics about h-levels *)



(** *** h-levels of types *)


Fixpoint isofhlevel (n:nat) (X:UU): UU:=
match n with
O => iscontr X |
S m => forall x:X, forall x':X, (isofhlevel m (paths x x'))
end.

(* induction induction *)

Theorem hlevelretract (n:nat) { X Y : UU } ( p : X -> Y ) ( s : Y -> X ) ( eps : forall y : Y , paths ( p ( s y ) ) y ) : isofhlevel n X -> isofhlevel n Y .
Proof. intro. induction n as [ | n IHn ].  intros X Y p s eps X0. unfold isofhlevel.  apply ( iscontrretract p s eps X0).
 unfold isofhlevel. intros X Y p s eps X0 x x'. unfold isofhlevel in X0. assert (is: isofhlevel n (paths (s x) (s x'))).  apply X0. set (s':= @maponpaths _ _ s x x'). set (p':= pathssec2  s p eps x x').  set (eps':= @pathssec3 _ _  s p eps x x' ). simpl. apply (IHn  _ _ p' s' eps' is). Defined.

Corollary  isofhlevelweqf (n:nat) { X Y : UU } ( f : weq X Y ) : isofhlevel n X  ->  isofhlevel n Y .
Proof. intros n X Y f X0.  apply (hlevelretract n  f (invmap f ) (homotweqinvweq  f )). assumption. Defined.

Corollary  isofhlevelweqb (n:nat) { X Y : UU } ( f : weq X Y ) : isofhlevel n Y  ->  isofhlevel n X .
Proof. intros n X Y f X0 .  apply (hlevelretract n  (invmap  f ) f (homotinvweqweq  f )). assumption. Defined.

Lemma isofhlevelsn ( n : nat ) { X : UU } ( f : X -> isofhlevel ( S n ) X ) : isofhlevel ( S n ) X.
Proof. intros . simpl . intros x x' . apply ( f x x x'). Defined.

Lemma isofhlevelssn (n:nat) { X : UU } ( is : forall x:X, isofhlevel (S n) (paths x x)) : isofhlevel (S (S n)) X.
Proof. intros . simpl.  intros x x'.  change ( forall ( x0 x'0 : paths x x' ), isofhlevel n ( paths x0 x'0 ) ) with ( isofhlevel (S n) (paths x x') ).
assert ( X1 : paths x x' -> isofhlevel (S n) (paths x x') ) . intro X2. induction X2. apply ( is x ). apply  ( isofhlevelsn n X1 ). Defined.







(** *** h-levels of functions *)


Definition isofhlevelf ( n : nat ) { X Y : UU } ( f : X -> Y ) : UU := forall y:Y, isofhlevel n (hfiber  f y).


Theorem isofhlevelfhomot ( n : nat ) { X Y : UU }(f f':X -> Y)(h: forall x:X, paths (f x) (f' x)): isofhlevelf n f -> isofhlevelf n  f'.
Proof. intros n X Y f f' h X0. unfold isofhlevelf. intro y . apply ( isofhlevelweqf n ( weqhfibershomot f f' h y ) ( X0 y )) .   Defined .


Theorem isofhlevelfpmap ( n : nat ) { X Y : UU } ( f : X -> Y ) ( Q : Y -> UU ) : isofhlevelf n  f -> isofhlevelf n ( fpmap f Q ) .
Proof. intros n X Y f Q X0. unfold isofhlevelf. unfold isofhlevelf in X0.  intro y . set (yy:= pr1  y). set ( g := hfiberfpmap  f Q y). set (is:= isweqhfiberfp  f Q y). set (isy:= X0 yy).  apply (isofhlevelweqb n  ( weqpair g is ) isy). Defined.



Theorem isofhlevelfffromZ ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( isz : isofhlevel ( S n ) Z ) : isofhlevelf n f .
Proof. intros . intro y .  assert ( w : weq ( hfiber f y ) ( paths ( g y ) z ) ) .  apply ( invweq ( ezweq1 f g z fs y ) ) .  apply ( isofhlevelweqb n w ( isz (g y ) z ) ) . Defined.


Theorem isofhlevelXfromg ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) : isofhlevelf n g -> isofhlevel n X  .
Proof.  intros n X Y Z f g z fs isf . assert ( w : weq X ( hfiber g z ) ) . apply ( weqpair _ ( pr2 fs ) ) . apply ( isofhlevelweqb n w ( isf z ) ) . Defined .


Theorem isofhlevelffromXY ( n : nat ) { X Y : UU } ( f : X -> Y ) : isofhlevel n X -> isofhlevel (S n) Y -> isofhlevelf n f.
Proof. intro. induction n as [ | n IHn ] .  intros X Y f X0 X1.
assert (is1: isofhlevel O Y). split with ( f ( pr1 X0 ) ) . intro t .  unfold isofhlevel in X1 .  set ( is := X1 t ( f ( pr1 X0 ) ) ) . apply ( pr1 is ).
apply (isweqcontrcontr  f X0 is1).

intros X Y f X0 X1.  unfold isofhlevelf. simpl.
assert  (is1: forall x' x:X, isofhlevel n (paths x' x)). simpl in X0.  assumption.
assert (is2: forall y' y:Y, isofhlevel (S n) (paths y' y)). simpl in X1.  simpl. assumption.
assert (is3: forall (y:Y)(x:X)(xe': hfiber  f y), isofhlevelf n  (d2g  f x xe')).  intros. apply (IHn  _ _ (d2g  f x xe') (is1 (pr1  xe') x) (is2 (f x) y)).
assert (is4: forall (y:Y)(x:X)(xe': hfiber  f y)(e: paths (f x) y), isofhlevel n (paths (hfiberpair  f x e) xe')). intros.
apply (isofhlevelweqb n  ( ezweq3g f x xe' e)  (is3 y x xe' e)).
intros y xe xe' .  induction xe as [ t x ]. apply (is4 y t xe' x). Defined.



Theorem isofhlevelXfromfY ( n : nat ) { X Y : UU } ( f : X -> Y ) : isofhlevelf n f -> isofhlevel n Y -> isofhlevel n X.
Proof. intro. induction n as [ | n IHn ] .  intros X Y f X0 X1.  apply (iscontrweqb ( weqpair f X0 ) X1). intros X Y f X0 X1. simpl.
assert (is1: forall (y:Y)(xe xe': hfiber  f y), isofhlevel n (paths xe xe')). intros. apply (X0 y).
assert (is2: forall (y:Y)(x:X)(xe': hfiber  f y), isofhlevelf n  (d2g  f x xe')). intros. unfold isofhlevel. intro y0.
apply (isofhlevelweqf n ( ezweq3g  f x xe' y0 ) (is1 y (hfiberpair  f x y0) xe')).
assert (is3: forall (y' y : Y), isofhlevel n (paths y' y)). simpl in X1. assumption.
intros x' x .
set (y:= f x').  set (e':= idpath y). set (xe':= hfiberpair  f x' e').
apply (IHn  _ _ (d2g  f x xe') (is2 y x xe') (is3 (f x) y)). Defined.






Theorem  isofhlevelffib ( n : nat ) { X : UU } ( P : X -> UU ) ( x : X ) ( is : forall x':X, isofhlevel n (paths x' x) ) : isofhlevelf n ( tpair P x ) .
Proof . intros . unfold isofhlevelf . intro xp .   apply (isofhlevelweqf n ( ezweq1pr1 P x xp) ( is ( pr1 xp ) ) ) . Defined .



Theorem isofhlevelfhfiberpr1y ( n : nat ) { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : forall y':Y, isofhlevel n (paths  y' y) ) : isofhlevelf n ( hfiberpr1 f y).
Proof.  intros .  unfold isofhlevelf. intro x.  apply (isofhlevelweqf n ( ezweq1g f y x ) ( is ( f x ) ) ) . Defined.


(* destruct -> induction ok to this point *)



Theorem isofhlevelfsnfib (n:nat) { X : UU } (P:X -> UU)(x:X) ( is : isofhlevel (S n) (paths x x) ) : isofhlevelf (S n) ( tpair P x ).
Proof. intros .  unfold isofhlevelf. intro xp. apply (isofhlevelweqf (S n) ( ezweq1pr1 P x xp ) ).  apply isofhlevelsn . intro X1 . induction X1 . assumption .  Defined .




Theorem isofhlevelfsnhfiberpr1 ( n : nat ) { X Y : UU } (f : X -> Y ) ( y : Y ) ( is : isofhlevel (S n) (paths y y) ) : isofhlevelf (S n) (hfiberpr1 f y).
Proof.  intros .  unfold isofhlevelf. intro x. apply (isofhlevelweqf (S n)  ( ezweq1g f y x ) ). apply isofhlevelsn. intro X1. induction X1.  assumption. Defined .




Corollary isofhlevelfhfiberpr1 ( n : nat ) { X Y : UU }  ( f : X -> Y ) ( y : Y ) ( is : isofhlevel (S n) Y ) : isofhlevelf n ( hfiberpr1 f y ) .
Proof. intros. apply isofhlevelfhfiberpr1y. intro y' . apply (is y' y).   Defined.






Theorem isofhlevelff ( n : nat ) { X Y Z : UU } (f : X -> Y ) ( g : Y -> Z ) : isofhlevelf n  (fun x : X => g ( f x) ) -> isofhlevelf (S n)  g -> isofhlevelf n  f.
Proof. intros n X Y Z f g X0 X1. unfold isofhlevelf. intro y . set (ye:= hfiberpair  g  y (idpath (g y))).
apply (isofhlevelweqb n  ( ezweqhf  f g (g y) ye ) (isofhlevelffromXY n  _ (X0 (g y)) (X1 (g y)) ye)). Defined.



Theorem isofhlevelfgf ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) : isofhlevelf n  f -> isofhlevelf n  g -> isofhlevelf n  (fun x:X => g(f x)).
Proof. intros n X Y Z f g X0 X1.  unfold isofhlevelf. intro z.
assert (is1: isofhlevelf n  (hfibersgftog  f g z)). unfold isofhlevelf. intro ye. apply (isofhlevelweqf n ( ezweqhf  f g z ye ) (X0 (pr1  ye))).
assert (is2: isofhlevel n (hfiber  g z)). apply (X1 z).
apply (isofhlevelXfromfY n  _ is1 is2). Defined.



Theorem isofhlevelfgwtog (n:nat ) { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isofhlevelf n  (fun x : X => g ( w x ) ) ) : isofhlevelf n g  .
Proof. intros . intro z . assert ( is' : isweq ( hfibersgftog w g z ) ) .  intro ye . apply ( iscontrweqf ( ezweqhf w g z ye ) ( pr2 w ( pr1 ye ) ) ) .  apply ( isofhlevelweqf _ ( weqpair _ is' ) ( is _ ) ) .  Defined .



Theorem isofhlevelfgtogw (n:nat ) { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isofhlevelf n g ) :  isofhlevelf n  (fun x : X => g ( w x ) ) .
Proof. intros . intro z . assert ( is' : isweq ( hfibersgftog w g z ) ) .  intro ye . apply ( iscontrweqf ( ezweqhf w g z ye ) ( pr2 w ( pr1 ye ) ) ) .  apply ( isofhlevelweqb _ ( weqpair _ is' ) ( is _ ) ) .  Defined .



Corollary isofhlevelfhomot2 (n:nat) { X X' Y : UU } (f:X -> Y)(f':X' -> Y)(w : weq X X' )(h:forall x:X, paths (f x) (f' (w x))) : isofhlevelf n  f -> isofhlevelf n  f'.
Proof. intros n X X' Y f f' w h X0.  assert (X1: isofhlevelf n  (fun x:X => f' (w x))). apply (isofhlevelfhomot n _ _ h X0).
apply (isofhlevelfgwtog n  w f' X1). Defined.




Theorem isofhlevelfonpaths (n:nat) { X Y : UU }(f:X -> Y)(x x':X): isofhlevelf (S n)  f -> isofhlevelf n  (@maponpaths _ _ f x x').
Proof. intros n X Y f x x' X0.
set (y:= f x'). set (xe':= hfiberpair  f x' (idpath _ )).
assert (is1: isofhlevelf n  (d2g  f x xe')). unfold isofhlevelf. intro y0 .  apply (isofhlevelweqf n  ( ezweq3g  f x xe' y0  ) (X0 y (hfiberpair  f x y0) xe')).
assert (h: forall ee:paths x' x, paths (d2g  f x xe' ee) (maponpaths f  (pathsinv0  ee))). intro.
assert (e0: paths (pathscomp0   (maponpaths f  (pathsinv0 ee)) (idpath _ ))  (maponpaths f  (pathsinv0  ee)) ). induction ee.  simpl.  apply idpath. apply (e0). apply (isofhlevelfhomot2 n _ _  ( weqpair (@pathsinv0 _ x' x ) (isweqpathsinv0 _ _ ) ) h is1) . Defined.



Theorem isofhlevelfsn (n:nat) { X Y : UU } (f:X -> Y): (forall x x':X, isofhlevelf n  (@maponpaths _ _ f x x')) -> isofhlevelf (S n)  f.
Proof. intros n X Y f X0.  unfold isofhlevelf. intro y .  simpl.  intros x x' . induction x as [ x e ]. induction x' as [ x' e' ].  induction e' . set (xe':= hfiberpair  f x' ( idpath _ ) ).  set (xe:= hfiberpair  f x e). set (d3:= d2g  f x xe'). simpl in d3.
assert (is1: isofhlevelf n  (d2g  f x xe')).
assert (h: forall ee: paths x' x, paths (maponpaths f  (pathsinv0  ee)) (d2g  f x xe' ee)). intro. unfold d2g. simpl .  apply ( pathsinv0 ( pathscomp0rid _ ) ) .
assert (is2: isofhlevelf n  (fun ee: paths x' x => maponpaths f  (pathsinv0  ee))).  apply (isofhlevelfgtogw n  ( weqpair _ (isweqpathsinv0  _ _  ) ) (@maponpaths _ _ f x x') (X0 x x')).
apply (isofhlevelfhomot n  _ _  h is2).
apply (isofhlevelweqb n  (  ezweq3g f x xe' e )  (is1 e)).  Defined.


Theorem isofhlevelfssn (n:nat) { X Y : UU } (f:X -> Y): (forall x:X, isofhlevelf (S n)  (@maponpaths _ _ f x x)) -> isofhlevelf (S (S n))  f.
Proof.  intros n X Y f X0.  unfold isofhlevelf. intro y .
assert (forall xe0: hfiber  f y, isofhlevel (S n) (paths xe0 xe0)). intro. induction xe0 as [ x e ].  induction e . set (e':= idpath ( f x ) ).  set (xe':= hfiberpair  f x e').  set (xe:= hfiberpair  f x e' ). set (d3:= d2g  f x xe'). simpl in d3.
assert (is1: isofhlevelf (S n)  (d2g  f x xe')).
assert (h: forall ee: paths x x, paths (maponpaths f  (pathsinv0  ee))  (d2g  f x xe' ee)). intro. unfold d2g . simpl . apply ( pathsinv0 ( pathscomp0rid _ ) ) .
assert (is2: isofhlevelf (S n)  (fun ee: paths x x => maponpaths f  (pathsinv0  ee))).  apply (isofhlevelfgtogw ( S n )  ( weqpair _ (isweqpathsinv0  _ _  ) ) (@maponpaths _ _ f x x) ( X0 x )) .
apply (isofhlevelfhomot (S n) _ _  h is2).
apply (isofhlevelweqb (S n)  ( ezweq3g  f x xe' e' )  (is1 e')).
apply (isofhlevelssn).  assumption. Defined.



(** ** h -levels of [ pr1 ], fiber inclusions, fibers, total spaces and bases of fibrations *)


(** *** h-levelf of [ pr1 ] *)


Theorem isofhlevelfpr1 (n:nat) { X : UU } (P:X -> UU)(is: forall x:X, isofhlevel n (P x)) : isofhlevelf n  (@pr1 X P).
Proof. intros. unfold isofhlevelf. intro x .  apply (isofhlevelweqf n  ( ezweqpr1  _ x)    (is x)). Defined.

Lemma isweqpr1 { Z : UU } ( P : Z -> UU ) ( is1 : forall z : Z, iscontr ( P z ) ) : isweq ( @pr1 Z P ) .
Proof. intros. unfold isweq.  intro y. set (isy:= is1 y). apply (iscontrweqf ( ezweqpr1 P y)) . assumption. Defined.

Definition weqpr1 { Z : UU } ( P : Z -> UU ) ( is : forall z : Z , iscontr ( P z ) ) : weq ( total2 P ) Z := weqpair _ ( isweqpr1 P is ) .




(** *** h-level of the total space [ total2 ] *)

Theorem isofhleveltotal2 ( n : nat ) { X : UU } ( P : X -> UU ) ( is1 : isofhlevel n X )( is2 : forall x:X, isofhlevel n (P x) ) : isofhlevel n (total2 P).
Proof. intros. apply (isofhlevelXfromfY n  (@pr1 _ _ )). apply isofhlevelfpr1. assumption. assumption. Defined.

Corollary isofhleveldirprod ( n : nat ) ( X Y : UU ) ( is1 : isofhlevel n X ) ( is2 : isofhlevel n Y ) : isofhlevel n (dirprod X Y).
Proof. intros. apply isofhleveltotal2. assumption. intro. assumption. Defined.
















(** ** Propositions, inclusions  and sets *)







(** *** Basics about types of h-level 1 - "propositions" *)


Definition isaprop  := isofhlevel 1 .

Definition isPredicate {X} (Y : X->UU) := ∀ x, isaprop (Y x).

Definition isapropunit : isaprop unit := iscontrpathsinunit .

Definition isapropdirprod X Y : isaprop X -> isaprop Y -> isaprop (X×Y) := isofhleveldirprod 1 X Y .

Lemma isapropifcontr { X : UU } ( is : iscontr X ) : isaprop X .
Proof. intros . set (f:= fun x:X => tt). assert (isw : isweq f). apply isweqcontrtounit.  assumption. apply (isofhlevelweqb (S O) ( weqpair f isw ) ).  intros x x' . apply iscontrpathsinunit. Defined.
Coercion isapropifcontr : iscontr >-> isaprop  .

Theorem hlevelntosn ( n : nat ) ( T : UU )  ( is : isofhlevel n T ) : isofhlevel (S n) T.
Proof. intro.   induction n as [ | n IHn ] . intro. apply isapropifcontr. intro.  intro X. change (forall t1 t2:T, isofhlevel (S n) (paths t1 t2)). intros t1 t2 . change (forall t1 t2 : T, isofhlevel n (paths t1 t2)) in X. set (XX := X t1 t2). apply (IHn _ XX).  Defined.

Corollary isofhlevelcontr (n:nat) { X : UU } ( is : iscontr X ) : isofhlevel n X.
Proof. intro. induction n as [ | n IHn ] . intros X X0 . assumption.
intros X X0. simpl. intros x x' . assert (is: iscontr (paths x x')). apply (isapropifcontr X0 x x'). apply (IHn _ is). Defined.

Lemma isofhlevelfweq ( n : nat ) { X Y : UU } ( f : weq X Y ) :  isofhlevelf n f .
Proof. intros n X Y f .  unfold isofhlevelf.   intro y . apply ( isofhlevelcontr n ). apply ( pr2 f ). Defined.

Corollary isweqfinfibseq  { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z  ) ( isz : iscontr Z ) : isweq f .
Proof. intros . apply ( isofhlevelfffromZ 0 f g z fs ( isapropifcontr isz ) ) .  Defined .

Corollary weqhfibertocontr { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : iscontr Y ) : weq ( hfiber f y ) X .
Proof. intros . split with ( hfiberpr1 f y ) . apply ( isofhlevelfhfiberpr1 0 f y ( hlevelntosn 0 _ is ) ) . Defined.

Corollary weqhfibertounit ( X : UU ) : weq ( hfiber ( fun x : X => tt ) tt ) X .
Proof.  intro . apply ( weqhfibertocontr _ tt iscontrunit ) . Defined.

Corollary isofhleveltofun ( n : nat ) ( X : UU ) : isofhlevel n X -> isofhlevelf n ( fun x : X => tt ) .
Proof. intros n X is .  intro t . induction t . apply ( isofhlevelweqb n ( weqhfibertounit X ) is ) .  Defined .

Corollary isofhlevelfromfun ( n : nat ) ( X : UU ) : isofhlevelf n ( fun x : X => tt ) ->  isofhlevel n X .
Proof. intros n X is .  apply ( isofhlevelweqf n ( weqhfibertounit X ) ( is tt ) ) .  Defined .

Definition weqhfiberunit {X Z} (i:X->Z) (z:Z) : (Σ x, hfiber (λ _:unit, z) (i x)) ≃ hfiber i z.
Proof.
  intros. simple refine (weqgradth _ _ _ _).
  + intros [x [t e]]. exact (x,,!e).
  + intros [x e]. exact (x,,tt,,!e).
  + intros [x [t e]]. apply maponpaths. simple refine (total2_paths2 _ _).
    * apply isapropunit.
    * simpl. induction e. rewrite pathsinv0inv0. induction t. reflexivity.
  + intros [x e]. apply maponpaths. apply pathsinv0inv0.
Defined.

Lemma isofhlevelsnprop (n:nat) { X : UU } ( is : isaprop X ) : isofhlevel (S n) X.
Proof. intros n X X0. simpl. unfold isaprop in X0.  simpl in X0. intros x x' . apply isofhlevelcontr. apply (X0 x x'). Defined.

Lemma iscontraprop1 { X : UU } ( is : isaprop X ) ( x : X ) : iscontr X .
Proof. intros . unfold iscontr. split with x . intro t .  unfold isofhlevel in is .  set (is' := is t x ). apply ( pr1 is' ).
Defined.

Lemma iscontraprop1inv { X : UU } ( f : X -> iscontr X ) : isaprop X .
Proof. intros X X0. assert ( H : X -> isofhlevel (S O) X). intro X1.  apply (hlevelntosn O _ ( X0 X1 ) ) . apply ( isofhlevelsn O H ) . Defined.

Lemma proofirrelevance ( X : UU ) ( is : isaprop X ) : forall x x' : X , paths x x' .
Proof. intros . unfold isaprop in is . unfold isofhlevel in is .   apply ( pr1 ( is x x' ) ). Defined.

Lemma invproofirrelevance ( X : UU ) ( ee : forall x x' : X , paths x x' ) : isaprop X.
Proof. intros . unfold isaprop. unfold isofhlevel .  intro x .
assert ( is1 : iscontr X ).  split with x. intro t .  apply ( ee t x). assert ( is2 : isaprop X).  apply isapropifcontr. assumption.
unfold isaprop in is2. unfold isofhlevel in is2.  apply (is2 x). Defined.

Lemma isapropcoprod P Q : isaprop P -> isaprop Q -> (P -> Q -> ∅) -> isaprop (P ⨿ Q).
Proof.
  intros ? ? i j n. apply invproofirrelevance. intros a b. apply inv_equality_by_case.
  induction a as [a|a].
  - induction b as [b|b].
    + apply i.
    + contradicts (n a) b.
  - induction b as [b|b].
    + contradicts (n b) a.
    + apply j.
Defined.

Lemma isweqimplimpl { X Y : UU } ( f : X -> Y ) ( g : Y -> X ) ( isx : isaprop X ) ( isy : isaprop Y ) : isweq f.
Proof. intros.
assert (isx0: forall x:X, paths (g (f x)) x). intro. apply proofirrelevance . apply isx .
assert (isy0 : forall y : Y, paths (f (g y)) y). intro. apply proofirrelevance . apply isy .
apply (gradth  f g isx0 isy0).  Defined.

Definition weqimplimpl { X Y : UU } ( f : X -> Y ) ( g : Y -> X ) ( isx : isaprop X ) ( isy : isaprop Y ) := weqpair _ ( isweqimplimpl f g isx isy ) .

Definition weqiff { X Y : UU } : (X <-> Y) -> isaprop X -> isaprop Y -> X ≃ Y
  := λ f i j, weqpair _ ( isweqimplimpl (pr1 f) (pr2 f) i j).

Definition weq_to_iff { X Y : UU } : X ≃ Y -> (X <-> Y)
  := λ f, (pr1weq f ,, invmap f).

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros x x' . induction x. Defined.

Theorem isapropifnegtrue { X : UU } ( a : X -> empty ) : isaprop X .
Proof . intros . set ( w := weqpair _ ( isweqtoempty a ) ) . apply ( isofhlevelweqb 1 w isapropempty ) .  Defined .

(** Basic facts about complementary propositions  *)

Lemma isapropretract {P Q} (i: isaprop Q) (f:P->Q) (g:Q->P) (h: g∘f ~ idfun _): isaprop P.
Proof.
  intros.
  apply invproofirrelevance; intros p p'.
  refine (_ @ (_ : g (f p) = g (f p')) @ _).
  - apply pathsinv0. apply h.
  - apply maponpaths. now apply proofirrelevance.
  - apply h.
Defined.

Lemma isapropcomponent1 P Q : isaprop ( P ⨿ Q ) -> isaprop P.
Proof.
  (* see also [isofhlevelsnsummand1] *)
  intros ? ? i. apply invproofirrelevance; intros p p'.
  exact (equality_by_case (proofirrelevance _ i (ii1 p) (ii1 p'))).
Defined.

Lemma isapropcomponent2 P Q : isaprop ( P ⨿ Q ) -> isaprop Q.
Proof.
  (* see also [isofhlevelsnsummand2] *)
  intros ? ? i. apply invproofirrelevance; intros q q'.
  exact (equality_by_case (proofirrelevance _ i (ii2 q) (ii2 q'))).
Defined.

(** *** Two pairs are equal if their first components are and the type of the second
        component is a proposition for one of the components *)


(** *** Inclusions - functions of h-level 1 *)


Definition isincl { X Y : UU } (f : X -> Y ) := isofhlevelf 1 f .

Definition incl ( X Y : UU ) := total2 ( fun f : X -> Y => isincl f ) .
Definition inclpair { X Y : UU } ( f : X -> Y ) ( is : isincl f ) : incl X Y := tpair _ f is .
Definition pr1incl ( X Y : UU ) : incl X Y -> ( X -> Y ) := @pr1 _ _ .
Coercion pr1incl : incl >-> Funclass .

Lemma isinclweq ( X Y : UU ) ( f : X -> Y ) : isweq f -> isincl f .
Proof . intros X Y f is . apply ( isofhlevelfweq 1 ( weqpair _ is ) ) .  Defined .
Coercion isinclweq : isweq >-> isincl .

Lemma isofhlevelfsnincl (n:nat) { X Y : UU } (f:X -> Y)(is: isincl  f): isofhlevelf (S n)  f.
Proof. intros. unfold isofhlevelf.  intro y . apply isofhlevelsnprop. apply (is y). Defined.

Definition weqtoincl ( X Y : UU ) : weq X Y -> incl X Y :=  fun w => inclpair ( pr1weq w ) ( pr2 w ) .
Coercion weqtoincl : weq >-> incl .

Lemma isinclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : isincl ( funcomp ( pr1 f ) ( pr1 g ) ) .
Proof . intros . apply ( isofhlevelfgf 1 f g ( pr2 f ) ( pr2 g ) ) . Defined .

Definition inclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : incl X Z := inclpair ( funcomp ( pr1 f ) ( pr1 g ) ) ( isinclcomp f g ) .

Lemma isincltwooutof3a { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isg : isincl g ) ( isgf : isincl ( funcomp f g ) ) : isincl f .
Proof . intros . apply ( isofhlevelff 1 f g isgf ) .  apply ( isofhlevelfsnincl 1 g isg ) . Defined .

Lemma isinclgwtog { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isincl ( funcomp w g ) ) : isincl g .
Proof . intros . apply ( isofhlevelfgwtog 1 w g is ) .  Defined .

Lemma isinclgtogw { X Y Z : UU }  ( w : weq X Y ) ( g : Y -> Z ) ( is : isincl g ) : isincl ( funcomp w g ) .
Proof . intros . apply  ( isofhlevelfgtogw 1 w g is ) . Defined .


Lemma isinclhomot { X Y : UU } ( f g : X -> Y ) ( h : homot f g ) ( isf : isincl f ) : isincl g .
Proof . intros . apply ( isofhlevelfhomot ( S O ) f g h isf ) . Defined .



Definition isofhlevelsninclb (n:nat) { X Y : UU } (f:X -> Y)(is: isincl  f) : isofhlevel (S n) Y -> isofhlevel (S n) X:= isofhlevelXfromfY (S n)  f (isofhlevelfsnincl n  f is).

Definition  isapropinclb { X Y : UU } ( f : X -> Y ) ( isf : isincl f ) : isaprop Y ->  isaprop X := isofhlevelXfromfY 1 _ isf .


Lemma iscontrhfiberofincl { X Y : UU } (f:X -> Y): isincl  f -> (forall x:X, iscontr (hfiber  f (f x))).
Proof. intros X Y f X0 x. unfold isofhlevelf in X0. set (isy:= X0 (f x)).  apply (iscontraprop1 isy (hfiberpair  f _ (idpath (f x)))). Defined.

(* see incl_injectivity for the equivalence between isincl and isInjective *)
Definition isInjective { X Y : UU } (f:X -> Y) := ∀ (x x':X), isweq (maponpaths f : x = x' -> f x = f x').

Definition Injectivity { X Y : UU } (f:X -> Y) :
  isInjective f -> ∀ (x x':X), x = x'  ≃  f x = f x'.
Proof. intros ? ? ? i ? ?. exact (weqpair _ (i x x')). Defined.

Lemma isweqonpathsincl { X Y : UU } (f:X -> Y) : isincl f -> isInjective f.
Proof. intros ? ? ? is x x'. apply (isofhlevelfonpaths O  f x x' is). Defined.

Definition weqonpathsincl  { X Y : UU } (f:X -> Y) (is: isincl  f)(x x':X) := weqpair _ ( isweqonpathsincl f is x x' ) .

Definition invmaponpathsincl { X Y : UU } (f:X -> Y) : isincl f -> ∀ x x', f x = f x' -> x = x'.
Proof.
  intros ? ? ? is x x'.
  exact (invmap (weqonpathsincl  f is x x')).
Defined.

Lemma isinclweqonpaths { X Y : UU } (f:X -> Y): isInjective f -> isincl  f.
Proof. intros X Y f X0.  apply (isofhlevelfsn O f X0). Defined.

Definition isinclpr1 { X : UU } (P:X -> UU)(is: forall x:X, isaprop (P x)): isincl  (@pr1 X P):= isofhlevelfpr1 (S O) P is.

Theorem subtypeInjectivity {A : UU} (B : A -> UU) :
  isPredicate B -> ∀ (x y : total2 B), (x = y) ≃ (pr1 x = pr1 y).
Proof. intros. apply Injectivity. apply isweqonpathsincl. now apply isinclpr1.
Defined.

Corollary subtypeEquality {A : UU} {B : A -> UU} (is : isPredicate B)
   {s s' : total2 (fun x => B x)} : pr1 s = pr1 s' -> s = s'.
Proof. intros A B H s s'. apply invmap. now apply subtypeInjectivity.
Defined.

Corollary subtypeEquality' {A : UU} {B : A -> UU}
   {s s' : total2 (fun x => B x)} : pr1 s = pr1 s' -> isaprop (B (pr1 s')) -> s = s'.
(* This variant of subtypeEquality is not often needed. *)
Proof. intros ? ? ? ? e is. apply (total2_paths e). apply is. Defined.

(* This corollary of subtypeEquality is used for categories. *)
Corollary unique_exists {A : UU} {B : A -> UU} (x : A) (b : B x)
          (h : forall y, isaprop (B y)) (H : forall y, B y -> y = x) :
  iscontr (total2 (fun t : A => B t)).
Proof.
  intros A B x b h H.
  use iscontrpair.
  exact (x,,b).
  intros t.
  apply subtypeEquality'.
  apply (H (pr1 t)). apply (pr2 t).
  apply (h (pr1 (x,,b))).
Defined.

Definition subtypePairEquality {X} {P:X -> UU} (is: isPredicate P)
           {x y:X} {p:P x} {q:P y} :
  x = y -> (x,,p) = (y,,q).
Proof. intros X P is x y p q e. apply (total2_paths2 e). apply is. Defined.

Definition subtypePairEquality' {X} {P:X -> UU}
           {x y:X} {p:P x} {q:P y} :
  x = y -> isaprop(P y) -> (x,,p) = (y,,q).
(* This variant of subtypePairEquality is never needed. *)
Proof. intros X P x y p q e is. apply (total2_paths2 e). apply is. Defined.

Theorem samehfibers { X Y Z : UU } (f: X -> Y) (g: Y -> Z) (is1: isincl g) (y:Y) :
  hfiber f y ≃ hfiber (g ∘ f) (g y) .
Proof.
  intros. exists (hfibersftogf f g (g y) (hfiberpair g y (idpath _))).
  set (z := g y). set (ye := hfiberpair g y (idpath _)). intro xe.
  apply (iscontrweqf (X := hfibersgftog f g z xe = ye)).
  { exists (ezmap _ _ _ (fibseq1 _ _ _ (fibseqhf f g z ye) _)).
    exact (isweqezmap1 _ _ _ _ _). }
  apply isapropifcontr. now apply iscontrhfiberofincl.
Defined.

(** *** Basics about types of h-level 2 - "sets" *)

Definition isaset ( X : UU ) : UU := ∀ x x' : X , isaprop ( x = x' ) .

(* Definition isaset := isofhlevel 2 . *)

Notation isasetdirprod := ( isofhleveldirprod 2 ) .

Lemma isasetunit : isaset unit .
Proof . apply ( isofhlevelcontr 2 iscontrunit ) . Defined .

Lemma isasetempty : isaset empty .
Proof. apply ( isofhlevelsnprop 1 isapropempty ) .  Defined .

Lemma isasetifcontr { X : UU } ( is : iscontr X ) : isaset X .
Proof . intros . apply ( isofhlevelcontr 2 is ) . Defined .

Lemma isasetaprop { X : UU } ( is : isaprop X ) : isaset X .
Proof . intros . apply ( isofhlevelsnprop 1 is ) . Defined .

Corollary isaset_total2 {X:UU} (P:X->UU) : isaset X -> (∀ x, isaset (P x)) -> isaset (Σ x, P x).
Proof. intros. apply (isofhleveltotal2 2); assumption. Defined.

Corollary isaset_dirprod {X Y:UU} : isaset X -> isaset Y -> isaset (X × Y).
Proof. intros. apply isaset_total2. assumption. intro. assumption. Defined.

(** The following lemma assert "uniqueness of identity proofs" (uip) for sets. *)

Lemma uip { X : UU } ( is : isaset X ) { x x' : X } ( e e' : x = x' ) : e = e' .
Proof. intros . apply ( proofirrelevance _ ( is x x' ) e e' ) . Defined .

(** For the theorem about the coproduct of two sets see [ isasetcoprod ] below. *)


Lemma isofhlevelssnset (n:nat) ( X : UU ) ( is : isaset X ) : isofhlevel ( S (S n) ) X.
Proof. intros n X X0. simpl. unfold isaset in X0.   intros x x' . apply isofhlevelsnprop. set ( int := X0 x x'). assumption . Defined.

Lemma isasetifiscontrloops (X:UU): (forall x:X, iscontr (paths x x)) -> isaset X.
Proof. intros X X0. unfold isaset. unfold isofhlevel. intros x x' x0 x0' .   induction x0. set (is:= X0 x). apply isapropifcontr. assumption.  Defined.

Lemma iscontrloopsifisaset (X:UU): (isaset X) -> (forall x:X, iscontr (paths x x)).
Proof. intros X X0 x. unfold isaset in X0. unfold isofhlevel in X0.  change (forall (x x' : X) (x0 x'0 : paths x x'), iscontr (paths x0 x'0))  with (forall (x x':X),  isaprop (paths x x')) in X0.  apply (iscontraprop1 (X0 x x) (idpath x)). Defined.



(**  A monic subtype of a set is a set. *)

Theorem isasetsubset { X Y : UU } (f: X -> Y) (is1: isaset Y) (is2: isincl  f): isaset X.
Proof. intros. apply  (isofhlevelsninclb (S O)  f is2). apply is1. Defined.



(** The morphism from hfiber of a map to a set is an inclusion. *)

Theorem isinclfromhfiber { X Y : UU } (f: X -> Y) (is : isaset Y) ( y: Y ) : @isincl (hfiber  f y) X ( @pr1 _ _  ).
Proof. intros. refine (isofhlevelfhfiberpr1 _ _ _ _). assumption. Defined.


(** Criterion for a function between sets being an inclusion.  *)


Theorem isinclbetweensets { X Y : UU } ( f : X -> Y ) ( isx : isaset X ) ( isy : isaset Y ) ( inj : forall x x' : X , ( paths ( f x ) ( f x' ) -> paths x x' ) ) : isincl f .
Proof. intros .  apply isinclweqonpaths .  intros x x' .  apply ( isweqimplimpl ( @maponpaths _ _ f x x' ) (  inj x x' ) ( isx x x' ) ( isy ( f x ) ( f x' ) ) ) . Defined .

(** A map from [ unit ] to a set is an inclusion. *)

Theorem isinclfromunit { X : UU } ( f : unit -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isofhlevelcontr 2 ( iscontrunit ) )  is ) .  intros .  induction x . induction x' . apply idpath . Defined .




Corollary set_bijection_to_weq {X Y:UU} (f:X->Y) : bijective f -> isaset Y -> isweq f.
Proof.
  (* compare with bijection_to_weq: this one doesn't use gradth *)
  intros ? ? ? bij i y. set (sur := pr1 bij); set (inj := pr2 bij).
  unshelve refine (_,,_).
  - exists (pr1 (sur y)). exact (pr2 (sur y)).
  - intro w.
    unshelve refine (total2_paths _ _).
    + simpl. apply inj. intermediate_path y.
      * exact (pr2 w).
      * exact (! pr2 (sur y)).
    + induction w as [x e]; simpl. induction e.
      apply i.
Defined.


(* End of the file uu0b.v *)
