(** * Univalent Basics. Vladimir Voevodsky. Feb. 2010 - Sep. 2011. Port to coq trunk (8.4-8.5) in
 March 2014. The third part of the original uu0 file, created on Dec. 3, 2014.

Only one usniverse is used and never as a type. We use general functional extensionality [ funextfunax ] asserting that two homotopic functions are equal. Since [ funextfunax ] itself is  not an "axiom"  in our sense, i.e., its type is not of h-level 1, we show that it is logically equivalent to a real  axiom [ funcontr ] which asserts that the space of sections of a family with contractible  fibers is contractible.

*)


(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with
Coq8.2 *)

(** Imports *)

Require Export UniMath.Foundations.Basics.PartC.


(** *** Deduction of functional extnsionality for dependent functions (sections) from functional extensionality of usual functions *)

Axiom funextfunax : forall (X Y:UU)(f g:X->Y),  (forall x:X, paths (f x) (g x)) -> (paths f g).


Lemma isweqlcompwithweq { X X' : UU} (w: weq X X') (Y:UU) : isweq (fun a:X'->Y => (fun x:X => a (w x))).
Proof. intros. set (f:= (fun a:X'->Y => (fun x:X => a (w x)))). set (g := fun b:X-> Y => fun x':X' => b ( invweq  w x')).
set (egf:= (fun a:X'->Y => funextfunax X' Y (fun x':X' => (g (f a)) x') a (fun x': X' =>  maponpaths a  (homotweqinvweq w x')))).
set (efg:= (fun a:X->Y => funextfunax X Y (fun x:X => (f (g a)) x) a (fun x: X =>  maponpaths a  (homotinvweqweq w x)))).
apply (gradth  f g egf efg). Defined.



Lemma isweqrcompwithweq { Y Y':UU } (w: weq Y Y')(X:UU): isweq (fun a:X->Y => (fun x:X => w (a x))).
Proof. intros. set (f:= (fun a:X->Y => (fun x:X => w (a x)))). set (g := fun a':X-> Y' => fun x:X => (invweq  w (a' x))).
set (egf:= (fun a:X->Y => funextfunax X Y (fun x:X => (g (f a)) x) a (fun x: X => (homotinvweqweq w (a x))))).
set (efg:= (fun a':X->Y' => funextfunax X Y' (fun x:X => (f (g a')) x) a' (fun x: X =>  (homotweqinvweq w (a' x))))).
apply (gradth  f g egf efg). Defined.



Theorem funcontr { X : UU } (P:X -> UU) : (forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x).
Proof. intros X P X0 . set (T1 := forall x:X, P x). set (T2 := (hfiber (fun f: (X -> total2 P)  => fun x: X => pr1  (f x)) (fun x:X => x))). assert (is1:isweq (@pr1 X P)). apply isweqpr1. assumption.  set (w1:= weqpair  (@pr1 X P) is1).
assert (X1:iscontr T2).  apply (isweqrcompwithweq  w1 X (fun x:X => x)).
apply ( iscontrretract  _ _  (sectohfibertosec P ) X1). Defined.

Corollary funcontrtwice { X : UU } (P: X-> X -> UU)(is: forall (x x':X), iscontr (P x x')): iscontr (forall (x x':X), P x x').
Proof. intros.
assert (is1: forall x:X, iscontr (forall x':X, P x x')). intro. apply (funcontr _ (is x)). apply (funcontr _ is1). Defined.


(** Proof of the fact that the [ toforallpaths ] from [paths s1 s2] to [forall t:T, paths (s1 t) (s2 t)] is a weak equivalence - a strong form
of functional extensionality for sections of general families. The proof uses only [funcontr] which is an axiom i.e. its type satisfies [ isaprop ].  *)

Lemma funextweql1 { T : UU } (P:T -> UU) (g: ∀ t, P t) : ∃! (f:∀ t, P t), ∀ t:T, f t = g t.
Proof.
  intros. unshelve refine (iscontrretract (X := ∀ t, Σ p, p = g t) _ _ _ _).
  - intros x. unshelve refine (_,,_).
    + intro t. exact (pr1 (x t)).
    + intro t; simpl. exact (pr2 (x t)).
  - intros y t. exists (pr1 y t). exact (pr2 y t).
  - intros u. induction u as [t x]. reflexivity.
  - apply funcontr. intro t. apply iscontrcoconustot.
Defined.

Theorem isweqtoforallpaths { T : UU } (P:T -> UU) (f g: ∀ t:T, P t) :
  isweq (toforallpaths P f g).
Proof.
  intros.
  refine (isweqtotaltofib _ _ (λ (h:∀ t, P t), toforallpaths P h g) _ f).
  refine (isweqcontrcontr (X := Σ (h: ∀ t, P t), h = g)
            (λ ff, tpair _ (pr1 ff) (toforallpaths P (pr1 ff) g (pr2 ff))) _ _).
  { exact (iscontrcoconustot _ g). }
  { apply funextweql1. }
Qed.

Theorem weqtoforallpaths { T : UU } (P:T -> UU)(f g : forall t:T, P t) :
  (f = g) ≃ (∀ t:T, f t = g t).
Proof. intros. exists (toforallpaths P f g). apply isweqtoforallpaths. Defined.

Definition funextsec {T:UU} (P: T-> UU) (f g : ∀ t:T, P t) : (∀ t, f t = g t) -> f = g
  := invmap (weqtoforallpaths _ f g) .

Definition funextfun { X Y:UU } (f g:X->Y) : (∀ x:X, f x = g x) -> f = g
  := funextsec _ _ _.

(** I do not know at the moment whether [funextfun] is equal (homotopic) to [funextfunax]. It is advisable in all cases to use [funextfun] or, equivalently, [funextsec], since it can be produced from [funcontr] and therefore is well defined up to a canonical equivalence.  In addition it is a homotopy inverse of [toforallpaths] which may be true or not for [funextsecax]. *)

Theorem isweqfunextsec { T : UU } (P:T -> UU)(f g : forall t:T, P t) : isweq (funextsec P f g).
Proof. intros. apply (isweqinvmap ( weqtoforallpaths _  f g ) ). Defined.

Definition weqfunextsec { T : UU } (P:T -> UU)(f g : forall t:T, P t) : weq  (forall t:T, paths (f t) (g t)) (paths f g) := weqpair _ ( isweqfunextsec P f g ) .






(** ** Sections of "double fibration" [(P: T -> UU)(PP: forall t:T, P t -> UU)] and pairs of sections *)



(** *** General case *)

Definition totaltoforall { X : UU } (P : X -> UU ) ( PP : forall x:X, P x -> UU ) : total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) -> forall x:X, total2 (PP x).
Proof.
  intros X P PP X0 x.
  exists (pr1 X0 x).
  apply (pr2 X0 x).
Defined.


Definition foralltototal  { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ):  (forall x:X, total2 (PP x)) -> total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)).
Proof.
  intros X P PP X0.
  exists (fun x:X => pr1  (X0 x)).
  apply (fun x:X => pr2  (X0 x)).
Defined.

Lemma lemmaeta1 { X : UU } (P:X->UU) (Q:(forall x:X, P x) -> UU)(s0: forall x:X, P x)(q: Q (fun x:X => (s0 x))): paths (tpair (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) s0 q) (tpair (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) (fun x:X => (s0 x)) q).
Proof. intros. set (ff:= fun tp:total2 (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) => tpair _ (fun x:X => pr1  tp x) (pr2  tp)). assert (X0 : isweq ff).  apply (isweqfpmap  ( weqeta P ) Q ).
assert (ee: paths (ff (tpair (fun s : forall x : X, P x => Q (fun x : X => s x)) s0 q)) (ff (tpair (fun s : forall x : X, P x => Q (fun x : X => s x)) (fun x : X => s0 x) q))). apply idpath.

apply (invmaponpathsweq ( weqpair ff X0 ) _ _ ee). Defined.



Definition totaltoforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU )( ss : total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) ): paths (foralltototal _ _ (totaltoforall  _ _ ss)) ss.
Proof. intros.  induction ss as [ t x ]. unfold foralltototal. unfold totaltoforall.  simpl.  set (et:= fun x:X => t x).

assert (paths (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) t x) (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x)). apply (lemmaeta1 P (fun s: forall x:X, P x =>  forall x:X, PP x (s x)) t x).

assert (ee: paths (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x) (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et (fun x0 : X => x x0))).
assert (eee: paths x (fun x0:X => x x0)). apply etacorrection. induction eee. apply idpath. induction ee. apply pathsinv0. assumption. Defined.



Definition foralltototaltoforall { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) ( ss : forall x:X, total2 (PP x)): paths (totaltoforall _ _ (foralltototal _ _ ss)) ss.
Proof. intros. unfold foralltototal. unfold totaltoforall.  simpl. assert (ee: forall x:X, paths (tpair (PP x) (pr1 (ss x)) (pr2 (ss x))) (ss x)).  intro. apply (pathsinv0   (tppr  (ss x))).  apply (funextsec). assumption. Defined.

Theorem isweqforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) : isweq (foralltototal P PP).
Proof. intros.  apply (gradth  (foralltototal P PP) (totaltoforall P PP) (foralltototaltoforall P PP) (totaltoforalltototal P PP)). Defined.

Theorem isweqtotaltoforall { X : UU } (P:X->UU)(PP:forall x:X, P x -> UU): isweq (totaltoforall P PP).
Proof. intros.  apply (gradth   (totaltoforall P PP) (foralltototal P PP)  (totaltoforalltototal P PP) (foralltototaltoforall P PP)). Defined.

Definition weqforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) := weqpair _ ( isweqforalltototal P PP ) .

Definition weqtotaltoforall { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) := invweq ( weqforalltototal P PP ) .



(** *** Functions to a dependent sum (to a [ total2 ]) *)

Definition weqfuntototaltototal ( X : UU ) { Y : UU } ( Q : Y -> UU ) : weq ( X -> total2 Q ) ( total2 ( fun f : X -> Y => forall x : X , Q ( f x ) ) ) := weqforalltototal ( fun x : X => Y ) ( fun x : X => Q ) .


(** *** Functions to direct product *)

(** Note: we give direct proofs for this special case. *)


Definition funtoprodtoprod { X Y Z : UU } ( f : X -> dirprod Y Z ) : dirprod ( X -> Y ) ( X -> Z ) := dirprodpair ( fun x : X => pr1 ( f x ) ) ( fun x : X => ( pr2 ( f x ) ) ) .

Definition prodtofuntoprod { X Y Z : UU } ( fg : dirprod ( X -> Y ) ( X -> Z ) ) : X -> dirprod Y Z := match fg with tpair _ f g => fun x : X => dirprodpair ( f x ) ( g x ) end .

Theorem weqfuntoprodtoprod ( X Y Z : UU ) : weq ( X -> dirprod Y Z ) ( dirprod ( X -> Y ) ( X -> Z ) ) .
Proof. intros. set ( f := @funtoprodtoprod X Y Z ) . set ( g := @prodtofuntoprod X Y Z ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . apply funextfun .  intro x .  simpl . apply pathsinv0 . apply tppr .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . induction a as [ fy fz ] . apply pathsdirprod .  simpl . apply pathsinv0 . apply etacorrection . simpl . apply pathsinv0 . apply etacorrection .
apply ( gradth _ _ egf efg ) . Defined .







(** ** Homotopy fibers of the map [forall x:X, P x -> forall x:X, Q x] *)

(** *** General case *)

Definition maponsec { X:UU }  (P Q : X -> UU) (f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) :=
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 { X Y : UU } (P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).



Definition hfibertoforall { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): hfiber  (@maponsec _ _ _ f) s -> forall x:X, hfiber  (f x) (s x).
Proof. intro. intro. intro. intro. intro.  unfold hfiber.

set (map1:= totalfun (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ (fun x : X => f x (pointover x)) s )).

set (map2 := totaltoforall P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

set (themap := fun a:_ => map2 (map1 a)). assumption. Defined.



Definition foralltohfiber  { X : UU } ( P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): (forall x:X, hfiber  (f x) (s x)) -> hfiber  (maponsec _ _ f) s.
Proof.  intro. intro. intro. intro.   intro. unfold hfiber.

set (map2inv := foralltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).
set (map1inv :=  totalfun (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ (fun x : X => f x (pointover x)) s)).
set (themap := fun a:_=> map1inv (map2inv a)). assumption. Defined.


Theorem isweqhfibertoforall  { X : UU } (P Q :X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq (hfibertoforall _ _ f s).
Proof. intro. intro. intro. intro. intro.

set (map1:= totalfun (fun pointover : forall x : X, P x =>
      paths  (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

assert (is1: isweq map1). apply (isweqfibtototal _ _ (fun pointover: forall x:X, P x => weqtoforallpaths _ (fun x : X => f x (pointover x)) s )).

assert (is2: isweq map2). apply isweqtotaltoforall.

apply (twooutof3c map1 map2 is1 is2). Defined.


Definition weqhfibertoforall  { X : UU } (P Q :X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x) := weqpair _ ( isweqhfibertoforall P Q f s ) .



Theorem isweqforalltohfiber  { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq (foralltohfiber  _ _ f s).
Proof. intro. intro. intro. intro. intro.

set (map2inv := foralltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

assert (is2: isweq map2inv). apply (isweqforalltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

set (map1inv :=  totalfun (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _  (fun x : X => f x (pointover x)) s)).

assert (is1: isweq map1inv).

(* ??? in this place 8.4 (actually trunk to 8.5) hangs if the next command is

apply (isweqfibtototal _ _ (fun pointover: forall x:X, P x => weqfunextsec _ (fun x : X => f x (pointover x)) s ) ).

and no -no-sharing option is turned on. It also hangs on

exact (isweqfibtototal (fun pointover : forall x : X, P x =>
                forall x : X, paths (f x (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
                paths (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => weqfunextsec Q (fun x : X => f x (pointover x)) s ) ).

for at least 2hrs. After adding "Opaque funextsec ." the "exact" commend goes through in <1sec and so does the "apply". If "Transparent funextsec." added after the "apply" the compilation hangs on "Define".

Resoved (2014.10.23). *)

apply (isweqfibtototal _ _ (fun pointover: forall x:X, P x => weqfunextsec _ (fun x : X => f x (pointover x)) s ) ).
apply (twooutof3c map2inv map1inv is2 is1). Defined.


Definition weqforalltohfiber  { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x) := weqpair _ ( isweqforalltohfiber P Q f s ) .



(** *** The weak equivalence  between section spaces (dependent products) defined by a family of weak equivalences  [ weq ( P x ) ( Q x ) ] *)




Corollary isweqmaponsec { X : UU } (P Q : X-> UU) (f: forall x:X, weq ( P x ) ( Q x) ) : isweq (maponsec _ _ f).
Proof. intros. unfold isweq.  intro y.
assert (is1: iscontr (forall x:X, hfiber  (f x) (y x))). assert (is2: forall x:X, iscontr (hfiber  (f x) (y x))). intro x. apply ( ( pr2 ( f x ) )  (y x)). apply funcontr. assumption.
apply (iscontrweqb  (weqhfibertoforall P Q f y) is1 ). Defined.

Definition weqonsecfibers { X : UU } (P Q : X-> UU) (f: forall x:X, weq ( P x ) ( Q x )) := weqpair _ ( isweqmaponsec P Q f ) .


(** *** Composition of functions with a weak equivalence on the right *)

Definition  weqffun ( X : UU ) { Y Z : UU } ( w : weq Y Z ) : weq ( X -> Y ) ( X -> Z ) := weqonsecfibers _ _ ( fun x : X => w ) .








(** ** The map between section spaces (dependent products) defined by the map between the bases [ f: Y -> X ] *)


(** *** General case *)


Definition maponsec1l0 { X : UU } (P:X -> UU)(f:X-> X)(h: forall x:X, paths (f x) x)(s: forall x:X, P x): (forall x:X, P x) := (fun x:X => transportf P  (h x) (s (f x))).

Lemma maponsec1l1  { X : UU } (P:X -> UU)(x:X)(s:forall x:X, P x): paths (maponsec1l0 P (fun x:X => x) (fun x:X => idpath x) s x) (s x).
Proof. intros. unfold maponsec1l0.   apply idpath. Defined.


Lemma maponsec1l2 { X : UU } (P:X -> UU)(f:X-> X)(h: forall x:X, paths (f x) x)(s: forall x:X, P x)(x:X): paths (maponsec1l0 P f h s x) (s x).
Proof. intros.

set (map:= fun ff: total2 (fun f0:X->X => forall x:X, paths (f0 x) x) => maponsec1l0 P (pr1  ff) (pr2  ff) s x).
assert (is1: iscontr (total2 (fun f0:X->X => forall x:X, paths (f0 x) x))). apply funextweql1. assert (e: paths (tpair  (fun f0:X->X => forall x:X, paths (f0 x) x) f h) (tpair  (fun f0:X->X => forall x:X, paths (f0 x) x) (fun x0:X => x0) (fun x0:X => idpath x0))). apply proofirrelevancecontr.  assumption.  apply (maponpaths map  e). Defined.


Theorem isweqmaponsec1 { X Y : UU } (P:Y -> UU)(f: weq X Y ) : isweq (maponsec1 P f).
Proof. intros.

set (map:= maponsec1  P f).
set (invf:= invmap f). set (e1:= homotweqinvweq f). set (e2:= homotinvweqweq f ).
set (im1:= fun sx: forall x:X, P (f x) => (fun y:Y => sx (invf y))).
set (im2:= fun sy': forall y:Y, P (f (invf y)) => (fun y:Y => transportf _ (homotweqinvweq f y) (sy' y))).
set (invmapp := (fun sx: forall x:X, P (f x) => im2 (im1 sx))).

assert (efg0: forall sx: (forall x:X, P (f x)), forall x:X, paths ((map (invmapp sx)) x) (sx x)).  intro. intro. unfold map. unfold invmapp. unfold im1. unfold im2. unfold maponsec1.  simpl. fold invf.  set (ee:=e2 x).  fold invf in ee.

set (e3x:= fun x0:X => invmaponpathsweq f (invf (f x0)) x0 (homotweqinvweq f (f x0))). set (e3:=e3x x). assert (e4: paths (homotweqinvweq f (f x)) (maponpaths f  e3)). apply (pathsinv0  (pathsweq4  f (invf (f x)) x _)).

assert  (e5:paths (transportf P  (homotweqinvweq f (f x)) (sx (invf (f x)))) (transportf P  (maponpaths f  e3) (sx (invf (f x))))). apply (maponpaths (fun e40:_ => (transportf P e40 (sx (invf (f x)))))  e4).

assert (e6: paths (transportf P (maponpaths f e3) (sx (invf (f x)))) (transportf (fun x:X => P (f x))  e3 (sx (invf (f x))))). apply (pathsinv0 (functtransportf  f P  e3 (sx (invf (f x))))).

set (ff:= fun x:X => invf (f x)).
assert (e7: paths (transportf (fun x : X => P (f x)) e3 (sx (invf (f x)))) (sx x)). apply (maponsec1l2 (fun x:X => P (f x)) ff e3x sx x).  apply (pathscomp0   (pathscomp0   e5 e6) e7).

assert (efg: forall sx: (forall x:X, P (f x)), paths  (map (invmapp sx)) sx). intro. apply (funextsec _ _ _ (efg0 sx)).

assert (egf0: forall sy: (forall y:Y, P y), forall y:Y, paths ((invmapp (map sy)) y) (sy y)). intros. unfold invmapp. unfold map.  unfold im1. unfold im2. unfold maponsec1.

set (ff:= fun y:Y => f (invf y)). fold invf. apply (maponsec1l2 P ff ( homotweqinvweq f ) sy y).
assert (egf: forall sy: (forall y:Y, P y), paths  (invmapp (map sy)) sy). intro. apply (funextsec _ _ _ (egf0 sy)).

apply (gradth  map invmapp egf efg). Defined.

Definition weqonsecbase { X Y : UU } ( P : Y -> UU ) ( f : weq X Y )
  : weq (forall y : Y, P y) (forall x : X, P (f x))
  := weqpair _ ( isweqmaponsec1 P f ) .


(** *** Composition of functions with a weak equivalence on the left *)


Definition  weqbfun  { X Y : UU } ( Z : UU ) ( w : weq X Y ) : weq ( Y -> Z ) ( X -> Z ) := weqonsecbase _ w .



















(** ** Sections of families over an empty type and over coproducts *)

(** *** General case *)

Definition iscontrsecoverempty ( P : empty -> UU ) : iscontr ( forall x : empty , P x ) .
Proof . intro . split with ( fun x : empty => fromempty x )  .  intro t .  apply funextsec .  intro t0 . induction t0 . Defined .

Definition iscontrsecoverempty2 { X : UU } ( P : X -> UU ) ( is : neg X ) : iscontr ( forall x : X , P x ) .
Proof . intros .  set ( w := weqtoempty is ) . set ( w' := weqonsecbase P ( invweq w ) ) .   apply ( iscontrweqb w' ( iscontrsecoverempty _ ) ) . Defined .

Definition secovercoprodtoprod { X Y : UU } ( P : coprod X Y -> UU ) ( a: forall xy : coprod X Y , P xy ) : dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) := dirprodpair ( fun x : X => a ( ii1 x ) ) ( fun y : Y => a ( ii2 y ) )  .

Definition prodtosecovercoprod { X Y : UU } ( P : coprod X Y -> UU ) ( a : dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) ) :  forall xy : coprod X Y , P xy .
Proof . intros . induction xy as [ x | y ] . apply ( pr1 a x ) .    apply ( pr2 a y ) . Defined .


Definition weqsecovercoprodtoprod { X Y : UU } ( P : coprod X Y -> UU ) : weq ( forall xy : coprod X Y , P xy ) ( dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) ) .
Proof . intros . set ( f := secovercoprodtoprod P ) .  set ( g := prodtosecovercoprod P ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro t .  induction t as [ x | y ] .  apply idpath . apply idpath .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro .  induction a as [ ax ay ] . apply ( pathsdirprod ) .  apply funextsec . intro x . apply idpath .  apply funextsec . intro y . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .



(** *** Functions from the empty type *)

Theorem iscontrfunfromempty ( X : UU ) : iscontr ( empty -> X ) .
Proof . intro . split with fromempty . intro t .  apply funextfun .  intro x . induction x . Defined .

Theorem iscontrfunfromempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : iscontr ( Y -> X ) .
Proof. intros . set ( w := weqtoempty is ) . set ( w' := weqbfun X ( invweq w ) ) .  apply ( iscontrweqb w' ( iscontrfunfromempty X ) ) . Defined .



(** *** Functions from a coproduct *)

Definition funfromcoprodtoprod { X Y Z : UU } ( f : coprod X Y -> Z ) : dirprod ( X -> Z ) ( Y -> Z ) := dirprodpair ( fun x : X => f ( ii1 x ) ) ( fun y : Y => f ( ii2 y ) ) .

Definition prodtofunfromcoprod { X Y Z : UU } ( fg : dirprod ( X -> Z ) ( Y -> Z ) ) : coprod X Y -> Z := match fg with tpair _ f g => sumofmaps f g end .

Theorem weqfunfromcoprodtoprod ( X Y Z : UU ) : weq ( coprod X Y -> Z ) ( dirprod ( X -> Z ) ( Y -> Z ) ) .
Proof. intros . set ( f := @funfromcoprodtoprod X Y Z ) . set ( g := @prodtofunfromcoprod X Y Z ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) .  intro a . apply funextfun .   intro xy .  induction xy as [ x | y ] .  apply idpath . apply idpath .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . induction a as [ fx fy ] . simpl . apply pathsdirprod .  simpl . apply pathsinv0 . apply etacorrection . simpl . apply pathsinv0 . apply etacorrection .
apply ( gradth _ _ egf efg ) . Defined .
















(** ** Sections of families over contractible types and over [ total2 ] (over dependent sums) *)



(** *** General case *)


Definition tosecoverunit ( P : unit -> UU ) ( p : P tt ) : forall t : unit , P t .
Proof . intros . induction t . apply p . Defined .

Definition weqsecoverunit ( P : unit -> UU ) : weq ( forall t : unit , P t ) ( P tt ) .
Proof . intro. set ( f := fun a : forall t : unit , P t => a tt ) . set ( g := tosecoverunit P ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro t . induction t . apply idpath .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intros . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .


Definition weqsecovercontr { X : UU } ( P : X -> UU ) ( is : iscontr X ) : weq ( forall x : X , P x ) ( P ( pr1 is ) ) .
Proof . intros . set ( w1 := weqonsecbase P ( wequnittocontr is ) ) . apply ( weqcomp w1 ( weqsecoverunit _ ) ) .  Defined .

Definition tosecovertotal2 { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) ( a : forall x : X , forall p : P x , Q ( tpair _ x p ) ) : forall xp : total2 P , Q xp .
Proof . intros . induction xp as [ x p ] . apply ( a x p ) . Defined .


Definition weqsecovertotal2 { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : weq ( forall xp : total2 P , Q xp ) ( forall x : X , forall p : P x , Q ( tpair _ x p ) ) .
Proof . intros . set  ( f := fun a : forall xp : total2 P , Q xp => fun x : X => fun p : P x => a ( tpair _ x p ) ) . set ( g := tosecovertotal2 P Q ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro xp . induction xp as [ x p ] . apply idpath .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro . apply funextsec . intro x . apply funextsec . intro p . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .


(** *** Functions from [ unit ] and from contractible types *)


Definition weqfunfromunit ( X : UU ) : weq ( unit -> X ) X := weqsecoverunit _ .

Definition  weqfunfromcontr { X : UU } ( Y : UU ) ( is : iscontr X ) : weq ( X -> Y ) Y := weqsecovercontr _ is .


(** *** Functions from [ total2 ] *)

Definition weqfunfromtotal2 { X : UU } ( P : X -> UU ) ( Y : UU ) : weq ( total2 P -> Y ) ( forall x : X , P x -> Y ) := weqsecovertotal2 P _ .

(** *** Functions from direct product *)

Definition weqfunfromdirprod ( X X' Y : UU ) : weq ( dirprod X X' -> Y ) ( forall x : X , X' -> Y ) := weqsecovertotal2 _ _ .
















(** ** Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

(** *** General case *)

Theorem impred (n:nat) { T : UU } (P:T -> UU): (forall t:T, isofhlevel n (P t)) -> (isofhlevel n (forall t:T, P t)).
Proof. intro. induction n as [ | n IHn ] . intros T P X.  apply (funcontr P X). intros T P X. unfold isofhlevel in X.  unfold isofhlevel. intros x x' .

assert (is: forall t:T, isofhlevel n (paths (x t) (x' t))).  intro. apply (X t (x t) (x' t)).
assert (is2: isofhlevel n (forall t:T, paths (x t) (x' t))). apply (IHn _ (fun t0:T => paths (x t0) (x' t0)) is).
set (u:=toforallpaths P x x').  assert (is3:isweq u). apply isweqtoforallpaths.  set (v:= invmap ( weqpair u is3) ). assert (is4: isweq v). apply isweqinvmap. apply (isofhlevelweqf n  ( weqpair v is4 )). assumption. Defined.

Corollary impred_iscontr { T : UU } (P:T -> UU): (forall t:T, iscontr (P t)) -> (iscontr (forall t:T, P t)).
Proof. intros. apply (impred 0). assumption. Defined.

Corollary impred_isaprop { T : UU } (P:T -> UU): (forall t:T, isaprop (P t)) -> (isaprop (forall t:T, P t)).
Proof. apply impred. Defined.

Corollary impred_isaset { T : UU } (P:T -> UU): (forall t:T, isaset (P t)) -> (isaset (forall t:T, P t)).
Proof. intros. apply (impred 2). assumption. Defined.

Corollary impredtwice  (n:nat) { T T' : UU } (P:T -> T' -> UU): (forall (t:T)(t':T'), isofhlevel n (P t t')) -> (isofhlevel n (forall (t:T)(t':T'), P t t')).
Proof.  intros n T T' P X. assert (is1: forall t:T, isofhlevel n (forall t':T', P t t')). intro. apply (impred n _ (X t)). apply (impred n _ is1). Defined.


Corollary impredfun (n:nat)(X Y:UU)(is: isofhlevel n Y) : isofhlevel n (X -> Y).
Proof. intros. apply (impred n (fun x:_ => Y) (fun x:X => is)). Defined.


Theorem impredtech1 (n:nat)(X Y: UU) : (X -> isofhlevel n Y) -> isofhlevel n (X -> Y).
Proof. intro. induction n as [ | n IHn ] . intros X Y X0. simpl. split with (fun x:X => pr1  (X0 x)).  intro t .
assert (s1: forall x:X, paths (t x) (pr1  (X0 x))). intro. apply proofirrelevancecontr. apply (X0 x).
apply funextsec. assumption.

intros X Y X0. simpl. assert (X1: X -> isofhlevel (S n) (X -> Y)). intro X1 . apply impred. assumption. intros x x' .
assert (s1: isofhlevel n (forall xx:X, paths (x xx) (x' xx))). apply impred. intro t . apply (X0 t).
assert (w: weq (forall xx:X, paths (x xx) (x' xx)) (paths x x')). apply (weqfunextsec  _ x x' ). apply (isofhlevelweqf n w s1). Defined.



(** ***  Functions to a contractible type *)

Theorem iscontrfuntounit ( X : UU ) : iscontr ( X -> unit ) .
Proof . intro . split with ( fun x : X => tt ) . intro f .   apply funextfun . intro x . induction ( f x ) .  apply idpath . Defined .

Theorem iscontrfuntocontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : iscontr ( X -> Y ) .
Proof . intros . set ( w := weqcontrtounit is ) .   set ( w' := weqffun X w ) .  apply ( iscontrweqb w' ( iscontrfuntounit X ) ) . Defined .


(** *** Functions to a proposition *)

Lemma isapropimpl ( X Y : UU ) ( isy : isaprop Y ) : isaprop ( X -> Y ) .
Proof. intros. apply impred. intro.   assumption.  Defined.



(** *** Functions to an empty type (generalization of [ isapropneg ]) *)


Theorem isapropneg2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( X -> Y ) .
Proof . intros .  apply impred . intro . apply ( isapropifnegtrue  is ) . Defined .





(** ** Theorems saying that  [ iscontr T ], [ isweq f ] etc. are of h-level 1 *)



Theorem iscontriscontr { X : UU } ( is : iscontr X ) : iscontr ( iscontr X ).
Proof. intros X X0 .

assert (is0: forall (x x':X), paths x x'). apply proofirrelevancecontr. assumption.

assert (is1: forall cntr:X, iscontr (forall x:X, paths x cntr)). intro.
assert (is2: forall x:X, iscontr (paths x cntr)).
assert (is2: isaprop X). apply isapropifcontr. assumption.
unfold isaprop in is2. unfold isofhlevel in is2. intro x . apply (is2 x cntr).
apply funcontr. assumption.

set (f:= @pr1 X (fun cntr:X => forall x:X, paths x cntr)).
assert (X1:isweq f).  apply isweqpr1. assumption. change (total2 (fun cntr : X => forall x : X, paths x cntr)) with (iscontr X) in X1.  apply (iscontrweqb ( weqpair f X1 ) ) . assumption.  Defined.



Theorem isapropiscontr (T:UU): isaprop (iscontr T).
Proof. intros.  unfold isaprop.  unfold isofhlevel. intros x x' . assert (is: iscontr(iscontr T)). apply iscontriscontr. apply x. assert (is2: isaprop (iscontr T)). apply ( isapropifcontr is  ) . apply (is2 x x'). Defined.


Theorem isapropisweq { X Y : UU } (f:X-> Y) : isaprop (isweq f).
Proof. intros. unfold isweq.  apply (impred (S O) (fun y:Y => iscontr (hfiber f y)) (fun y:Y => isapropiscontr (hfiber  f y))).  Defined.


Theorem isapropisisolated ( X : UU ) ( x : X ) : isaprop ( isisolated X x ) .
Proof. intros . apply isofhlevelsn .  intro is . apply impred . intro x' .  apply ( isapropdec _ ( isaproppathsfromisolated X x is x' ) ) .  Defined .

Theorem isapropisdeceq (X:UU): isaprop (isdeceq X).
Proof. intro. apply ( isofhlevelsn 0 ) .  intro is . unfold isdeceq. apply impred . intro x .  apply ( isapropisisolated X x ) .   Defined .

Theorem isapropisofhlevel (n:nat)(X:UU): isaprop (isofhlevel n X).
Proof. intro.  unfold isofhlevel.    induction n as [ | n IHn ] . apply isapropiscontr.  intro X .
assert (X0: forall (x x':X), isaprop  ((fix isofhlevel (n0 : nat) (X0 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X0
         | S m => forall x0 x'0 : X0, isofhlevel m (paths x0 x'0)
         end) n (paths x x'))). intros. apply (IHn (paths x x')).
assert (is1:
     (forall x:X, isaprop (forall  x' : X,
      (fix isofhlevel (n0 : nat) (X1 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X1
         | S m => forall x0 x'0 : X1, isofhlevel m (paths x0 x'0)
         end) n (paths x x')))). intro.  apply (impred ( S O ) _  (X0 x)). apply (impred (S O) _ is1). Defined.

Corollary isapropisaprop (X:UU) : isaprop (isaprop X).
Proof. intro. apply (isapropisofhlevel (S O)). Defined.

Definition isapropisdecprop ( X : UU ) : isaprop ( isdecprop X ).
Proof.
  intros.
  unfold isdecprop.
  apply (isofhlevelweqf 1 (weqdirprodcomm _ _)).
  apply isofhleveltotal2.
  - apply isapropisaprop.
  - intro i. now apply isapropdec.
Defined.

Corollary isapropisaset (X:UU): isaprop (isaset X).
Proof. intro. apply (isapropisofhlevel (S (S O))). Defined.


Theorem isapropisofhlevelf ( n : nat ) { X Y : UU } ( f : X -> Y ) : isaprop ( isofhlevelf n f ) .
Proof . intros . unfold isofhlevelf .    apply impred . intro y . apply isapropisofhlevel .  Defined .

Definition isapropisincl { X Y : UU } ( f : X -> Y ) := isapropisofhlevelf 1 f .

Lemma isaprop_isInjective { X Y : UU } (f:X -> Y): isaprop (isInjective f).
Proof.
  intros.
  unfold isInjective.
  apply impred; intro.
  apply impred; intro.
  apply isapropisweq.
Defined.

Lemma incl_injectivity { X Y : UU } (f:X -> Y): isincl f ≃ isInjective f.
Proof.
  intros.
  apply weqimplimpl.
  - apply isweqonpathsincl.
  - apply isinclweqonpaths.
  - apply isapropisincl.
  - apply isaprop_isInjective.
Defined.

(** ** Theorems saying that various [ pr1 ] maps are inclusions *)


Theorem isinclpr1weq ( X Y : UU ) : isincl ( pr1weq : X≃Y -> X->Y ) .
Proof. intros . refine (isinclpr1 _ _) . intro f.   apply isapropisweq .  Defined .

Corollary isinjpr1weq ( X Y : UU ) : isInjective ( pr1weq : X≃Y -> X->Y ) .
Proof. intros. apply isweqonpathsincl. apply isinclpr1weq. Defined.

Theorem isinclpr1isolated ( T : UU ) : isincl ( pr1isolated T ) .
Proof . intro . apply ( isinclpr1 _ ( fun t : T => isapropisisolated T t ) ) . Defined .

(** associativity of weqcomp **)

Definition weqcomp_assoc {W X Y Z : UU} (f:W≃X) (g:X≃Y) (h:Y≃Z) : (h∘(g∘f) = (h∘g)∘f) %weq.
Proof. intros. apply subtypeEquality. { intros p. apply isapropisweq. } simpl. reflexivity.
Defined.

(** ** Various weak equivalences between spaces of weak equivalences *)

(** *** Composition with a weak quivalence is a weak equivalence on weak equivalences *)

Theorem weqfweq ( X : UU ) { Y Z : UU } ( w : weq Y Z ) : weq ( weq X Y ) ( weq X Z ) .
Proof. intros . set ( f := fun a : weq X Y => weqcomp a w ) . set ( g := fun b : weq X Z  => weqcomp b ( invweq w ) ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun .  intro x .  apply ( homotinvweqweq w ( a x ) ) .
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x . apply ( homotweqinvweq w ( b x ) ) .
apply ( gradth _ _ egf efg ) . Defined .

Theorem weqbweq  { X Y : UU } ( Z : UU ) ( w : weq X Y ) : weq ( weq Y Z ) ( weq X Z ) .
Proof. intros . set ( f := fun a : weq Y Z =>  weqcomp w a ) . set ( g := fun b : weq X Z  => weqcomp ( invweq w ) b ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun .  intro y .  apply ( maponpaths a ( homotweqinvweq w y ) ) .
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x . apply ( maponpaths b ( homotinvweqweq w x ) ) .
apply ( gradth _ _ egf efg ) . Defined .

Theorem weqweq {X Y:UU} (w:X≃Y) : (X≃X) ≃ (Y≃Y).
Proof.
  intros. intermediate_weq (X≃Y).
  - now apply weqfweq.
  - apply invweq. now apply weqbweq.
Defined.

(** *** Invertion on weak equivalences as a weak equivalence *)

(** Comment : note that full form of [ funextfun ] is only used in the proof of this theorem in the form of [ isapropisweq ]. The rest of the proof can be completed using eta-conversion . *)

Theorem weqinvweq ( X Y : UU ) : weq ( weq X Y ) ( weq Y X ) .
Proof . intros . set ( f := fun w : weq X Y => invweq w ) . set ( g := fun w : weq Y X => invweq w ) . split with f .
assert ( egf : forall w : _ , paths ( g ( f w ) ) w ) . intro . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x .   unfold f.  unfold g . unfold invweq . simpl . unfold invmap . simpl . apply idpath .
assert ( efg : forall w : _ , paths ( f ( g w ) ) w ) . intro . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x .   unfold f.  unfold g . unfold invweq . simpl . unfold invmap . simpl . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .



(** ** h-levels of spaces of weak equivalences *)


(** *** Weak equivalences to and from types of h-level ( S n ) *)

Theorem isofhlevelsnweqtohlevelsn ( n : nat ) ( X Y : UU ) ( is : isofhlevel ( S n ) Y ) : isofhlevel ( S n ) ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsninclb n _ ( isinclpr1weq _ _ ) ) .  apply impred . intro .  apply is .  Defined .

Theorem isofhlevelsnweqfromhlevelsn ( n : nat ) ( X Y : UU ) ( is : isofhlevel ( S n ) Y ) : isofhlevel ( S n ) ( weq Y X ) .
Proof. intros .  apply ( isofhlevelweqf ( S n ) ( weqinvweq X Y ) ( isofhlevelsnweqtohlevelsn n X Y is ) ) .  Defined .




(** *** Weak equivalences to and from contractible types *)

Theorem isapropweqtocontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : isaprop ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropifcontr is ) ) . Defined .

Theorem isapropweqfromcontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropifcontr is ) ) . Defined .


(** *** Weak equivalences to and from propositions *)


Theorem isapropweqtoprop ( X  Y : UU ) ( is : isaprop Y ) : isaprop ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ is ) . Defined .

Theorem isapropweqfromprop ( X Y : UU )( is : isaprop Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ is ) . Defined .


(** *** Weak equivalences to and from sets *)

Theorem isasetweqtoset ( X  Y : UU ) ( is : isaset Y ) : isaset ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 1 _ _ is ) . Defined .

Theorem isasetweqfromset ( X Y : UU )( is : isaset Y ) : isaset ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 1 X _ is ) . Defined .



(** *** Weak equivalences to an empty type *)

Theorem isapropweqtoempty  ( X : UU ) : isaprop ( weq X empty ) .
Proof . intro . apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropempty ) ) . Defined .


Theorem isapropweqtoempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( weq X Y ) .
Proof. intros . apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropifnegtrue is ) ) . Defined .


(** *** Weak equivalences from an empty type *)

Theorem isapropweqfromempty ( X : UU ) : isaprop ( weq empty X ) .
Proof . intro . apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropempty ) ) . Defined .

Theorem isapropweqfromempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropifnegtrue is ) ) .  Defined .

(** *** Weak equivalences to and from [ unit ] *)

Theorem isapropweqtounit ( X : UU ) : isaprop ( weq X unit ) .
Proof . intro .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropunit ) ) . Defined .

Theorem isapropweqfromunit ( X : UU ) : isaprop ( weq unit X ) .
Proof. intros . apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropunit ) ) .  Defined .

(** ** Weak auto-equivalences of a type with an isolated point *)

Definition cutonweq {T:UU} t (is:isisolated T t) (w : T ≃ T ) :
  isolated T × (compl T t ≃ compl T t).
Proof.
  intros. split.
  - exists (w t). now apply isisolatedweqf.
  - intermediate_weq (compl T (w t)).
    + apply weqoncompl.
    + apply weqtranspos0.
      * now apply isisolatedweqf.
      * assumption.
Defined.

Definition invcutonweq  { T : UU } ( t : T )
           ( is : isisolated T t )
           ( t'w : isolated T × ( compl T t ≃ compl T t ) ) : T ≃ T
  := weqcomp ( weqrecomplf t t is is ( pr2 t'w ) )
             ( weqtranspos t ( pr1 ( pr1 t'w ) ) is ( pr2 ( pr1 t'w ) ) ) .

Lemma pathsinvcuntonweqoft  { T : UU } ( t : T )
      ( is : isisolated T t )
      ( t'w : isolated T × ( compl T t ≃ compl T t ) ) :
  invcutonweq t is t'w t = pr1 ( pr1 t'w ) .
Proof. intros . unfold invcutonweq . simpl . unfold recompl . unfold coprodf .
       unfold invmap .    simpl .  unfold invrecompl .
       induction ( is t ) as [ ett | nett ] .
       - apply pathsfuntransposoft1 .
       - induction ( nett ( idpath _ ) ) .
Defined .

Definition weqcutonweq (T:UU) (t:T) (is:isisolated T t) : (T ≃ T) ≃ isolated T × (compl T t ≃ compl T t) .
Proof.
  intros. set (f := cutonweq t is). set (g := invcutonweq t is). apply (weqgradth f g).
  {
    intro w. Set Printing Coercions. idtac.
    apply (invmaponpathsincl _ (isinclpr1weq _ _)).
    apply funextfun; intro t'. simpl.
    unfold invmap; simpl. unfold coprodf, invrecompl.
    induction (is t') as [ ett' | nett' ].
    { simpl. rewrite (pathsinv0 ett'). apply pathsfuntransposoft1. }
    unfold funtranspos0; simpl.
    induction (is (w t)) as [ etwt | netwt ].
    { induction (is (w t')) as [ etwt' | netwt' ].
      { induction (negf (invmaponpathsincl w (isofhlevelfweq 1 w) t t') nett' (pathscomp0 (pathsinv0 etwt) etwt')). }
      simpl. assert (newtt'' := netwt'). rewrite etwt in netwt'.
      apply (pathsfuntransposofnet1t2 t (w t) is _ (w t') newtt'' netwt').
    }
    simpl. induction (is (w t')) as [ etwt' | netwt' ].
    { simpl. rewrite (pathsinv0 etwt'). apply (pathsfuntransposoft2 t (w t) is _). }
    simpl. assert (ne:neg (paths (w t) (w t'))).
    { apply (negf (invmaponpathsweq w _ _) nett'). }
    apply (pathsfuntransposofnet1t2 t (w t) is _  (w t') netwt' ne). }
  { intro xw. induction xw as [ x w ]. induction x as [ t' is' ].
    simpl in w. apply pathsdirprod.
    { apply (invmaponpathsincl _ (isinclpr1isolated _)).
      simpl. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
      induction (is t) as [ ett | nett ].
      { apply pathsfuntransposoft1. }
      induction (nett (idpath _)).
    }
    simpl.
    apply (invmaponpathsincl _ (isinclpr1weq _ _) _ _). apply funextfun.
    intro x. induction x as [ x netx ].
    unfold g, invcutonweq; simpl.
    set (int := funtranspos (tpair _ t is) (tpair _ t' is') (recompl T t (coprodf w (fun x0:unit => x0) (invmap (weqrecompl T t is) t)))).
    assert (eee:paths int t').
    { unfold int. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
      induction (is t) as [ ett | nett ].
      { apply (pathsfuntransposoft1). }
      induction (nett (idpath _)).
    }
    assert (isint:isisolated _ int).
    { rewrite eee. apply is'. }
    apply (ishomotinclrecomplf _ _ isint (funtranspos0 _ _ _) _ _).
    simpl.
    change (recomplf int t isint (funtranspos0 int t is)) with (funtranspos (tpair _ int isint) (tpair _ t is)).
    assert (ee:paths (tpair _ int isint) (tpair _ t' is')).
    { apply (invmaponpathsincl _ (isinclpr1isolated _) _ _).
      simpl.
      apply eee. }
    rewrite ee.
    set (e := homottranspost2t1t1t2 t t' is is' (recompl T t (coprodf w (fun x0:unit => x0) (invmap (weqrecompl T t is) x)))).
    unfold funcomp,idfun in e.
    rewrite e. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
    induction (is x) as [ etx | netx' ].
    { induction (netx etx). }
    apply (maponpaths (@pr1 _ _)). apply (maponpaths w).
    apply (invmaponpathsincl _ (isinclpr1compl _ _) _ _).
    simpl. apply idpath. }
  Unset Printing Coercions.
Defined.

(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y


Definition locsplit (X:UU)(Y:UU)(f:X -> Y):= forall y:Y, coprod (hfiber  f y) (hfiber  f y -> empty).

Definition dnegimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber  f y)).
Definition dnegimageincl (X Y:UU)(f:X -> Y):= pr1 Y (fun y:Y => dneg(hfiber  f y)).

Definition xtodnegimage (X:UU)(Y:UU)(f:X -> Y): X -> dnegimage  f:= fun x:X => tpair  (f x) ((todneg _) (hfiberpair  f (f x) x (idpath (f x)))).

Definition locsplitsec (X:UU)(Y:UU)(f:X->Y)(ls: locsplit  f): dnegimage  f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with
ii1 z => pr1  z|
ii2 phi => fromempty  (psi phi)
end
end.

Definition locsplitsecissec  (X Y:UU)(f:X->Y)(ls: locsplit  f)(u:dnegimage  f): paths (xtodnegimage  f (locsplitsec  f ls u)) u.
Proof. intros.  set (p:= xtodnegimage  f). set (s:= locsplitsec  f ls).
assert (paths (pr1  (p (s u))) (pr1  u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst.  simpl. apply (pr2  x0). induction (x y).
assert (is: isofhlevelf (S O)  (dnegimageincl  f)). apply (isofhlevelfpr1 (S O)  (fun y:Y => isapropdneg (hfiber  f y))).
assert (isw: isweq (maponpaths (dnegimageincl  f) (p (s u)) u)). apply (isofhlevelfonpaths O   _ is).
apply (invmap  _ isw X0). Defined.



Definition negimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber  f y)).
Definition negimageincl (X Y:UU)(f:X -> Y):= pr1 Y (fun y:Y => neg(hfiber  f y)).


Definition imsum (X:UU)(Y:UU)(f:X -> Y): coprod (dnegimage  f) (negimage  f) -> Y:= fun u:_ =>
match u with
ii1 z => pr1  z|
ii2 z => pr1  z
end.

 *)



(* End of the file uu0d.v *)
