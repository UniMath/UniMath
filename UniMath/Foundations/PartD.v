(** * Univalent Foundations. Vladimir Voevodsky. Feb. 2010 - Sep. 2011.
  Port to coq trunk (8.4-8.5) in March 2014. The third part of the original
  uu0 file, created on Dec. 3, 2014.

Only one universe is used and never as a type.

*)

(** ** Contents
- Sections of "double fibration" [(P : T -> UU) (PP : ∏ t : T, P t -> UU)] and
  pairs of sections
 - General case
 - Functions on dependent sum (to a [total2])
 - Functions to direct product
- Homotopy fibers of the map [∏ x : X, P x -> ∏ x : X, Q x]
 - General case
 - The weak equivalence between sections spaces (dependent products) defined
   by a family of weak equivalences [(P x) ≃ (Q x)]
 - Composition of functions with a weak equaivalence on the right
- The map between section spaces (dependent products) defined by the map
  between the bases [ f : Y -> X ]
 - General case
 - Composition of functions with a weak equivalence on the left
- Sections of families over an empty type and over coproducts
 - General case
 - Functions from the empty type
 - Functions from a coproduct
- Sections of families over contractible types and over [ total2 ]
  (over dependent sums)
 - General case
 - Functions from [unit] and from contractible types
 - Functions from [total2]
 - Functiosn from direct product
- Theorem saying that if each member of a family is of h-level n then the
  space of sections of the family is of h-level n.
 - General case
 - Functions to a contractible type
 - Functions to a proposition
 - Functions to an empty type (generalization of [isapropneg])
- Theorems saying that  [ iscontr T ], [ isweq f ] etc. are of h-level 1
- Theorems saying that various [ pr1 ] maps are inclusions
- Various weak equivalences between spaces of weak equivalences
 - Composition with a weak equivalence is a weak equivalence on weak
   equivalences
 - Invertion on weak equivalences as a weak equivalence
- h-levels of spaces of weak equivalences
 - Weak equivalences to and from types of h-level (S n)
 - Weak equivalences to and from contractible types
 - Weak equivalences to and from propositions
 - Weak equivalences to and from sets
 - Weak equivalences to an empty type
 - Weak equivalences from an empty type
 - Weak equivalences to and from [unit]
- Weak auto-equivalences of a type with an isolated point
*)

(** ** Preamble *)

(** Settings *)

(* The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

(** Imports *)

Require Export UniMath.Foundations.PartC.

(** ** Sections of "double fibration" [(P : T -> UU) (PP : ∏ t : T, P t -> UU)] and pairs of sections *)



(** *** General case *)

Definition totaltoforall {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU) :
  total2 (fun s0 : ∏ x : X, P x
          => ∏ x : X, PP x (s0 x)) -> ∏ x : X, total2 (PP x).
Proof.
  intros X P PP X0 x.
  exists (pr1 X0 x).
  apply (pr2 X0 x).
Defined.


Definition foralltototal {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU) :
  (∏ x : X, total2 (PP x))
  -> total2 (fun s0 : ∏ x : X, P x => ∏ x : X, PP x (s0 x)).
Proof.
  intros X P PP X0.
  exists (λ x : X, pr1 (X0 x)).
  apply (λ x : X, pr2 (X0 x)).
Defined.

Theorem isweqforalltototal {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU) :
  isweq (foralltototal P PP).
Proof.
  intros.
  simple refine (gradth (foralltototal P PP) (totaltoforall P PP) _ _).
  - apply idpath.
  - apply idpath.
Defined.

Theorem isweqtotaltoforall {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU) :
  isweq (totaltoforall P PP).
Proof.
  intros.
  simple refine (gradth (totaltoforall P PP) (foralltototal P PP) _ _).
  - apply idpath.
  - apply idpath.
Defined.

Definition weqforalltototal {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU)
  := weqpair _ (isweqforalltototal P PP).

Definition weqtotaltoforall {X : UU} (P : X -> UU) (PP : ∏ x : X, P x -> UU)
  := invweq (weqforalltototal P PP).



(** *** Functions to a dependent sum (to a [ total2 ]) *)

Definition weqfuntototaltototal (X : UU) {Y : UU} (Q : Y -> UU) :
  weq (X -> total2 Q) (total2 (fun f : X -> Y => ∏ x : X, Q (f x)))
  := weqforalltototal (λ x : X, Y) (λ x : X, Q).


(** *** Functions to direct product *)

(** Note: we give direct proofs for this special case. *)


Definition funtoprodtoprod {X Y Z : UU} (f : X -> dirprod Y Z) :
  (X -> Y) × (X -> Z)
  := dirprodpair (λ x : X, pr1 (f x)) (λ x : X, (pr2 (f x))).

Definition prodtofuntoprod {X Y Z : UU} (fg : (X -> Y) × (X -> Z))
  : X -> dirprod Y Z
  := match fg with tpair _ f g => λ x : X, dirprodpair (f x) (g x) end.

Theorem weqfuntoprodtoprod (X Y Z : UU) :
  weq (X -> dirprod Y Z) ((X -> Y) × (X -> Z)).
Proof.
  intros.
  simple refine (weqpair _ (gradth (@funtoprodtoprod X Y Z)
                                   (@prodtofuntoprod X Y Z) _ _)).
  - intro a. apply funextfun. intro x. apply idpath.
  - intro a. induction a as [ fy fz ]. apply idpath.
Defined.

(** ** Homotopy fibers of the map [∏ x : X, P x -> ∏ x : X, Q x] *)

(** *** General case *)

Definition maponsec {X : UU}  (P Q : X -> UU) (f : ∏ x : X, P x -> Q x) :
  (∏ x : X, P x) -> (∏ x : X, Q x)
  := fun s : ∏ x : X, P x => (λ x : X, (f x) (s x)).

Definition maponsec1 {X Y : UU} (P : Y -> UU) (f : X -> Y) :
  (∏ y : Y, P y) -> (∏ x : X, P (f x))
  := fun sy : ∏ y : Y, P y => (λ x : X, sy (f x)).



Definition hfibertoforall {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
           (s : ∏ x : X, Q x) :
  hfiber  (@maponsec _ _ _ f) s -> ∏ x : X, hfiber  (f x) (s x).
Proof.
  intro. intro. intro. intro. intro. unfold hfiber.
  set (map1 := totalfun (fun pointover : ∏ x : X, P x =>
                           paths (λ x : X, f x (pointover x)) s)
                        (fun pointover : ∏ x : X, P x =>
                           ∏ x : X, paths  ((f x) (pointover x)) (s x))
                        (fun pointover: ∏ x : X, P x =>
                           toforallpaths _ (λ x : X, f x (pointover x)) s)).
  set (map2 := totaltoforall P (λ x : X,
                                  (λ pointover : P x,
                                     paths (f x pointover) (s x)))).
  set (themap := λ a : _, map2 (map1 a)). assumption.
Defined.



Definition foralltohfiber {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
           (s : ∏ x : X, Q x) :
  (∏ x : X, hfiber (f x) (s x)) -> hfiber (maponsec _ _ f) s.
Proof.
  intro. intro. intro. intro. intro. unfold hfiber.
  set (map2inv := foralltototal P (λ x : X, (λ pointover : P x,
                                                paths (f x pointover) (s x)))).
  set (map1inv :=  totalfun (fun pointover : ∏ x : X, P x =>
                               ∏ x : X, paths  ((f x) (pointover x)) (s x))
                            (fun pointover : ∏ x : X, P x =>
                               paths (λ x : X, f x (pointover x)) s)
                            (fun pointover: ∏ x : X, P x =>
                               funextsec _ (λ x : X, f x (pointover x)) s)).
  set (themap := λ a : _, map1inv (map2inv a)). assumption.
Defined.


Theorem isweqhfibertoforall {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
        (s : ∏ x : X, Q x) : isweq (hfibertoforall _ _ f s).
Proof.
  intro. intro. intro. intro. intro.
  set (map1 := totalfun (fun pointover : ∏ x : X, P x =>
                           paths  (λ x : X, f x (pointover x)) s)
                        (fun pointover : ∏ x : X, P x =>
                           ∏ x : X, paths  ((f x) (pointover x)) (s x))
                        (fun pointover: ∏ x : X, P x =>
                           toforallpaths _ (λ x : X, f x (pointover x)) s)).
  set (map2 := totaltoforall P (λ x : X, (λ pointover : P x,
                                             paths (f x pointover) (s x)))).
  assert (is1 : isweq map1)
    by apply (isweqfibtototal _ _ (fun pointover: ∏ x : X, P x =>
                                     weqtoforallpaths
                                       _ (λ x : X, f x (pointover x)) s)).
  assert (is2 : isweq map2)
    by apply isweqtotaltoforall.
  apply (twooutof3c map1 map2 is1 is2).
Defined.


Definition weqhfibertoforall {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
           (s : ∏ x : X, Q x) := weqpair _ (isweqhfibertoforall P Q f s).



Theorem isweqforalltohfiber {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
        (s : ∏ x : X, Q x) : isweq (foralltohfiber  _ _ f s).
Proof.
  intro. intro. intro. intro. intro.
  set (map2inv := foralltototal P (λ x : X, (λ pointover : P x,
                                                paths (f x pointover) (s x)))).

  assert (is2 : isweq map2inv).
  apply (isweqforalltototal P (λ x : X, (λ pointover : P x,
                                            paths (f x pointover) (s x)))).
  set (map1inv := totalfun (fun pointover : ∏ x : X, P x =>
                              ∏ x : X, paths ((f x) (pointover x)) (s x))
                           (fun pointover : ∏ x : X, P x =>
                              paths (λ x : X, f x (pointover x)) s)
                           (fun pointover: ∏ x : X, P x =>
                              funextsec _  (λ x : X, f x (pointover x)) s)).
  assert (is1 : isweq map1inv).

  (* ??? in this place 8.4 (actually trunk to 8.5) hangs if the next command is

    apply (isweqfibtototal _ _ (fun pointover: ∏ x : X, P x =>
    weqfunextsec _ (λ x : X, f x (pointover x)) s)).

    and no -no-sharing option is turned on. It also hangs on

    exact (isweqfibtototal (fun pointover : ∏ x : X, P x =>
                ∏ x : X, paths (f x (pointover x)) (s x))
                  (fun pointover : ∏ x : X, P x =>
                paths (λ x : X, f x (pointover x)) s)
                  (fun pointover: ∏ x : X, P x =>
                weqfunextsec Q (λ x : X, f x (pointover x)) s)).

    for at least 2hrs. After adding "Opaque funextsec." the "exact" commend
    goes through in <1sec and so does the "apply". If "Transparent funextsec."
    added after the "apply" the compilation hangs on "Define".

    Resoved (2014.10.23). *)

  apply (isweqfibtototal _ _ (fun pointover: ∏ x : X, P x =>
                                weqfunextsec _ (λ x : X, f x (pointover x))
                                             s)).
  apply (twooutof3c map2inv map1inv is2 is1).
Defined.


Definition weqforalltohfiber {X : UU} (P Q : X -> UU) (f : ∏ x : X, P x -> Q x)
           (s : ∏ x : X, Q x) := weqpair _ (isweqforalltohfiber P Q f s).



(** *** The weak equivalence  between section spaces (dependent products) defined by a family of weak equivalences  [ (P x) ≃ (Q x) ] *)




Corollary isweqmaponsec {X : UU} (P Q : X -> UU) (f : ∏ x : X, (P x) ≃ (Q x)) :
  isweq (maponsec _ _ f).
Proof.
  intros. unfold isweq. intro y.
  assert (is1 : iscontr (∏ x : X, hfiber (f x) (y x))).
  {
    assert (is2 : ∏ x : X, iscontr (hfiber (f x) (y x)))
      by (intro x; apply ((pr2 (f x)) (y x))).
    apply funcontr. assumption.
  }
  apply (iscontrweqb (weqhfibertoforall P Q f y) is1).
Defined.

Definition weqonsecfibers {X : UU} (P Q : X -> UU) (f : ∏ x : X, (P x) ≃ (Q x))
  := weqpair _ (isweqmaponsec P Q f).


(** *** Composition of functions with a weak equivalence on the right *)

Definition weqffun (X : UU) {Y Z : UU} (w : Y ≃ Z) : (X -> Y) ≃ (X -> Z)
  := weqonsecfibers _ _ (λ x : X, w).








(** ** The map between section spaces (dependent products) defined by the map between the bases [ f : Y -> X ] *)


(** *** General case *)


Definition maponsec1l0 {X : UU} (P : X -> UU) (f : X -> X)
           (h : ∏ x : X, (f x) = x) (s : ∏ x : X, P x) : (∏ x : X, P x)
  := (λ x : X, transportf P (h x) (s (f x))).

Lemma maponsec1l1 {X : UU} (P : X -> UU) (x : X) (s :∏ x : X, P x) :
  paths (maponsec1l0 P (λ x : X, x) (λ x : X, idpath x) s x) (s x).
Proof. intros. unfold maponsec1l0. apply idpath. Defined.


Lemma maponsec1l2 {X : UU} (P : X -> UU) (f : X -> X) (h : ∏ x : X, (f x) = x)
      (s : ∏ x : X, P x) (x : X) : paths (maponsec1l0 P f h s x) (s x).
Proof.
  intros.
  set (map := fun ff : total2 (fun f0 : X ->X => ∏ x : X, (f0 x) = x) =>
                maponsec1l0 P (pr1 ff) (pr2 ff) s x).
  assert (is1 : iscontr (total2 (fun f0 : X ->X => ∏ x : X, (f0 x) = x)))
    by apply funextcontr.
  assert (e: paths (tpair (fun f0 : X ->X => ∏ x : X, (f0 x) = x) f h)
                   (tpair (fun f0 : X ->X => ∏ x : X, (f0 x) = x)
                          (λ x0 : X, x0) (λ x0 : X, idpath x0)))
    by (apply proofirrelevancecontr; assumption).
  apply (maponpaths map e).
Defined.


Theorem isweqmaponsec1 {X Y : UU} (P : Y -> UU) (f : X ≃ Y) :
  isweq (maponsec1 P f).
Proof.
  intros.
  set (map := maponsec1  P f).
  set (invf := invmap f).
  set (e1 := homotweqinvweq f). set (e2 := homotinvweqweq f).
  set (im1 := fun sx : ∏ x : X, P (f x) => (λ y : Y, sx (invf y))).
  set (im2 := fun sy': ∏ y : Y, P (f (invf y)) =>
                (λ y : Y, transportf _ (homotweqinvweq f y) (sy' y))).
  set (invmapp := (fun sx : ∏ x : X, P (f x) => im2 (im1 sx))).

  assert (efg0 : ∏ sx : (∏ x : X, P (f x)),
                        ∏ x : X, paths ((map (invmapp sx)) x) (sx x)).
  {
    intro. intro. unfold map. unfold invmapp. unfold im1. unfold im2.
    unfold maponsec1. simpl. fold invf. set (ee := e2 x). fold invf in ee.
    set (e3x := λ x0 : X, invmaponpathsweq f (invf (f x0)) x0
                                            (homotweqinvweq f (f x0))).
    set (e3 := e3x x).
    assert (e4 : paths (homotweqinvweq f (f x)) (maponpaths f  e3))
      by apply (pathsinv0 (pathsweq4 f (invf (f x)) x _)).
    assert  (e5 : paths (transportf P (homotweqinvweq f (f x))
                                    (sx (invf (f x))))
                        (transportf P (maponpaths f  e3) (sx (invf (f x)))))
      by apply (maponpaths (λ e40 : _, (transportf P e40 (sx (invf (f x)))))
                           e4).
    assert (e6 : paths (transportf P (maponpaths f e3) (sx (invf (f x))))
                       (transportf (λ x : X, P (f x)) e3 (sx (invf (f x)))))
      by apply (pathsinv0 (functtransportf f P e3 (sx (invf (f x))))).
    set (ff := λ x : X, invf (f x)).
    assert (e7 : paths (transportf (λ x : X, P (f x)) e3 (sx (invf (f x))))
                       (sx x))
      by apply (maponsec1l2 (λ x : X, P (f x)) ff e3x sx x).
    apply (pathscomp0 (pathscomp0 e5 e6) e7).
  }
  assert (efg : ∏ sx : (∏ x : X, P (f x)), paths (map (invmapp sx)) sx)
    by (intro; apply (funextsec _ _ _ (efg0 sx))).

  assert (egf0 : ∏ sy : (∏ y : Y, P y), ∏ y : Y, paths ((invmapp (map sy)) y)
                                                       (sy y)).
  {
    intros. unfold invmapp. unfold map. unfold im1. unfold im2.
    unfold maponsec1.
    set (ff := λ y : Y, f (invf y)). fold invf.
    apply (maponsec1l2 P ff (homotweqinvweq f) sy y).
  }
  assert (egf : ∏ sy : (∏ y : Y, P y), paths (invmapp (map sy)) sy)
    by (intro; apply (funextsec _ _ _ (egf0 sy))).

  apply (gradth map invmapp egf efg).
Defined.

Definition weqonsecbase {X Y : UU} (P : Y -> UU) (f : X ≃ Y)
  : weq (∏ y : Y, P y) (∏ x : X, P (f x))
  := weqpair _ (isweqmaponsec1 P f).


(** *** Composition of functions with a weak equivalence on the left *)


Definition weqbfun {X Y : UU} (Z : UU) (w : X ≃ Y) : (Y -> Z) ≃ (X -> Z)
  := weqonsecbase _ w.



















(** ** Sections of families over an empty type and over coproducts *)

(** *** General case *)

Definition iscontrsecoverempty (P : empty -> UU) : iscontr (∏ x : empty, P x).
Proof.
  intro. split with (λ x : empty, fromempty x).
  intro t. apply funextsec.
  intro t0. induction t0.
Defined.

Definition iscontrsecoverempty2 {X : UU} (P : X -> UU) (is : neg X) :
  iscontr (∏ x : X, P x).
Proof.
  intros. set (w := weqtoempty is). set (w' := weqonsecbase P (invweq w)).
  apply (iscontrweqb w' (iscontrsecoverempty _)).
Defined.

Definition secovercoprodtoprod {X Y : UU} (P : coprod X Y -> UU)
           (a : ∏ xy : coprod X Y, P xy) :
  dirprod (∏ x : X, P (ii1 x)) (∏ y : Y, P (ii2 y))
  := dirprodpair (λ x : X, a (ii1 x)) (λ y : Y, a (ii2 y)).

Definition prodtosecovercoprod {X Y : UU} (P : coprod X Y -> UU)
           (a : dirprod (∏ x : X, P (ii1 x)) (∏ y : Y, P (ii2 y))) :
  ∏ xy : coprod X Y, P xy.
Proof.
  intros. induction xy as [ x | y ].
  - apply (pr1 a x).
  - apply (pr2 a y).
Defined.


Definition weqsecovercoprodtoprod {X Y : UU} (P : coprod X Y -> UU) :
  weq (∏ xy : coprod X Y, P xy)
      (dirprod (∏ x : X, P (ii1 x)) (∏ y : Y, P (ii2 y))).
Proof.
  intros.
  set (f := secovercoprodtoprod P). set (g := prodtosecovercoprod P).
  split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro. apply funextsec.
    intro t. induction t as [ x | y ].
    apply idpath. apply idpath.
  }
  assert (efg : ∏ a : _, paths (f (g a)) a).
  {
    intro. induction a as [ ax ay ].
    apply (pathsdirprod). apply funextsec.
    intro x. apply idpath. apply funextsec.
    intro y. apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.



(** *** Functions from the empty type *)

Theorem iscontrfunfromempty (X : UU) : iscontr (empty -> X).
Proof.
  intro. split with fromempty.
  intro t. apply funextfun.
  intro x. induction x.
Defined.

Theorem iscontrfunfromempty2 (X : UU) {Y : UU} (is : neg Y) : iscontr (Y -> X).
Proof.
  intros. set (w := weqtoempty is). set (w' := weqbfun X (invweq w)).
  apply (iscontrweqb w' (iscontrfunfromempty X)).
Defined.



(** *** Functions from a coproduct *)

Definition funfromcoprodtoprod {X Y Z : UU} (f : coprod X Y -> Z) :
  (X -> Z) × (Y -> Z)
  := dirprodpair (λ x : X, f (ii1 x)) (λ y : Y, f (ii2 y)).

Definition prodtofunfromcoprod {X Y Z : UU} (fg : (X -> Z) × (Y -> Z)) :
  coprod X Y -> Z := match fg with tpair _ f g => sumofmaps f g end.

Theorem weqfunfromcoprodtoprod (X Y Z : UU) :
  weq (coprod X Y -> Z) ((X -> Z) × (Y -> Z)).
Proof.
  intros.
  simple refine (
           weqpair _ (gradth (@funfromcoprodtoprod X Y Z)
                             (@prodtofunfromcoprod X Y Z) _ _)).
  - intro a. apply funextfun; intro xy. induction xy as [ x | y ]; apply idpath.
  - intro a. induction a as [fx fy]. apply idpath.
Defined.

(** ** Sections of families over contractible types and over [ total2 ] (over dependent sums) *)



(** *** General case *)


Definition tosecoverunit (P : unit -> UU) (p : P tt) : ∏ t : unit, P t.
Proof. intros. induction t. apply p. Defined.

Definition weqsecoverunit (P : unit -> UU) : (∏ t : unit, P t) ≃ (P tt).
Proof.
  intro.
  set (f := fun a : ∏ t : unit, P t => a tt). set (g := tosecoverunit P).
  split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro. apply funextsec.
    intro t. induction t. apply idpath.
  }
  assert (efg : ∏ a : _, paths (f (g a)) a) by (intros; apply idpath).
  apply (gradth _ _ egf efg).
Defined.


Definition weqsecovercontr {X : UU} (P : X -> UU) (is : iscontr X) :
  weq (∏ x : X, P x) (P (pr1 is)).
Proof.
  intros. set (w1 := weqonsecbase P (wequnittocontr is)).
  apply (weqcomp w1 (weqsecoverunit _)).
Defined.

Definition tosecovertotal2 {X : UU} (P : X -> UU) (Q : total2 P -> UU)
           (a : ∏ x : X, ∏ p : P x, Q (tpair _ x p)) :
  ∏ xp : total2 P, Q xp.
Proof. intros. induction xp as [ x p ]. apply (a x p). Defined.


Definition weqsecovertotal2 {X : UU} (P : X -> UU) (Q : total2 P -> UU) :
  weq (∏ xp : total2 P, Q xp) (∏ x : X, ∏ p : P x, Q (tpair _ x p)).
Proof.
  intros.
  set (f := fun a : ∏ xp : total2 P, Q xp => λ x : X, λ p : P x,
                                                      a (tpair _ x p)).
  set (g := tosecovertotal2 P Q). split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro. apply funextsec.
    intro xp. induction xp as [ x p ]. apply idpath.
  }
  assert (efg : ∏ a : _, paths (f (g a)) a).
  {
    intro. apply funextsec.
    intro x. apply funextsec.
    intro p. apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.


(** *** Functions from [ unit ] and from contractible types *)


Definition weqfunfromunit (X : UU) : weq (unit -> X) X := weqsecoverunit _.

Definition weqfunfromcontr {X : UU} (Y : UU) (is : iscontr X) : weq (X -> Y) Y
  := weqsecovercontr _ is.


(** *** Functions from [ total2 ] *)

Definition weqfunfromtotal2 {X : UU} (P : X -> UU) (Y : UU) :
  (total2 P -> Y) ≃ (∏ x : X, P x -> Y) := weqsecovertotal2 P _.

(** *** Functions from direct product *)

Definition weqfunfromdirprod (X X' Y : UU) :
  (dirprod X X' -> Y) ≃ (∏ x : X, X' -> Y) := weqsecovertotal2 _ _.
















(** ** Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

(** *** General case *)

Theorem impred (n : nat) {T : UU} (P : T -> UU) :
  (∏ t : T, isofhlevel n (P t)) -> (isofhlevel n (∏ t : T, P t)).
Proof.
  intro. induction n as [ | n IHn ].
  - intros T P X. apply (funcontr P X).
  - intros T P X. unfold isofhlevel in X. unfold isofhlevel. intros x x'.
    assert (is : ∏ t : T, isofhlevel n (paths (x t) (x' t)))
      by (intro; apply (X t (x t) (x' t))).
    assert (is2 : isofhlevel n (∏ t : T, paths (x t) (x' t)))
      by apply (IHn _ (λ t0 : T, paths (x t0) (x' t0)) is).
    set (u := toforallpaths P x x').
    assert (is3: isweq u) by apply isweqtoforallpaths.
    set (v:= invmap (weqpair u is3)).
    assert (is4: isweq v) by apply isweqinvmap.
    apply (isofhlevelweqf n (weqpair v is4)).
    assumption.
Defined.

Corollary impred_iscontr {T : UU} (P : T -> UU) :
  (∏ t : T, iscontr (P t)) -> (iscontr (∏ t : T, P t)).
Proof. intros. apply (impred 0). assumption. Defined.

Corollary impred_isaprop {T : UU} (P : T -> UU) :
  (∏ t : T, isaprop (P t)) -> (isaprop (∏ t : T, P t)).
Proof. apply impred. Defined.

Corollary impred_isaset {T : UU} (P : T -> UU) :
  (∏ t : T, isaset (P t)) -> (isaset (∏ t : T, P t)).
Proof. intros. apply (impred 2). assumption. Defined.

Corollary impredtwice  (n : nat) {T T' : UU} (P : T -> T' -> UU) :
  (∏ (t : T) (t': T'), isofhlevel n (P t t'))
  -> (isofhlevel n (∏ (t : T) (t': T'), P t t')).
Proof.
  intros n T T' P X.
  assert (is1 : ∏ t : T, isofhlevel n (∏ t': T', P t t'))
    by (intro; apply (impred n _ (X t))).
  apply (impred n _ is1).
Defined.


Corollary impredfun (n : nat) (X Y : UU) (is : isofhlevel n Y) :
  isofhlevel n (X -> Y).
Proof. intros. apply (impred n (λ x , Y) (λ x : X, is)). Defined.


Theorem impredtech1 (n : nat) (X Y : UU) :
  (X -> isofhlevel n Y) -> isofhlevel n (X -> Y).
Proof.
  intro. induction n as [ | n IHn ]. intros X Y X0. simpl.
  split with (λ x : X, pr1 (X0 x)).
  - intro t.
    assert (s1 : ∏ x : X, paths (t x) (pr1 (X0 x)))
           by (intro; apply proofirrelevancecontr; apply (X0 x)).
    apply funextsec. assumption.
  - intros X Y X0. simpl.
    assert (X1 : X -> isofhlevel (S n) (X -> Y))
      by (intro X1; apply impred; assumption).
    intros x x'.
    assert (s1 : isofhlevel n (∏ xx : X, paths (x xx) (x' xx)))
           by (apply impred; intro t; apply (X0 t)).
    assert (w : weq (∏ xx : X, paths (x xx) (x' xx)) (x = x'))
      by apply (weqfunextsec  _ x x').
    apply (isofhlevelweqf n w s1).
Defined.



(** ***  Functions to a contractible type *)

Theorem iscontrfuntounit (X : UU) : iscontr (X -> unit).
Proof.
  intro. split with (λ x : X, tt).
  intro f. apply funextfun.
  intro x. induction (f x). apply idpath.
Defined.

Theorem iscontrfuntocontr (X : UU) {Y : UU} (is : iscontr Y) : iscontr (X -> Y).
Proof.
  intros.
  set (w := weqcontrtounit is). set (w' := weqffun X w).
  apply (iscontrweqb w' (iscontrfuntounit X)).
Defined.


(** *** Functions to a proposition *)

Lemma isapropimpl (X Y : UU) (isy : isaprop Y) : isaprop (X -> Y).
Proof. intros. apply impred. intro. assumption. Defined.



(** *** Functions to an empty type (generalization of [ isapropneg ]) *)


Theorem isapropneg2 (X : UU) {Y : UU} (is : neg Y) : isaprop (X -> Y).
Proof. intros. apply impred. intro. apply (isapropifnegtrue is). Defined.





(** ** Theorems saying that  [ iscontr T ], [ isweq f ] etc. are of h-level 1 *)



Theorem iscontriscontr {X : UU} (is : iscontr X) : iscontr (iscontr X).
Proof.
  intros X X0.
  assert (is0 : ∏ (x x' : X), x = x')
         by (apply proofirrelevancecontr; assumption).
  assert (is1 : ∏ cntr : X, iscontr (∏ x : X, x = cntr)).
  {
    intro.
    assert (is2 : ∏ x : X, iscontr (x = cntr)).
    {
      assert (is2 : isaprop X)
             by (apply isapropifcontr; assumption).
      unfold isaprop in is2. unfold isofhlevel in is2.
      intro x. apply (is2 x cntr).
    }
    apply funcontr. assumption.
  }
  set (f := @pr1 X (λ cntr : X, ∏ x : X, x = cntr)).
  assert (X1 : isweq f)
    by (apply isweqpr1; assumption).
  change (total2 (λ cntr : X, ∏ x : X, x = cntr)) with (iscontr X) in X1.
  apply (iscontrweqb (weqpair f X1)). assumption.
Defined.



Theorem isapropiscontr (T : UU) : isaprop (iscontr T).
Proof.
  intros. unfold isaprop. unfold isofhlevel.
  intros x x'. assert (is : iscontr(iscontr T)).
  apply iscontriscontr. apply x.
  assert (is2 : isaprop (iscontr T)) by apply (isapropifcontr is).
  apply (is2 x x').
Defined.


Theorem isapropisweq {X Y : UU} (f : X -> Y) : isaprop (isweq f).
Proof.
  intros. unfold isweq.
  apply (impred (S O) (λ y : Y, iscontr (hfiber f y))
                (λ y : Y, isapropiscontr (hfiber f y))).
Defined.


Theorem isapropisisolated (X : UU) (x : X) : isaprop (isisolated X x).
(* uses funextemptyAxiom *)
Proof.
  intros. apply isofhlevelsn. intro is. apply impred. intro x'.
  apply (isapropdec _ (isaproppathsfromisolated X x is x')).
Defined.

Theorem isapropisdeceq (X : UU) : isaprop (isdeceq X).
(* uses funextemptyAxiom *)
Proof.
  intro. apply (isofhlevelsn 0). intro is. unfold isdeceq. apply impred.
  intro x. apply (isapropisisolated X x).
Defined.

Theorem isapropisofhlevel (n : nat) (X : UU) : isaprop (isofhlevel n X).
Proof.
  intro. induction n as [ | n IHn ].
  - apply isapropiscontr.
  - intro X.
    apply impred. intros t.
    apply impred. intros t0.
    apply IHn.
Defined.

Corollary isapropisaprop (X : UU) : isaprop (isaprop X).
Proof. intro. apply (isapropisofhlevel (S O)). Defined.

Definition isapropisdecprop (X : UU) : isaprop (isdecprop X).
Proof.
  intros.
  unfold isdecprop.
  apply (isofhlevelweqf 1 (weqdirprodcomm _ _)).
  apply isofhleveltotal2.
  - apply isapropisaprop.
  - intro i. apply isapropdec. assumption.
Defined.

Corollary isapropisaset (X : UU) : isaprop (isaset X).
Proof. intro. apply (isapropisofhlevel (S (S O))). Defined.

Theorem isapropisofhlevelf (n : nat) {X Y : UU} (f : X -> Y) :
  isaprop (isofhlevelf n f).
Proof.
  intros. unfold isofhlevelf. apply impred. intro y. apply isapropisofhlevel.
Defined.

Definition isapropisincl {X Y : UU} (f : X -> Y) : isaprop (isofhlevelf 1 f)
  := isapropisofhlevelf 1 f.

Lemma isaprop_isInjective {X Y : UU} (f : X -> Y) : isaprop (isInjective f).
Proof.
  intros.
  unfold isInjective.
  apply impred; intro.
  apply impred; intro.
  apply isapropisweq.
Defined.

Lemma incl_injectivity {X Y : UU} (f : X -> Y) : isincl f ≃ isInjective f.
Proof.
  intros.
  apply weqimplimpl.
  - apply isweqonpathsincl.
  - apply isinclweqonpaths.
  - apply isapropisincl.
  - apply isaprop_isInjective.
Defined.

(** ** Theorems saying that various [ pr1 ] maps are inclusions *)


Theorem isinclpr1weq (X Y : UU) : isincl (pr1weq : X ≃ Y -> X -> Y).
Proof. intros. refine (isinclpr1 _ _). intro f.   apply isapropisweq.  Defined.

Corollary isinjpr1weq (X Y : UU) : isInjective (pr1weq : X ≃ Y -> X -> Y).
Proof. intros. apply isweqonpathsincl. apply isinclpr1weq. Defined.

Theorem isinclpr1isolated (T : UU) : isincl (pr1isolated T).
Proof. intro. apply (isinclpr1 _ (λ t : T, isapropisisolated T t)). Defined.

(** associativity of weqcomp **)

Definition weqcomp_assoc {W X Y Z : UU} (f : W ≃ X) (g: X ≃ Y) (h : Y ≃ Z) :
  (h ∘ (g ∘ f) = (h ∘ g) ∘ f)%weq.
Proof.
  intros. apply subtypeEquality.
  - intros p. apply isapropisweq.
  - simpl. apply idpath.
Defined.

Lemma eqweqmap_pathscomp0 {A B C : UU} (p : A = B) (q : B = C)
  : weqcomp (eqweqmap p) (eqweqmap q)
  = eqweqmap (pathscomp0 p q).
Proof.
  induction p.
  induction q.
  eapply total2_paths_f.
    apply isapropisweq.
    Unshelve.
  apply idpath.
Defined.

Lemma inv_idweq_is_idweq {A : UU} :
  idweq A = invweq (idweq A).
Proof.
  intros A.
  eapply total2_paths_f.
  apply isapropisweq.
  Unshelve.
  apply idpath.
Defined.

Lemma eqweqmap_pathsinv0 {A B : UU} (p : A = B)
  : eqweqmap (!p) = invweq (eqweqmap p).
Proof.
  induction p.
  exact inv_idweq_is_idweq.
Defined.

(** ** Various weak equivalences between spaces of weak equivalences *)

(** *** Composition with a weak quivalence is a weak equivalence on weak equivalences *)

Theorem weqfweq (X : UU) {Y Z : UU} (w : Y ≃ Z) : (X ≃ Y) ≃ (X ≃ Z).
Proof.
  intros.
  set (f := λ a : X ≃ Y, weqcomp a w).
  set (g := λ b : X ≃ Z, weqcomp b (invweq w)).
  split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro a. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro x. apply (homotinvweqweq w (a x)).
  }
  assert (efg : ∏ b : _, paths (f (g b)) b).
  {
    intro b. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro x. apply (homotweqinvweq w (b x)).
  }
  apply (gradth _ _ egf efg).
Defined.

Theorem weqbweq {X Y : UU} (Z : UU) (w : X ≃ Y) : (Y ≃ Z) ≃ (X ≃ Z).
Proof.
  intros.
  set (f := λ a : Y ≃ Z, weqcomp w a).
  set (g := λ b : X ≃ Z, weqcomp (invweq w) b).
  split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro a. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro y. apply (maponpaths a (homotweqinvweq w y)).
  }
  assert (efg : ∏ b : _, paths (f (g b)) b).
  {
    intro b. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro x. apply (maponpaths b (homotinvweqweq w x)).
  }
  apply (gradth _ _ egf efg).
Defined.

Theorem weqweq {X Y : UU} (w: X ≃ Y) : (X ≃ X) ≃ (Y ≃ Y).
Proof.
  intros. intermediate_weq (X ≃ Y).
  - apply weqfweq. assumption.
  - apply invweq. apply weqbweq. assumption.
Defined.

(** *** Invertion on weak equivalences as a weak equivalence *)

(** Comment : note that full form of [ funextfun ] is only used in the proof of
  this theorem in the form of [ isapropisweq ]. The rest of the proof can be
  completed using eta-conversion. *)

Theorem weqinvweq (X Y : UU) : (X ≃ Y) ≃ (Y ≃ X).
Proof.
  intros.
  set (f := λ w : X ≃ Y, invweq w).
  set (g := λ w : Y ≃ X, invweq w).
  split with f.
  assert (egf : ∏ w : _, paths (g (f w)) w).
  {
    intro. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro x. apply idpath.
  }
  assert (efg : ∏ w : _, paths (f (g w)) w).
  {
    intro. apply (invmaponpathsincl _ (isinclpr1weq _ _)). apply funextfun.
    intro x. apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.



(** ** h-levels of spaces of weak equivalences *)


(** *** Weak equivalences to and from types of h-level (S n) *)

Theorem isofhlevelsnweqtohlevelsn (n : nat) (X Y : UU)
        (is : isofhlevel (S n) Y) : isofhlevel (S n) (X ≃ Y).
Proof.
  intros.
  apply (isofhlevelsninclb n _ (isinclpr1weq _ _)).
  apply impred. intro. apply is.
Defined.

Theorem isofhlevelsnweqfromhlevelsn (n : nat) (X Y : UU)
        (is : isofhlevel (S n) Y) : isofhlevel (S n) (Y ≃ X).
Proof.
  intros.
  apply (isofhlevelweqf (S n) (weqinvweq X Y)
                        (isofhlevelsnweqtohlevelsn n X Y is)).
Defined.




(** *** Weak equivalences to and from contractible types *)

Theorem isapropweqtocontr (X : UU) {Y : UU} (is : iscontr Y) : isaprop (X ≃ Y).
Proof. intros. apply (isofhlevelsnweqtohlevelsn 0 _ _ (isapropifcontr is)). Defined.

Theorem isapropweqfromcontr (X : UU) {Y : UU} (is : iscontr Y) : isaprop (Y ≃ X).
Proof. intros. apply (isofhlevelsnweqfromhlevelsn 0 X _ (isapropifcontr is)). Defined.


(** *** Weak equivalences to and from propositions *)


Theorem isapropweqtoprop (X  Y : UU) (is : isaprop Y) : isaprop (X ≃ Y).
Proof. intros. apply (isofhlevelsnweqtohlevelsn 0 _ _ is). Defined.

Theorem isapropweqfromprop (X Y : UU) (is : isaprop Y) : isaprop (Y ≃ X).
Proof. intros. apply (isofhlevelsnweqfromhlevelsn 0 X _ is). Defined.


(** *** Weak equivalences to and from sets *)

Theorem isasetweqtoset (X  Y : UU) (is : isaset Y) : isaset (X ≃ Y).
Proof. intros. apply (isofhlevelsnweqtohlevelsn 1 _ _ is). Defined.

Theorem isasetweqfromset (X Y : UU) (is : isaset Y) : isaset (Y ≃ X).
Proof. intros. apply (isofhlevelsnweqfromhlevelsn 1 X _ is). Defined.



(** *** Weak equivalences to an empty type *)

Theorem isapropweqtoempty (X : UU) : isaprop (X ≃ empty).
Proof. intro. apply (isofhlevelsnweqtohlevelsn 0 _ _ (isapropempty)). Defined.


Theorem isapropweqtoempty2 (X : UU) {Y : UU} (is : neg Y) : isaprop (X ≃ Y).
Proof. intros. apply (isofhlevelsnweqtohlevelsn 0 _ _ (isapropifnegtrue is)). Defined.


(** *** Weak equivalences from an empty type *)

Theorem isapropweqfromempty (X : UU) : isaprop (empty ≃ X).
Proof. intro. apply (isofhlevelsnweqfromhlevelsn 0 X _ (isapropempty)). Defined.

Theorem isapropweqfromempty2 (X : UU) {Y : UU} (is : neg Y) : isaprop (Y ≃ X).
Proof. intros. apply (isofhlevelsnweqfromhlevelsn 0 X _ (isapropifnegtrue is)). Defined.

(** *** Weak equivalences to and from [ unit ] *)

Theorem isapropweqtounit (X : UU) : isaprop (X ≃ unit).
Proof. intro. apply (isofhlevelsnweqtohlevelsn 0 _ _ (isapropunit)). Defined.

Theorem isapropweqfromunit (X : UU) : isaprop (unit ≃ X).
Proof. intros. apply (isofhlevelsnweqfromhlevelsn 0 X _ (isapropunit)). Defined.

(** ** Weak auto-equivalences of a type with an isolated point *)

Definition cutonweq {T : UU} t (is : isisolated T t) (w : T ≃ T) :
  isolated T × (compl T t ≃ compl T t).
Proof.
  intros. split.
  - exists (w t). apply isisolatedweqf. assumption.
  - intermediate_weq (compl T (w t)).
    + apply weqoncompl.
    + apply weqtranspos0.
      * apply isisolatedweqf. assumption.
      * assumption.
Defined.

Definition invcutonweq {T : UU} (t : T)
           (is : isisolated T t)
           (t'w : isolated T × (compl T t ≃ compl T t)) : T ≃ T
  := weqcomp (weqrecomplf t t is is (pr2 t'w))
             (weqtranspos t (pr1 (pr1 t'w)) is (pr2 (pr1 t'w))).

Lemma pathsinvcuntonweqoft {T : UU} (t : T)
      (is : isisolated T t)
      (t'w : isolated T × (compl T t ≃ compl T t)) :
  invcutonweq t is t'w t = pr1 (pr1 t'w).
Proof.
  intros. unfold invcutonweq. simpl. unfold recompl. unfold coprodf.
  unfold invmap. simpl. unfold invrecompl.
  induction (is t) as [ ett | nett ].
  - apply pathsfuntransposoft1.
  - induction (nett (idpath _)).
Defined.

Definition weqcutonweq (T : UU) (t : T) (is : isisolated T t) :
  (T ≃ T) ≃ isolated T × (compl T t ≃ compl T t).
Proof.
  intros.
  set (f := cutonweq t is). set (g := invcutonweq t is).
  apply (weqgradth f g).
  - intro w. Set Printing Coercions. idtac.
    apply (invmaponpathsincl _ (isinclpr1weq _ _)).
    apply funextfun; intro t'. simpl.
    unfold invmap; simpl. unfold coprodf, invrecompl.
    induction (is t') as [ ett' | nett' ].
    + simpl. rewrite (pathsinv0 ett'). apply pathsfuntransposoft1.
    + unfold funtranspos0; simpl.
      induction (is (w t)) as [ etwt | netwt ].
      * induction (is (w t')) as [ etwt' | netwt' ].
        -- induction (negf (invmaponpathsincl w (isofhlevelfweq 1 w) t t') nett'
                           (pathscomp0 (pathsinv0 etwt) etwt')).
        -- simpl. assert (newtt'' := netwt'). rewrite etwt in netwt'.
           apply (pathsfuntransposofnet1t2 t (w t) is _ (w t') newtt'' netwt').
      * simpl. induction (is (w t')) as [ etwt' | netwt' ].
        -- simpl. rewrite (pathsinv0 etwt').
           apply (pathsfuntransposoft2 t (w t) is _).
        -- simpl.
           assert (ne : neg (paths (w t) (w t')))
             by apply (negf (invmaponpathsweq w _ _) nett').
           apply (pathsfuntransposofnet1t2 t (w t) is _  (w t') netwt' ne).
  - intro xw. induction xw as [ x w ]. induction x as [ t' is' ].
    simpl in w. apply pathsdirprod.
    + apply (invmaponpathsincl _ (isinclpr1isolated _)).
      simpl. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
      induction (is t) as [ ett | nett ].
      * apply pathsfuntransposoft1.
      * induction (nett (idpath _)).
    + simpl.
      apply (invmaponpathsincl _ (isinclpr1weq _ _) _ _). apply funextfun.
      intro x. induction x as [ x netx ].
      unfold g, invcutonweq; simpl.
      set (int := funtranspos
                    (tpair _ t is) (tpair _ t' is')
                    (recompl T t (coprodf w (λ x0 :unit, x0)
                                          (invmap (weqrecompl T t is) t)))).
      assert (eee : int = t').
      {
        unfold int. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
        induction (is t) as [ ett | nett ].
        - apply (pathsfuntransposoft1).
        - induction (nett (idpath _)).
      }
      assert (isint : isisolated _ int).
      {
        rewrite eee. apply is'.
      }
      apply (ishomotinclrecomplf _ _ isint (funtranspos0 _ _ _) _ _).
      simpl.
      change (recomplf int t isint (funtranspos0 int t is))
      with (funtranspos (tpair _ int isint) (tpair _ t is)).
      assert (ee : paths (tpair _ int isint) (tpair _ t' is')).
      {
        apply (invmaponpathsincl _ (isinclpr1isolated _) _ _).
        simpl. apply eee.
      }
      rewrite ee.
      set (e := homottranspost2t1t1t2
                  t t' is is'
                  (recompl T t (coprodf w (λ x0 : unit, x0)
                                        (invmap (weqrecompl T t is) x)))).
      unfold funcomp,idfun in e.
      rewrite e. unfold recompl, coprodf, invmap; simpl. unfold invrecompl.
      induction (is x) as [ etx | netx' ].
      * induction (netx etx).
      * apply (maponpaths (@pr1 _ _)). apply (maponpaths w).
        apply (invmaponpathsincl _ (isinclpr1compl _ _) _ _).
        simpl. apply idpath.
        Unset Printing Coercions.
Defined.

(* Coprojections i.e. functions which are weakly equivalent to functions of the
  form ii1 : X -> coprod X Y


Definition locsplit (X : UU) (Y : UU) (f : X -> Y)
:= ∏ y : Y, (hfiber  f y) ⨿ (hfiber  f y -> empty).

Definition dnegimage (X : UU) (Y : UU) (f : X -> Y)
:= total2 Y (λ y : Y, dneg(hfiber  f y)).
Definition dnegimageincl (X Y : UU) (f : X -> Y)
:= pr1 Y (λ y : Y, dneg(hfiber  f y)).

Definition xtodnegimage (X : UU) (Y : UU) (f : X -> Y) : X -> dnegimage f
:= λ x : X, tpair (f x) ((todneg _) (hfiberpair  f (f x) x (idpath (f x)))).

Definition locsplitsec (X : UU) (Y : UU) (f : X -> Y) (ls : locsplit  f) :
dnegimage f -> X
:= λ u: _,
match u with
tpair y psi =>
match (ls y) with
ii1 z => pr1  z|
ii2 phi => fromempty (psi phi)
end
end.

Definition locsplitsecissec (X Y : UU) (f : X -> Y) (ls : locsplit f)
(u:dnegimage  f) : paths (xtodnegimage f (locsplitsec  f ls u)) u.
Proof. intros. set (p := xtodnegimage f). set (s := locsplitsec f ls).
assert (paths (pr1 (p (s u))) (pr1  u)). unfold p. unfold xtodnegimage.
unfold s. unfold locsplitsec. simpl. induction u. set (lst := ls t).
induction lst.  simpl. apply (pr2  x0). induction (x y).
assert (is : isofhlevelf (S O) (dnegimageincl f)).
apply (isofhlevelfpr1 (S O) (λ y : Y, isapropdneg (hfiber f y))).
assert (isw: isweq (maponpaths (dnegimageincl f) (p (s u)) u)).
apply (isofhlevelfonpaths O  _ is).
apply (invmap  _ isw X0).
Defined.



Definition negimage (X : UU) (Y : UU) (f : X -> Y)
:= total2 Y (λ y : Y, neg(hfiber f y)).
Definition negimageincl (X Y : UU) (f : X -> Y)
:= pr1 Y (λ y : Y, neg(hfiber f y)).


Definition imsum (X : UU) (Y : UU) (f : X -> Y) :
(dnegimage  f) ⨿ (negimage  f) -> Y
:= λ u,
match u with
ii1 z => pr1  z|
ii2 z => pr1  z
end.

 *)


(** some lemmas about weak equivalences *)

Definition weqcompidl {X Y} (f:X ≃ Y) : weqcomp (idweq X) f = f.
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
  apply funextsec; intro x; simpl. apply idpath.
Defined.

Definition weqcompidr {X Y} (f:X ≃ Y) : weqcomp f (idweq Y) = f.
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
  apply funextsec; intro x; simpl. apply idpath.
Defined.

Definition weqcompinvl {X Y} (f:X ≃ Y) : weqcomp (invweq f) f = idweq Y.
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
  apply funextsec; intro y; simpl. apply homotweqinvweq.
Defined.

Definition weqcompinvr {X Y} (f:X ≃ Y) : weqcomp f (invweq f) = idweq X.
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
  apply funextsec; intro x; simpl. apply homotinvweqweq.
Defined.

Definition weqcompassoc {X Y Z W} (f:X ≃ Y) (g:Y ≃ Z) (h:Z ≃ W) :
  weqcomp (weqcomp f g) h = weqcomp f (weqcomp g h).
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
  apply funextsec; intro x; simpl. apply idpath.
Defined.

Definition weqcompweql {X Y Z} (f:X ≃ Y) :
  isweq (fun g:Y ≃ Z => weqcomp f g).
Proof.
  intros. simple refine (gradth _ _ _ _).
  { intro h. exact (weqcomp (invweq f) h). }
  { intro g. simpl. rewrite <- weqcompassoc. rewrite weqcompinvl. apply weqcompidl. }
  { intro h. simpl. rewrite <- weqcompassoc. rewrite weqcompinvr. apply weqcompidl. }
Defined.

Definition weqcompweqr {X Y Z} (g:Y ≃ Z) :
  isweq (fun f:X ≃ Y => weqcomp f g).
Proof.
  intros. simple refine (gradth _ _ _ _).
  { intro h. exact (weqcomp h (invweq g)). }
  { intro f. simpl. rewrite weqcompassoc. rewrite weqcompinvr. apply weqcompidr. }
  { intro h. simpl. rewrite weqcompassoc. rewrite weqcompinvl. apply weqcompidr. }
Defined.

Definition weqcompinjr {X Y Z} {f f':X ≃ Y} (g:Y ≃ Z) :
  weqcomp f g = weqcomp f' g -> f = f'.
Proof.
  intros ? ? ? ? ? ?.
  apply (invmaponpathsincl _ (isinclweq _ _ _ (weqcompweqr g))).
Defined.

Definition weqcompinjl {X Y Z} (f:X ≃ Y) {g g':Y ≃ Z} :
  weqcomp f g = weqcomp f g' -> g = g'.
Proof.
  intros ? ? ? ? ? ?.
  apply (invmaponpathsincl _ (isinclweq _ _ _ (weqcompweql f))).
Defined.

Definition invweqcomp {X Y Z} (f:X ≃ Y) (g:Y ≃ Z) :
  invweq (weqcomp f g) = weqcomp (invweq g) (invweq f).
Proof.
  intros. apply (weqcompinjr (weqcomp f g)). rewrite weqcompinvl.
  rewrite weqcompassoc. rewrite <- (weqcompassoc (invweq f)).
  rewrite weqcompinvl. rewrite weqcompidl. rewrite weqcompinvl. apply idpath.
Defined.

Definition invmapweqcomp {X Y Z} (f:X ≃ Y) (g:Y ≃ Z) :
  invmap (weqcomp f g) = weqcomp (invweq g) (invweq f).
Proof.
  intros. exact (maponpaths pr1weq (invweqcomp f g)).
Defined.

(* End of the file uu0d.v *)
