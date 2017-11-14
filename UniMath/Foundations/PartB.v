(** * Univalent Foundations. Vladimir Voevodsky. Feb. 2010 - Sep. 2011.
  Port to coq trunk (8.4-8.5) in March 2014. The second part of the original
  uu0 file, created on Dec. 3, 2014.

This file starts with the definition of h-levels. No axioms are used. Only one
universe [ UU ] is used, except in one case.

In the current approach to dependent eliminators for inductive types, in this case for [ nat ],
the type family appears as an argument of the eliminator in the form of a function. Therefore,
if one wants to use the eliminator [ nat_rect ] to define a function [ nat -> UU ] one must use,
as an argument, the function [ n : nat => UU ] whose type is [ forall n : nat, UU' ] where [ UU' ]
is the type of [ UU ]. Therefore, the eliminator must be defined on arguments whose type contains
[ UU' ] and we should acknowledge it as an instance of using a second universe.

 *)

(** ** Contents
- Basics about h-levels
 - h-levels of types
 - h-levels of functions
 - h-levelf of pr1
 - h-level of the total space of total2
- Basics on propositions, inclusions and sets
 - Propositions, types of h-level 1
 - Inclusions, functions of h-level 1
 - Sets, types of h-level 2
*)


(** ** Preamble *)

(** Settings *)

(* The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.


(** Imports *)

Require Export UniMath.Foundations.PartA.



(** ** Basics about h-levels *)



(** *** h-levels of types *)


Fixpoint isofhlevel (n : nat) (X : UU) : UU
  := match n with
     | O => iscontr X
     | S m => ∏ x : X, ∏ x' : X, (isofhlevel m (x = x'))
     end.

(* induction induction *)

Theorem hlevelretract (n : nat) {X Y : UU} (p : X -> Y) (s : Y -> X)
        (eps : ∏ y : Y , paths (p (s y)) y) : isofhlevel n X -> isofhlevel n Y.
Proof.
  intro.
  induction n as [ | n IHn ].
  - intros X Y p s eps X0. unfold isofhlevel.
    apply (iscontrretract p s eps X0).
  - unfold isofhlevel. intros X Y p s eps X0 x x'. unfold isofhlevel in X0.
    assert (is: isofhlevel n (paths (s x) (s x'))) by apply X0.
    set (s':= @maponpaths _ _ s x x'). set (p':= pathssec2  s p eps x x').
    set (eps':= @pathssec3 _ _  s p eps x x'). simpl.
    apply (IHn  _ _ p' s' eps' is).
Defined.

Corollary isofhlevelweqf (n : nat) {X Y : UU} (f : X ≃ Y) :
  isofhlevel n X -> isofhlevel n Y.
Proof.
  intros n X Y f X0.
  apply (hlevelretract n f (invmap f) (homotweqinvweq f)).
  assumption.
Defined.

Corollary isofhlevelweqb (n : nat) {X Y : UU} (f : X ≃ Y) :
  isofhlevel n Y -> isofhlevel n X.
Proof.
  intros n X Y f X0.
  apply (hlevelretract n (invmap f) f (homotinvweqweq f)).
  assumption.
Defined.

Lemma isofhlevelsn (n : nat) {X : UU} (f : X -> isofhlevel (S n) X) :
  isofhlevel (S n) X.
Proof. intros. simpl. intros x x'. apply (f x x x'). Defined.

Lemma isofhlevelssn (n : nat) {X : UU}
      (is : ∏ x : X, isofhlevel (S n) (x = x)) : isofhlevel (S (S n)) X.
Proof.
  intros. simpl. intros x x'.
  change (∏ (x0 x'0 : x = x'), isofhlevel n (x0 = x'0))
  with (isofhlevel (S n) (x = x')).
  assert (X1 : x = x' -> isofhlevel (S n) (x = x'))
    by (intro X2; induction X2; apply (is x)).
  apply (isofhlevelsn n X1).
Defined.







(** *** h-levels of functions *)


Definition isofhlevelf (n : nat) {X Y : UU} (f : X -> Y) : UU
  := ∏ y : Y, isofhlevel n (hfiber f y).


Theorem isofhlevelfhomot (n : nat) {X Y : UU} (f f' : X -> Y)
        (h : ∏ x : X, paths (f x) (f' x)) :
  isofhlevelf n f -> isofhlevelf n f'.
Proof.
  intros n X Y f f' h X0.
  unfold isofhlevelf. intro y.
  apply (isofhlevelweqf n (weqhfibershomot f f' h y) (X0 y)).
Defined.


Theorem isofhlevelfpmap (n : nat) {X Y : UU} (f : X -> Y) (Q : Y -> UU) :
  isofhlevelf n f -> isofhlevelf n (fpmap f Q).
Proof.
  intros n X Y f Q X0.
  unfold isofhlevelf. unfold isofhlevelf in X0.
  intro y.
  set (yy := pr1 y).
  set (g := hfiberfpmap f Q y).
  set (is := isweqhfiberfp f Q y).
  set (isy := X0 yy).
  apply (isofhlevelweqb n (weqpair g is) isy).
Defined.



Theorem isofhlevelfffromZ (n : nat) {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (fs : fibseqstr f g z) (isz : isofhlevel (S n) Z) : isofhlevelf n f.
Proof.
  intros. intro y.
  assert (w : (hfiber f y) ≃ ((g y) = z)).
  apply (invweq (ezweq1 f g z fs y)).
  apply (isofhlevelweqb n w (isz (g y) z)).
Defined.


Theorem isofhlevelXfromg (n : nat) {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (fs : fibseqstr f g z) : isofhlevelf n g -> isofhlevel n X.
Proof.
  intros n X Y Z f g z fs isf.
  assert (w : X ≃ (hfiber g z)).
  apply (weqpair _ (pr2 fs)).
  apply (isofhlevelweqb n w (isf z)).
Defined.


Theorem isofhlevelffromXY (n : nat) {X Y : UU} (f : X -> Y) :
  isofhlevel n X -> isofhlevel (S n) Y -> isofhlevelf n f.
Proof.
  intro. induction n as [ | n IHn ].
  - intros X Y f X0 X1.
    assert (is1 : isofhlevel O Y).
    {
      split with (f (pr1 X0)).
      intro t. unfold isofhlevel in X1.
      set (is := X1 t (f (pr1 X0))).
      apply (pr1 is).
    }
    apply (isweqcontrcontr f X0 is1).

  - intros X Y f X0 X1. unfold isofhlevelf. simpl.
    assert (is1 : ∏ x' x : X, isofhlevel n (x' = x))
      by (simpl in X0; assumption).
    assert (is2 : ∏ y' y : Y, isofhlevel (S n) (y' = y))
      by (simpl in X1; simpl; assumption).
    assert (is3 : ∏ (y : Y) (x : X) (xe' : hfiber f y),
                  isofhlevelf n (d2g f x xe'))
      by (intros; apply (IHn _ _ (d2g  f x xe') (is1 (pr1 xe') x)
                             (is2 (f x) y))).
    assert (is4 : ∏ (y : Y) (x : X) (xe' : hfiber f y) (e : (f x) = y),
                  isofhlevel n ((hfiberpair f x e) = xe'))
      by (intros; apply (isofhlevelweqb n (ezweq3g f x xe' e) (is3 y x xe' e))).
    intros y xe xe'. induction xe as [ t x ].
    apply (is4 y t xe' x).
Defined.



Theorem isofhlevelXfromfY (n : nat) {X Y : UU} (f : X -> Y) :
  isofhlevelf n f -> isofhlevel n Y -> isofhlevel n X.
Proof.
  intro. induction n as [ | n IHn ].
  - intros X Y f X0 X1.
    apply (iscontrweqb (weqpair f X0) X1).
  - intros X Y f X0 X1. simpl.
    assert (is1 : ∏ (y : Y) (xe xe': hfiber f y), isofhlevel n (xe = xe'))
           by (intros; apply (X0 y)).
    assert (is2 : ∏ (y : Y) (x : X) (xe' : hfiber f y),
                  isofhlevelf n (d2g f x xe')).
    {
      intros. unfold isofhlevel. intro y0.
      apply (isofhlevelweqf n (ezweq3g f x xe' y0)
                            (is1 y (hfiberpair f x y0) xe')).
    }
    assert (is3 : ∏ (y' y : Y), isofhlevel n (y' = y))
      by (simpl in X1; assumption).
    intros x' x.
    set (y := f x'). set (e' := idpath y). set (xe' := hfiberpair f x' e').
    apply (IHn  _ _ (d2g  f x xe') (is2 y x xe') (is3 (f x) y)).
Defined.






Theorem  isofhlevelffib (n : nat) {X : UU} (P : X -> UU) (x : X)
         (is : ∏ x' : X, isofhlevel n (x' = x)) : isofhlevelf n (tpair P x).
Proof.
  intros. unfold isofhlevelf. intro xp.
  apply (isofhlevelweqf n (ezweq1pr1 P x xp) (is (pr1 xp))).
Defined.



Theorem isofhlevelfhfiberpr1y (n : nat) {X Y : UU} (f : X -> Y) (y : Y)
        (is : ∏ y' : Y, isofhlevel n (y' = y)) :
  isofhlevelf n (hfiberpr1 f y).
Proof.
  intros. unfold isofhlevelf. intro x.
  apply (isofhlevelweqf n (ezweq1g f y x) (is (f x))).
Defined.


(* destruct -> induction ok to this point *)



Theorem isofhlevelfsnfib (n : nat) {X : UU} (P : X -> UU) (x : X)
        (is : isofhlevel (S n) (x = x)) : isofhlevelf (S n) (tpair P x).
Proof.
  intros. unfold isofhlevelf. intro xp.
  apply (isofhlevelweqf (S n) (ezweq1pr1 P x xp)).
  apply isofhlevelsn. intro X1. induction X1. assumption.
Defined.




Theorem isofhlevelfsnhfiberpr1 (n : nat) {X Y : UU} (f : X -> Y) (y : Y)
        (is : isofhlevel (S n) (y = y)) : isofhlevelf (S n) (hfiberpr1 f y).
Proof.
  intros. unfold isofhlevelf. intro x.
  apply (isofhlevelweqf (S n) ( ezweq1g f y x)). apply isofhlevelsn.
  intro X1. induction X1. assumption.
Defined.




Corollary isofhlevelfhfiberpr1 (n : nat) {X Y : UU} (f : X -> Y) (y : Y)
          (is : isofhlevel (S n) Y) : isofhlevelf n (hfiberpr1 f y).
Proof. intros. apply isofhlevelfhfiberpr1y. intro y'. apply (is y' y). Defined.






Theorem isofhlevelff (n : nat) {X Y Z : UU} (f : X -> Y) (g : Y -> Z) :
  isofhlevelf n (λ x : X, g (f x)) -> isofhlevelf (S n)  g -> isofhlevelf n f.
Proof.
  intros n X Y Z f g X0 X1. unfold isofhlevelf. intro y.
  set (ye := hfiberpair g y (idpath (g y))).
  apply (isofhlevelweqb n ( ezweqhf f g (g y) ye)
                        (isofhlevelffromXY n _ (X0 (g y)) (X1 (g y)) ye)).
Defined.



Theorem isofhlevelfgf (n : nat) {X Y Z : UU} (f : X -> Y) (g : Y -> Z) :
  isofhlevelf n f -> isofhlevelf n g -> isofhlevelf n (λ x : X, g (f x)).
Proof.
  intros n X Y Z f g X0 X1. unfold isofhlevelf. intro z.
  assert (is1 : isofhlevelf n (hfibersgftog f g z)).
  {
    unfold isofhlevelf. intro ye.
    apply (isofhlevelweqf n (ezweqhf f g z ye) (X0 (pr1 ye))).
  }
  assert (is2 : isofhlevel n (hfiber g z))
    by apply (X1 z).
  apply (isofhlevelXfromfY n  _ is1 is2).
Defined.



Theorem isofhlevelfgwtog (n : nat) {X Y Z : UU} (w : X ≃ Y) (g : Y -> Z)
        (is : isofhlevelf n (λ x : X, g (w x))) : isofhlevelf n g.
Proof.
  intros. intro z.
  assert (is' : isweq (hfibersgftog w g z)).
  {
    intro ye.
    apply (iscontrweqf (ezweqhf w g z ye) (pr2 w (pr1 ye))).
  }
  apply (isofhlevelweqf _ (weqpair _ is') (is _)).
Defined.



Theorem isofhlevelfgtogw (n : nat) {X Y Z : UU} (w : X ≃ Y) (g : Y -> Z)
        (is : isofhlevelf n g) : isofhlevelf n (λ x : X, g (w x)).
Proof.
  intros. intro z.
  assert (is' : isweq (hfibersgftog w g z)).
  {
    intro ye.
    apply (iscontrweqf (ezweqhf w g z ye) (pr2 w (pr1 ye))).
  }
  apply (isofhlevelweqb _ (weqpair _ is') (is _)).
Defined.



Corollary isofhlevelfhomot2 (n : nat) {X X' Y : UU} (f : X -> Y) (f' : X' -> Y)
          (w : X ≃ X') (h : ∏ x : X, paths (f x) (f' (w x))) :
  isofhlevelf n f -> isofhlevelf n f'.
Proof.
  intros n X X' Y f f' w h X0.
  assert (X1 : isofhlevelf n  (λ x : X, f' (w x)))
    by apply (isofhlevelfhomot n _ _ h X0).
  apply (isofhlevelfgwtog n w f' X1).
Defined.




Theorem isofhlevelfonpaths (n : nat) {X Y : UU} (f : X -> Y) (x x' : X) :
  isofhlevelf (S n) f -> isofhlevelf n (@maponpaths _ _ f x x').
Proof.
  intros n X Y f x x' X0.
  set (y := f x'). set (xe' := hfiberpair  f x' (idpath _)).
  assert (is1 : isofhlevelf n (d2g f x xe')).
  {
    unfold isofhlevelf. intro y0.
    apply (isofhlevelweqf n (ezweq3g f x xe' y0)
                          (X0 y (hfiberpair f x y0) xe')).
  }
  assert (h : ∏ ee : x' = x, paths (d2g f x xe' ee)
                                       (maponpaths f (pathsinv0 ee))).
  {
    intro.
    assert (e0: paths (pathscomp0 (maponpaths f (pathsinv0 ee)) (idpath _))
                      (maponpaths f (pathsinv0 ee)))
      by (induction ee; simpl; apply idpath).
    apply (e0).
  }
  apply (isofhlevelfhomot2 n _ _ (weqpair (@pathsinv0 _ x' x)
                                          (isweqpathsinv0 _ _)) h is1).
Defined.



Theorem isofhlevelfsn (n : nat) {X Y : UU} (f : X -> Y) :
  (∏ x x' : X, isofhlevelf n (@maponpaths _ _ f x x')) -> isofhlevelf (S n) f.
Proof.
  intros n X Y f X0. unfold isofhlevelf. intro y. simpl.
  intros x x'.
  induction x as [ x e ]. induction x' as [ x' e' ]. induction e'.
  set (xe' := hfiberpair f x' (idpath _)).
  set (xe := hfiberpair f x e).
  set (d3 := d2g f x xe'). simpl in d3.
  assert (is1 : isofhlevelf n (d2g f x xe')).
  assert (h : ∏ ee : x' = x, paths (maponpaths f (pathsinv0  ee))
                                       (d2g  f x xe' ee)).
  {
    intro. unfold d2g. simpl.
    apply (pathsinv0 (pathscomp0rid _)).
  }
  assert (is2 : isofhlevelf n (λ ee: x' = x, maponpaths f (pathsinv0 ee)))
    by apply (isofhlevelfgtogw n ( weqpair _ (isweqpathsinv0  _ _))
                               (@maponpaths _ _ f x x') (X0 x x')).
  apply (isofhlevelfhomot n _ _  h is2).
  apply (isofhlevelweqb n (ezweq3g f x xe' e) (is1 e)).
Defined.


Theorem isofhlevelfssn (n : nat) {X Y : UU} (f : X -> Y) :
  (∏ x : X, isofhlevelf (S n) (@maponpaths _ _ f x x))
  -> isofhlevelf (S (S n)) f.
Proof.
  intros n X Y f X0. unfold isofhlevelf. intro y.
  assert (∏ xe0 : hfiber f y, isofhlevel (S n) (xe0 = xe0)).
  {
    intro. induction xe0 as [ x e ]. induction e.
    set (e':= idpath (f x)).
    set (xe':= hfiberpair f x e').
    set (xe:= hfiberpair f x e').
    set (d3:= d2g f x xe'). simpl in d3.
    assert (is1: isofhlevelf (S n) (d2g f x xe')).
    {
      assert (h : ∏ ee: x = x, paths (maponpaths f (pathsinv0 ee))
                                         (d2g f x xe' ee)).
      {
        intro. unfold d2g. simpl.
        apply (pathsinv0 (pathscomp0rid _)).
      }
      assert (is2 : isofhlevelf (S n) (fun ee : x = x
                                       => maponpaths f (pathsinv0 ee)))
        by apply (isofhlevelfgtogw (S n)  (weqpair _ (isweqpathsinv0  _ _))
                                   (@maponpaths _ _ f x x) (X0 x)).
      apply (isofhlevelfhomot (S n) _ _  h is2).
    }
    apply (isofhlevelweqb (S n) (ezweq3g f x xe' e') (is1 e')).
  }
  apply (isofhlevelssn).
  assumption.
Defined.



(** ** h -levels of [ pr1 ], fiber inclusions, fibers, total spaces and bases of fibrations *)


(** *** h-levelf of [ pr1 ] *)


Theorem isofhlevelfpr1 (n : nat) {X : UU} (P : X -> UU)
        (is : ∏ x : X, isofhlevel n (P x)) : isofhlevelf n (@pr1 X P).
Proof.
  intros. unfold isofhlevelf. intro x.
  apply (isofhlevelweqf n (ezweqpr1  _ x) (is x)).
Defined.

Lemma isweqpr1 {Z : UU} (P : Z -> UU) (is1 : ∏ z : Z, iscontr (P z)) :
  isweq (@pr1 Z P).
Proof.
  intros. unfold isweq. intro y.
  set (isy := is1 y). apply (iscontrweqf (ezweqpr1 P y)).
  assumption.
Defined.

Definition weqpr1 {Z : UU} (P : Z -> UU) (is : ∏ z : Z , iscontr (P z)) :
  weq (total2 P) Z := weqpair _ (isweqpr1 P is).




(** *** h-level of the total space [ total2 ] *)

Theorem isofhleveltotal2 (n : nat) {X : UU} (P : X -> UU) (is1 : isofhlevel n X)
        (is2 : ∏ x : X, isofhlevel n (P x)) : isofhlevel n (total2 P).
Proof.
  intros.
  apply (isofhlevelXfromfY n (@pr1 _ _)).
  apply isofhlevelfpr1.
  assumption. assumption.
Defined.

Corollary isofhleveldirprod (n : nat) (X Y : UU) (is1 : isofhlevel n X)
          (is2 : isofhlevel n Y) : isofhlevel n (X × Y).
Proof. intros. apply isofhleveltotal2. assumption. intro. assumption. Defined.
















(** ** Propositions, inclusions  and sets *)







(** *** Basics about types of h-level 1 - "propositions" *)


Definition isaprop := isofhlevel 1.

Definition isPredicate {X : UU} (Y : X -> UU) := ∏ x : X, isaprop (Y x).

Definition isapropunit : isaprop unit := iscontrpathsinunit.

Definition isapropdirprod (X Y : UU) : isaprop X -> isaprop Y -> isaprop (X × Y)
  := isofhleveldirprod 1 X Y.

Lemma isapropifcontr {X : UU} (is : iscontr X) : isaprop X.
Proof.
  intros. set (f := λ x : X, tt).
  assert (isw : isweq f)
    by (apply isweqcontrtounit; assumption).
  apply (isofhlevelweqb (S O) (weqpair f isw)).
  intros x x'.
  apply iscontrpathsinunit.
Defined.

Theorem hlevelntosn (n : nat) (T : UU) (is : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  intro. induction n as [ | n IHn ].
  - intro. apply isapropifcontr.
  - intro. intro X.
    change (∏ t1 t2 : T, isofhlevel (S n) (t1 = t2)).
    intros t1 t2.
    change (∏ t1 t2 : T, isofhlevel n (t1 = t2)) in X.
    set (XX := X t1 t2).
    apply (IHn _ XX).
Defined.

Corollary isofhlevelcontr (n : nat) {X : UU} (is : iscontr X) : isofhlevel n X.
Proof.
  intro. induction n as [ | n IHn ].
  - intros X X0. assumption.
  - intros X X0. simpl. intros x x'.
    assert (is : iscontr (x = x')).
    apply (isapropifcontr X0 x x').
    apply (IHn _ is).
Defined.

Lemma isofhlevelfweq (n : nat) {X Y : UU} (f : X ≃ Y) : isofhlevelf n f.
Proof.
  intros n X Y f. unfold isofhlevelf. intro y.
  apply (isofhlevelcontr n).
  apply (pr2 f).
Defined.

Corollary isweqfinfibseq {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
          (fs : fibseqstr f g z) (isz : iscontr Z) : isweq f.
Proof.
  intros. apply (isofhlevelfffromZ 0 f g z fs (isapropifcontr isz)).
Defined.

Corollary weqhfibertocontr {X Y : UU} (f : X -> Y) (y : Y) (is : iscontr Y) :
  weq (hfiber f y) X.
Proof.
  intros. split with (hfiberpr1 f y).
  apply (isofhlevelfhfiberpr1 0 f y (hlevelntosn 0 _ is)).
Defined.

Corollary weqhfibertounit (X : UU) : (hfiber (λ x : X, tt) tt) ≃ X.
Proof. intro. apply (weqhfibertocontr _ tt iscontrunit). Defined.

Corollary isofhleveltofun (n : nat) (X : UU) :
  isofhlevel n X -> isofhlevelf n (λ x : X, tt).
Proof.
  intros n X is. intro t. induction t.
  apply (isofhlevelweqb n (weqhfibertounit X) is).
Defined.

Corollary isofhlevelfromfun (n : nat) (X : UU) :
  isofhlevelf n (λ x : X, tt) -> isofhlevel n X.
Proof.
  intros n X is. apply (isofhlevelweqf n (weqhfibertounit X) (is tt)).
Defined.

Definition weqhfiberunit {X Z : UU} (i : X -> Z) (z : Z) :
  (∑ x, hfiber (λ _ : unit, z) (i x)) ≃ hfiber i z.
Proof.
  intros. use weqgradth.
  + intros [x [t e]]. exact (x,,!e).
  + intros [x e]. exact (x,,tt,,!e).
  + intros [x [t e]]. apply maponpaths. simple refine (two_arg_paths_f _ _).
    * apply isapropunit.
    * simpl. induction e. rewrite pathsinv0inv0. induction t. apply idpath.
  + intros [x e]. apply maponpaths. apply pathsinv0inv0.
Defined.

Lemma isofhlevelsnprop (n : nat) {X : UU} (is : isaprop X) : isofhlevel (S n) X.
Proof.
  intros n X X0. simpl. unfold isaprop in X0. simpl in X0.
  intros x x'. apply isofhlevelcontr. apply (X0 x x').
Defined.

Lemma iscontraprop1 {X : UU} (is : isaprop X) (x : X) : iscontr X.
Proof.
  intros. unfold iscontr. split with x. intro t.
  unfold isofhlevel in is.
  set (is' := is t x).
  apply (pr1 is').
Defined.

Lemma iscontraprop1inv {X : UU} (f : X -> iscontr X) : isaprop X.
Proof.
  intros X c. apply (isofhlevelsn O). intro x. exact (hlevelntosn O X (c x)).
Defined.

Definition isProofIrrelevant (X:UU) := ∏ x y:X, x = y.

Lemma proofirrelevance (X : UU) : isaprop X -> isProofIrrelevant X.
Proof.
  intros ? is x x'. unfold isaprop in is. unfold isofhlevel in is. exact (iscontrpr1 (is x x')).
Defined.

Lemma invproofirrelevance (X : UU) : isProofIrrelevant X -> isaprop X.
Proof.
  intros ? ee x x'. apply isapropifcontr. exists x. intros t. exact (ee t x).
Defined.

Lemma isProofIrrelevant_paths {X} (irr:isProofIrrelevant X) {x y:X} : isProofIrrelevant (x=y).
Proof.
  intros ? ? ? ? p q. assert (r := invproofirrelevance X irr x y). exact (pr2 r p @ ! pr2 r q).
Defined.

Lemma isapropcoprod (P Q : UU) :
  isaprop P -> isaprop Q -> (P -> Q -> ∅) -> isaprop (P ⨿ Q).
Proof.
  intros ? ? i j n. apply invproofirrelevance.
  intros a b. apply inv_equality_by_case.
  induction a as [a|a].
  - induction b as [b|b].
    + apply i.
    + contradicts (n a) b.
  - induction b as [b|b].
    + contradicts (n b) a.
    + apply j.
Defined.

Lemma isweqimplimpl {X Y : UU} (f : X -> Y) (g : Y -> X) (isx : isaprop X)
      (isy : isaprop Y) : isweq f.
Proof.
  intros.
  assert (isx0: ∏ x : X, paths (g (f x)) x)
         by (intro; apply proofirrelevance; apply isx).
  assert (isy0 : ∏ y : Y, paths (f (g y)) y)
         by (intro; apply proofirrelevance; apply isy).
  apply (gradth f g isx0 isy0).
Defined.

Definition weqimplimpl {X Y : UU} (f : X -> Y) (g : Y -> X) (isx : isaprop X)
           (isy : isaprop Y) := weqpair _ (isweqimplimpl f g isx isy).

Definition weqiff {X Y : UU} : (X <-> Y) -> isaprop X -> isaprop Y -> X ≃ Y
  := λ f i j, weqpair _ (isweqimplimpl (pr1 f) (pr2 f) i j).

Definition weq_to_iff {X Y : UU} : X ≃ Y -> (X <-> Y)
  := λ f, (pr1weq f ,, invmap f).

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros x x'. induction x. Defined.

Theorem isapropifnegtrue {X : UU} (a : X -> empty) : isaprop X.
Proof.
  intros. set (w := weqpair _ (isweqtoempty a)).
  apply (isofhlevelweqb 1 w isapropempty).
Defined.

Lemma isapropretract {P Q : UU} (i : isaprop Q) (f : P -> Q) (g : Q -> P)
      (h : g ∘ f ~ idfun _) : isaprop P.
Proof.
  intros.
  apply invproofirrelevance; intros p p'.
  refine (_ @ (_ : g (f p) = g (f p')) @ _).
  - apply pathsinv0. apply h.
  - apply maponpaths. apply proofirrelevance. exact i.
  - apply h.
Defined.

Lemma isapropcomponent1 (P Q : UU) : isaprop (P ⨿ Q) -> isaprop P.
Proof.
  (* see also [isofhlevelsnsummand1] *)
  intros ? ? i. apply invproofirrelevance; intros p p'.
  exact (equality_by_case (proofirrelevance _ i (ii1 p) (ii1 p'))).
Defined.

Lemma isapropcomponent2 (P Q : UU) : isaprop (P ⨿ Q) -> isaprop Q.
Proof.
  (* see also [isofhlevelsnsummand2] *)
  intros ? ? i. apply invproofirrelevance; intros q q'.
  exact (equality_by_case (proofirrelevance _ i (ii2 q) (ii2 q'))).
Defined.

(** *** Inclusions - functions of h-level 1 *)


Definition isincl {X Y : UU} (f : X -> Y) := isofhlevelf 1 f.

Definition incl (X Y : UU) := total2 (fun f : X -> Y => isincl f).
Definition inclpair {X Y : UU} (f : X -> Y) (is : isincl f) :
  incl X Y := tpair _ f is.
Definition pr1incl (X Y : UU) : incl X Y -> (X -> Y) := @pr1 _ _.
Coercion pr1incl : incl >-> Funclass.

Lemma isinclweq (X Y : UU) (f : X -> Y) : isweq f -> isincl f.
Proof. intros X Y f is. apply (isofhlevelfweq 1 (weqpair _ is)). Defined.
Coercion isinclweq : isweq >-> isincl.

Lemma isofhlevelfsnincl (n : nat) {X Y : UU} (f : X -> Y) (is : isincl f) :
  isofhlevelf (S n) f.
Proof.
  intros. unfold isofhlevelf. intro y.
  apply isofhlevelsnprop.
  apply (is y).
Defined.

Definition weqtoincl (X Y : UU) : X ≃ Y -> incl X Y
  := λ w, inclpair (pr1weq w) (pr2 w).
Coercion weqtoincl : weq >-> incl.

Lemma isinclcomp {X Y Z : UU} (f : incl X Y) (g : incl Y Z) :
  isincl (funcomp (pr1 f) (pr1 g)).
Proof. intros. apply (isofhlevelfgf 1 f g (pr2 f) (pr2 g)). Defined.

Definition inclcomp {X Y Z : UU} (f : incl X Y) (g : incl Y Z) :
  incl X Z := inclpair (funcomp (pr1 f) (pr1 g)) (isinclcomp f g).

Lemma isincltwooutof3a {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (isg : isincl g)
      (isgf : isincl (funcomp f g)) : isincl f.
Proof.
  intros.
  apply (isofhlevelff 1 f g isgf).
  apply (isofhlevelfsnincl 1 g isg).
Defined.

Lemma isinclgwtog {X Y Z : UU} (w : X ≃ Y) (g : Y -> Z)
      (is : isincl (funcomp w g)) : isincl g.
Proof. intros. apply (isofhlevelfgwtog 1 w g is). Defined.

Lemma isinclgtogw {X Y Z : UU}  (w : X ≃ Y) (g : Y -> Z) (is : isincl g) :
  isincl (funcomp w g).
Proof. intros. apply (isofhlevelfgtogw 1 w g is). Defined.


Lemma isinclhomot {X Y : UU} (f g : X -> Y) (h : homot f g) (isf : isincl f) :
  isincl g.
Proof. intros. apply (isofhlevelfhomot (S O) f g h isf). Defined.



Definition isofhlevelsninclb (n : nat) {X Y : UU} (f : X -> Y) (is : isincl f) :
  isofhlevel (S n) Y -> isofhlevel (S n) X
  := isofhlevelXfromfY (S n) f (isofhlevelfsnincl n f is).

Definition isapropinclb {X Y : UU} (f : X -> Y) (isf : isincl f) :
  isaprop Y -> isaprop X := isofhlevelXfromfY 1 _ isf.


Lemma iscontrhfiberofincl {X Y : UU} (f : X -> Y) :
  isincl f -> (∏ x : X, iscontr (hfiber f (f x))).
Proof.
  intros X Y f X0 x. unfold isofhlevelf in X0.
  set (isy := X0 (f x)).
  apply (iscontraprop1 isy (hfiberpair f _ (idpath (f x)))).
Defined.

(* see incl_injectivity for the equivalence between isincl and isInjective *)
Definition isInjective {X Y : UU} (f : X -> Y)
  := ∏ (x x' : X), isweq (maponpaths f : x = x' -> f x = f x').

Definition Injectivity {X Y : UU} (f : X -> Y) :
  isInjective f -> ∏ (x x' : X), x = x'  ≃  f x = f x'.
Proof. intros ? ? ? i ? ?. exact (weqpair _ (i x x')). Defined.

Lemma isweqonpathsincl {X Y : UU} (f : X -> Y) : isincl f -> isInjective f.
Proof. intros ? ? ? is x x'. apply (isofhlevelfonpaths O f x x' is). Defined.

Definition weqonpathsincl {X Y : UU} (f : X -> Y) (is : isincl f) (x x' : X)
  := weqpair _ (isweqonpathsincl f is x x').

Definition invmaponpathsincl {X Y : UU} (f : X -> Y) :
  isincl f -> ∏ x x', f x = f x' -> x = x'.
Proof.
  intros ? ? ? is x x'.
  exact (invmap (weqonpathsincl f is x x')).
Defined.

Lemma isinclweqonpaths {X Y : UU} (f : X -> Y) : isInjective f -> isincl f.
Proof. intros X Y f X0. apply (isofhlevelfsn O f X0). Defined.

Definition isinclpr1 {X : UU} (P : X -> UU) (is : ∏ x : X, isaprop (P x)) :
  isincl (@pr1 X P):= isofhlevelfpr1 (S O) P is.

Theorem subtypeInjectivity {A : UU} (B : A -> UU) :
  isPredicate B -> ∏ (x y : total2 B), (x = y) ≃ (pr1 x = pr1 y).
Proof.
  intros. apply Injectivity. apply isweqonpathsincl. apply isinclpr1. exact X.
Defined.

Corollary subtypeEquality {A : UU} {B : A -> UU} (is : isPredicate B)
   {s s' : total2 (λ x, B x)} : pr1 s = pr1 s' -> s = s'.
Proof.
  intros A B H s s'. apply invmap. apply subtypeInjectivity. exact H.
Defined.

Corollary subtypeEquality' {A : UU} {B : A -> UU}
   {s s' : total2 (λ x, B x)} : pr1 s = pr1 s' -> isaprop (B (pr1 s')) -> s = s'.
(* This variant of subtypeEquality is not often needed. *)
Proof. intros ? ? ? ? e is. apply (total2_paths_f e). apply is. Defined.

(* This corollary of subtypeEquality is used for categories. *)
Corollary unique_exists {A : UU} {B : A -> UU} (x : A) (b : B x)
          (h : ∏ y, isaprop (B y)) (H : ∏ y, B y -> y = x) :
  iscontr (total2 (λ t : A, B t)).
Proof.
  intros A B x b h H.
  use iscontrpair.
  exact (x,,b).
  intros t.
  apply subtypeEquality'.
  apply (H (pr1 t)). apply (pr2 t).
  apply (h (pr1 (x,,b))).
Defined.

Definition subtypePairEquality {X : UU} {P : X -> UU} (is : isPredicate P)
           {x y : X} {p : P x} {q : P y} :
  x = y -> (x,,p) = (y,,q).
Proof. intros X P is x y p q e. apply (two_arg_paths_f e). apply is. Defined.

Definition subtypePairEquality' {X : UU} {P : X -> UU}
           {x y : X} {p : P x} {q : P y} :
  x = y -> isaprop(P y) -> (x,,p) = (y,,q).
(* This variant of subtypePairEquality is never needed. *)
Proof. intros X P x y p q e is. apply (two_arg_paths_f e). apply is. Defined.

Theorem samehfibers {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (is1 : isincl g)
        (y : Y) :  hfiber f y ≃ hfiber (g ∘ f) (g y).
Proof.
  intros. exists (hfibersftogf f g (g y) (hfiberpair g y (idpath _))).
  set (z := g y). set (ye := hfiberpair g y (idpath _)). intro xe.
  apply (iscontrweqf (X := hfibersgftog f g z xe = ye)).
  { exists (ezmap _ _ _ (fibseq1 _ _ _ (fibseqhf f g z ye) _)).
    exact (isweqezmap1 _ _ _ _ _). }
  apply isapropifcontr. apply iscontrhfiberofincl. exact is1.
Defined.

(** *** Basics about types of h-level 2 - "sets" *)

Definition isaset (X : UU) : UU := ∏ x x' : X, isaprop (x = x').

(* Definition isaset := isofhlevel 2. *)

Notation isasetdirprod := (isofhleveldirprod 2).

Lemma isasetunit : isaset unit.
Proof. apply (isofhlevelcontr 2 iscontrunit). Defined.

Lemma isasetempty : isaset empty.
Proof. apply (isofhlevelsnprop 1 isapropempty). Defined.

Lemma isasetifcontr {X : UU} (is : iscontr X) : isaset X.
Proof. intros. apply (isofhlevelcontr 2 is). Defined.

Lemma isasetaprop {X : UU} (is : isaprop X) : isaset X.
Proof. intros. apply (isofhlevelsnprop 1 is). Defined.

Corollary isaset_total2 {X : UU} (P : X->UU) :
  isaset X -> (∏ x, isaset (P x)) -> isaset (∑ x, P x).
Proof. intros. apply (isofhleveltotal2 2); assumption. Defined.

Corollary isaset_dirprod {X Y : UU} : isaset X -> isaset Y -> isaset (X × Y).
Proof. intros. apply isaset_total2. assumption. intro. assumption. Defined.

Corollary isaset_hfiber {X Y : UU} (f : X -> Y) (y : Y) : isaset X -> isaset Y -> isaset (hfiber f y).
Proof. intros X Y f y isX isY. apply isaset_total2. assumption. intro. apply isasetaprop. apply isY. Defined.

(** The following lemma asserts "uniqueness of identity proofs" (uip) for
  sets. *)

Lemma uip {X : UU} (is : isaset X) {x x' : X} (e e' : x = x') : e = e'.
Proof. intros. apply (proofirrelevance _ (is x x') e e'). Defined.

(** For the theorem about the coproduct of two sets see [ isasetcoprod ]
  below. *)


Lemma isofhlevelssnset (n : nat) (X : UU) (is : isaset X) :
  isofhlevel (S (S n)) X.
Proof.
  intros n X X0. simpl. unfold isaset in X0. intros x x'.
  apply isofhlevelsnprop.
  exact (X0 x x').
Defined.

Lemma isasetifiscontrloops (X : UU) : (∏ x : X, iscontr (x = x)) -> isaset X.
Proof.
  intros X X0. unfold isaset. unfold isofhlevel. intros x x' x0 x0'.
  induction x0.
  apply isapropifcontr.
  exact (X0 x).
Defined.

Lemma iscontrloopsifisaset (X : UU) :
  (isaset X) -> (∏ x : X, iscontr (x = x)).
Proof.
  intros X X0 x. unfold isaset in X0. unfold isofhlevel in X0.
  change (∏ (x x' : X) (x0 x'0 : x = x'), iscontr (x0 = x'0))
  with (∏ (x x' : X), isaprop (x = x')) in X0.
  apply (iscontraprop1 (X0 x x) (idpath x)).
Defined.



(**  A monic subtype of a set is a set. *)

Theorem isasetsubset {X Y : UU} (f : X -> Y) (is1 : isaset Y) (is2 : isincl f) :
  isaset X.
Proof. intros. apply (isofhlevelsninclb (S O) f is2). apply is1. Defined.



(** The morphism from hfiber of a map to a set is an inclusion. *)

Theorem isinclfromhfiber {X Y : UU} (f: X -> Y) (is : isaset Y) (y : Y) :
  @isincl (hfiber f y) X (@pr1 _ _).
Proof. intros. refine (isofhlevelfhfiberpr1 _ _ _ _). assumption. Defined.


(** Criterion for a function between sets being an inclusion.  *)


Theorem isinclbetweensets {X Y : UU} (f : X -> Y)
        (isx : isaset X) (isy : isaset Y)
        (inj : ∏ x x' : X , (paths (f x) (f x') -> x = x')) : isincl f.
Proof.
  intros. apply isinclweqonpaths. intros x x'.
  apply (isweqimplimpl (@maponpaths _ _ f x x') (inj x x') (isx x x')
                       (isy (f x) (f x'))).
Defined.

(** A map from [ unit ] to a set is an inclusion. *)

Theorem isinclfromunit {X : UU} (f : unit -> X) (is : isaset X) : isincl f.
Proof.
  intros.
  apply (isinclbetweensets f (isofhlevelcontr 2 (iscontrunit)) is).
  intros. induction x. induction x'. apply idpath.
Defined.




Corollary set_bijection_to_weq {X Y : UU} (f : X -> Y) :
  UniqueConstruction f -> isaset Y -> isweq f.
Proof.
  (* compare with bijection_to_weq: this one doesn't use gradth *)
  intros ? ? ? bij i y. set (sur := pr1 bij); set (inj := pr2 bij).
  use tpair.
  - exists (pr1 (sur y)). exact (pr2 (sur y)).
  - intro w.
    use total2_paths_f.
    + simpl. apply inj. intermediate_path y.
      * exact (pr2 w).
      * exact (! pr2 (sur y)).
    + induction w as [x e]; simpl. induction e.
      apply i.
Defined.

(** *** Propositions equivalent to negations of propositions *)

Definition negProp P := ∑ Q, isaprop Q × (¬P <-> Q).

Definition negProp_to_type {P} (negP : negProp P) := pr1 negP.

Coercion negProp_to_type : negProp >-> UU.

Definition negProp_to_isaprop {P} (nP : negProp P) : isaprop nP
  := pr1 (pr2 nP).

Definition negProp_to_iff {P} (nP : negProp P) : ¬P <-> nP
  := pr2 (pr2 nP).

Definition negProp_to_neg {P} {nP : negProp P} : nP -> ¬P.
Proof. intros ? ? np. exact (pr2 (negProp_to_iff nP) np). Defined.

Coercion negProp_to_neg : negProp >-> Funclass.

Definition neg_to_negProp {P} {nP : negProp P} : ¬P -> nP.
Proof. intros ? ? np. exact (pr1 (negProp_to_iff nP) np). Defined.

Definition negPred {X:UU} (x  :X) (P:∏ y:X, UU)      := ∏ y  , negProp (P y).

Definition negReln {X:UU}         (P:∏ (x y:X), UU)  := ∏ x y, negProp (P x y).

Definition neqProp {X:UU} (x y:X) :=            negProp (x=y).

Definition neqPred {X:UU} (x  :X) := ∏ y,       negProp (x=y).

Definition neqReln (X:UU)         := ∏ (x y:X), negProp (x=y).

(** Complementary types *)

Definition complementary P Q := (P -> Q -> ∅) × (P ⨿ Q).

Definition complementary_to_neg_iff {P Q} : complementary P Q -> ¬P <-> Q.
Proof.
  intros ? ? c.
  induction c as [n c]. split.
  - intro np. induction c as [p|q].
    * contradicts p np.
    * exact q.
  - intro q. induction c as [p|_].
    * intros _. exact (n p q).
    * intros p. exact (n p q).
Defined.

Definition decidable (X:UU) := X ⨿ ¬X.

Definition decidable_to_complementary {X} : decidable X -> complementary X (¬X).
Proof.
  intros ? d. split.
  - intros x n. exact (n x).
  - exact d.
Defined.

Definition decidable_dirprod (X Y : UU) :
  decidable X -> decidable Y -> decidable (X × Y).
Proof.
  intros ? ? b c.
  induction b as [b|b'].
  - induction c as [c|c'].
    + apply ii1. exact (b,,c).
    + apply ii2. clear b. intro k. apply c'. exact (pr2 k).
  - clear c. apply ii2. intro k. apply b'. exact (pr1 k).
Defined.

Lemma negProp_to_complementary P (Q:negProp P) : P ⨿ Q <-> complementary P Q.
Proof.
  intros ? [Q [i [r s]]]; simpl in *.
  split.
  * intros pq. split.
    - intros p q. apply s.
      + assumption.
      + assumption.
    - assumption.
      * intros [j c].
        assumption.
Defined.

Lemma negProp_to_uniqueChoice P (Q:negProp P) : (isaprop P × (P ⨿ Q)) <-> iscontr (P ⨿ Q).
Proof.
  intros ? [Q [j [r s]]]; simpl in *. split.
  * intros [i v]. exists v. intro w.
    induction v as [v|v].
    - induction w as [w|w].
      + apply maponpaths, i.
      + contradicts (s w) v.
    - induction w as [w|w].
      + contradicts (s v) w.
      + apply maponpaths, j.
  * intros [c e]. split.
    - induction c as [c|c].
      + apply invproofirrelevance; intros p p'.
        exact (equality_by_case (e (ii1 p) @ !e (ii1 p'))).
      + apply invproofirrelevance; intros p p'.
        contradicts (s c) p.
    - exact c.
Defined.

(** *** Decidable propositions [ isdecprop ] *)

Definition isdecprop (P:UU) := (P ⨿ ¬P) × isaprop P.

Definition isdecproptoisaprop ( X : UU ) ( is : isdecprop X ) : isaprop X := pr2 is.
Coercion isdecproptoisaprop : isdecprop >-> isaprop .

Lemma isdecpropif ( X : UU ) : isaprop X -> X ⨿ ¬ X -> isdecprop X.
Proof. intros ? i c. exact (c,,i). Defined.

Lemma isdecpropfromiscontr {P} : iscontr P -> isdecprop P.
Proof.
  intros ? i.
  split.
  - exact (ii1 (iscontrpr1 i)).
  - apply isapropifcontr. assumption.
Defined.

Lemma isdecpropempty : isdecprop ∅.
Proof.
  unfold isdecprop.
  split.
  - exact (ii2 (idfun ∅)).
  - exact isapropempty.
Defined.

Lemma isdecpropweqf {X Y} : X≃Y -> isdecprop X -> isdecprop Y.
Proof.
  intros ? ? w i. unfold isdecprop in *. induction i as [xnx i]. split.
  - clear i. induction xnx as [x|nx].
    * apply ii1. apply w. assumption.
    * apply ii2. intro x'. apply nx. apply (invmap w). assumption.
  - apply (isofhlevelweqf 1 (X:=X)).
    { exact w. }
    { exact i. }
Defined.

Lemma isdecpropweqb {X Y} : X≃Y -> isdecprop Y -> isdecprop X.
Proof.
  intros ? ? w i. unfold isdecprop in *. induction i as [yny i]. split.
  - clear i. induction yny as [y|ny].
    * apply ii1. apply (invmap w). assumption.
    * apply ii2. intro x. apply ny. apply w. assumption.
  - apply (isofhlevelweqb 1 (Y:=Y)).
    { exact w. }
    { exact i. }
Defined.

Lemma isdecproplogeqf {X Y : UU} (isx : isdecprop X) (isy : isaprop Y)
      (lg : X <-> Y) : isdecprop Y.
Proof.
  intros.
  set (w := weqimplimpl (pr1 lg) (pr2 lg) isx isy).
  apply (isdecpropweqf w isx).
Defined.

Lemma isdecproplogeqb {X Y : UU} (isx : isaprop X) (isy : isdecprop Y)
      (lg : X <-> Y) : isdecprop X.
Proof.
  intros.
  set (w := weqimplimpl (pr1 lg) (pr2 lg) isx isy).
  apply (isdecpropweqb w isy).
Defined.

Lemma isdecpropfromneg {P : UU} : ¬P -> isdecprop P.
Proof.
  intros ? n. split.
  - exact (ii2 n).
  - apply isapropifnegtrue. assumption.
Defined.

(** *** Types with decidable equality *)

Definition isdeceq (X:UU) : UU := ∏ (x x':X), decidable (x=x').

Lemma isdeceqweqf {X Y : UU} (w : X ≃ Y) (is : isdeceq X) : isdeceq Y.
Proof.
  intros. intros y y'.
  set (w' := weqonpaths (invweq w) y y').
  set (int := is ((invweq w) y) ((invweq w) y')).
  induction int as [ i | ni ].
  - apply (ii1 ((invweq w') i)).
  - apply (ii2 ((negf w') ni)).
Defined.

Lemma isdeceqweqb {X Y : UU} (w : X ≃ Y) (is : isdeceq Y) : isdeceq X.
Proof. intros. apply (isdeceqweqf (invweq w) is). Defined.

Theorem isdeceqinclb {X Y : UU} (f : X -> Y) (is : isdeceq Y) (is' : isincl f) :
  isdeceq X.
Proof.
  intros. intros x x'.
  set (w := weqonpathsincl f is' x x'). set (int := is (f x) (f x')).
  induction int as [ i | ni ].
  - apply (ii1 ((invweq w) i)).
  - apply (ii2 ((negf w) ni)).
Defined.

Lemma isdeceqifisaprop (X : UU) : isaprop X -> isdeceq X.
Proof.
  intros X is. intros x x'. apply (ii1 (proofirrelevance _ is x x')).
Defined.

Definition booleq {X : UU} (is : isdeceq X) (x x' : X) : bool.
Proof. intros. induction (is x x'). apply true. apply false. Defined.

Lemma eqfromdnegeq (X : UU) (is : isdeceq X) (x x' : X) :
  dneg (x = x') -> x = x'.
Proof.
  intros X is x x' X0. induction (is x x') as [ y | n ].
  - assumption.
  - induction (X0 n).
Defined.

Lemma isdecequnit : isdeceq unit.
Proof. apply (isdeceqifisaprop _ isapropunit). Defined.

Theorem isdeceqbool: isdeceq bool.
Proof.
  unfold isdeceq. intros x' x. induction x.
  - induction x'.
    + apply (ii1 (idpath true)).
    + apply (ii2 nopathsfalsetotrue).
  - induction x'.
    + apply (ii2 nopathstruetofalse).
    + apply (ii1 (idpath false)).
Defined.

Lemma isdeceqcoprod {A B : UU} (h1 : isdeceq A) (h2 : isdeceq B) :
  isdeceq (A ⨿ B).
Proof.
intros A B h1 h2 ab ab'.
induction ab as [a|b]; induction ab' as [a'|b'].
- induction (h1 a a') as [p|p].
  + apply inl, (maponpaths (@ii1 A B) p).
  + apply inr; intro H; apply (p (ii1_injectivity _ _ H)).
- apply inr, negpathsii1ii2.
- apply inr, negpathsii2ii1.
- induction (h2 b b') as [p|p].
  + apply inl, (maponpaths (@ii2 A B) p).
  + apply inr; intro H; apply (p (ii2_injectivity _ _ H)).
Defined.


(** *** Isolated points *)

Definition isisolated (X:UU) (x:X) := ∏ x':X, (x = x') ⨿ (x != x').
Definition isisolated_ne (X:UU) (x:X) (neq_x:neqPred x) := ∏ y:X, (x=y) ⨿ neq_x y.

Definition isisolated_to_isisolated_ne {X x neq_x} :
  isisolated X x -> isisolated_ne X x neq_x.
Proof.
  intros ? ? ? i y. induction (i y) as [eq|ne].
  - exact (ii1 eq).
  - apply ii2. apply neg_to_negProp. assumption.
Defined.

Definition isisolated_ne_to_isisolated {X x neq_x} :
  isisolated_ne X x neq_x -> isisolated X x.
Proof.
  intros ? ? ? i y. induction (i y) as [eq|ne].
  - exact (ii1 eq).
  - apply ii2. use negProp_to_neg.
    + exact (neq_x y).
    + exact ne.
Defined.

Definition isolated ( T : UU ) := ∑ t:T, isisolated _ t.
Definition isolated_ne ( T : UU ) (neq:neqReln T) := ∑ t:T, isisolated_ne _ t (neq t).

Definition isolatedpair ( T : UU ) (t:T) (i:isisolated _ t) : isolated T
  := (t,,i).
Definition isolatedpair_ne (T : UU) (t:T) (neq:neqReln T) (i:isisolated_ne _ t (neq t)) :
  isolated_ne T neq
  := (t,,i).

Definition pr1isolated ( T : UU ) (x:isolated T) : T := pr1 x.
Definition pr1isolated_ne ( T : UU ) (neq:neqReln T) (x:isolated_ne T neq) : T := pr1 x.

Theorem isaproppathsfromisolated (X : UU) (x : X) (is : isisolated X x) :
  ∏ x', isaprop(x = x').
Proof.
  intros. apply iscontraprop1inv. intro e. induction e.
  set (f := λ e : x = x, coconusfromtpair _ e).
  assert (is' : isweq f)
    by apply (onefiber (λ x' : X, x = x') (x : X) (λ x' : X, is x')).
  assert (is2 : iscontr (coconusfromt _ x))
    by apply iscontrcoconusfromt.
  apply (iscontrweqb (weqpair f is')).
  assumption.
Defined.

Local Open Scope transport.

Theorem isaproppathsfromisolated_ne (X : UU) (x : X) (neq_x : neqPred x)
        (is : isisolated_ne X x neq_x) (y : X)
  : isaprop (x = y).
Proof.
  (* we could follow the proof of isaproppathsfromisolated here, but we try a
     different way *)
  intros. unfold isisolated_ne in is. apply invproofirrelevance; intros m n.
  set (Q y := (x = y) ⨿ (neq_x y)).
  assert (a := (transport_section is m) @ !(transport_section is n)).
  induction (is x) as [j|k].
  - assert (b := transport_map (λ y p, ii1 p : Q y) m j); simpl in b;
      assert (c := transport_map (λ y p, ii1 p : Q y) n j); simpl in c.
    assert (d := equality_by_case (!b @ a @ c)); simpl in d.
    rewrite 2? transportf_id1 in d. apply (pathscomp_cancel_left j). assumption.
  - contradicts (neq_x x k) (idpath x).
Defined.

Theorem isaproppathstoisolated (X : UU) (x : X) (is : isisolated X x) :
  ∏ x' : X, isaprop (x' = x).
Proof.
  intros.
  apply (isofhlevelweqf 1 (weqpathsinv0 x x')
                        (isaproppathsfromisolated X x is x')).
Defined.

Lemma isisolatedweqf { X Y : UU } (f : X ≃ Y) (x:X) : isisolated X x -> isisolated Y (f x).
Proof.
  intros ? ? ? ? is. unfold isisolated. intro y.
  induction (is (invmap f y)) as [ eq | ne ].
  { apply ii1. apply pathsweq1'. assumption. }
  { apply ii2. intro eq. apply ne; clear ne. apply pathsweq1. assumption. }
Defined.

Theorem isisolatedinclb {X Y : UU} (f : X -> Y) (is : isincl f) (x : X)
        (is0 : isisolated _ (f x)) : isisolated _ x.
Proof.
  intros. unfold isisolated. intro x'. set (a := is0 (f x')).
  induction a as [ a1 | a2 ]. apply (ii1 (invmaponpathsincl f is _ _ a1)).
  apply (ii2 ((negf (@maponpaths _ _ f _ _)) a2)).
Defined.

Lemma disjointl1 (X : UU) : isisolated (coprod X unit) (ii2 tt).
Proof.
  intros. unfold isisolated. intros x'. induction x' as [ x | u ].
  apply (ii2 (negpathsii2ii1 x tt)). induction u.
  apply (ii1 (idpath _)).
Defined.

(** *** Decidable types are sets *)

Theorem isasetifdeceq (X : UU) : isdeceq X -> isaset X.
Proof.
  intro X. intro is. intros x x'. apply (isaproppathsfromisolated X x (is x)).
Defined.

(** *** Decidable equality on a sigma type *)
Lemma isdeceq_total2 {X : UU} {P : X -> UU}
  : isdeceq X -> (∏ x : X, isdeceq (P x)) → isdeceq (∑ x : X, P x).
Proof.
  intros X P HX HP.
  intros xp yq.
  induction (HX (pr1 xp) (pr1 yq)) as [e_xy | ne_xy].
  - induction ((HP _) (transportf _ e_xy (pr2 xp)) (pr2 yq)) as [e_pq | ne_pq].
    + apply inl. exact (total2_paths_f e_xy e_pq).
    + apply inr. intro e_xpyq. apply ne_pq.
      set (e_pq := fiber_paths e_xpyq).
      refine (_ @ e_pq).
      refine (maponpaths (λ e, transportf _ e _) _).
  (* NOTE: want [maponpaths_2] from the [TypeTheory] library here. Upstream it to [Foundations], perhaps? *)
      apply isasetifdeceq, HX.
  - apply inr. intros e_xypq. apply ne_xy, base_paths, e_xypq.
Defined.


(** *** Construction of functions with specified values at a few isolated points *)

Definition isolfun1 {X Y:UU} (x1:X) (i1 : isisolated _ x1) (y1 y':Y) : X → Y.
Proof.
  intros ? ? ? ? ? ? x.
  induction (i1 x).
  - exact y1.
  - exact y'.
Defined.

Definition decfun1 {X Y:UU} (i : isdeceq X) (x1:X) (y1 y':Y) : X → Y.
Proof.
  intros ? ? ? ?.
  exact (isolfun1 x1 (i x1)).
Defined.

Definition isolfun2 {X Y:UU} (x1 x2:X) (i1 : isisolated _ x1) (i2 : isisolated _ x2) (y1 y2 y':Y) : X → Y.
Proof.
  intros ? ? ? ? ? ? ? ? ? x.
  induction (i1 x).
  - exact y1.
  - induction (i2 x).
    + exact y2.
    + exact y'.
Defined.

Definition decfun2 {X Y:UU} (i : isdeceq X) (x1 x2:X) (y1 y2 y':Y) : X → Y.
Proof.
  intros ? ? ? ? ?.
  exact (isolfun2 x1 x2 (i x1) (i x2)).
Defined.

Definition isolfun3 {X Y:UU} (x1 x2 x3:X) (i1 : isisolated _ x1) (i2 : isisolated _ x2) (i3 : isisolated _ x3) (y1 y2 y3 y':Y) : X → Y.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? x.
  induction (i1 x).
  - exact y1.
  - induction (i2 x).
    + exact y2.
    + induction (i3 x).
      * exact y3.
      * exact y'.
Defined.

Definition decfun3 {X Y:UU} (i : isdeceq X) (x1 x2 x3:X) (y1 y2 y3 y':Y) : X → Y.
  intros ? ? ? ? ? ?.
  exact (isolfun3 x1 x2 x3 (i x1) (i x2) (i x3)).
Defined.

(** **** [ bool ] is a set *)

Theorem isasetbool: isaset bool.
Proof. apply (isasetifdeceq _ isdeceqbool). Defined.

(** ** Splitting of [ X ] into a coproduct defined by a function [ X -> bool ] *)


Definition subsetsplit {X : UU} (f : X -> bool) (x : X) :
  (hfiber f true) ⨿ (hfiber f false).
Proof.
  intros. induction (boolchoice (f x)) as [ a | b ].
  - apply (ii1 (hfiberpair f x a)).
  - apply (ii2 (hfiberpair f x b)).
Defined.

Definition subsetsplitinv {X : UU} (f : X -> bool)
           (ab : (hfiber f true) ⨿ (hfiber f false)) : X
  := match ab with ii1 xt => pr1 xt | ii2 xf => pr1 xf end.

Theorem weqsubsetsplit {X : UU} (f : X -> bool) :
  weq X ((hfiber f true) ⨿ (hfiber f false)).
Proof.
  intros.
  set (ff := subsetsplit f). set (gg := subsetsplitinv f).
  split with ff.
  assert (egf : ∏ a : _, paths (gg (ff a)) a).
  {
    intros. unfold ff. unfold subsetsplit.
    induction (boolchoice (f a)) as [ et | ef ]. simpl. apply idpath. simpl.
    apply idpath.
  }
  assert (efg : ∏ a : _, paths (ff (gg a)) a).
  {
    intros. induction a as [ et | ef ].
    - induction et as [ x et' ]. simpl. unfold ff. unfold subsetsplit.
      induction (boolchoice (f x)) as [ e1 | e2 ].
      + apply (maponpaths (@ii1 _ _ )). apply (maponpaths (hfiberpair f x)).
        apply uip. apply isasetbool.
      + induction (nopathstruetofalse (pathscomp0 (pathsinv0 et') e2)).
    - induction ef as [ x et' ]. simpl. unfold ff. unfold subsetsplit.
      induction (boolchoice (f x)) as [ e1 | e2 ].
      + induction (nopathsfalsetotrue (pathscomp0 (pathsinv0 et') e1)).
      + apply (maponpaths (@ii2 _ _ )). apply (maponpaths (hfiberpair f x)).
        apply uip. apply isasetbool.
  }
  apply (gradth _ _ egf efg).
Defined.

(* End of file *)
