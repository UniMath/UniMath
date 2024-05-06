(** For some examples, see [UniMath.NumberSystems.NaturalNumbersAlgebra] *)
(** *** Abelian (commutative) monoids *)
(**
 - Abelian (commutative) monoids
  - Basic definitions
  - Univalence for abelian monoids
  - Subobjects
  - Quotient objects
  - Direct products
  - Monoid of fractions of an abelian monoid
  - Canonical homomorphism to the monoid of fractions
  - Abelian monoid of fractions in the case when elements of the
    localization submonoid are cancelable
  - Relations on the abelian monoid of fractions
  - Relations and canonical homomorphism to [abmonoidfrac]
*)

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.

Require Import UniMath.Algebra.Monoids2.

Declare Scope addmonoid.
Delimit Scope addmonoid with addmonoid.
Notation "x + y" := (op x y) : addmonoid.
Notation "0" := (unel _) : addmonoid.

(** **** Basic definitions *)

Local Open Scope addmonoid.

Definition abmonoid : UU := ∑ (X : setwithbinop), isabmonoidop (@op X).

Definition make_abmonoid (t : setwithbinop) (H : isabmonoidop (@op t))
  : abmonoid
  := t ,, H.

Definition abmonoidtomonoid : abmonoid  → monoid :=
  λ X, make_monoid (pr1 X) (pr1 (pr2 X)).
Coercion abmonoidtomonoid : abmonoid >-> monoid.

Definition commax (X : abmonoid) : iscomm (@op X) := pr2 (pr2 X).

Definition abmonoidrer (X : abmonoid) (a b c d : X) :
  (a + b) + (c + d) = (a + c) + (b + d) := abmonoidoprer (pr2 X) a b c d.

Definition abmonoid_of_monoid (X : monoid) (H : iscomm (@op X)) : abmonoid :=
  make_abmonoid X (make_isabmonoidop (pr2 X) H).


(** **** Construction of the trivial abmonoid consisting of one element given by unit. *)

Definition unitabmonoid_isabmonoid : isabmonoidop (@op unitmonoid).
Proof.
  use make_isabmonoidop.
  - exact unitmonoid_ismonoid.
  - intros x x'. use isProofIrrelevantUnit.
Qed.

Definition unitabmonoid : abmonoid := make_abmonoid unitmonoid unitabmonoid_isabmonoid.

Lemma abmonoidfuntounit_ismonoidfun (X : abmonoid) : ismonoidfun (Y := unitabmonoid) (λ x : X, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use isProofIrrelevantUnit.
  - use isProofIrrelevantUnit.
Qed.

Definition abmonoidfuntounit (X : abmonoid) : monoidfun X unitabmonoid :=
  monoidfunconstr (abmonoidfuntounit_ismonoidfun X).

Lemma abmonoidfunfromunit_ismonoidfun (X : abmonoid) : ismonoidfun (Y := X) (λ x : unitabmonoid, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. exact (!runax X _).
  - use idpath.
Qed.

Definition abmonoidfunfromunit (X : abmonoid) : monoidfun unitabmonoid X :=
  monoidfunconstr (abmonoidfunfromunit_ismonoidfun X).

Lemma unelabmonoidfun_ismonoidfun (X Y : abmonoid) : ismonoidfun (Y := Y) (λ x : X, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. exact (!lunax _ _).
  - use idpath.
Qed.

Definition unelabmonoidfun (X Y : abmonoid) : monoidfun X Y :=
  monoidfunconstr (unelabmonoidfun_ismonoidfun X Y).


(** **** Abelian monoid structure on homsets
    If f g : X  → Y are morphisms of abelian monoids, then we define f + g to be the morphism
    (f + g)(x) = f(x) + g(x).
 *)

Lemma abmonoidshombinop_ismonoidfun {X Y : abmonoid} (f g : monoidfun X Y) :
  @ismonoidfun X Y (λ x : pr1 X, pr1 f x + pr1 g x).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun.
    intros x x'. cbn. rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
    rewrite (assocax Y). rewrite (assocax Y). use maponpaths.
    rewrite <- (assocax Y). rewrite <- (assocax Y).
    use (maponpaths (λ y : Y, y + pr1 g x')).
    use (commax Y).
  - refine (maponpaths (λ h : Y, pr1 f 0 + h)
                                (monoidfununel g) @ _).
    rewrite runax. exact (monoidfununel f).
Qed.

Definition abmonoidshombinop {X Y : abmonoid} : binop (monoidfun X Y) :=
  (λ f g, monoidfunconstr (abmonoidshombinop_ismonoidfun f g)).

Lemma abmonoidsbinop_runax {X Y : abmonoid} (f : monoidfun X Y) :
  abmonoidshombinop f (unelmonoidfun X Y) = f.
Proof.
  use monoidfun_paths. use funextfun. intros x. use (runax Y).
Qed.

Lemma abmonoidsbinop_lunax {X Y : abmonoid} (f : monoidfun X Y) :
  abmonoidshombinop (unelmonoidfun X Y) f = f.
Proof.
  use monoidfun_paths. use funextfun. intros x. use (lunax Y).
Qed.

Lemma abmonoidshombinop_assoc {X Y : abmonoid} (f g h : monoidfun X Y) :
  abmonoidshombinop (abmonoidshombinop f g) h = abmonoidshombinop f (abmonoidshombinop g h).
Proof.
  use monoidfun_paths. use funextfun. intros x. use assocax.
Qed.

Lemma abmonoidshombinop_comm {X Y : abmonoid} (f g : monoidfun X Y) :
  abmonoidshombinop f g = abmonoidshombinop g f.
Proof.
  use monoidfun_paths. use funextfun. intros x. use (commax Y).
Qed.

Lemma abmonoidshomabmonoid_ismonoidop (X Y : abmonoid) :
  @ismonoidop (make_hSet (monoidfun X Y) (isasetmonoidfun X Y))
              (λ f g : monoidfun X Y, abmonoidshombinop f g).
Proof.
  use make_ismonoidop.
  - intros f g h. exact (abmonoidshombinop_assoc f g h).
  - use make_isunital.
    + exact (unelmonoidfun X Y).
    + use make_isunit.
      * intros f. exact (abmonoidsbinop_lunax f).
      * intros f. exact (abmonoidsbinop_runax f).
Defined.

Lemma abmonoidshomabmonoid_isabmonoid (X Y : abmonoid) :
  @isabmonoidop (make_hSet (monoidfun X Y) (isasetmonoidfun X Y))
                (λ f g : monoidfun X Y, abmonoidshombinop f g).
Proof.
  use make_isabmonoidop.
  - exact (abmonoidshomabmonoid_ismonoidop X Y).
  - intros f g. exact (abmonoidshombinop_comm f g).
Defined.

Definition abmonoidshomabmonoid (X Y : abmonoid) : abmonoid.
Proof.
  use make_abmonoid.
  - use make_setwithbinop.
    + use make_hSet.
      * exact (monoidfun X Y).
      * exact (isasetmonoidfun X Y).
    + intros f g. exact (abmonoidshombinop f g).
  - exact (abmonoidshomabmonoid_isabmonoid X Y).
Defined.


(** **** (X = Y) ≃ (monoidiso X Y)
    We use the following composition

                      (X = Y) ≃ ((make_abmonoid' X) = (make_abmonoid' Y))
                              ≃ ((pr1 (make_abmonoid' X)) = (pr1 (make_abmonoid' Y)))
                              ≃ (monoidiso X Y)

    where the third weak equivalence is given by univalence for monoids, [monoid_univalence].
*)

Local Definition abmonoid' : UU := ∑ m : monoid, iscomm (@op m).

Local Definition make_abmonoid' (X : abmonoid) : abmonoid' :=
  (pr1 X ,, dirprod_pr1 (pr2 X)) ,, dirprod_pr2 (pr2 X).

Definition abmonoid_univalence_weq1 : abmonoid ≃ abmonoid' :=
  weqtotal2asstol (λ X : setwithbinop, ismonoidop (@op X))
                  (λ y : (∑ X : setwithbinop, ismonoidop op), iscomm (@op (pr1 y))).

Definition abmonoid_univalence_weq1' (X Y : abmonoid) :
  (X = Y) ≃ ((make_abmonoid' X) = (make_abmonoid' Y)) :=
  make_weq _ (@isweqmaponpaths abmonoid abmonoid' abmonoid_univalence_weq1 X Y).

Definition abmonoid_univalence_weq2 (X Y : abmonoid) :
  ((make_abmonoid' X) = (make_abmonoid' Y)) ≃ ((pr1 (make_abmonoid' X)) = (pr1 (make_abmonoid' Y))).
Proof.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque abmonoid_univalence_weq2.

Definition abmonoid_univalence_weq3 (X Y : abmonoid) :
  ((pr1 (make_abmonoid' X)) = (pr1 (make_abmonoid' Y))) ≃ (monoidiso X Y) :=
  monoid_univalence (pr1 (make_abmonoid' X)) (pr1 (make_abmonoid' Y)).

Definition abmonoid_univalence_map (X Y : abmonoid) : (X = Y)  → (monoidiso X Y).
Proof.
  intro e. induction e. exact (idmonoidiso X).
Defined.

Lemma abmonoid_univalence_isweq (X Y : abmonoid) : isweq (abmonoid_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (abmonoid_univalence_weq1' X Y)
                   (weqcomp (abmonoid_univalence_weq2 X Y) (abmonoid_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque abmonoid_univalence_isweq.

Definition abmonoid_univalence (X Y : abmonoid) : (X = Y) ≃ (monoidiso X Y)
  := make_weq
    (abmonoid_univalence_map X Y)
    (abmonoid_univalence_isweq X Y).


(** **** Subobjects *)

Definition subabmonoid (X : abmonoid) := submonoid X.
Identity Coercion id_subabmonoid : subabmonoid >-> submonoid.

Lemma iscommcarrier {X : abmonoid} (A : submonoid X) : iscomm (@op A).
Proof.
  intros a a'.
  apply (invmaponpathsincl _ (isinclpr1carrier A)).
  simpl. apply (pr2 (pr2 X)).
Qed.

Definition isabmonoidcarrier {X : abmonoid} (A : submonoid X) :
  isabmonoidop (@op A) := ismonoidcarrier A ,, iscommcarrier A.

Definition carrierofsubabmonoid {X : abmonoid} (A : subabmonoid X) : abmonoid.
Proof.
  unfold subabmonoid in A. split with A. apply isabmonoidcarrier.
Defined.
Coercion carrierofsubabmonoid : subabmonoid >-> abmonoid.

Definition subabmonoid_incl {X : abmonoid} (A : subabmonoid X) : monoidfun A X :=
submonoid_incl A.

(** **** Quotient objects *)

Lemma iscommquot {X : abmonoid} (R : binopeqrel X) : iscomm (@op (setwithbinopquot R)).
Proof.
  intros.
  set (X0 := setwithbinopquot R).
  intros x x'.
  apply (setquotuniv2prop R (λ x x' : X0, make_hProp _ (setproperty X0 (x + x') (x' + x)))).
  intros x0 x0'.
  apply (maponpaths (setquotpr R) ((commax X) x0 x0')).
Qed.

Definition isabmonoidquot {X : abmonoid} (R : binopeqrel X) :
  isabmonoidop (@op (setwithbinopquot R)) := ismonoidquot R ,, iscommquot R.

Definition abmonoidquot {X : abmonoid} (R : binopeqrel X) : abmonoid.
Proof. split with (setwithbinopquot R). apply isabmonoidquot. Defined.


(** **** Direct products *)

Lemma iscommdirprod (X Y : abmonoid) : iscomm (@op (setwithbinopdirprod X Y)).
Proof.
  intros xy xy'.
  destruct xy as [ x y ]. destruct xy' as [ x' y' ]. simpl.
  apply pathsdirprod.
  - apply (commax X).
  - apply (commax Y).
Qed.

Definition isabmonoiddirprod (X Y : abmonoid) : isabmonoidop (@op (setwithbinopdirprod X Y)) :=
  ismonoiddirprod X Y ,, iscommdirprod X Y.

Definition abmonoiddirprod (X Y : abmonoid) : abmonoid.
Proof. split with (setwithbinopdirprod X Y). apply isabmonoiddirprod. Defined.


(** **** Monoid of fractions of an abelian monoid

Note : the following construction uses onbly associativity and commutativity
of the [abmonoid] operations but does not use the unit element. *)

Definition abmonoidfracopint (X : abmonoid) (A : submonoid X) :
  binop (X × A) := @op (setwithbinopdirprod X A).

Definition hrelabmonoidfrac (X : abmonoid) (A : submonoid X) : hrel (setwithbinopdirprod X A) :=
  λ xa yb, ∃ (a0 : A), (pr1 xa + pr1 (pr2 yb)) + pr1 a0 = (pr1 yb + pr1 (pr2 xa) + pr1 a0).

Lemma iseqrelabmonoidfrac (X : abmonoid) (A : submonoid X) : iseqrel (hrelabmonoidfrac X A).
Proof.
  intros.
  set (assoc := assocax X). set (comm := commax X).
  set (R := hrelabmonoidfrac X A).
  apply iseqrelconstr.
  - unfold istrans. intros ab cd ef. simpl. apply hinhfun2.
    destruct ab as [ a b ]. destruct cd as [ c d ]. destruct ef as [ e f ].
    destruct b as [ b isb ]. destruct d as [ d isd ].  destruct f as [ f isf ].
    intros eq1 eq2. destruct eq1 as [ x1 eq1 ]. destruct eq2 as [ x2 eq2 ].
    simpl in *. split with (@op A (d ,, isd) (@op A x1 x2)).
    destruct x1 as [ x1 isx1 ]. destruct x2 as [ x2 isx2 ].
    destruct A as [ A ax ].
    simpl in *.
    rewrite (assoc a f (d + (x1 + x2))). rewrite (comm f (d + (x1 + x2))).
    destruct (assoc a (d + (x1 + x2)) f). destruct (assoc a d (x1 + x2)).
    destruct (assoc (a + d) x1 x2).
    rewrite eq1. rewrite (comm x1 x2). rewrite (assoc e b (d + (x2 + x1))).
    rewrite (comm b (d + (x2 + x1))).
    destruct (assoc e (d + (x2 + x1)) b). destruct (assoc e d (x2 + x1)).
    destruct (assoc (e + d) x2 x1). destruct eq2. rewrite (assoc (c + b) x1 x2).
    rewrite (assoc (c + f) x2 x1). rewrite (comm x1 x2).
    rewrite (assoc (c + b) (x2 + x1) f). rewrite (assoc (c + f) (x2 + x1) b).
    rewrite (comm (x2 + x1) f). rewrite (comm (x2 + x1) b).
    destruct (assoc (c + b) f (x2 + x1)). destruct (assoc (c + f) b (x2 + x1)).
    rewrite (assoc c b f). rewrite (assoc c f b). rewrite (comm b f).
    apply idpath.
  - intro xa. simpl. apply hinhpr. split with (pr2 xa). apply idpath.
  - intros xa yb. unfold R. simpl. apply hinhfun. intro eq1.
    destruct eq1 as [ x1 eq1 ]. split with x1. destruct x1 as [ x1 isx1 ].
    simpl. apply (!eq1).
Qed.

Definition eqrelabmonoidfrac (X : abmonoid) (A : submonoid X) : eqrel (setwithbinopdirprod X A) :=
  make_eqrel (hrelabmonoidfrac X A) (iseqrelabmonoidfrac X A).

Lemma isbinophrelabmonoidfrac (X : abmonoid) (A : submonoid X) :
  @isbinophrel (setwithbinopdirprod X A) (eqrelabmonoidfrac X A).
Proof.
  intros.
  apply (isbinopreflrel (eqrelabmonoidfrac X A) (eqrelrefl (eqrelabmonoidfrac X A))).
  set (rer := abmonoidoprer (pr2 X)). intros a b c d. simpl.
  apply hinhfun2.
  destruct a as [ a a' ]. destruct a' as [ a' isa' ].
  destruct b as [ b b' ]. destruct b' as [ b' isb' ].
  destruct c as [ c c' ]. destruct c' as [ c' isc' ].
  destruct d as [ d d' ]. destruct d' as [ d' isd' ].
  intros ax ay.
  destruct ax as [ a1 eq1 ]. destruct ay as [ a2 eq2 ].
  split with (@op A  a1 a2).
  destruct a1 as [ a1 aa1 ]. destruct a2 as [ a2 aa2 ].
  simpl in *.
  rewrite (rer a c b' d'). rewrite (rer b d a' c').
  rewrite (rer (a + b') (c + d') a1 a2).
  rewrite (rer (b + a') (d + c') a1 a2).
  destruct eq1. destruct eq2.
  apply idpath.
Qed.

Definition abmonoidfracop (X : abmonoid) (A : submonoid X) :
  binop (setquot (hrelabmonoidfrac X A)) :=
  setquotfun2 (hrelabmonoidfrac X A) (eqrelabmonoidfrac X A) (abmonoidfracopint X A)
              ((iscompbinoptransrel _ (eqreltrans _) (isbinophrelabmonoidfrac X A))).

Definition binopeqrelabmonoidfrac (X : abmonoid) (A : subabmonoid X) :
  binopeqrel (abmonoiddirprod X A) :=
  @make_binopeqrel (setwithbinopdirprod X A) (eqrelabmonoidfrac X A) (isbinophrelabmonoidfrac X A).

Definition abmonoidfrac (X : abmonoid) (A : submonoid X) : abmonoid :=
  abmonoidquot (binopeqrelabmonoidfrac X A).

Definition prabmonoidfrac (X : abmonoid) (A : submonoid X) : X  → A  → abmonoidfrac X A :=
  λ (x : X) (a : A), setquotpr (eqrelabmonoidfrac X A) (x ,, a).

(* ??? could the use of [issubabmonoid] in [binopeqrelabmonoidfrac] and
 [submonoid] in [abmonoidfrac] lead to complications for the unification
 machinery? See also [abmonoidfracisbinoprelint] below. *)

Lemma invertibilityinabmonoidfrac (X : abmonoid) (A : submonoid X) :
  ∏ a a' : A, isinvertible (@op (abmonoidfrac X A)) (prabmonoidfrac X A (pr1 a) a').
Proof.
  intros a a'.
  set (R := eqrelabmonoidfrac X A). unfold isinvertible.
  assert (isl : islinvertible (@op (abmonoidfrac X A))
                              (prabmonoidfrac X A (pr1 a) a')).
  {
    unfold islinvertible.
    set (f := λ x0 : abmonoidfrac X A, prabmonoidfrac X A (pr1 a) a' + x0).
    set (g := λ x0 : abmonoidfrac X A, prabmonoidfrac X A (pr1 a') a + x0).
    assert (egf : ∏ x0, g (f x0) = x0).
    {
      apply (setquotunivprop R (λ x, _ = _)%logic).
      intro xb. simpl.
      apply (iscompsetquotpr
               R (pr1 a' + (pr1 a + pr1 xb) ,, (@op A) a ((@op A) a' (pr2 xb)))).
      simpl. apply hinhpr. split with (unel A). unfold pr1carrier. simpl.
      set (e := assocax X (pr1 a) (pr1 a') (pr1 (pr2 xb))).
      simpl in e. destruct e.
      set (e := assocax X (pr1 xb) (pr1 a + pr1 a') (pr1 (pr2 xb))).
      simpl in e. destruct e.
      set (e := assocax X (pr1 a') (pr1 a) (pr1 xb)).
      simpl in e. destruct e.
      set (e := commax X (pr1 a) (pr1 a')).
      simpl in e. destruct e.
      set (e := commax X (pr1 a + pr1 a') (pr1 xb)).
      simpl in e. destruct e.
      apply idpath.
    }
    assert (efg : ∏ x0, f (g x0) = x0).
    {
      apply (setquotunivprop R (λ x0, _ = _)%logic).
      intro xb. simpl.
      apply (iscompsetquotpr
               R (pr1 a + (pr1 a' + pr1 xb) ,, (@op A) a' ((@op A) a (pr2 xb)))).
      simpl. apply hinhpr. split with (unel A). unfold pr1carrier. simpl.
      set (e := assocax X (pr1 a') (pr1 a) (pr1 (pr2 xb))).
      simpl in e. destruct e.
      set (e := assocax X (pr1 xb) (pr1 a' + pr1 a) (pr1 (pr2 xb))).
      simpl in e. destruct e.
      set (e := assocax X (pr1 a) (pr1 a') (pr1 xb)).
      simpl in e. destruct e.
      set (e := commax X (pr1 a') (pr1 a)).
      simpl in e. destruct e.
      set (e := commax X (pr1 a' + pr1 a) (pr1 xb)).
      simpl in e. destruct e.
      apply idpath.
    }
    apply (isweq_iso _ _ egf efg).
  }
  exact (
    isl ,,
    weqlinvertiblerinvertible op (commax (abmonoidfrac X A)) (prabmonoidfrac X A (pr1 a) a') isl
  ).
Defined.

(** **** Canonical homomorphism to the monoid of fractions *)

Definition toabmonoidfrac (X : abmonoid) (A : submonoid X) (x : X) : abmonoidfrac X A :=
  setquotpr _ (x ,, unel A).

Lemma isbinopfuntoabmonoidfrac (X : abmonoid) (A : submonoid X) : isbinopfun (toabmonoidfrac X A).
Proof.
  unfold isbinopfun. intros x1 x2.
  change (setquotpr _ (x1 + x2 ,, @unel A)
          = setquotpr (eqrelabmonoidfrac X A) (x1 + x2 ,, unel A + unel A)).
  apply (maponpaths (setquotpr _)).
  apply (@pathsdirprod X A).
  apply idpath.
  exact (!lunax A 0).
Defined.

Lemma isunitalfuntoabmonoidfrac (X : abmonoid) (A : submonoid X) :
  toabmonoidfrac X A 0 = 0.
Proof. apply idpath. Defined.

Definition ismonoidfuntoabmonoidfrac (X : abmonoid) (A : submonoid X) :
  ismonoidfun (toabmonoidfrac X A) :=
  isbinopfuntoabmonoidfrac X A ,, isunitalfuntoabmonoidfrac X A.


(** **** Abelian monoid of fractions in the case when elements of the localziation submonoid are cancelable *)

Definition hrel0abmonoidfrac (X : abmonoid) (A : submonoid X) : hrel (X × A) :=
  λ xa yb : setdirprod X A, (pr1 xa + pr1 (pr2 yb) = pr1 yb + pr1 (pr2 xa))%logic.

Lemma weqhrelhrel0abmonoidfrac (X : abmonoid) (A : submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a))
      (xa xa' : X × A) : (eqrelabmonoidfrac X A xa xa') ≃ (hrel0abmonoidfrac X A xa xa').
Proof.
  unfold eqrelabmonoidfrac. unfold hrelabmonoidfrac. simpl.
  apply weqimplimpl.
  apply (@hinhuniv _ (pr1 xa + pr1 (pr2 xa') = pr1 xa' + pr1 (pr2 xa))%logic).
  intro ae. destruct ae as [ a eq ].
  apply (invmaponpathsincl _ (iscanc a) _ _ eq).
  intro eq. apply hinhpr. split with (unel A). rewrite (runax X).
  rewrite (runax X). apply eq. apply (isapropishinh _).
  apply (setproperty X).
Defined.

Lemma isinclprabmonoidfrac (X : abmonoid) (A : submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) :
  ∏ a' : A, isincl (λ x, prabmonoidfrac X A x a').
Proof.
  intro a'. apply isinclbetweensets.
  - apply (setproperty X).
  - apply (setproperty (abmonoidfrac X A)).
  - intros x x'. intro e.
    set (e' := invweq (weqpathsinsetquot (eqrelabmonoidfrac X A) (x ,, a')
                                         (x' ,, a')) e).
    set (e'' := weqhrelhrel0abmonoidfrac X A iscanc (_ ,, _) (_ ,, _) e').
    simpl in e''.
    apply (invmaponpathsincl _ (iscanc a')).
    apply e''.
Defined.

Definition isincltoabmonoidfrac (X : abmonoid) (A : submonoid X)
           (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) :
  isincl (toabmonoidfrac X A) := isinclprabmonoidfrac X A iscanc (unel A).

Lemma isdeceqabmonoidfrac (X : abmonoid) (A : submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) (is : isdeceq X) :
  isdeceq (abmonoidfrac X A).
Proof.
  apply (isdeceqsetquot (eqrelabmonoidfrac X A)). intros xa xa'.
  apply (isdecpropweqb (weqhrelhrel0abmonoidfrac X A iscanc xa xa')).
  apply isdecpropif. unfold isaprop. simpl.
  set (int := setproperty X (pr1 xa + pr1 (pr2 xa')) (pr1 xa' + pr1 (pr2 xa))).
  simpl in int. apply int. unfold hrel0abmonoidfrac.
  simpl. apply (is _ _).
Defined.


(** **** Relations on the abelian monoid of fractions *)

Definition abmonoidfracrelint (X : abmonoid) (A : subabmonoid X) (L : hrel X) :
  hrel (setwithbinopdirprod X A) :=
  λ xa yb, ∃ (c0 : A), L (((pr1 xa) + (pr1 (pr2 yb))) + (pr1 c0))
                                  (((pr1 yb) + (pr1 (pr2 xa))) + (pr1 c0)).

Lemma iscomprelabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) : iscomprelrel (eqrelabmonoidfrac X A) (abmonoidfracrelint X A L).
Proof.
  set (assoc := (assocax X) : isassoc (@op X)).
  unfold isassoc in assoc. set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X). apply iscomprelrelif.
  apply (eqrelsymm (eqrelabmonoidfrac X A)).
  - intros xa xa' yb. unfold hrelabmonoidfrac. simpl. apply (@hinhfun2).
    intros t2e t2l.
    destruct t2e as [ c1a e ]. destruct t2l as [ c0a l ].
    set (x := pr1 xa). set (a := pr1 (pr2 xa)).
    set (x' := pr1 xa'). set (a' := pr1 (pr2 xa')).
    set (y := pr1 yb). set (b := pr1 (pr2 yb)).
    set (c0 := pr1 c0a). set (c1 := pr1 c1a).
    split with ((pr2 xa) + c1a + c0a).
    change (L ((x' + b) + ((a + c1) + c0)) ((y + a') + ((a + c1) + c0))).
    change (x + a' + c1 = x' + a + c1) in e.
    rewrite (rer x' _ _ c0).
    destruct (assoc x' a c1). destruct e.
    rewrite (assoc x a' c1). rewrite (rer x _ _ c0). rewrite (assoc a c1 c0).
    rewrite (rer _ a' a _). rewrite (assoc a' c1 c0). rewrite (comm a' _).
    rewrite (comm c1 _). rewrite (assoc  c0 c1 a').
    destruct (assoc (x + b) c0 (@op X c1 a')).
    destruct (assoc (y + a) c0 (@op X c1 a')).
    apply ((pr2 is) _ _ _ (pr2 (@op A c1a (pr2 xa'))) l).
  - intros xa yb yb'. unfold hrelabmonoidfrac. simpl. apply (@hinhfun2).
    intros t2e t2l.
    destruct t2e as [ c1a e ]. destruct t2l as [ c0a l ].
    set (x := pr1 xa). set (a := pr1 (pr2 xa)).
    set (y' := pr1 yb'). set (b' := pr1 (pr2 yb')).
    set (y := pr1 yb). set (b := pr1 (pr2 yb)).
    set (c0 := pr1 c0a). set (c1 := pr1 c1a).
    split with ((pr2 yb) + c1a + c0a).
    change (L ((x + b') + ((b + c1) + c0)) ((y' + a) + ((b + c1) + c0))).
    change (y + b' + c1 = y' + b + c1) in e.
    rewrite (rer y' _ _ c0).
    destruct (assoc y' b c1). destruct e.
    rewrite (assoc y b' c1).  rewrite (rer y _ _ c0).
    rewrite (assoc b c1 c0). rewrite (rer _ b' b _).
    rewrite (assoc b' c1 c0). rewrite (comm b' _).
    rewrite (comm c1 _). rewrite (assoc  c0 c1 b').
    destruct (assoc (x + b) c0 (@op X c1 b')).
    destruct (assoc (y + a) c0 (@op X c1 b')).
    apply ((pr2 is) _ _ _ (pr2 (@op A c1a (pr2 yb'))) l).
Qed.

Definition abmonoidfracrel (X : abmonoid) (A : submonoid X) {L : hrel X}
           (is : ispartbinophrel A L) := quotrel (iscomprelabmonoidfracrelint X A is).

Lemma istransabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istrans L) : istrans (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm. set (rer := abmonoidrer X).
  intros xa1 xa2 xa3. unfold abmonoidfracrelint. simpl.
  apply hinhfun2. intros t2l1 t2l2.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  set (c2a := pr1 t2l2). set (l2 := pr2 t2l2).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  set (x3 := pr1 xa3). set (a3 := pr1 (pr2 xa3)).
  set (c1 := pr1 c1a). set (c2 := pr1 c2a).
  split with ((pr2 xa2) + (@op A c1a c2a)).
  change (L ((x1 + a3) + (a2 + (c1 + c2))) ((x3 + a1) + (a2 + (c1 + c2)))).
  assert (ll1 : L ((x1 + a3) + (a2 + (@op X c1 c2)))
                  (((x2 + a1) + c1) + (c2 + a3))).
  {
    rewrite (rer _ a3 a2 _). rewrite (comm a3 (@op X c1 c2)).
    rewrite (assoc c1 c2 a3).
    destruct (assoc (x1 + a2) c1 (@op X c2 a3)).
    apply ((pr2 is) _ _ _ (pr2 (@op A c2a (pr2 xa3))) l1).
  }
  assert (ll2 : L (((x2 + a3) + c2) + (@op X a1 c1))
                  ((x3 + a1) + (a2 + (@op X c1 c2)))).
  {
    rewrite (rer _ a1 a2 _). destruct (assoc a1 c1 c2).
    rewrite (comm (a1 + c1) c2).
    destruct (assoc (x3 + a2) c2 (@op X a1 c1)).
    apply ((pr2 is) _ _ _ (pr2 (@op A (pr2 xa1) c1a)) l2).
  }
  assert (e : x2 + a1 + c1 + (c2 + a3) =
              x2 + a3 + c2 + (a1 + c1)).
  {
    rewrite (assoc (x2 + a1) c1 _). rewrite (assoc (x2 + a3) c2 _).
    rewrite (assoc x2 a1 _). rewrite (assoc x2 a3 _).
    destruct (assoc a1 c1 (c2 + a3)). destruct (assoc a3 c2 (a1 + c1)).
    destruct (comm (c2 + a3) (a1 + c1)).
    rewrite (comm a3 c2). apply idpath.
  }
  destruct e. apply (isl _ _ _ ll1 ll2).
Qed.

Lemma istransabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istrans L) : istrans (abmonoidfracrel X A is).
Proof.
  apply istransquotrel. apply istransabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma issymmabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : issymm L) : issymm (abmonoidfracrelint X A L).
Proof.
  intros xa1 xa2. unfold abmonoidfracrelint. simpl.
  apply hinhfun. intros t2l1.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  split with (c1a). apply (isl _ _ l1).
Qed.

Lemma issymmabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : issymm L) : issymm (abmonoidfracrel X A is).
Proof.
  apply issymmquotrel. apply issymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isreflabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isrefl L) : isrefl (abmonoidfracrelint X A L).
Proof.
  intro xa. unfold abmonoidfracrelint. simpl. apply hinhpr.
  split with (unel A). apply (isl _).
Defined.

Lemma isreflabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isrefl L) : isrefl (abmonoidfracrel X A is).
Proof.
  apply isreflquotrel. apply isreflabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma ispoabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : ispreorder L) : ispreorder (abmonoidfracrelint X A L).
Proof.
  split with (istransabmonoidfracrelint X A is (pr1 isl)).
  apply (isreflabmonoidfracrelint X A is (pr2 isl)).
Defined.

Lemma ispoabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : ispreorder L) : ispreorder (abmonoidfracrel X A is).
Proof.
  apply ispoquotrel. apply ispoabmonoidfracrelint.
  apply is. apply isl.
Defined.

Lemma iseqrelabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iseqrel L) : iseqrel (abmonoidfracrelint X A L).
Proof.
  split with (ispoabmonoidfracrelint X A is (pr1 isl)).
  apply (issymmabmonoidfracrelint X A is (pr2 isl)).
Defined.

Lemma iseqrelabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iseqrel L) : iseqrel (abmonoidfracrel X A is).
Proof.
  apply iseqrelquotrel. apply iseqrelabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isirreflabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isirrefl L) : isirrefl (abmonoidfracrelint X A L).
Proof.
  unfold isirrefl. intro xa. unfold abmonoidfracrelint. simpl.
  unfold neg. apply (@hinhuniv _ (make_hProp _ isapropempty)).
  intro t2. apply (isl _ (pr2 t2)).
Defined.

Lemma isirreflabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isirrefl L) : isirrefl (abmonoidfracrel X A is).
Proof.
  apply isirreflquotrel. apply isirreflabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isasymmabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isasymm L) : isasymm (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)).
  unfold isassoc in assoc. set (comm := commax X).
  unfold iscomm in comm. unfold isasymm.
  intros xa1 xa2. unfold abmonoidfracrelint. simpl.
  apply (@hinhuniv2 _ _ (make_hProp _ isapropempty)).
  intros t2l1 t2l2.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  set (c2a := pr1 t2l2). set (l2 := pr2 t2l2).
  set (c1 := pr1 c1a). set (c2 := pr1 c2a).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  assert (ll1 : L ((x1 + a2) + (@op X c1 c2)) ((x2 + a1) + (@op X c1 c2))).
  {
    destruct (assoc (x1 + a2) c1 c2). destruct (assoc (x2 + a1) c1 c2).
    apply ((pr2 is) _ _ _ (pr2 c2a)). apply l1.
  }
  assert (ll2 : L ((x2 + a1) + (@op X c1 c2)) ((x1 + a2) + (@op X c1 c2))).
  {
    destruct (comm c2 c1). destruct (assoc (x1 + a2) c2 c1).
    destruct (assoc (x2 + a1) c2 c1).
    apply ((pr2 is) _ _ _ (pr2 c1a)).
    apply l2.
  }
  apply (isl _ _ ll1 ll2).
Qed.

Lemma isasymmabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isasymm L) : isasymm (abmonoidfracrel X A is).
Proof.
  apply isasymmquotrel. apply isasymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iscoasymmabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscoasymm L) : iscoasymm (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm. unfold iscoasymm.
  intros xa1 xa2. intro nl0.
  set (nl := neghexisttoforallneg _ nl0 (unel A)).
  simpl in nl.
  set (l := isl _ _ nl).
  apply hinhpr.
  split with (unel A).
  apply l.
Qed.

Lemma iscoasymmabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscoasymm L) : iscoasymm (abmonoidfracrel X A is).
Proof.
  apply iscoasymmquotrel. apply iscoasymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma istotalabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istotal L) : istotal (abmonoidfracrelint X A L).
Proof.
  unfold istotal. intros x1 x2. unfold abmonoidfracrelint.
  set (int := isl (pr1 x1 + pr1 (pr2 x2)) (pr1 x2 + pr1 (pr2 x1))).
  generalize int. clear int. simpl.
  apply hinhfun. apply coprodf. intro l.
  apply hinhpr.
  split with (unel A).  rewrite (runax X _).
  rewrite (runax X _). apply l.  intro l.
  apply hinhpr. split with (unel A).
  rewrite (runax X _). rewrite (runax X _).
  apply l.
Defined.

Lemma istotalabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istotal L) : istotal (abmonoidfracrel X A is).
Proof.
  apply istotalquotrel. apply istotalabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iscotransabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscotrans L) : iscotrans (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := (commax X) : iscomm (@op X)). unfold iscomm in comm.
  set (rer := abmonoidrer X). unfold iscotrans.
  intros xa1 xa2 xa3. unfold abmonoidfracrelint. simpl.
  apply (@hinhuniv _ (ishinh _)).
  intro t2.
  set (c0a := pr1 t2). set (l0 := pr2 t2).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  set (x3 := pr1 xa3). set (a3 := pr1 (pr2 xa3)).
  set (c0 := pr1 c0a).
  set (z1 := (x1 + a3 + (a2 + c0))).
  set (z2 := x2 + a1 + (a3 + c0)).
  set (z3 := x3 + a1 + (a2 + c0)).
  assert (int : L z1 z3).
  {
    unfold z1. unfold z3. rewrite (comm a2 c0).
    rewrite <- (assoc _ _ a2).
    rewrite <- (assoc _ _ a2).
    apply ((pr2 is) _ _ _ (pr2 (pr2 xa2)) l0).
  }
  set (int' := isl z1 z2 z3 int). generalize int'. clear int'.
  simpl. apply hinhfun. intro cc.
  destruct cc as [ l12 | l23 ].
  - apply ii1. apply hinhpr. split with ((pr2 xa3) + c0a).
    change (L (x1 + a2 + (a3 + c0)) (x2 + a1 + (a3 + c0))).
    rewrite (rer _ a2 a3 _). apply l12.
  - apply ii2. apply hinhpr. split with ((pr2 xa1) + c0a).
    change (L (x2 + a3 + (a1 + c0)) (x3 + a2 + (a1 + c0))).
    rewrite (rer _ a3 a1 _). rewrite (rer _ a2 a1 _).
    apply l23.
Qed.

Lemma iscotransabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscotrans L) : iscotrans (abmonoidfracrel X A is).
Proof.
  apply iscotransquotrel. apply iscotransabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isStrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : hrel X)
      (Hgt : ispartbinophrel Y gt) :
  isStrongOrder gt → isStrongOrder (abmonoidfracrel X Y Hgt).
Proof.
  intros H.
  split ; [ | split].
  - apply istransabmonoidfracrel, (istrans_isStrongOrder H).
  - apply iscotransabmonoidfracrel, (iscotrans_isStrongOrder H).
  - apply isirreflabmonoidfracrel, (isirrefl_isStrongOrder H).
Qed.

Definition StrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : StrongOrder X)
           (Hgt : ispartbinophrel Y gt) : StrongOrder (abmonoidfrac X Y) :=
  abmonoidfracrel X Y Hgt,, isStrongOrder_abmonoidfrac Y gt Hgt (pr2 gt).

Lemma isantisymmnegabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isantisymmneg L) : isantisymmneg (abmonoidfracrel X A is).
Proof.
  intros.
  assert (int : ∏ x1 x2, isaprop (neg (abmonoidfracrel X A is x1 x2)  →
                                  neg (abmonoidfracrel X A is x2 x1)  →
                                  x1 = x2)).
  {
    intros x1 x2.
    apply impred. intro.
    apply impred. intro.
    apply (isasetsetquot _ x1 x2).
  }
  unfold isantisymmneg.
  apply (setquotuniv2prop _ (λ x1 x2, make_hProp _ (int x1 x2))).
  intros xa1 xa2. intros r r'. apply (weqpathsinsetquot _).
  generalize r r'. clear r r'.
  change (neg (abmonoidfracrelint X A L xa1 xa2)  →
          neg (abmonoidfracrelint X A L xa2 xa1)  →
          (eqrelabmonoidfrac X A xa1 xa2)).
  intros nr12 nr21.
  set (nr12' := neghexisttoforallneg _ nr12 (unel A)).
  set (nr21' := neghexisttoforallneg _ nr21 (unel A)).
  set (int' := isl _ _ nr12' nr21').
  simpl. apply hinhpr. split with (unel A). apply int'.
Qed.

Lemma isantisymmabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isantisymm L) : isantisymm (abmonoidfracrel X A is).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm. unfold isantisymm.
  assert (int : ∏ x1 x2, isaprop ((abmonoidfracrel X A is x1 x2)  →
                                  (abmonoidfracrel X A is x2 x1)  →
                                  x1 = x2)).
  {
    intros x1 x2.
    apply impred. intro.
    apply impred. intro.
    apply (isasetsetquot _ x1 x2).
  }
  apply (setquotuniv2prop _ (λ x1 x2, make_hProp _ (int x1 x2))).
  intros xa1 xa2. intros r r'. apply (weqpathsinsetquot _).
  generalize r r'. clear r r'.
  change ((abmonoidfracrelint X A L xa1 xa2)  →
          (abmonoidfracrelint X A L xa2 xa1)  →
          (eqrelabmonoidfrac X A xa1 xa2)).
  unfold abmonoidfracrelint. unfold eqrelabmonoidfrac. simpl.
  apply hinhfun2. intros t2l1 t2l2.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  set (c2a := pr1 t2l2). set (l2 := pr2 t2l2).
  set (c1 := pr1 c1a). set (c2 := pr1 c2a).
  split with (@op A c1a c2a).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  change (x1 + a2 + (c1 + c2) = x2 + a1 + (@op X c1 c2)).
  assert (ll1 : L ((x1 + a2) + (@op X c1 c2)) ((x2 + a1) + (@op X c1 c2))).
  {
    destruct (assoc (x1 + a2) c1 c2).
    destruct (assoc (x2 + a1) c1 c2).
    apply ((pr2 is) _ _ _ (pr2 c2a)).
    apply l1.
  }
  assert (ll2 : L ((x2 + a1) + (@op X c1 c2)) ((x1 + a2) + (@op X c1 c2))).
  {
    destruct (comm c2 c1).
    destruct (assoc (x1 + a2) c2 c1).
    destruct (assoc (x2 + a1) c2 c1).
    apply ((pr2 is) _ _ _ (pr2 c1a)).
    apply l2.
  }
  apply (isl _ _ ll1 ll2).
Qed.

Lemma ispartbinopabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) :
  @ispartbinophrel (setwithbinopdirprod X A) (λ xa, A (pr1 xa)) (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X).
  apply ispartbinophrelif. apply (commax (abmonoiddirprod X A)).
  intros xa yb zc s. unfold abmonoidfracrelint. simpl.
  apply (@hinhfun). intro t2l. destruct t2l as [ c0a l ].
  set (x := pr1 xa). set (a := pr1 (pr2 xa)).
  set (y := pr1 yb). set (b := pr1 (pr2 yb)).
  set (z := pr1 zc). set (c := pr1 (pr2 zc)).
  set (c0 := pr1 c0a).
  split with c0a.
  change (L (((z + x) + (c + b)) + c0) (((z + y) + (c + a)) + c0)).
  change (pr1 (L ((x + b) + c0) ((y + a) + c0))) in l.
  rewrite (rer z _ _ b). rewrite (assoc (z + c) _ _).
  rewrite (rer z _ _ a). rewrite (assoc (z + c) _ _).
  apply ((pr1 is) _ _ _ (pr2 (@op A (make_carrier A z s) (pr2 zc)))).
  apply l.
Qed.


Lemma ispartlbinopabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (aa aa' : A) (z z' : abmonoidfrac X A)
      (l : abmonoidfracrel X A is z z') :
  abmonoidfracrel X A is
                  ((prabmonoidfrac X A (pr1 aa) aa') + z) ((prabmonoidfrac X A (pr1 aa) aa') + z').
Proof.
  revert z z' l.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X).
  assert (int : ∏ z z', isaprop (abmonoidfracrel X A is z z'  →
                                 abmonoidfracrel
                                   X A is (prabmonoidfrac X A (pr1 aa) aa' + z)
                                   (prabmonoidfrac X A (pr1 aa) aa' + z'))).
  {
    intros z z'.
    apply impred. intro.
    apply (pr2 (abmonoidfracrel _ _ _ _ _)).
  }
  apply (setquotuniv2prop _ (λ z z', make_hProp _ (int z z'))).
  intros xa1 xa2.
  change (abmonoidfracrelint X A L xa1 xa2  →
          abmonoidfracrelint X A L
                             (@op (abmonoiddirprod X A) (pr1 aa ,, aa') xa1)
                             (@op (abmonoiddirprod X A) (pr1 aa ,, aa') xa2)).
  unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2l.
  set (a := pr1 aa). set (a' := pr1 aa').
  set (c0a := pr1 t2l). set (l := pr2 t2l).
  set (c0 := pr1 c0a). set (x1 := pr1 xa1).
  set (a1 := pr1 (pr2 xa1)). set (x2 := pr1 xa2).
  set (a2 := pr1 (pr2 xa2)). split with c0a.

  change (L (a + x1 + (a' + a2) + c0) (a + x2 + (a' + a1) + c0)).
  rewrite (rer _ x1 a' _). rewrite (rer _ x2 a' _).
  rewrite (assoc _ (x1 + a2) c0). rewrite (assoc _ (x2 + a1) c0).
  apply ((pr1 is) _ _ _ (pr2 (@op A aa aa'))). apply l.
Qed.

Lemma ispartrbinopabmonoidfracrel (X : abmonoid) (A : subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (aa aa' : A) (z z' : abmonoidfrac X A)
      (l : abmonoidfracrel X A is z z') :
  abmonoidfracrel X A is
                  (z + (prabmonoidfrac X A (pr1 aa) aa')) (z' + (prabmonoidfrac X A (pr1 aa) aa')).
Proof.
  revert z z' l.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X).
  assert (int : ∏ (z z' : abmonoidfrac X A),
                isaprop (abmonoidfracrel X A is z z'  →
                         abmonoidfracrel X A is
                                         (z + (prabmonoidfrac X A (pr1 aa) aa'))
                                         (z' + prabmonoidfrac X A (pr1 aa) aa'))).
  {
    intros z z'.
    apply impred. intro.
    apply (pr2 (abmonoidfracrel _ _ _ _ _)).
  }
  apply (setquotuniv2prop _ (λ z z', make_hProp _ (int z z'))).
  intros xa1 xa2.
  change (abmonoidfracrelint X A L xa1 xa2  →
          abmonoidfracrelint X A L
                             (@op (abmonoiddirprod X A) xa1 (pr1 aa ,, aa'))
                             (@op (abmonoiddirprod X A) xa2 (pr1 aa ,, aa'))).
  unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2l.
  set (a := pr1 aa). set (a' := pr1 aa').
  set (c0a := pr1 t2l). set (l := pr2 t2l).
  set (c0 := pr1 c0a). set (x1 := pr1 xa1).
  set (a1 := pr1 (pr2 xa1)). set (x2 := pr1 xa2).
  set (a2 := pr1 (pr2 xa2)). split with c0a.

  change (L (x1 + a + (a2 + a') + c0) (x2 + a + (a1 + a') + c0)).
  rewrite (rer _ a a2 _). rewrite (rer _ a a1 _).
  rewrite (assoc (x1 + a2) _ c0). rewrite (assoc (x2 + a1) _ c0).
  rewrite (comm _ c0).
  destruct (assoc (x1 + a2) c0 (a + a')).
  destruct (assoc (x2 + a1) c0 (a + a')).
  apply ((pr2 is) _ _ _ (pr2 (@op A aa aa'))).
  apply l.
Qed.

Lemma abmonoidfracrelimpl (X : abmonoid) (A : subabmonoid X) {L L' : hrel X}
      (is : ispartbinophrel A L) (is' : ispartbinophrel A L')
      (impl : ∏ x x', L x x'  → L' x x') (x x' : abmonoidfrac X A)
      (ql : abmonoidfracrel X A is x x') : abmonoidfracrel X A is' x x'.
Proof.
  generalize ql. apply quotrelimpl. intros x0 x0'.
  unfold abmonoidfracrelint. simpl. apply hinhfun.
  intro t2. split with (pr1 t2). apply (impl _ _ (pr2 t2)).
Qed.

Lemma abmonoidfracrellogeq (X : abmonoid) (A : subabmonoid X) {L L' : hrel X}
      (is : ispartbinophrel A L) (is' : ispartbinophrel A L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abmonoidfrac X A) :
  (abmonoidfracrel X A is x x') <-> (abmonoidfracrel X A is' x x').
Proof.
  apply quotrellogeq. intros x0 x0'. split.
  - unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2.
    split with (pr1 t2). apply (pr1 (lg _ _) (pr2 t2)).
  - unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2.
    split with (pr1 t2). apply (pr2 (lg _ _) (pr2 t2)).
Qed.

Definition isdecabmonoidfracrelint (X : abmonoid) (A : subabmonoid X) {L : hrel X}
           (is : ispartinvbinophrel A L) (isl : isdecrel L) : isdecrel (abmonoidfracrelint X A L).
Proof.
  intros xa1 xa2.
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  assert (int : coprod (L (x1 + a2) (x2 + a1)) (neg (L (x1 + a2) (x2 + a1)))) by apply (isl _ _).
  destruct int as [ l | nl ].
  - apply ii1. unfold abmonoidfracrelint.
    apply hinhpr. split with (unel A).
    rewrite (runax X _). rewrite (runax X _).
    apply l.
  - apply ii2. generalize nl. clear nl. apply negf.
    unfold abmonoidfracrelint. simpl.
    apply (@hinhuniv _ (make_hProp _ (pr2 (L _ _)))).
    intro t2l. destruct t2l as [ c0a l ].
    simpl.
    apply ((pr2 is) _ _ _ (pr2 c0a) l).
Defined.

Definition isdecabmonoidfracrel (X : abmonoid) (A : submonoid X) {L : hrel X}
           (is : ispartbinophrel A L) (isi : ispartinvbinophrel A L)
           (isl : isdecrel L) : isdecrel (abmonoidfracrel X A is).
Proof.
  apply isdecquotrel. apply isdecabmonoidfracrelint.
  - apply isi.
  - apply isl.
Defined.


(** **** Relations and the canonical homomorphism to [abmonoidfrac] *)

Lemma iscomptoabmonoidfrac (X : abmonoid) (A : submonoid X) {L : hrel X}
      (is : ispartbinophrel A L) : iscomprelrelfun L (abmonoidfracrel X A is) (toabmonoidfrac X A).
Proof.
  unfold iscomprelrelfun. intros x x' l.
  change (abmonoidfracrelint X A L (x ,, unel A) (x' ,, unel A)).
  simpl. apply (hinhpr). split with (unel A). apply ((pr2 is) _ _ 0).
  apply (pr2 (unel A)). apply ((pr2 is) _ _ 0). apply (pr2 (unel A)).
  apply l.
Qed.
