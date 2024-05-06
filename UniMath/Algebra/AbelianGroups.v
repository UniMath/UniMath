(**
 - Abelian groups
  - Basic definitions
  - Univalence for abelian groups
  - Subobjects
  - Kernels
  - Quotient objects
  - Direct products
  - Abelian group of fractions of an abelian unitary monoid
  - Abelian group of fractions and abelian monoid of fractions
  - Canonical homomorphism to the abelian group of fractions
  - Abelian group of fractions in the case when all elements are
    cancelable
  - Relations on the abelian group of fractions
  - Relations and the canonical homomorphism to [abgrdiff]
*)
(** *** Abelian group of fractions of an abelian unitary monoid *)

Require Import UniMath.MoreFoundations.Orders.
Require Import UniMath.MoreFoundations.Subtypes.

Require Export UniMath.Algebra.Groups2.
Require Export UniMath.Algebra.AbelianMonoids.

(** ** Abelian groups *)

(** *** Basic definitions *)

Local Open Scope addmonoid.

Definition abgr : UU := ∑ (X : setwithbinop), isabgrop (@op X).

Definition make_abgr (X : setwithbinop) (is : isabgrop (@op X)) : abgr :=
  X ,, is.

Definition abgrconstr (X : abmonoid) (inv0 : X → X) (is : isinv (@op X) 0 inv0) : abgr :=
  make_abgr X (make_isgrop (pr2 X) (inv0 ,, is) ,, commax X).

Definition abgrtogr : abgr → gr := λ X, make_gr (pr1 X) (pr1 (pr2 X)).
Coercion abgrtogr : abgr >-> gr.

Definition abgrtoabmonoid : abgr → abmonoid :=
  λ X, make_abmonoid (pr1 X) (pr1 (pr1 (pr2 X)) ,, pr2 (pr2 X)).
Coercion abgrtoabmonoid : abgr >-> abmonoid.

Definition abgr_of_gr (X : gr) (H : iscomm (@op X)) : abgr :=
  make_abgr X (make_isabgrop (pr2 X) H).

Declare Scope abgr.
Delimit Scope abgr with abgr.
Notation "x - y" := (op x (grinv _ y)) : abgr.
Notation   "- y" := (grinv _ y) : abgr.

(** *** Construction of the trivial abgr consisting of one element given by unit. *)

Definition unitabgr_isabgrop : isabgrop (@op unitabmonoid).
Proof.
  use make_isabgrop.
  - exact unitgr_isgrop.
  - exact (commax unitabmonoid).
Qed.

Definition unitabgr : abgr := make_abgr unitabmonoid unitabgr_isabgrop.

Lemma abgrfuntounit_ismonoidfun (X : abgr) : ismonoidfun (Y := unitabgr) (λ x : X, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use isProofIrrelevantUnit.
  - use isProofIrrelevantUnit.
Qed.

Definition abgrfuntounit (X : abgr) : monoidfun X unitabgr :=
  monoidfunconstr (abgrfuntounit_ismonoidfun X).

Lemma abgrfunfromunit_ismonoidfun (X : abgr) : ismonoidfun (Y := X) (λ x : unitabgr, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. exact (!runax X _).
  - use idpath.
Qed.

Definition abgrfunfromunit (X : abgr) : monoidfun unitabgr X :=
  monoidfunconstr (abgrfunfromunit_ismonoidfun X).

Lemma unelabgrfun_ismonoidfun (X Y : abgr) : ismonoidfun (Y := Y) (λ x : X, 0).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. exact (!lunax _ _).
  - use idpath.
Qed.

Definition unelabgrfun (X Y : abgr) : monoidfun X Y :=
  monoidfunconstr (unelgrfun_ismonoidfun X Y).


(** *** Abelian group structure on morphism between abelian groups *)

Definition abgrshombinop_inv_ismonoidfun {X Y : abgr} (f : monoidfun X Y) :
  ismonoidfun (λ x : X, grinv Y (pr1 f x)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 Y)). use (grinvop Y).
  - refine (maponpaths (grinv Y) (monoidfununel f) @ _).
    use grinvunel.
Qed.

Definition abgrshombinop_inv {X Y : abgr} (f : monoidfun X Y) : monoidfun X Y :=
  monoidfunconstr (abgrshombinop_inv_ismonoidfun f).

Definition abgrshombinop_linvax {X Y : abgr} (f : monoidfun X Y) :
  @abmonoidshombinop X Y (abgrshombinop_inv f) f = unelmonoidfun X Y.
Proof.
  use monoidfun_paths. use funextfun. intros x. use (@grlinvax Y).
Qed.

Definition abgrshombinop_rinvax {X Y : abgr} (f : monoidfun X Y) :
  @abmonoidshombinop X Y f (abgrshombinop_inv f) = unelmonoidfun X Y.
Proof.
  use monoidfun_paths. use funextfun. intros x. use (grrinvax Y).
Qed.

Lemma abgrshomabgr_isabgrop (X Y : abgr) :
  @isabgrop (abmonoidshomabmonoid X Y) (λ f g : monoidfun X Y, @abmonoidshombinop X Y f g).
Proof.
  use make_isabgrop.
  - use make_isgrop.
    + exact (abmonoidshomabmonoid_ismonoidop X Y).
    + use make_invstruct.
      * intros f. exact (abgrshombinop_inv f).
      * use make_isinv.
          intros f. exact (abgrshombinop_linvax f).
          intros f. exact (abgrshombinop_rinvax f).
  - intros f g. exact (abmonoidshombinop_comm f g).
Defined.

Definition abgrshomabgr (X Y : abgr) : abgr.
Proof.
  use make_abgr.
  - exact (abmonoidshomabmonoid X Y).
  - exact (abgrshomabgr_isabgrop X Y).
Defined.


(** *** (X = Y) ≃ (monoidiso X Y)
   The idea is to use the following composition

        (X = Y) ≃ (make_abgr' X = make_abgr' Y)
                ≃ (pr1 (make_abgr' X) = pr1 (make_abgr' Y))
                ≃ (monoidiso X Y)

    We use abgr' so that we can use univalence for groups, [gr_univalence]. See
    [abgr_univalence_weq3].
 *)

Local Definition abgr' : UU :=
  ∑ g : (∑ X : setwithbinop, isgrop (@op X)), iscomm (pr2 (pr1 g)).

Local Definition make_abgr' (X : abgr) : abgr' :=
  (pr1 X ,, dirprod_pr1 (pr2 X)) ,, dirprod_pr2 (pr2 X).

Local Definition abgr_univalence_weq1 : abgr ≃ abgr' :=
  weqtotal2asstol (λ Z : setwithbinop, isgrop (@op Z))
                  (λ y : (∑ x : setwithbinop, isgrop (@op x)), iscomm (@op (pr1 y))).

Definition abgr_univalence_weq1' (X Y : abgr) : (X = Y) ≃ (make_abgr' X = make_abgr' Y) :=
  make_weq _ (@isweqmaponpaths abgr abgr' abgr_univalence_weq1 X Y).

Definition abgr_univalence_weq2 (X Y : abgr) :
  (make_abgr' X = make_abgr' Y) ≃ (pr1 (make_abgr' X) = pr1 (make_abgr' Y)).
Proof.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque abgr_univalence_weq2.

Definition abgr_univalence_weq3 (X Y : abgr) :
  (pr1 (make_abgr' X) = pr1 (make_abgr' Y)) ≃ (monoidiso X Y) :=
  gr_univalence (pr1 (make_abgr' X)) (pr1 (make_abgr' Y)).

Definition abgr_univalence_map (X Y : abgr) : (X = Y) → (monoidiso X Y).
Proof.
  intro e. induction e. exact (idmonoidiso X).
Defined.

Lemma abgr_univalence_isweq (X Y : abgr) : isweq (abgr_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (abgr_univalence_weq1' X Y)
                   (weqcomp (abgr_univalence_weq2 X Y) (abgr_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque abgr_univalence_isweq.

Definition abgr_univalence (X Y : abgr) : (X = Y) ≃ (monoidiso X Y)
  := make_weq
    (abgr_univalence_map X Y)
    (abgr_univalence_isweq X Y).


(** *** Subobjects *)

Definition subabgr (X : abgr) := subgr X.
Identity Coercion id_subabgr : subabgr >-> subgr.

Lemma isabgrcarrier {X : abgr} (A : subgr X) : isabgrop (@op A).
Proof.
  split with (isgrcarrier A).
  apply (pr2 (@isabmonoidcarrier X A)).
Defined.

Definition carrierofasubabgr {X : abgr} (A : subabgr X) : abgr.
Proof. split with A. apply isabgrcarrier. Defined.
Coercion carrierofasubabgr : subabgr >-> abgr.

Definition subabgr_incl {X : abgr} (A : subabgr X) : monoidfun A X :=
  submonoid_incl A.

Definition abgr_kernel_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype A :=
  monoid_kernel_hsubtype f.

Definition abgr_image_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype B :=
  (λ y : B, ∃ x : A, (f x) = y).

(** * Kernels
    Let f : X → Y be a morphism of abelian groups. A kernel of f is given by the subgroup of X
    consisting of elements x such that [f x = 0].
 *)

(** ** Kernel as abelian group *)

Definition abgr_Kernel_subabgr_issubgr {A B : abgr} (f : monoidfun A B) :
  issubgr (abgr_kernel_hsubtype f).
Proof.
  use make_issubgr.
  - apply kernel_issubmonoid.
  - intros x a.
    apply (grrcan B (f x)).
    refine (! (binopfunisbinopfun f (grinv A x) x) @ _).
    refine (maponpaths (λ a : A, f a) (grlinvax A x) @ _).
    refine (monoidfununel f @ !_).
    refine (lunax B (f x) @ _).
    exact a.
Defined.

Definition abgr_Kernel_subabgr {A B : abgr} (f : monoidfun A B) : @subabgr A :=
  subgrconstr (@abgr_kernel_hsubtype A B f) (abgr_Kernel_subabgr_issubgr f).

(** ** The inclusion Kernel f --> X is a morphism of abelian groups *)

Definition abgr_Kernel_monoidfun_ismonoidfun {A B : abgr} (f : monoidfun A B) :
  @ismonoidfun (abgr_Kernel_subabgr f) A
               (make_incl (pr1carrier (abgr_kernel_hsubtype f))
                         (isinclpr1carrier (abgr_kernel_hsubtype f))).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use idpath.
  - use idpath.
Qed.

  (** ** Image of f is a subgroup *)

Definition abgr_image_issubgr {A B : abgr} (f : monoidfun A B) : issubgr (abgr_image_hsubtype f).
Proof.
  use make_issubgr.
  - use make_issubmonoid.
    + intros a a'.
      use (hinhuniv _ (pr2 a)). intros ae.
      use (hinhuniv _ (pr2 a')). intros a'e.
      use hinhpr.
      use tpair.
      * exact (@op A (pr1 ae) (pr1 a'e)).
      * refine (binopfunisbinopfun f (pr1 ae) (pr1 a'e) @ _).
        use two_arg_paths.
          exact (pr2 ae).
          exact (pr2 a'e).
    + use hinhpr. use tpair.
      * exact (unel A).
      * exact (monoidfununel f).
  - intros b b'.
    use (hinhuniv _ b'). intros eb.
    use hinhpr.
    use tpair.
    + exact (grinv A (pr1 eb)).
    + refine (_ @ maponpaths (λ bb : B, (grinv B bb)) (pr2 eb)).
      use monoidfuninvtoinv.
Qed.

Definition abgr_image {A B : abgr} (f : monoidfun A B) : @subabgr B :=
  @subgrconstr B (@abgr_image_hsubtype A B f) (abgr_image_issubgr f).


(** *** Quotient objects *)

Lemma isabgrquot {X : abgr} (R : binopeqrel X) : isabgrop (@op (setwithbinopquot R)).
Proof.
  split with (isgrquot R).
  apply (pr2 (@isabmonoidquot X R)).
Defined.

Definition abgrquot {X : abgr} (R : binopeqrel X) : abgr.
Proof. split with (setwithbinopquot R). apply isabgrquot. Defined.


(** *** Direct products *)

Lemma isabgrdirprod (X Y : abgr) : isabgrop (@op (setwithbinopdirprod X Y)).
Proof.
  split with (isgrdirprod X Y).
  apply (pr2 (isabmonoiddirprod X Y)).
Defined.

Definition abgrdirprod (X Y : abgr) : abgr.
Proof.
  split with (setwithbinopdirprod X Y).
  apply isabgrdirprod.
Defined.

Section Fractions.

Definition hrelabgrdiff (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2, ∃ (x0 : X), (pr1 xa1 + pr2 xa2) + x0 = (pr1 xa2 + pr2 xa1) + x0.

Definition abgrdiffphi (X : abmonoid) (xa : X × X) :
  X × (totalsubtype X) := pr1 xa ,, make_carrier (λ x : X, htrue) (pr2 xa) tt.

Definition hrelabgrdiff' (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2, eqrelabmonoidfrac X (totalsubmonoid X) (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqhrelsabgrdiff (X : abmonoid) : hrellogeq (hrelabgrdiff' X) (hrelabgrdiff X).
Proof.
  split. simpl. apply hinhfun. intro t2.
  set (a0 := pr1 (pr1 t2)). split with a0. apply (pr2 t2). simpl.
  apply hinhfun. intro t2. set (x0 := pr1 t2). split with (x0 ,, tt).
  apply (pr2 t2).
Defined.

Lemma iseqrelabgrdiff (X : abmonoid) : iseqrel (hrelabgrdiff X).
Proof.
  apply (iseqrellogeqf (logeqhrelsabgrdiff X)).
  apply (iseqrelconstr).
  intros xx' xx'' xx'''.
  intros r1 r2.
  apply (eqreltrans (eqrelabmonoidfrac X (totalsubmonoid X)) _ _ _ r1 r2).
  intro xx. apply (eqrelrefl (eqrelabmonoidfrac X (totalsubmonoid X)) _).
  intros xx xx'. intro r.
  apply (eqrelsymm (eqrelabmonoidfrac X (totalsubmonoid X)) _ _ r).
Qed.

Definition eqrelabgrdiff (X : abmonoid) : @eqrel (abmonoiddirprod X X) :=
  make_eqrel _ (iseqrelabgrdiff X).

Lemma isbinophrelabgrdiff (X : abmonoid) : @isbinophrel (abmonoiddirprod X X) (hrelabgrdiff X).
Proof.
  apply (@isbinophrellogeqf (abmonoiddirprod X X) _ _ (logeqhrelsabgrdiff X)).
  split. intros a b c r.
  apply (pr1 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (pr1 c ,, make_carrier (λ x : X, htrue) (pr2 c) tt)
             r).
  intros a b c r.
  apply (pr2 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (pr1 c ,, make_carrier (λ x : X, htrue) (pr2 c) tt)
             r).
Qed.

Definition binopeqrelabgrdiff (X : abmonoid) : binopeqrel (abmonoiddirprod X X) :=
  make_binopeqrel (eqrelabgrdiff X) (isbinophrelabgrdiff X).

Definition abgrdiffcarrier (X : abmonoid) : abmonoid := @abmonoidquot (abmonoiddirprod X X)
                                                                      (binopeqrelabgrdiff X).

Definition abgrdiffinvint (X : abmonoid) : X × X → X × X :=
  λ xs, pr2 xs ,, pr1 xs.

Lemma abgrdiffinvcomp (X : abmonoid) :
  iscomprelrelfun (hrelabgrdiff X) (eqrelabgrdiff X) (abgrdiffinvint X).
Proof.
  unfold iscomprelrelfun. unfold eqrelabgrdiff. unfold hrelabgrdiff.
  unfold eqrelabmonoidfrac. unfold hrelabmonoidfrac. simpl. intros xs xs'.
  apply (hinhfun). intro tt0.
  set (x := pr1 xs). set (s := pr2 xs).
  set (x' := pr1 xs'). set (s' := pr2 xs').
  split with (pr1 tt0).
  destruct tt0 as [ a eq ]. change (s + x' + a = s' + x + a).
  set(e := commax X s' x). simpl in e. rewrite e. clear e.
  set (e := commax X s x'). simpl in e. rewrite e. clear e.
  exact (!eq).
Qed.

Definition abgrdiffinv (X : abmonoid) : abgrdiffcarrier X → abgrdiffcarrier X :=
  setquotfun (hrelabgrdiff X) (eqrelabgrdiff X) (abgrdiffinvint X) (abgrdiffinvcomp X).

Lemma abgrdiffisinv (X : abmonoid) :
  isinv (@op (abgrdiffcarrier X)) 0 (abgrdiffinv X).
Proof.
  set (R := eqrelabgrdiff X).
  assert (isl : islinv (@op (abgrdiffcarrier X)) 0 (abgrdiffinv X)).
  {
    unfold islinv.
    apply (setquotunivprop R (λ x, _ = _)%logic).
    intro xs.
    set (x := pr1 xs). set (s := pr2 xs).
    apply (iscompsetquotpr R (@op (abmonoiddirprod X X) (abgrdiffinvint X xs) xs) 0).
    simpl. apply hinhpr. split with (unel X).
    change (s + x + 0 + 0 = 0 + (x + s) + 0).
    destruct (commax X x s). destruct (commax X 0 (x + s)).
    apply idpath.
  }
  exact (isl ,, weqlinvrinv (@op (abgrdiffcarrier X)) (commax (abgrdiffcarrier X))
                                      0 (abgrdiffinv X) isl).
Qed.

Definition abgrdiff (X : abmonoid) : abgr
  := abgrconstr (abgrdiffcarrier X) (abgrdiffinv X) (abgrdiffisinv X).

Definition prabgrdiff (X : abmonoid) : X → X → abgrdiff X :=
  λ x x' : X, setquotpr (eqrelabgrdiff X) (x ,, x').


(** *** Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrdiffint (X : abmonoid) : weq (X × X) (X × totalsubtype X) :=
  weqdirprodf (idweq X) (invweq (weqtotalsubtype X)).

Definition weqabgrdiff (X : abmonoid) : weq (abgrdiff X) (abmonoidfrac X (totalsubmonoid X)).
Proof.
  intros.
  apply (weqsetquotweq (eqrelabgrdiff X)
                       (eqrelabmonoidfrac X (totalsubmonoid X)) (weqabgrdiffint X)).
  - simpl. intros x x'. destruct x as [ x1 x2 ]. destruct x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. destruct tt0 as [ xx0 is0 ].
    split with (make_carrier (λ x : X, htrue) xx0 tt). apply is0.
  - simpl. intros x x'. destruct x as [ x1 x2 ]. destruct x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. destruct tt0 as [ xx0 is0 ].
    split with (pr1 xx0). apply is0.
Defined.


(** *** Canonical homomorphism to the abelian group of fractions *)

Definition toabgrdiff (X : abmonoid) (x : X) : abgrdiff X := setquotpr _ (x ,, 0).

Lemma isbinopfuntoabgrdiff (X : abmonoid) : isbinopfun (toabgrdiff X).
Proof.
  unfold isbinopfun. intros x1 x2.
  change (setquotpr _ (x1 + x2 ,, 0) =
          setquotpr (eqrelabgrdiff X) (x1 + x2 ,, 0 + 0)).
  apply (maponpaths (setquotpr _)).
  apply (@pathsdirprod X X).
  - apply idpath.
  - exact (!lunax X 0).
Defined.

Lemma isunitalfuntoabgrdiff (X : abmonoid) : toabgrdiff X 0 = 0.
Proof. apply idpath. Defined.

Definition ismonoidfuntoabgrdiff (X : abmonoid) : ismonoidfun (toabgrdiff X) :=
  isbinopfuntoabgrdiff X ,, isunitalfuntoabgrdiff X.


(** *** Abelian group of fractions in the case when all elements are cancelable *)

Lemma isinclprabgrdiff (X : abmonoid) (iscanc : ∏ x : X, isrcancelable (@op X) x) :
  ∏ x' : X, isincl (λ x, prabgrdiff X x x').
Proof.
  intros.
  set (int := isinclprabmonoidfrac X (totalsubmonoid X) (λ a : totalsubmonoid X, iscanc (pr1 a))
                                   (make_carrier (λ x : X, htrue) x' tt)).
  set (int1 := isinclcomp (make_incl _ int) (weqtoincl (invweq (weqabgrdiff X)))).
  apply int1.
Defined.

Definition isincltoabgrdiff (X : abmonoid) (iscanc : ∏ x : X, isrcancelable (@op X) x) :
  isincl (toabgrdiff X) := isinclprabgrdiff X iscanc 0.

Lemma isdeceqabgrdiff (X : abmonoid) (iscanc : ∏ x : X, isrcancelable (@op X) x) (is : isdeceq X) :
  isdeceq (abgrdiff X).
Proof.
  intros.
  apply (isdeceqweqf (invweq (weqabgrdiff X))).
  apply (isdeceqabmonoidfrac X (totalsubmonoid X) (λ a : totalsubmonoid X, iscanc (pr1 a)) is).
Defined.


(** *** Relations on the abelian group of fractions *)

Definition abgrdiffrelint (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa yb, ∃ (c0 : X), L ((pr1 xa + pr2 yb) + c0) ((pr1 yb + pr2 xa) + c0).

Definition abgrdiffrelint' (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa1 xa2, abmonoidfracrelint _ (totalsubmonoid X) L (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqabgrdiffrelints (X : abmonoid) (L : hrel X) :
  hrellogeq (abgrdiffrelint' X L) (abgrdiffrelint X L).
Proof.
  split. unfold abgrdiffrelint. unfold abgrdiffrelint'.
  simpl. apply hinhfun. intro t2. set (a0 := pr1 (pr1 t2)).
  split with a0. apply (pr2 t2). simpl. apply hinhfun.
  intro t2. set (x0 := pr1 t2). split with (x0 ,, tt). apply (pr2 t2).
Defined.

Lemma iscomprelabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrel (eqrelabgrdiff X) (abgrdiffrelint X L).
Proof.
  apply (iscomprelrellogeqf1 _ (logeqhrelsabgrdiff X)).
  apply (iscomprelrellogeqf2 _ (logeqabgrdiffrelints X L)).
  intros x x' x0 x0' r r0.
  apply (iscomprelabmonoidfracrelint
           _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)  _ _ _ _ r r0).
Qed.

Definition abgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) :=
  quotrel (iscomprelabgrdiffrelint X is).

Definition abgrdiffrel' (X : abmonoid) {L : hrel X} (is : isbinophrel L) : hrel (abgrdiff X) :=
  λ x x', abmonoidfracrel X (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                           (weqabgrdiff X x) (weqabgrdiff X x').

Definition logeqabgrdiffrels (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  hrellogeq (abgrdiffrel' X is) (abgrdiffrel X is).
Proof.
  intros x1 x2. split.
  - assert (int : ∏ x x', isaprop (abgrdiffrel' X is x x' → abgrdiffrel X is x x')).
    {
      intros x x'.
      apply impred. intro.
      apply (pr2 _).
    }
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', make_hProp _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint' X L x x') → (abgrdiffrelint _ L x x')).
    apply (pr1 (logeqabgrdiffrelints X L x x')).
  - assert (int : ∏ x x', isaprop (abgrdiffrel X is x x' → abgrdiffrel' X is x x')).
    intros x x'.
    apply impred. intro.
    apply (pr2 _).
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', make_hProp _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint X L x x') → (abgrdiffrelint' _ L x x')).
    apply (pr2 (logeqabgrdiffrelints X L x x')).
Defined.

Lemma istransabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istrans L) :
  istrans (abgrdiffrelint X L).
Proof.
  apply (istranslogeqf (logeqabgrdiffrelints X L)).
  intros a b c rab rbc.
  apply (istransabmonoidfracrelint
           _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)  isl _ _ _ rab rbc).
Qed.

Lemma istransabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istrans L) :
  istrans (abgrdiffrel X is).
Proof.
  refine (istransquotrel _ _). apply istransabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma issymmabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : issymm L) :
  issymm (abgrdiffrelint X L).
Proof.
  apply (issymmlogeqf (logeqabgrdiffrelints X L)).
  intros a b rab.
  apply (issymmabmonoidfracrelint _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is) isl _ _ rab).
Qed.

Lemma issymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : issymm L) :
  issymm (abgrdiffrel X is).
Proof.
  refine (issymmquotrel _ _). apply issymmabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isreflabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isrefl L) :
  isrefl (abgrdiffrelint X L).
Proof.
  intro xa. unfold abgrdiffrelint. simpl.
  apply hinhpr. split with (unel X). apply (isl _).
Defined.

Lemma isreflabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isrefl L) :
  isrefl (abgrdiffrel X is).
Proof.
  refine (isreflquotrel _ _). apply isreflabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma ispoabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : ispreorder L) :
  ispreorder (abgrdiffrelint X L).
Proof.
  split with (istransabgrdiffrelint X is (pr1 isl)).
  apply (isreflabgrdiffrelint X is (pr2 isl)).
Defined.

Lemma ispoabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : ispreorder L) :
  ispreorder (abgrdiffrel X is).
Proof.
  refine (ispoquotrel _ _). apply ispoabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iseqrelabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iseqrel L) :
  iseqrel (abgrdiffrelint X L).
Proof.
  split with (ispoabgrdiffrelint X is (pr1 isl)).
  apply (issymmabgrdiffrelint X is (pr2 isl)).
Defined.

Lemma iseqrelabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iseqrel L) :
  iseqrel (abgrdiffrel X is).
Proof.
  refine (iseqrelquotrel _ _). apply iseqrelabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isantisymmnegabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L)
      (isl : isantisymmneg L) : isantisymmneg (abgrdiffrel X is).
Proof.
  apply (isantisymmneglogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  set (int := isantisymmnegabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                           isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
  apply (invmaponpathsweq _ _ _ int).
Defined.

Lemma isantisymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isantisymm L) :
  isantisymm (abgrdiffrel X is).
Proof.
  apply (isantisymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  set (int := isantisymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                        isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
  apply (invmaponpathsweq _ _ _ int).
Qed.

Lemma isirreflabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isirrefl L) :
  isirrefl (abgrdiffrel X is).
Proof.
  apply (isirrefllogeqf (logeqabgrdiffrels X is)).
  intros a raa.
  apply (isirreflabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                 isl (weqabgrdiff X a) raa).
Qed.

Lemma isasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isasymm L) :
  isasymm (abgrdiffrel X is).
Proof.
  apply (isasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  apply (isasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
Qed.

Lemma iscoasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscoasymm L) :
  iscoasymm (abgrdiffrel X is).
Proof.
  apply (iscoasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab.
  apply (iscoasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) rab).
Qed.

Lemma istotalabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istotal L) :
  istotal (abgrdiffrel X is).
Proof.
  apply (istotallogeqf (logeqabgrdiffrels X is)).
  intros a b.
  apply (istotalabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b)).
Qed.

Lemma iscotransabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscotrans L) :
  iscotrans (abgrdiffrel X is).
Proof.
  apply (iscotranslogeqf (logeqabgrdiffrels X is)).
  intros a b c.
  apply (iscotransabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) (weqabgrdiff X c)).
Qed.

Lemma isStrongOrder_abgrdiff {X : abmonoid} (gt : hrel X)
      (Hgt : isbinophrel gt) :
  isStrongOrder gt → isStrongOrder (abgrdiffrel X Hgt).
Proof.
  intros H.
  repeat split.
  - apply istransabgrdiffrel, (istrans_isStrongOrder H).
  - apply iscotransabgrdiffrel, (iscotrans_isStrongOrder H).
  - apply isirreflabgrdiffrel, (isirrefl_isStrongOrder H).
Qed.

Definition StrongOrder_abgrdiff {X : abmonoid} (gt : StrongOrder X)
           (Hgt : isbinophrel gt) : StrongOrder (abgrdiff X) :=
  abgrdiffrel X Hgt,, isStrongOrder_abgrdiff gt Hgt (pr2 gt).

Lemma abgrdiffrelimpl (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (impl : ∏ x x', L x x' → L' x x') (x x' : abgrdiff X) (ql : abgrdiffrel X is x x') :
  abgrdiffrel X is' x x'.
Proof.
  generalize ql. refine (quotrelimpl _ _ _ _ _).
  intros x0 x0'. simpl. apply hinhfun. intro t2. split with (pr1 t2).
  apply (impl _ _ (pr2 t2)).
Qed.

Lemma abgrdiffrellogeq (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abgrdiff X) :
  (abgrdiffrel X is x x') <-> (abgrdiffrel X is' x x').
Proof.
  refine (quotrellogeq _ _ _ _ _). intros x0 x0'. split.
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr1 (lg _ _) (pr2 t2)).
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr2 (lg _ _) (pr2 t2)).
Qed.

Lemma isbinopabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  @isbinophrel (setwithbinopdirprod X X) (abgrdiffrelint X L).
Proof.
  apply (isbinophrellogeqf (logeqabgrdiffrelints X L)). split.
  - intros a b c lab.
    apply (pr1 (ispartbinopabmonoidfracrelint _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is))
               (abgrdiffphi X a) (abgrdiffphi X b) (abgrdiffphi X c) tt lab).
  - intros a b c lab.
    apply (pr2 (ispartbinopabmonoidfracrelint _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is))
               (abgrdiffphi X a) (abgrdiffphi X b) (abgrdiffphi X c) tt lab).
Qed.

Lemma isbinopabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  @isbinophrel (abgrdiff X) (abgrdiffrel X is).
Proof.
  intros.
  apply (isbinopquotrel (binopeqrelabgrdiff X) (iscomprelabgrdiffrelint X is)).
  apply (isbinopabgrdiffrelint X is).
Defined.

Definition isdecabgrdiffrelint (X : abmonoid) {L : hrel X}
           (is : isinvbinophrel L) (isl : isdecrel L) : isdecrel (abgrdiffrelint X L).
Proof.
  intros xa1 xa2.
  set (x1 := pr1 xa1). set (a1 := pr2 xa1).
  set (x2 := pr1 xa2). set (a2 := pr2 xa2).
  assert (int : coprod (L (x1 + a2) (x2 + a1)) (neg (L (x1 + a2) (x2 + a1)))) by apply (isl _ _).
  destruct int as [ l | nl ].
  - apply ii1. unfold abgrdiffrelint. apply hinhpr. split with 0.
    rewrite (runax X _). rewrite (runax X _). apply l.
  - apply ii2. generalize nl. clear nl. apply negf. unfold abgrdiffrelint.
    simpl. apply (@hinhuniv _ (make_hProp _ (pr2 (L _ _)))).
    intro t2l. destruct t2l as [ c0a l ]. simpl. apply ((pr2 is) _ _ c0a l).
Defined.

Definition isdecabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L)
           (isi : isinvbinophrel L) (isl : isdecrel L) : isdecrel (abgrdiffrel X is).
Proof.
  refine (isdecquotrel _ _). apply isdecabgrdiffrelint.
  - apply isi.
  - apply isl.
Defined.


(** *** Relations and the canonical homomorphism to [ abgrdiff ] *)

Lemma iscomptoabgrdiff (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrelfun L (abgrdiffrel X is) (toabgrdiff X).
Proof.
  unfold iscomprelrelfun.
  intros x x' l.
  change (abgrdiffrelint X L (x ,, 0) (x' ,, 0)).
  simpl. apply (hinhpr). split with (unel X).
  apply ((pr2 is) _ _ 0). apply ((pr2 is) _ _ 0).
  apply l.
Qed.

End Fractions.
