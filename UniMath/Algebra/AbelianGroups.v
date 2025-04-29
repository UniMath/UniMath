(**

  Abelian (Commutative) Groups

  Contents
  1. Basic definitions
  2. Subobjects
  3. Kernels
  4. Quotient objects
  5. Direct products
  6. Abelian group of fractions of an abelian unitary monoid
  7. Abelian group of fractions and abelian monoid of fractions
  8. Canonical homomorphism to the abelian group of fractions
  9. Abelian group of fractions in the case when all elements are cancelable
  10. Relations on the abelian group of fractions
  11. Relations and the canonical homomorphism to [abgrdiff]

 *)
Require Import UniMath.MoreFoundations.Orders.
Require Import UniMath.MoreFoundations.Subtypes.

Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Export UniMath.Algebra.Groups2.
Require Export UniMath.Algebra.AbelianMonoids.

(** * 1. Basic definitions *)

Local Open Scope addmonoid.

Definition abgr : UU := abelian_group_category.

Definition make_abgr (X : setwithbinop) (is : isabgrop (@op X)) : abgr :=
  X ,, is.

Definition abgrconstr (X : abmonoid) (inv0 : X → X) (is : isinv (@op X) 0 inv0) : abgr.
Proof.
  use make_abgr.
  - exact X.
  - use make_isabgrop.
    + use make_isgrop.
      * apply (make_ismonoidop (assocax X)).
        exact (make_isunital (unel X) (unax X)).
      * exact (make_invstruct inv0 is).
    + exact (commax X).
Defined.

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

Definition abelian_group_morphism
  (X Y : abgr)
  : UU
  := abelian_group_category⟦X, Y⟧%cat.

Definition abelian_group_morphism_to_group_morphism
  {X Y : abgr}
  (f : abelian_group_morphism X Y)
  : group_morphism X Y
  := pr1 f ,, pr12 f.

Coercion abelian_group_morphism_to_group_morphism : abelian_group_morphism >-> group_morphism.

Definition abelian_group_to_monoid_morphism
  {X Y : abgr}
  (f : abelian_group_morphism X Y)
  : abelian_monoid_morphism X Y.
Proof.
  use make_abelian_monoid_morphism.
  - exact f.
  - apply make_ismonoidfun.
    + apply binopfunisbinopfun.
    + exact (monoidfununel f).
Defined.

Definition make_abelian_group_morphism
  {X Y : abgr}
  (f : X → Y)
  (H : isbinopfun f)
  : abelian_group_morphism X Y
  := (f ,, H) ,, (((tt ,, binopfun_preserves_unit f H) ,, binopfun_preserves_inv f H) ,, tt).

Definition binopfun_to_abelian_group_morphism
  {X Y : abgr}
  (f : binopfun X Y)
  : abelian_group_morphism X Y
  := make_abelian_group_morphism f (binopfunisbinopfun f).

Lemma abelian_group_morphism_paths
  {X Y : abgr}
  (f g : abelian_group_morphism X Y)
  (H : (f : X → Y) = g)
  : f = g.
Proof.
  apply subtypePath.
  {
    refine (λ (h : magma_morphism _ _), _).
    refine (isapropdirprod _ _ _ isapropunit).
    apply (isapropdirprod _ (∏ x, (h (grinv X x) = grinv Y (h x)))).
    - apply (isapropdirprod _ _ isapropunit).
      apply setproperty.
    - apply impred_isaprop.
      intro.
      apply setproperty.
  }
  apply binopfun_paths.
  exact H.
Qed.

Definition abelian_group_morphism_eq
  {X Y : abgr}
  {f g : abelian_group_morphism X Y}
  : (f = g) ≃ (∏ x, f x = g x).
Proof.
  use weqimplimpl.
  - intros e x.
    exact (maponpaths (λ (f : abelian_group_morphism _ _), f x) e).
  - intro e.
    apply abelian_group_morphism_paths, funextfun.
    exact e.
  - abstract apply homset_property.
  - abstract (
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
Defined.

Definition identity_abelian_group_morphism
  (X : abgr)
  : abelian_group_morphism X X
  := identity X.

Definition composite_abelian_group_morphism
  {X Y Z : abgr}
  (f : abelian_group_morphism X Y)
  (g : abelian_group_morphism Y Z)
  : abelian_group_morphism X Z
  := (f · g)%cat.

(** *** Construction of the trivial abgr consisting of one element given by unit. *)

Definition unitabgr_isabgrop : isabgrop (@op unitabmonoid).
Proof.
  use make_isabgrop.
  - exact unitgr_isgrop.
  - exact (commax unitabmonoid).
Qed.

Definition unitabgr : abgr := make_abgr unitabmonoid unitabgr_isabgrop.

Definition unel_abelian_group_morphism (X Y : abgr) : abelian_group_morphism X Y :=
  binopfun_to_abelian_group_morphism (unelmonoidfun X Y).

(** *** Abelian group structure on morphism between abelian groups *)

Definition abgrshombinop
  {X Y : abgr} (f g : abelian_group_morphism X Y)
  : abelian_group_morphism X Y.
Proof.
  apply binopfun_to_abelian_group_morphism.
  exact (abmonoidshombinop (X := X) (Y := Y) f g).
Defined.

Definition abgrshombinop_inv_isbinopfun {X Y : abgr} (f : abelian_group_morphism X Y) :
  isbinopfun (λ x : X, grinv Y (f x)).
Proof.
  apply make_isbinopfun. intros x x'. cbn.
  rewrite (monoidfunmul f). rewrite (pr2 (pr2 Y)). apply (grinvop Y).
Qed.

Definition abgrshombinop_inv {X Y : abgr} (f : abelian_group_morphism X Y) : abelian_group_morphism X Y :=
  make_abelian_group_morphism _ (abgrshombinop_inv_isbinopfun f).

Definition abgrshombinop_linvax {X Y : abgr} (f : abelian_group_morphism X Y) :
  abgrshombinop (abgrshombinop_inv f) f = unel_abelian_group_morphism X Y.
Proof.
  apply abelian_group_morphism_eq. intros x. apply (@grlinvax Y).
Qed.

Definition abgrshombinop_rinvax {X Y : abgr} (f : abelian_group_morphism X Y) :
  abgrshombinop f (abgrshombinop_inv f) = unel_abelian_group_morphism X Y.
Proof.
  apply abelian_group_morphism_eq. intros x. apply (grrinvax Y).
Qed.

Lemma abgrshomabgr_isabgrop (X Y : abgr) :
  isabgrop (abgrshombinop (X := X) (Y := Y)).
Proof.
  use make_isabgrop.
  - use make_isgrop.
    + apply make_ismonoidop.
      * abstract (
          do 3 intro;
          apply abelian_group_morphism_eq;
          intro;
          apply assocax
        ).
      * apply (make_isunital (unel_abelian_group_morphism X Y));
          abstract (
            apply make_isunit;
            intro;
            apply abelian_group_morphism_eq;
            intro;
            [ apply lunax
            | apply runax ]
          ).
    + use make_invstruct.
      * intros f. exact (abgrshombinop_inv f).
      * use make_isinv.
          intros f. exact (abgrshombinop_linvax f).
          intros f. exact (abgrshombinop_rinvax f).
  - abstract (
      intros f g;
      apply abelian_group_morphism_eq;
      intro;
      apply (commax Y)
    ).
Defined.

Definition abgrshomabgr (X Y : abgr) : abgr.
Proof.
  use make_abgr.
  - exact (make_setwithbinop (homset X Y) abgrshombinop).
  - exact (abgrshomabgr_isabgrop X Y).
Defined.


(** * 2. Subobjects *)

Definition subabgr (X : abgr) := subgr X.
Identity Coercion id_subabgr : subabgr >-> subgr.

Lemma isabgrcarrier {X : abgr} (A : subgr X) : isabgrop (@op A).
Proof.
  exists (isgrcarrier A).
  apply (pr2 (@isabmonoidcarrier X A)).
Defined.

Definition carrierofasubabgr {X : abgr} (A : subabgr X) : abgr.
Proof.
  use make_abgr.
  - exact A.
  - apply isabgrcarrier.
Defined.
Coercion carrierofasubabgr : subabgr >-> abgr.

Definition subabgr_incl {X : abgr} (A : subabgr X) : abelian_group_morphism A X :=
  binopfun_to_abelian_group_morphism (X := A) (submonoid_incl A).

Definition abgr_kernel_hsubtype {A B : abgr} (f : abelian_group_morphism A B) : hsubtype A :=
  monoid_kernel_hsubtype f.

Definition abgr_image_hsubtype {A B : abgr} (f : abelian_group_morphism A B) : hsubtype B :=
  (λ y : B, ∃ x : A, (f x) = y).

(** * 3. Kernels
    Let f : X → Y be a morphism of abelian groups. A kernel of f is given by the subgroup of X
    consisting of elements x such that [f x = 0].
 *)

(** ** Kernel as abelian group *)

Definition abgr_Kernel_subabgr_issubgr {A B : abgr} (f : abelian_group_morphism A B) :
  issubgr (abgr_kernel_hsubtype f).
Proof.
  apply make_issubgr.
  - apply kernel_issubmonoid.
  - intros x a.
    apply (grrcan B (f x)).
    refine (! (binopfunisbinopfun f (grinv A x) x) @ _).
    refine (maponpaths (λ a : A, f a) (grlinvax A x) @ _).
    refine (monoidfununel f @ !_).
    refine (lunax B (f x) @ _).
    exact a.
Defined.

Definition abgr_Kernel_subabgr {A B : abgr} (f : abelian_group_morphism A B) : @subabgr A :=
  subgrconstr (@abgr_kernel_hsubtype A B f) (abgr_Kernel_subabgr_issubgr f).

(** ** The inclusion Kernel f --> X is a morphism of abelian groups *)

Definition abgr_Kernel_abelian_group_morphism_isbinopfun {A B : abgr} (f : abelian_group_morphism A B) :
  isbinopfun (X := abgr_Kernel_subabgr f)
               (make_incl (pr1carrier (abgr_kernel_hsubtype f))
                         (isinclpr1carrier (abgr_kernel_hsubtype f))).
Proof.
  apply make_isbinopfun. intros x x'. apply idpath.
Qed.

  (** ** Image of f is a subgroup *)

Definition abgr_image_issubgr {A B : abgr} (f : abelian_group_morphism A B) : issubgr (abgr_image_hsubtype f).
Proof.
  apply make_issubgr.
  - apply make_issubmonoid.
    + intros a a'.
      refine (hinhuniv _ (pr2 a)). intros ae.
      refine (hinhuniv _ (pr2 a')). intros a'e.
      apply hinhpr.
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
      apply group_morphism_inv.
Qed.

Definition abgr_image {A B : abgr} (f : abelian_group_morphism A B) : @subabgr B :=
  @subgrconstr B (@abgr_image_hsubtype A B f) (abgr_image_issubgr f).


(** * 4. Quotient objects *)

Lemma isabgrquot {X : abgr} (R : binopeqrel X) : isabgrop (@op (setwithbinopquot R)).
Proof.
  exists (isgrquot R).
  apply (pr2 (@isabmonoidquot X R)).
Defined.

Definition abgrquot {X : abgr} (R : binopeqrel X) : abgr.
Proof. exists (setwithbinopquot R). apply isabgrquot. Defined.


(** * 5. Direct products *)

Lemma isabgrdirprod (X Y : abgr) : isabgrop (@op (setwithbinopdirprod X Y)).
Proof.
  exists (isgrdirprod X Y).
  apply (pr2 (isabmonoiddirprod X Y)).
Defined.

Definition abgrdirprod (X Y : abgr) : abgr.
Proof.
  exists (setwithbinopdirprod X Y).
  apply isabgrdirprod.
Defined.

(** * 6. Abelian group of fractions of an abelian unitary monoid *)

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
  set (a0 := pr1 (pr1 t2)). exists a0. apply (pr2 t2). simpl.
  apply hinhfun. intro t2. set (x0 := pr1 t2). exists (x0 ,, tt).
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
  exists (pr1 tt0).
  induction tt0 as [ a eq ]. change (s + x' + a = s' + x + a).
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
    simpl. apply hinhpr. exists (unel X).
    change (s + x + 0 + 0 = 0 + (x + s) + 0).
    induction (commax X x s). induction (commax X 0 (x + s)).
    apply idpath.
  }
  exact (isl ,, weqlinvrinv (@op (abgrdiffcarrier X)) (commax (abgrdiffcarrier X))
                                      0 (abgrdiffinv X) isl).
Qed.

Definition abgrdiff (X : abmonoid) : abgr
  := abgrconstr (abgrdiffcarrier X) (abgrdiffinv X) (abgrdiffisinv X).

Definition prabgrdiff (X : abmonoid) : X → X → abgrdiff X :=
  λ x x' : X, setquotpr (eqrelabgrdiff X) (x ,, x').


(** * 7. Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrdiffint (X : abmonoid) : weq (X × X) (X × totalsubtype X) :=
  weqdirprodf (idweq X) (invweq (weqtotalsubtype X)).

Definition weqabgrdiff (X : abmonoid) : weq (abgrdiff X) (abmonoidfrac X (totalsubmonoid X)).
Proof.
  intros.
  apply (weqsetquotweq (eqrelabgrdiff X)
                       (eqrelabmonoidfrac X (totalsubmonoid X)) (weqabgrdiffint X)).
  - simpl. intros x x'. induction x as [ x1 x2 ]. induction x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. induction tt0 as [ xx0 is0 ].
    exists (make_carrier (λ x : X, htrue) xx0 tt). apply is0.
  - simpl. intros x x'. induction x as [ x1 x2 ]. induction x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. induction tt0 as [ xx0 is0 ].
    exists (pr1 xx0). apply is0.
Defined.


(** * 8. Canonical homomorphism to the abelian group of fractions *)

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


(** * 9. Abelian group of fractions in the case when all elements are cancelable *)

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


(** * 10. Relations on the abelian group of fractions *)

Definition abgrdiffrelint (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa yb, ∃ (c0 : X), L ((pr1 xa + pr2 yb) + c0) ((pr1 yb + pr2 xa) + c0).

Definition abgrdiffrelint' (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa1 xa2, abmonoidfracrelint _ (totalsubmonoid X) L (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqabgrdiffrelints (X : abmonoid) (L : hrel X) :
  hrellogeq (abgrdiffrelint' X L) (abgrdiffrelint X L).
Proof.
  split. unfold abgrdiffrelint. unfold abgrdiffrelint'.
  simpl. apply hinhfun. intro t2. set (a0 := pr1 (pr1 t2)).
  exists a0. apply (pr2 t2). simpl. apply hinhfun.
  intro t2. set (x0 := pr1 t2). exists (x0 ,, tt). apply (pr2 t2).
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
  apply hinhpr. exists (unel X). apply (isl _).
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
  exists (istransabgrdiffrelint X is (pr1 isl)).
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
  exists (ispoabgrdiffrelint X is (pr1 isl)).
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
  intros x0 x0'. simpl. apply hinhfun. intro t2. exists (pr1 t2).
  apply (impl _ _ (pr2 t2)).
Qed.

Lemma abgrdiffrellogeq (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abgrdiff X) :
  (abgrdiffrel X is x x') <-> (abgrdiffrel X is' x x').
Proof.
  refine (quotrellogeq _ _ _ _ _). intros x0 x0'. split.
  - simpl. apply hinhfun. intro t2. exists (pr1 t2).
    apply (pr1 (lg _ _) (pr2 t2)).
  - simpl. apply hinhfun. intro t2. exists (pr1 t2).
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
  induction int as [ l | nl ].
  - apply ii1. unfold abgrdiffrelint. apply hinhpr. exists 0.
    rewrite (runax X _). rewrite (runax X _). apply l.
  - apply ii2. generalize nl. clear nl. apply negf. unfold abgrdiffrelint.
    simpl. apply (@hinhuniv _ (make_hProp _ (pr2 (L _ _)))).
    intro t2l. induction t2l as [ c0a l ]. simpl. apply ((pr2 is) _ _ c0a l).
Defined.

Definition isdecabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L)
           (isi : isinvbinophrel L) (isl : isdecrel L) : isdecrel (abgrdiffrel X is).
Proof.
  refine (isdecquotrel _ _). apply isdecabgrdiffrelint.
  - apply isi.
  - apply isl.
Defined.


(** * 11. Relations and the canonical homomorphism to [abgrdiff] *)

Lemma iscomptoabgrdiff (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrelfun L (abgrdiffrel X is) (toabgrdiff X).
Proof.
  unfold iscomprelrelfun.
  intros x x' l.
  change (abgrdiffrelint X L (x ,, 0) (x' ,, 0)).
  simpl. apply (hinhpr). exists (unel X).
  apply ((pr2 is) _ _ 0). apply ((pr2 is) _ _ 0).
  apply l.
Qed.

End Fractions.
