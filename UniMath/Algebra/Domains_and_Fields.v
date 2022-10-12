(** * Algebra I. Part E. Integral domains and fields. Vladimir Voevodsky. Aug. 2011 - . *)
Require Import UniMath.Algebra.Groups.
(** ** Contents
- Integral domains and fields
 - Integral domains
  - General definitions
  - Computation lemmas for integral domains
  - Multiplicative submonoid of non-zero elements
  - Relations similar to "greater" on integral domains
 - Fields
  - Main definitions
  - Field of fractions of an integral domain with decidable equality
  - Canonical homomorphism to the field of fractions
 - Relations similar to "greater" on field of fractions
  - Description of the field of fractions as the ring of fractions
    with respect to the submonoid of "positive" elements
  - Definition and properties of "greater" on the field of fractions
  - Relations and the canonical homomorphism to the field of fractions
*)

Local Open Scope logic.

(** ** Preamble *)

(** Settings *)

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Algebra.RigsAndRings.

(** To upstream files *)

(** To one binary operation *)

Lemma islcancelableif {X : hSet} (opp : binop X) (x : X)
      (is : ∏ a b : X, paths (opp x a) (opp x b) -> a = b) : islcancelable opp x.
Proof.
  intros. apply isinclbetweensets.
  - apply (setproperty X).
  - apply (setproperty X).
  - apply is.
Defined.

Lemma isrcancelableif {X : hSet} (opp : binop X) (x : X)
      (is : ∏ a b : X, paths (opp a x) (opp b x) -> a = b) : isrcancelable opp x.
Proof.
  intros. apply isinclbetweensets.
  - apply (setproperty X).
  - apply (setproperty X).
  - apply is.
Defined.

Definition iscancelableif {X : hSet} (opp : binop X) (x : X)
           (isl : ∏ a b : X, paths (opp x a) (opp x b) -> a = b)
           (isr : ∏ a b : X, paths (opp a x) (opp b x) -> a = b) :
  iscancelable opp x := make_dirprod (islcancelableif opp x isl) (isrcancelableif opp x isr).

(** To monoids *)

(** TODO: this has now been upstreamed to BinaryOperations.v, these should be
    expunged. *)

Local Open Scope multmonoid_scope.

Definition linvpair (X : monoid) (x : X) : UU := total2 (λ x' : X, paths (x' * x) 1).

Definition pr1linvpair (X : monoid) (x : X) : linvpair X x -> X := @pr1 _ _.

Definition linvpairxy (X : monoid) (x y : X) (x' : linvpair X x) (y' : linvpair X y) :
  linvpair X (x * y).
Proof.
  intros. split with ((pr1 y') * (pr1 x')).
  rewrite (assocax _ _ _ (x * y)).
  rewrite (pathsinv0 (assocax _ _ x y)).
  rewrite (pr2 x').
  rewrite (lunax _ y).
  rewrite (pr2 y').
  apply idpath.
Defined.

Definition lcanfromlinv (X : monoid) (a b c : X) (c' : linvpair X c) (e : paths (c * a) (c * b)) :
  a = b.
Proof.
  intros.
  set (e' := maponpaths (λ x : X, (pr1 c') * x) e). simpl in e'.
  rewrite (pathsinv0 (assocax X _ _ _)) in e'.
  rewrite (pathsinv0 (assocax X _ _ _)) in e'.
  rewrite (pr2 c') in e'.
  rewrite (lunax X a) in e'.
  rewrite (lunax X b) in e'.
  apply e'.
Defined.

Definition rinvpair (X : monoid) (x : X) : UU := total2 (λ x' : X, paths (x * x') 1).

Definition pr1rinvpair (X : monoid) (x : X) : rinvpair X x -> X := @pr1 _ _.

Definition rinvpairxy (X : monoid) (x y : X) (x' : rinvpair X x) (y' : rinvpair X y) :
  rinvpair X (x * y).
Proof.
  intros. split with ((pr1 y') * (pr1 x')).
  rewrite (assocax _ x y _).
  rewrite (pathsinv0 (assocax _ y _ _)).
  rewrite (pr2 y').
  rewrite (lunax _ _).
  rewrite (pr2 x').
  apply idpath.
Defined.

Definition rcanfromrinv (X : monoid) (a b c : X) (c' : rinvpair X c) (e : paths (a * c ) (b * c)) :
  a = b.
Proof.
  intros.
  set (e' := maponpaths (λ x : X, x * (pr1 c')) e). simpl in e'.
  rewrite (assocax X _ _ _)  in e'.
  rewrite (assocax X _ _ _) in e'.
  rewrite (pr2 c') in e'.
  rewrite (runax X a) in e'.
  rewrite (runax X b) in e'.
  apply e'.
Defined.

Lemma pathslinvtorinv (X : monoid) (x : X) (x' : linvpair X x) (x'' : rinvpair X x) :
  paths (pr1 x') (pr1 x'').
Proof.
  intros. destruct (runax X (pr1 x')). (*unfold p.*)
  destruct (pr2 x'').
  set (int := x * pr1 x'').
  rewrite <- (lunax X (pr1 x'')).
  destruct (pr2 x').  (*unfold p1.*)
  unfold int.
  apply (pathsinv0 (assocax X _ _ _)).
Defined.

Definition invpair (X : monoid) (x : X) : UU :=
  total2 (λ x' : X, dirprod (paths (x' * x) 1) (paths (x * x') 1)).

Definition pr1invpair (X : monoid) (x : X) : invpair X x -> X := @pr1 _ _.

Definition invtolinv (X : monoid) (x : X) (x' : invpair X x) : linvpair X x :=
  tpair _ (pr1 x') (pr1 (pr2 x')).

Definition invtorinv (X : monoid) (x : X) (x' : invpair X x) : rinvpair X x :=
  tpair _ (pr1 x') (pr2 (pr2 x')).

Lemma isapropinvpair (X : monoid) (x : X) : isaprop (invpair X x).
Proof.
  intros. apply invproofirrelevance. intros x' x''.
  apply (invmaponpathsincl
           _ (isinclpr1 _ (λ a, isapropdirprod _ _ (setproperty X _ _) (setproperty X _ _)))).
  apply (pathslinvtorinv X x (invtolinv X x x') (invtorinv X x x'')).
Defined.

Definition invpairxy (X : monoid) (x y : X) (x' : invpair X x) (y' : invpair X y) :
  invpair X (x * y).
Proof.
  intros. split with ((pr1 y') * (pr1 x')). split.
  - apply (pr2 (linvpairxy _ x y (invtolinv _ x x') (invtolinv _ y y'))).
  - apply (pr2 (rinvpairxy _ x y (invtorinv _ x x') (invtorinv _ y y'))).
Defined.

(** To groups *)

Lemma grfrompathsxy (X : gr) {a b : X} (e : a = b) : paths (op a (grinv X b)) (unel X).
Proof.
  intros.
  set (e' := maponpaths (λ x : X, op x (grinv X b)) e). simpl in e'.
  rewrite (grrinvax X _) in e'. apply e'.
Defined.

Lemma grtopathsxy (X : gr) {a b : X} (e : paths (op a (grinv X b)) (unel X) ) : a = b .
Proof.
  intros.
  set (e' := maponpaths (λ x, op x b) e). simpl in e'.
  rewrite (assocax X) in e'. rewrite (grlinvax X) in e'.
  rewrite (lunax X) in e'. rewrite (runax X) in e'.
  apply e'.
Defined.

(** To rigs *)

Definition multlinvpair (X : rig) (x : X) : UU := linvpair (rigmultmonoid X) x.

Definition multrinvpair (X : rig) (x : X) : UU := rinvpair (rigmultmonoid X) x.

Definition multinvpair (X : rig) (x : X) : UU := invpair (rigmultmonoid X) x.

Definition rigneq0andmultlinv (X : rig) (n m : X) (isnm : ((n * m) != 0)%rig) :
  n != 0%rig.
Proof.
  intros. intro e. rewrite e in isnm.
  rewrite (rigmult0x X) in isnm.
  destruct (isnm (idpath _)).
Defined.

Definition rigneq0andmultrinv (X : rig) (n m : X) (isnm : ((n * m) != 0)%rig) :
  m != 0%rig.
Proof.
  intros. intro e. rewrite e in isnm. rewrite (rigmultx0 _) in isnm.
  destruct (isnm (idpath _)).
Defined.

(** To rings *)

Local Open Scope ring_scope.

Definition ringneq0andmultlinv (X : ring) (n m : X) (isnm : ((n * m) != 0)) : n != 0.
Proof.
  intros. intro e. rewrite e in isnm.
  rewrite (ringmult0x X) in isnm.
  destruct (isnm (idpath _)).
Defined.

Definition ringneq0andmultrinv (X : ring) (n m : X) (isnm : ((n * m) != 0)) : m != 0.
Proof.
  intros. intro e. rewrite e in isnm.
  rewrite (ringmultx0 _) in isnm.
  destruct (isnm (idpath _)).
Defined.

Definition ringpossubmonoid (X : ring) {R : hrel X} (is1 : isringmultgt X R) (is2 : R 1 0) :
  @submonoid (ringmultmonoid X).
Proof.
  intros. split with (λ x, R x 0). split.
  - intros x1 x2. apply is1. apply (pr2 x1). apply (pr2 x2).
  - apply is2.
Defined.

Lemma isinvringmultgtif (X : ring) {R : hrel X} (is0 : @isbinophrel X R) (is1 : isringmultgt X R)
      (nc : neqchoice R) (isa : isasymm R) : isinvringmultgt X R.
Proof.
  intros. split.
  - intros a b rab0 ra0.
    assert (int : b != 0).
    {
      intro e. rewrite e in rab0. rewrite (ringmultx0 X _) in rab0.
      apply (isa _ _ rab0 rab0).
    }
    destruct (nc _ _ int) as [ g | l ].
    + apply g.
    + set (int' := ringmultgt0lt0 X is0 is1 ra0 l).
      destruct (isa _ _ rab0 int').
  - intros a b rab0 rb0.
    assert (int : a != 0).
    {
      intro e. rewrite e in rab0. rewrite (ringmult0x X _) in rab0.
      apply (isa _ _ rab0 rab0).
    }
    destruct (nc _ _ int) as [ g | l ].
    + apply g.
    + set (int' := ringmultlt0gt0 X is0 is1 l rb0).
      destruct (isa _ _ rab0 int').
Defined.


(** ** Standard Algebraic Structures (cont.) Integral domains and Fileds.

Some of the notions considered in this section were introduced in C. Mulvey "Intuitionistic algebra
and representations of rings". See also P.T. Johnstone "Rings, fields and spectra". We only
consider here the strongest ("geometric") forms of the conditions of integrality and of being a
field. In particular all our fileds have decidable equality and p-adic numbers or reals are not
fileds in the sense of the definitions considered here. *)

Local Open Scope ring_scope.


(** *** Integral domains *)


(** **** General definitions *)

Lemma isnonzerolinvel (X : ring) (is : isnonzerorig X) (x : X) (x' : multlinvpair X x) :
  ((pr1 x') != 0).
Proof.
  intros.
  apply (negf (maponpaths (λ a : X, a * x))).
  assert (e := pr2 x'). change (paths (pr1 x' * x) 1) in e.
  change (neg (paths (pr1 x' * x) (0 * x))). rewrite e.
  rewrite (ringmult0x X _). apply is.
Defined.

Lemma isnonzerorinvel (X : ring) (is : isnonzerorig X) (x : X) (x' : multrinvpair X x) :
  ((pr1 x') != 0).
Proof.
  intros.
  apply (negf (maponpaths (λ a : X, x * a))).
  assert (e := pr2 x'). change (paths (x * pr1 x') 1) in e.
  change (neg (paths (x * pr1 x') (x * 0))).
  rewrite e. rewrite (ringmultx0 X _). apply is.
Defined.

Lemma isnonzerofromlinvel (X : ring) (is : isnonzerorig X) (x : X) (x' : multlinvpair X x) :
  x != 0.
Proof.
  intros. apply (negf (maponpaths (λ a : X, (pr1 x') * a))).
  assert (e := pr2 x'). change (paths (pr1 x' * x) 1) in e.
  change (neg (paths (pr1 x' * x) ((pr1 x') * 0))).
  rewrite e. rewrite (ringmultx0 X _). apply is.
Defined.

Lemma isnonzerofromrinvel (X : ring) (is : isnonzerorig X) (x : X) (x' : multrinvpair X x) :
  x != 0.
Proof.
  intros. apply (negf (maponpaths (λ a : X, a * (pr1 x')))).
  assert (e := pr2 x'). change (paths (x * pr1 x') 1) in e.
  change (neg (paths (x * pr1 x') (0 * (pr1 x')))).
  rewrite e. rewrite (ringmult0x X _). apply is.
Defined.

Definition isintdom (X : commring) : UU :=
  dirprod (isnonzerorig X) (∏ (a1 a2 : X), (a1 * a2 = 0) -> (a1 = 0) ∨ (a2 = 0)).

Lemma isapropisintdom (X : commring) : isaprop (isintdom X).
Proof.
  use isapropdirprod.
  - apply propproperty.
  - use impred. intros x1. use impred. intros x2. use impred. intros H.
    use propproperty.
Defined.
Opaque isapropisintdom.

Definition intdom : UU := total2 (λ X : commring, isintdom X).

Definition pr1intdom : intdom -> commring := @pr1 _ _.
Coercion pr1intdom : intdom >-> commring.

Definition nonzeroax (X : intdom) : neg (@paths X 1 0) := pr1 (pr2 X).

Definition intdomax (X : intdom) :
  ∏ (a1 a2 : X), (a1 * a2) = 0 -> (a1 = 0) ∨ (a2 = 0) := pr2 (pr2 X).


(** **** (X = Y) ≃ (ringiso X Y)
   We use the following composition

                            (X = Y) ≃ (pr1 X = pr1 Y)
                                    ≃ (ringiso X Y)

  where the second weak equivalence is given by univalence for commrings, [commring_univalence].
*)

Definition intdom_univalence_weq1 (X Y : intdom) : (X = Y) ≃ (pr1 X = pr1 Y).
Proof.
  use subtypeInjectivity.
  intros w. use isapropisintdom.
Defined.
Opaque intdom_univalence_weq1.

Definition intdom_univalence_weq2 (X Y : intdom) : (pr1 X = pr1 Y) ≃ (ringiso X Y) :=
  commring_univalence (pr1 X) (pr1 Y).

Definition intdom_univalence_map (X Y : intdom) : (X = Y) -> (ringiso X Y).
Proof.
  intros e. induction e. exact (idrigiso X).
Defined.

Lemma intdom_univalence_isweq (X Y : intdom) : isweq (intdom_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (intdom_univalence_weq1 X Y) (intdom_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque intdom_univalence_isweq.

Definition intdom_univalence (X Y : intdom) : (X = Y) ≃ (ringiso X Y).
Proof.
  use make_weq.
  - exact (intdom_univalence_map X Y).
  - exact (intdom_univalence_isweq X Y).
Defined.
Opaque intdom_univalence.


(** **** Computational lemmas for integral domains *)

Lemma intdomax2l (X : intdom) (x y : X) (is : paths (x * y) 0) (ne : x != 0) : y = 0.
Proof.
  intros.
  set (int := intdomax X _ _ is). generalize ne.
  assert (int' : isaprop (x != 0 -> y = 0)).
  {
    apply impred. intro.
    apply (setproperty X _ _).
  }
  generalize int. simpl.
  apply (@hinhuniv _ (make_hProp _ int')).
  intro ene. destruct ene as [ e'' | ne' ].
  - destruct (ne e'').
  - intro. apply ne'.
Defined.

Lemma intdomax2r (X : intdom) (x y : X) (is : paths (x * y) 0) (ne : y != 0) : x = 0.
Proof.
  intros.
  set (int := intdomax X _ _ is). generalize ne.
  assert (int' : isaprop (y != 0 -> x = 0)).
  {
    apply impred. intro.
    apply (setproperty X _ _).
  }
  generalize int. simpl. apply (@hinhuniv _ (make_hProp _ int')).
  intro ene. destruct ene as [ e'' | ne' ].
  - intro. apply e''.
  - destruct (ne ne').
Defined.

Definition intdomneq0andmult (X : intdom) (n m : X) (isn : n != 0)
           (ism : m != 0) : ((n * m) != 0).
Proof.
  intros. intro e. destruct (ism (intdomax2l X n m e isn )).
Defined.

Lemma intdomlcan (X : intdom) : ∏ (a b c : X), c != 0 -> paths (c * a) (c * b) -> a = b.
Proof.
  intros a b c ne e.
  apply (@grtopathsxy X a b). change (paths (a - b) 0).
  assert (e' := grfrompathsxy X e). change (paths ((c * a) - (c * b)) 0) in e'.
  rewrite (pathsinv0 (ringrmultminus X _ _)) in e'.
  rewrite (pathsinv0 (ringldistr X _ _ c)) in e'.
  set (int := intdomax X _ _ e'). generalize ne.
  assert (int' : isaprop (c != 0 -> paths (a - b) 0)).
  {
    apply impred. intro.
    apply (setproperty X _ _).
  }
  generalize int. simpl. apply (@hinhuniv _ (make_hProp _ int')).
  intro ene. destruct ene as [ e'' | ne' ].
  - destruct (ne e'').
  - intro. apply ne'.
Defined.
Opaque intdomlcan.

Lemma intdomrcan (X : intdom) : ∏ (a b c : X), c != 0 -> paths (a * c) (b * c) -> a = b.
Proof.
  intros a b c ne e. apply (@grtopathsxy X a b). change (paths (a - b) 0).
  assert (e' := grfrompathsxy X e). change (paths ((a * c) - (b * c)) 0) in e'.
  rewrite (pathsinv0 (ringlmultminus X _ _)) in e'.
  rewrite (pathsinv0 (ringrdistr X _ _ c)) in e'.
  set (int := intdomax X _ _ e'). generalize ne.
  assert (int' : isaprop (c != 0 -> paths (a - b) 0)).
  {
    apply impred. intro.
    apply (setproperty X _ _).
  }
  generalize int. simpl. apply (@hinhuniv _ (make_hProp _ int')).
  intro ene. destruct ene as [ e'' | ne' ].
  - intro. apply e''.
  - destruct (ne ne').
Defined.
Opaque intdomrcan.

Lemma intdomiscancelable (X : intdom) (x : X) (is : x != 0) : iscancelable (@op2 X) x.
Proof.
  intros. apply iscancelableif.
  - intros a b. apply (intdomlcan X a b x is).
  - intros a b. apply (intdomrcan X a b x is).
Defined.


(** **** Multiplicative submonoid of non-zero elements *)

Definition intdomnonzerosubmonoid (X : intdom) : @subabmonoid (ringmultabmonoid X).
Proof.
  intros. split with (λ x : X, make_hProp _ (isapropneg (x = 0))). split.
  - intros a b. simpl in *. intro e.
    set (int := intdomax X (pr1 a) (pr1 b) e). clearbody int. generalize int.
    apply toneghdisj. apply (make_dirprod (pr2 a) (pr2 b)).
  - simpl. apply (nonzeroax X).
Defined.


(** **** Relations similar to "greater" on integral domains *)

Definition intdomnonzerotopos (X : intdom) (R : hrel X) (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R)
           (x : intdomnonzerosubmonoid X) : ringpossubmonoid X is1 is2.
Proof.
  intros. destruct (nc (pr1 x) 0 (pr2 x)) as [ g | l ].
  - apply (tpair _ (pr1 x) g).
  - split with (- (pr1 x)). simpl.
    apply ringtogt0.
    + apply is0.
    + rewrite (ringminusminus X _). apply l.
Defined.


(** *** Ring units (i.e. multilicatively invertible elements) *)


(** *** Fields *)


(** **** Main definitions *)

Definition isafield (X : commring) : UU :=
  (isnonzerorig X) × (∏ x : X, (multinvpair X x) ⨿ (x = 0)).

Lemma isapropisafield (X : commring) : isaprop (isafield X).
Proof.
  use isofhleveltotal2.
  - apply propproperty.
  - intros H.
    use impred. intros x. use isapropcoprod.
    + use isapropinvpair.
    + use setproperty.
    + intros H' e. use H.
      use (pathscomp0
             _ (@multx0_is_l X (@op1 X) (@op2 X) (dirprod_pr1 (ringop1axs X)) (ringop2axs X)
                             (ringdistraxs X) (pr1 H'))).
      use (pathscomp0 _ (maponpaths (λ y : X , op2 (pr1 H') y) e)).
      exact (! dirprod_pr1 (pr2 H')).
Defined.
Opaque isapropisafield.

Definition fld : UU := total2 (λ X : commring, isafield X).

Definition make_fld (X : commring) (is : isafield X) : fld := tpair _ X is.

Definition pr1fld : fld -> commring := @pr1 _ _.

Definition fldtointdom (X : fld) : intdom.
Proof.
  split with (pr1 X). split with (pr1 (pr2 X)).
  intros a1 a2. destruct (pr2 (pr2 X) a1) as [ a1' | e0 ].
  - intro e12. rewrite (pathsinv0 (ringmultx0 (pr1 X) a1)) in e12.
    set (e2 := lcanfromlinv _ _ _ _ (invtolinv _ _ a1') e12).
    apply (hinhpr (ii2 e2)).
  - intro e12. apply (hinhpr (ii1 e0)).
Defined.
Coercion fldtointdom : fld >-> intdom.

Definition fldchoice {X : fld} (x : X) : (multinvpair X x) ⨿ (x = 0) := pr2 (pr2 X) x.

Definition fldmultinvpair (X : fld) (x : X) (ne : x != 0) : multinvpair X x.
Proof.
  intros. destruct (fldchoice x) as [ ne0 | e0 ].
  - apply ne0.
  - destruct (ne e0).
Defined.

Definition fldmultinv {X : fld} (x : X) (ne : x != 0) : X := pr1 (fldmultinvpair X x ne).


(** **** (X = Y) ≃ (ringiso X Y)
   We use the following composition

                                (X = Y) ≃ (pr1 X = pr1 Y)
                                        ≃ (ringiso X Y)

   where the second weak equivalence is given by univalence for commrings, [commring_univalence].
*)

Definition fld_univalence_weq1 (X Y : fld) : (X = Y) ≃ (pr1 X = pr1 Y).
Proof.
  use subtypeInjectivity.
  intros w. use isapropisafield.
Defined.
Opaque fld_univalence_weq1.

Definition fld_univalence_weq2 (X Y : fld) : (pr1 X = pr1 Y) ≃ (ringiso X Y) :=
  commring_univalence (pr1 X) (pr1 Y).

Definition fld_univalence_map (X Y : fld) : (X = Y) -> (ringiso X Y).
Proof.
  intros e. induction e. exact (idrigiso X).
Defined.

Lemma fld_univalence_isweq (X Y : fld) : isweq (fld_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (fld_univalence_weq1 X Y) (fld_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque fld_univalence_isweq.

Definition fld_univalence (X Y : fld) : (X = Y) ≃ (ringiso X Y).
Proof.
  use make_weq.
  - exact (fld_univalence_map X Y).
  - exact (fld_univalence_isweq X Y).
Defined.
Opaque fld_univalence.


(** **** Field of fractions of an integral domain with decidable equality *)

Definition fldfracmultinvint (X : intdom) (is : isdeceq X)
           (xa : dirprod X (intdomnonzerosubmonoid X)) : dirprod X (intdomnonzerosubmonoid X).
Proof.
  intros. destruct (is (pr1 xa) 0) as [ e0 | ne0 ].
  - apply (make_dirprod 1 (tpair (λ x, x != 0) 1 (nonzeroax X))).
  - apply (make_dirprod (pr1 (pr2 xa)) (tpair (λ x, x != 0) (pr1 xa) ne0)).
Defined.

(** Note: we choose a strange from the mathematicians perspective approach to the definition of the
multiplicative inverse on non-zero elements of a field due to the current, somewhat less than
satisfactory, situation with computational behavior of our construction of set-quotients. The
particular problem is that the weak equivalence between "quotient of subtype" and "subtype of a
quotient" is not isomorphism in the syntactic category. This can be corrected by extension of the
type system with tfc-terms. See discussion in hSet.v *)

Lemma fldfracmultinvintcomp (X : intdom) (is : isdeceq X) :
  iscomprelrelfun (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                  (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                  (fldfracmultinvint X is).
Proof.
  intros. intros xa1 xa2.
  set (x1 := pr1 xa1). set (aa1 := pr2 xa1). set (a1 := pr1 aa1).
  set (x2 := pr1 xa2). set (aa2 := pr2 xa2). set (a2 := pr1 aa2).
  simpl. apply hinhfun. intro t2. unfold fldfracmultinvint.
  destruct (is (pr1 xa1) 0) as [ e1 | ne1 ].
  - destruct (is (pr1 xa2) 0) as [ e2 | ne2 ].
    + simpl. split with (tpair (λ x, x != 0) 1 (nonzeroax X)).
      apply idpath.
    +  simpl. set (aa0 := pr1 t2). set (a0 := pr1 aa0).
       assert (e := pr2 t2). change (paths (x1 * a2 * a0) (x2 * a1 * a0)) in e.
       change (x1 = 0) in e1. rewrite e1 in e. rewrite (ringmult0x X _) in e.
       rewrite (ringmult0x X _) in e.
       assert (e' := intdomax2r X _ _ (pathsinv0 e) (pr2 aa0)).
       assert (e'' := intdomax2r X _ _ e' (pr2 aa1)).
       destruct (ne2 e'').
  - destruct (is (pr1 xa2) 0) as [ e2 | ne2 ].
    + simpl. set (aa0 := pr1 t2). set (a0 := pr1 aa0).
      assert (e := pr2 t2). change (paths (x1 * a2 * a0) (x2 * a1 * a0)) in e.
      change (x2 = 0) in e2. rewrite e2 in e. rewrite (ringmult0x X _) in e.
      rewrite (ringmult0x X _) in e.
      assert (e' := intdomax2r X _ _  e (pr2 aa0)).
      assert (e'' := intdomax2r X _ _ e' (pr2 aa2)).
      destruct (ne1 e'').
    + simpl. set (aa0 := pr1 t2). set (a0 := pr1 aa0).
      assert (e := pr2 t2). split with aa0.
      change (paths (a1 * x2 * a0) (a2 * x1 * a0)).
      change (paths (x1 * a2 * a0) (x2 * a1 * a0)) in e.
      rewrite (ringcomm2 X a1 x2). rewrite (ringcomm2 X a2 x1).
      apply (pathsinv0 e).
Defined.
Opaque fldfracmultinvintcomp.

Definition fldfracmultinv0 (X : intdom) (is : isdeceq X)
           (x : commringfrac X (intdomnonzerosubmonoid X)) :
  commringfrac X (intdomnonzerosubmonoid X) := setquotfun _ _ _ (fldfracmultinvintcomp X is) x.

Lemma nonzeroincommringfrac (X : commring) (S : @submonoid (ringmultmonoid X)) (xa : dirprod X S)
      (ne : (setquotpr (eqrelcommringfrac X S) xa !=
             setquotpr _ (make_dirprod 0 (unel S)))%type) : (pr1 xa != 0).
Proof.
  intros. set (x := pr1 xa). set (aa := pr2 xa).
  assert (e' := negf (weqpathsinsetquot (eqrelcommringfrac X S) _ _) ne).
  simpl in e'. generalize e'.
  apply negf. intro e. apply hinhpr. split with (unel S).
  change (paths (x * 1 * 1) (0 * (pr1 aa) * 1)). rewrite e.
  repeat rewrite (ringmult0x X _).
  apply idpath.
Defined.
Opaque nonzeroincommringfrac.

Lemma zeroincommringfrac (X : intdom) (S : @submonoid (ringmultmonoid X))
      (is : ∏ s : S, (pr1 s != 0)) (x : X) (aa : S)
      (e : paths (setquotpr (eqrelcommringfrac X S) (make_dirprod x aa))
                 (setquotpr _ (make_dirprod 0 (unel S)))) : x = 0.
Proof.
  intros.
  set (e' := invweq (weqpathsinsetquot _ _ _) e). simpl in e'. generalize e'.
  apply (@hinhuniv _ (make_hProp _ (setproperty X _ _))).
  intro t2. simpl.
  set (aa0 := pr1 t2). set (a0 := pr1 aa0). set (a := pr1 aa).
  assert (e2 := pr2 t2). simpl in e2.
  change (paths (x * 1 * a0) (0 * a * a0)) in e2.
  rewrite (ringmult0x X _) in e2.
  rewrite (ringmult0x X _) in e2.
  rewrite (ringrunax2 X _) in e2.
  apply (intdomax2r X x a0 e2 (is aa0)).
Defined.
Opaque zeroincommringfrac.

Lemma isdeceqfldfrac (X : intdom) (is : isdeceq X) :
  isdeceq (commringfrac X (intdomnonzerosubmonoid X)).
Proof.
  intros. apply isdeceqcommringfrac.
  - intro a. apply isrcancelableif.
    intros b0 b1 e. apply (intdomrcan X _ _ (pr1 a) (pr2 a) e).
  - apply is.
Defined.

Lemma islinvinfldfrac (X : intdom) (is : isdeceq X) (x : commringfrac X (intdomnonzerosubmonoid X))
      (ne : x != 0) : paths ((fldfracmultinv0 X is x) * x) 1.
Proof.
  revert x ne.
  assert (int : ∏ x0, isaprop (x0 != 0 -> paths ((fldfracmultinv0 X is x0) * x0) 1)).
  {
    intro x0.
    apply impred. intro.
    apply (setproperty (commringfrac X (intdomnonzerosubmonoid X)) (fldfracmultinv0 X is x0 * x0) _).
  }
  apply (setquotunivprop _ (λ x0, make_hProp _ (int x0))).
  simpl. intros xa ne.
  change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                           (make_dirprod ((pr1 (fldfracmultinvint X is xa)) * (pr1 xa))
                                        (@op (intdomnonzerosubmonoid X)
                                             (pr2 (fldfracmultinvint X is xa)) (pr2 xa))))
                (setquotpr _ (make_dirprod 1 (tpair _ 1 (nonzeroax X))))).
  apply (weqpathsinsetquot). unfold fldfracmultinvint. simpl.
  destruct (is (pr1 xa) 0 ) as [ e0 | ne0' ].
  - destruct (nonzeroincommringfrac X (intdomnonzerosubmonoid X) xa ne e0).
  - apply hinhpr.
    split with (tpair (λ a, a != 0) 1 (nonzeroax X)).
    set (x := (pr1 xa) : X). set (aa := pr2 xa). set (a := (pr1 aa) : X).
    simpl. change (paths (a * x * 1  * 1) (1 * (x * a) * 1)).
    rewrite (ringcomm2 X a x). repeat rewrite (ringrunax2 X _). rewrite (ringlunax2 X _).
    apply idpath.
Defined.
Opaque islinvinfldfrac.

Lemma isrinvinfldfrac (X : intdom) (is : isdeceq X) (x : commringfrac X (intdomnonzerosubmonoid X))
      (ne : x != 0) : paths (x * (fldfracmultinv0 X is x)) 1.
Proof.
  intros. rewrite (ringcomm2 _ _ _). apply islinvinfldfrac. apply ne.
Defined.

Definition fldfrac (X : intdom) (is : isdeceq X) : fld.
Proof.
  intros. split with (commringfrac X (intdomnonzerosubmonoid X)). split.
  - intro e.
    set (e' := zeroincommringfrac X (intdomnonzerosubmonoid X)
                                 (λ a : (intdomnonzerosubmonoid X), pr2 a) 1
                                 (unel (intdomnonzerosubmonoid X)) e).
    apply (nonzeroax X e').
  - intro x. destruct (isdeceqfldfrac X is x 0) as [ e | ne ].
    apply (ii2 e). apply ii1. split with (fldfracmultinv0 X is x). split.
    + apply (islinvinfldfrac X is x ne) .
    + apply (isrinvinfldfrac X is x ne).
Defined.


(** **** Canonical homomorphism to the field of fractions *)

Definition tofldfrac (X : intdom) (is : isdeceq X) (x : X) : fldfrac X is :=
  setquotpr _ (make_dirprod x (tpair (λ x, x != 0) 1 (nonzeroax X))).

Definition isbinop1funtofldfrac (X : intdom) (is : isdeceq X) :
  @isbinopfun X (fldfrac X is) (tofldfrac X is) := isbinop1funtocommringfrac X _.

Lemma isunital1funtofldfrac (X : intdom) (is : isdeceq X) : (tofldfrac X is 0) = 0.
Proof.
  intros. apply idpath.
Defined.

Definition isaddmonoidfuntofldfrac (X : intdom) (is : isdeceq X) :
  @ismonoidfun X (fldfrac X is) (tofldfrac X is) :=
  make_dirprod (isbinop1funtofldfrac X is) (isunital1funtofldfrac X is).

Definition tofldfracandminus0 (X : intdom) (is : isdeceq X) (x : X) :
  paths (tofldfrac X is (- x)) (- tofldfrac X is x) :=
  tocommringfracandminus0 _ _ x.

Definition tofldfracandminus (X : intdom) (is : isdeceq X) (x y : X) :
  paths (tofldfrac X is (x - y)) (tofldfrac X is x - tofldfrac X is y) :=
  tocommringfracandminus _ _ x y.

Definition isbinop2funtofldfrac (X : intdom) (is : isdeceq X) :
  @isbinopfun (ringmultmonoid X) (ringmultmonoid (fldfrac X is)) (tofldfrac X is) :=
  isbinopfuntoabmonoidfrac (ringmultabmonoid X) (intdomnonzerosubmonoid X).
Opaque isbinop2funtofldfrac.

Lemma isunital2funtofldfrac (X : intdom) (is : isdeceq X) : (tofldfrac X is 1) = 1.
Proof.
  intros. apply idpath.
Defined.
Opaque isunital2funtofldfrac.

Definition ismultmonoidfuntofldfrac (X : intdom) (is : isdeceq X) :
  @ismonoidfun (ringmultmonoid X) (ringmultmonoid (fldfrac X is)) (tofldfrac X is) :=
  make_dirprod (isbinop2funtofldfrac X is) (isunital2funtofldfrac X is).

Definition isringfuntofldfrac (X : intdom) (is : isdeceq X) :
  @isringfun X (fldfrac X is) (tofldfrac X is) :=
  make_dirprod (isaddmonoidfuntofldfrac X is) (ismultmonoidfuntofldfrac X is).

Definition isincltofldfrac (X : intdom) (is : isdeceq X) : isincl (tofldfrac X is) :=
  isincltocommringfrac X (intdomnonzerosubmonoid X)
                      (λ x : _, pr2 (intdomiscancelable X (pr1 x) (pr2 x))).


(** *** Relations similar to "greater" on fields of fractions

Our approach here is slightly different from the tranditional one used for example in Bourbaki
Algebra II, Ch. VI, Section 2 where one starts with a total ordering on a ring and extends it to
its field of fractions. This situation woud be exemplified by the extension of "greater or equal"
from integers to rationals. We have chosen to use instead as our archetypical example the extension
of "greater" from integers to rationals. There is no particular difference between the two choices
for types with decidable equality but in the setting of general rings in constructive mathematics
the relations such as "greater" appear to be more fundamental than relations such as "greater or
equal". For example, "greater or equal" on constructive real numbers can be obtained from "greater"
but not vice versa. *)


(** **** Description of the field of fractions as the ring of fractions with respect to the submonoid of "positive" elements *)

Definition weqfldfracgtint_f (X : intdom) {R : hrel X} (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R)
           (xa : dirprod X (intdomnonzerosubmonoid X)) : dirprod X (ringpossubmonoid X is1 is2).
Proof.
  intros. destruct (nc (pr1 (pr2 xa)) 0 (pr2 (pr2 xa))) as [ g | l ].
  - apply (make_dirprod (pr1 xa) (tpair _ (pr1 (pr2 xa)) g)).
  - split with (- (pr1 xa)). split with (- (pr1 (pr2 xa))).
    simpl. apply (ringfromlt0 X is0 l).
Defined.

Lemma weqfldfracgtintcomp_f (X : intdom) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) :
  iscomprelrelfun (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                  (eqrelcommringfrac X (ringpossubmonoid X is1 is2))
                  (weqfldfracgtint_f X is0 is1 is2 nc).
Proof.
  intros. intros xa1 xa2. simpl.
  set (x1 := pr1 xa1). set (aa1 := pr2 xa1). set (a1 := pr1 aa1).
  set (x2 := pr1 xa2). set (aa2 := pr2 xa2). set (a2 := pr1 aa2).
  apply hinhfun. intro t2. split with (tpair (λ x, R x 0) 1 is2).
  set (aa0 := pr1 t2). set (a0 := pr1 aa0).
  assert (e := pr2 t2). change (paths (x1 * a2 * a0) (x2 * a1 * a0)) in e.
  unfold weqfldfracgtint_f.
  destruct (nc (pr1 (pr2 xa1)) 0 (pr2 (pr2 xa1))) as [ g1 | l1 ].
  - destruct (nc (pr1 (pr2 xa2)) 0 (pr2 (pr2 xa2))) as [ g2 | l2 ].
    + simpl. rewrite (ringrunax2 X _). rewrite (ringrunax2 X _).
      apply (intdomrcan X _ _ _ (pr2 aa0) e).
    + simpl. rewrite (ringrunax2 X _). rewrite (ringrunax2 X _).
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      apply (maponpaths (λ x : X, - x)).
      apply (intdomrcan X _ _ _ (pr2 aa0) e).
  - destruct (nc (pr1 (pr2 xa2)) 0 (pr2 (pr2 xa2))) as [ g2 | l2 ].
    + simpl. rewrite (ringrunax2 X _). rewrite (ringrunax2 X _).
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      apply (maponpaths (λ x : X, - x)).
      apply (intdomrcan X _ _ _ (pr2 aa0) e).
    + simpl. rewrite (ringrunax2 X _). rewrite (ringrunax2 X _).
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      apply (maponpaths (λ x : X, - - x)).
      apply (intdomrcan X _ _ _ (pr2 aa0) e).
Defined.
Opaque weqfldfracgtintcomp_f.

Definition weqfldfracgt_f (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) :
  fldfrac X is -> commringfrac X (ringpossubmonoid X is1 is2) :=
  setquotfun _ _ _ (weqfldfracgtintcomp_f X is0 is1 is2 nc).

Definition weqfldfracgtint_b (X : intdom) {R : hrel X} (is1 : isringmultgt X R) (is2 : R 1 0)
           (ir : isirrefl R) (xa : dirprod X (ringpossubmonoid X is1 is2)) :
  dirprod X (intdomnonzerosubmonoid X) :=
  make_dirprod (pr1 xa) (tpair _ (pr1 (pr2 xa)) (rtoneq ir (pr2 (pr2 xa)))).

Lemma weqfldfracgtintcomp_b (X : intdom) {R : hrel X} (is1 : isringmultgt X R) (is2 : R 1 0)
      (ir : isirrefl R) : iscomprelrelfun (eqrelcommringfrac X (ringpossubmonoid X is1 is2))
                                          (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                                          (weqfldfracgtint_b X is1 is2 ir).
Proof.
  intros. intros xa1 xa2. simpl. apply hinhfun. intro t2.
  split with (tpair _ (pr1 (pr1 t2)) (rtoneq ir (pr2 (pr1 t2)))).
  apply (pr2 t2).
Defined.

Definition weqfldfracgt_b (X : intdom) (is : isdeceq X) {R : hrel X} (is1 : isringmultgt X R)
           (is2 : R 1 0) (ir : isirrefl R) :
  commringfrac X (ringpossubmonoid X is1 is2) -> fldfrac X is :=
  setquotfun _ _ _ (weqfldfracgtintcomp_b X is1 is2 ir).

Definition weqfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (ir : isirrefl R) :
  weq (fldfrac X is) (commringfrac X (ringpossubmonoid X is1 is2)).
Proof.
  intros.
  set (f := weqfldfracgt_f X is is0 is1 is2 nc).
  set (g := weqfldfracgt_b X is is1 is2 ir).
  split with f.
  assert (egf : ∏ a, paths (g (f a)) a).
  {
    unfold fldfrac. simpl.
    apply (setquotunivprop _ (λ a, make_hProp _ (isasetsetquot _ (g (f a)) a))).
    intro xa. simpl.
    change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                             (weqfldfracgtint_b
                                X is1 is2 ir (weqfldfracgtint_f X is0 is1 is2 nc xa)))
                  (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X)) xa)).
    apply (weqpathsinsetquot). simpl. apply hinhpr.
    split with (tpair (λ x, x != 0) 1 (nonzeroax X)). simpl.
    unfold weqfldfracgtint_f.
    destruct (nc (pr1 (pr2 xa)) 0 (pr2 (pr2 xa))) as [ g' | l' ].
    - simpl. apply idpath.
    - simpl.
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      apply idpath.
  }
  assert (efg : ∏ a, paths (f (g a)) a).
  {
    unfold fldfrac. simpl.
    apply (setquotunivprop _ (λ a, make_hProp _ (isasetsetquot _ (f (g a)) a))).
    intro xa. simpl.
    change (paths (setquotpr _ (weqfldfracgtint_f
                                  X is0 is1 is2 nc (weqfldfracgtint_b X is1 is2 ir xa)))
                  (setquotpr (eqrelcommringfrac X (ringpossubmonoid X is1 is2)) xa)).
    apply weqpathsinsetquot. simpl. apply hinhpr.
    split with (tpair (λ x, R x 0) 1 is2).
    unfold weqfldfracgtint_f. unfold weqfldfracgtint_b. simpl.
    set (int := nc (pr1 (pr2 xa)) 0 (rtoneq ir (pr2 (pr2 xa))) ).
    change (nc (pr1 (pr2 xa)) 0 (rtoneq ir (pr2 (pr2 xa)))) with int.
    destruct int as [ g' | l' ].
    - simpl. apply idpath.
    - simpl.
      rewrite (ringrmultminus X _ _). rewrite (ringlmultminus X _ _).
      apply idpath.
  }
  apply (isweq_iso _ _ egf efg).
Defined.

Lemma isringfunweqfldfracgt_b (X : intdom) (is : isdeceq X) {R : hrel X} (is1 : isringmultgt X R)
      (is2 : R 1 0) (ir : isirrefl R) : isringfun (weqfldfracgt_b X is is1 is2 ir).
Proof.
  intros.
  set (g :=  weqfldfracgt_b X is is1 is2 ir).
  set (g0 := weqfldfracgtint_b X is1 is2 ir).
  split.
  - split.
    + unfold isbinopfun.
      change (∏ x x' : commringfrac X (ringpossubmonoid X is1 is2),
                       paths (g (x + x')) ((g x) + (g x'))).
      apply (setquotuniv2prop
               _ (λ x x' : commringfrac X (ringpossubmonoid X is1 is2),
                    make_hProp _ (setproperty (fldfrac X is) (g (x + x')) ((g x) + (g x'))))).
      intros xa1 xa2.
      change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (g0 (commringfracop1int X (ringpossubmonoid X is1 is2) xa1 xa2)))
                    (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (commringfracop1int X (intdomnonzerosubmonoid X) (g0 xa1) (g0 xa2)))).
      apply (maponpaths (setquotpr _)).
      unfold g0. unfold weqfldfracgtint_b. unfold commringfracop1int. simpl.
      apply (pathsdirprod).
      * apply idpath.
      * destruct xa1 as [ x1 aa1 ]. destruct xa2 as [ x2 aa2 ]. simpl.
        destruct aa1 as [ a1 ia1 ]. destruct aa2 as [ a2 ia2 ]. simpl.
        apply (invmaponpathsincl
                 (@pr1 _ _) (isinclpr1 _ (λ a, (isapropneg (a = 0))))
                 (tpair _ (a1 * a2) (rtoneq ir (is1 a1 a2 ia1 ia2)))
                 (make_carrier (λ x : pr1 X, make_hProp (x = 0 -> empty) (isapropneg (x = 0)))
                              (a1 * a2) (fun e : paths (a1 * a2) 0 =>
                                           toneghdisj (make_dirprod (rtoneq ir ia1) (rtoneq ir ia2))
                                                      (intdomax X a1 a2 e))) (idpath _)).
    + change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (g0 (make_dirprod 0 (tpair _ 1 is2))))
                    (setquotpr _ (make_dirprod 0 (tpair _ 1 (nonzeroax X))))).
      apply (maponpaths (setquotpr _)).
      unfold g0. unfold weqfldfracgtint_b. simpl.
      apply pathsdirprod.
      * apply idpath.
      * apply (invmaponpathsincl (@pr1 _ _) (isinclpr1 _ (λ a, (isapropneg (a = 0))))
                                 (tpair _ 1 (rtoneq ir is2)) (tpair _  1 (nonzeroax X))).
        simpl. apply idpath.
  - split.
    + unfold isbinopfun.
      change (∏ x x' : commringfrac X (ringpossubmonoid X is1 is2),
                       paths (g (x * x')) ((g x) * (g x'))).
      apply (setquotuniv2prop
               _ (λ x x' : commringfrac X (ringpossubmonoid X is1 is2),
                    make_hProp _ (setproperty (fldfrac X is) (g (x * x')) ((g x) * (g x'))))).
      intros xa1 xa2.
      change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (g0 (commringfracop2int X (ringpossubmonoid X is1 is2) xa1 xa2)))
                    (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (commringfracop2int X (intdomnonzerosubmonoid X) (g0 xa1) (g0 xa2)))).
      apply (maponpaths (setquotpr _)).
      unfold g0. unfold weqfldfracgtint_b.
      unfold commringfracop2int. unfold abmonoidfracopint. simpl.
      apply (pathsdirprod).
      * apply idpath.
      * destruct xa1 as [ x1 aa1 ]. destruct xa2 as [ x2 aa2 ]. simpl.
        destruct aa1 as [ a1 ia1 ]. destruct aa2 as [ a2 ia2 ]. simpl.
        apply (invmaponpathsincl
                 (@pr1 _ _)
                 (isinclpr1 _ (λ a, (isapropneg (a = 0))))
                 (tpair _ (a1 * a2) (rtoneq ir (is1 a1 a2 ia1 ia2)))
                 (make_carrier (λ x : pr1 X, make_hProp (x = 0 -> empty) (isapropneg (x = 0)))
                              (a1 * a2) (fun e : paths (a1 * a2) 0 =>
                                           toneghdisj (make_dirprod (rtoneq ir ia1) (rtoneq ir ia2))
                                                      (intdomax X a1 a2 e))) (idpath _)).
    + change (paths (setquotpr (eqrelcommringfrac X (intdomnonzerosubmonoid X))
                               (g0 (make_dirprod 1 (tpair _ 1 is2))))
                    (setquotpr _ (make_dirprod 1 (tpair _ 1 (nonzeroax X))))).
      apply (maponpaths (setquotpr _)).
      unfold g0. unfold weqfldfracgtint_b. simpl.
      apply pathsdirprod.
      * apply idpath.
      * apply (invmaponpathsincl (@pr1 _ _) (isinclpr1 _ (λ a, (isapropneg (a = 0))))
                                 (tpair _ 1 (rtoneq ir is2)) (tpair _ 1 (nonzeroax X))).
        simpl. apply idpath.
Defined.
Opaque isringfunweqfldfracgt_b.

Lemma isringfunweqfldfracgt_f (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (ir : isirrefl R) :
  isringfun (weqfldfracgt_f X is is0 is1 is2 nc).
Proof.
  intros. unfold weqfldfracgt_f.
  set (int := make_ringiso (invweq (weqfldfracgt X is is0 is1 is2 nc ir))
                         (isringfunweqfldfracgt_b X is is1 is2 ir)).
  change (@isringfun (fldfrac X is) (commringfrac X (ringpossubmonoid X is1 is2)) (invmap int)).
  apply isringfuninvmap.
Defined.
Opaque isringfunweqfldfracgt_f.


(** **** Definition and properties of "greater" on the field of fractions *)

Definition fldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) : hrel (fldfrac X is) :=
  λ a b, commringfracgt X (ringpossubmonoid X is1 is2) is0 is1 (λ c r, r)
                        (weqfldfracgt_f X is is0 is1 is2 nc a)
                        (weqfldfracgt_f X is is0 is1 is2 nc b).

Lemma isringmultfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (ir : isirrefl R) :
  isringmultgt (fldfrac X is) (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros.
  refine (ringmultgtandfun (ringfunconstr (isringfunweqfldfracgt_f X is is0 is1 is2 nc ir)) _ _).
  apply isringmultcommringfracgt.
Defined.
Opaque isringmultfldfracgt.

Lemma isringaddfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (ir : isirrefl R) :
  @isbinophrel (fldfrac X is) (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros.
  refine (ringaddhrelandfun (ringfunconstr (isringfunweqfldfracgt_f X is is0 is1 is2 nc ir)) _ _).
  apply isringaddcommringfracgt.
Defined.
Opaque isringaddfldfracgt.

Lemma istransfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (isr : istrans R) :
  istrans (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros. intros a b c. unfold fldfracgt.
  apply istransabmonoidfracrel.
  apply isr.
Defined.
Opaque istransfldfracgt.

Lemma isirreflfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (isr : isirrefl R) :
  isirrefl (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros. intros a. unfold fldfracgt .
  apply isirreflabmonoidfracrel.
  apply isr.
Defined.
Opaque isirreflfldfracgt.

Lemma isasymmfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (isr : isasymm R) :
  isasymm (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros. intros a b. unfold fldfracgt .
  apply isasymmabmonoidfracrel.
  apply isr.
Defined.
Opaque isasymmfldfracgt.

Lemma iscotransfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (isr : iscotrans R) :
  iscotrans (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros. intros a b c. unfold fldfracgt .
  apply iscotransabmonoidfracrel.
  apply isr.
Defined.
Opaque iscotransfldfracgt.

Lemma isantisymmnegfldfracgt  (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
      (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (ir : isirrefl R)
      (isr : isantisymmneg R) : isantisymmneg (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros.
  assert (int : isantisymmneg (commringfracgt X (ringpossubmonoid X is1 is2) is0 is1 (λ c r, r))).
  {
    unfold commringfracgt.
    apply (isantisymmnegabmonoidfracrel
             (ringmultabmonoid X) (ringpossubmonoid X is1 is2)
             (ispartbinopcommringfracgt X (ringpossubmonoid X is1 is2) is0 is1
                                       (fun (c : X) (r : (ringpossubmonoid X is1 is2) c) => r))).
    apply isr.
  }
  intros a b n1 n2. set (e := int _ _ n1 n2).
  apply (invmaponpathsweq (weqfldfracgt X is is0 is1 is2 nc ir)  _ _ e).
Defined.
Opaque isantisymmnegfldfracgt.

Definition isdecfldfracgt (X : intdom) (is : isdeceq X) {R : hrel X} (is0 : @isbinophrel X R)
           (is1 : isringmultgt X R) (is2 : R 1 0) (nc : neqchoice R) (isa : isasymm R)
           (isr : isdecrel R) : isdecrel (fldfracgt X is is0 is1 is2 nc).
Proof.
  intros. unfold fldfracgt. intros a b. apply isdecabmonoidfracrel.
  - apply (pr1 (isinvringmultgtaspartinvbinophrel X R is0)).
    apply isinvringmultgtif.
    + apply is0.
    + apply is1.
    + apply nc.
    + apply isa.
  - apply isr.
Defined.


(** **** Relations and the canonical homomorphism to the field of fractions *)


Definition iscomptofldfrac (X : intdom) (is : isdeceq X) {L : hrel X} (is0 : @isbinophrel X L)
           (is1 : isringmultgt X L) (is2 : L 1 0) (nc : neqchoice L) (isa : isasymm L) :
  iscomprelrelfun L (fldfracgt X is is0 is1 is2 nc) (tofldfrac X is).
Proof.
  intros. intros x1 x2 l.
  assert (int := iscomptocommringfrac X (ringpossubmonoid X is1 is2) is0 is1 (λ c r, r)).
  simpl in int. unfold fldfracgt. unfold iscomprelrelfun in int.
  assert (ee : ∏ x : X, paths (tocommringfrac X (ringpossubmonoid X is1 is2) x)
                              (weqfldfracgt_f X is is0 is1 is2 nc (tofldfrac X is x))).
  {
    intros x.
    change (tocommringfrac X (ringpossubmonoid X is1 is2) x)
    with (setquotpr (eqrelcommringfrac X (ringpossubmonoid X is1 is2))
                    (make_dirprod x (tpair (λ a, L a 0) _ is2))).
    change (weqfldfracgt_f X is is0 is1 is2 nc (tofldfrac X is x))
    with (setquotpr (eqrelcommringfrac X (ringpossubmonoid X is1 is2))
                    (weqfldfracgtint_f
                       X is0 is1 is2 nc
                       (make_dirprod x (tpair (λ a, a != 0) 1 (nonzeroax X))))).
    apply (maponpaths (setquotpr (eqrelcommringfrac X (ringpossubmonoid X is1 is2)))).
    unfold weqfldfracgtint_f. simpl.
    destruct (nc 1 0 (nonzeroax X) ) as [ l' | nl ].
    - apply pathsdirprod.
      + apply idpath.
      + apply (invmaponpathsincl _ (isinclpr1 _ (λ a, (pr2 (L a 0))))).
        apply idpath.
    - destruct (isa _ _ is2 nl).
  }
  assert (int' := int x1 x2).
  rewrite (ee x1) in int'. rewrite (ee x2) in int'.
  apply int'. apply l.
Defined.
Opaque iscomptofldfrac.

(* End of the file *)
