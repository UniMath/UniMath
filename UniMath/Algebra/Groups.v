(** * Algebra I. Part C. Groups, abelian groups. Vladimir Voevodsky. Aug. 2011 - . *)

(** ** Contents

 - Groups
  - Basic definitions
  - Univalence for groups
  - Computation lemmas for groups
  - Relations on groups
  - Subobjects
  - Quotient objects
  - Cosets
  - Normal Subgroups
  - Direct products
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

Require Export UniMath.Algebra.BinaryOperations.
Require Export UniMath.Algebra.Monoids.
Require Import UniMath.MoreFoundations.All.

(** ** Groups *)

(** *** Basic definitions *)

Definition gr : UU := total2 (λ X : setwithbinop, isgrop (@op X)).

Definition make_gr :
  ∏ (t : setwithbinop), (λ X : setwithbinop, isgrop op) t → ∑ X : setwithbinop, isgrop op :=
  tpair (λ X : setwithbinop, isgrop (@op X)).

Definition grtomonoid : gr -> monoid := λ X : _, make_monoid (pr1 X) (pr1 (pr2 X)).
Coercion grtomonoid : gr >-> monoid.

Definition grinv (X : gr) : X -> X := pr1 (pr2 (pr2 X)).

Definition grlinvax (X : gr) : islinv (@op X) (unel X) (grinv X) := pr1 (pr2 (pr2 (pr2 X))).

Definition grrinvax (X : gr) : isrinv (@op X) (unel X) (grinv X) := pr2 (pr2 (pr2 (pr2 X))).

Definition gr_of_monoid (X : monoid) (H : invstruct (@op X) (pr2 X)) : gr :=
  make_gr X (make_isgrop (pr2 X) H).

Lemma monoidfuninvtoinv {X Y : gr} (f : monoidfun X Y) (x : X) :
  f (grinv X x) = grinv Y (f x).
Proof.
  intros.
  apply (invmaponpathsweq (make_weq _ (isweqrmultingr_is (pr2 Y) (f x)))).
  simpl.
  change (paths (op (pr1 f (grinv X x)) (pr1 f x)) (op (grinv Y (pr1 f x)) (pr1 f x))).
  rewrite (grlinvax Y (pr1 f x)).
  destruct (pr1 (pr2 f) (grinv X x) x).
  rewrite (grlinvax X x).
  apply (pr2 (pr2 f)).
Defined.

Lemma grinv_path_from_op_path {X : gr} {x y : X} (p : (x * y)%multmonoid = unel X) :
  grinv X x = y.
Proof.
  now rewrite <- (lunax X y), <- (grlinvax X x), assocax, p, runax.
Defined.

(** *** Construction of the trivial abmonoid consisting of one element given by unit. *)

Definition unitgr_isgrop : isgrop (@op unitmonoid).
Proof.
  use make_isgrop.
  - exact unitmonoid_ismonoid.
  - use make_invstruct.
    + intros i. exact i.
    + use make_isinv.
      * intros x. use isProofIrrelevantUnit.
      * intros x. use isProofIrrelevantUnit.
Qed.

Definition unitgr : gr := make_gr unitmonoid unitgr_isgrop.

Lemma grfuntounit_ismonoidfun (X : gr) : ismonoidfun (λ x : X, (unel unitgr)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use isProofIrrelevantUnit.
  - use isProofIrrelevantUnit.
Qed.

Definition grfuntounit (X : gr) : monoidfun X unitgr := monoidfunconstr (grfuntounit_ismonoidfun X).

Lemma grfunfromunit_ismonoidfun (X : gr) : ismonoidfun (λ x : unitgr, (unel X)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition grfunfromunit (X : gr) : monoidfun unitmonoid X :=
  monoidfunconstr (monoidfunfromunit_ismonoidfun X).

Lemma unelgrfun_ismonoidfun (X Y : gr) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Definition unelgrfun (X Y : gr) : monoidfun X Y :=
  monoidfunconstr (unelgrfun_ismonoidfun X Y).


(** *** (X = Y) ≃ (monoidiso X Y)
   The idea is to use the composition

            (X = Y) ≃ (make_gr' X = make_gr' Y)
                    ≃ ((gr'_to_monoid (make_gr' X)) = (gr'_to_monoid (make_gr' Y)))
                    ≃ (monoidiso X Y).

   The reason why we use gr' is that then we can use univalence for monoids. See
   [gr_univalence_weq3].
*)

Local Definition gr' : UU :=
  ∑ g : (∑ X : setwithbinop, ismonoidop (@op X)), invstruct (@op (pr1 g)) (pr2 g).

Local Definition make_gr' (X : gr) : gr' := tpair _ (tpair _ (pr1 X) (pr1 (pr2 X))) (pr2 (pr2 X)).

Local Definition gr'_to_monoid (X : gr') : monoid := pr1 X.

Definition gr_univalence_weq1 : gr ≃ gr' :=
  weqtotal2asstol
    (λ Z : setwithbinop, ismonoidop (@op Z))
    (fun y : (∑ (x : setwithbinop), ismonoidop (@op x)) => invstruct (@op (pr1 y)) (pr2 y)).

Definition gr_univalence_weq1' (X Y : gr) : (X = Y) ≃ (make_gr' X = make_gr' Y) :=
  make_weq _ (@isweqmaponpaths gr gr' gr_univalence_weq1 X Y).

Definition gr_univalence_weq2 (X Y : gr) :
  ((make_gr' X) = (make_gr' Y)) ≃ ((gr'_to_monoid (make_gr' X)) = (gr'_to_monoid (make_gr' Y))).
Proof.
  use subtypeInjectivity.
  intros w. use isapropinvstruct.
Defined.
Opaque gr_univalence_weq2.

Definition gr_univalence_weq3 (X Y : gr) :
  ((gr'_to_monoid (make_gr' X)) = (gr'_to_monoid (make_gr' Y))) ≃ (monoidiso X Y) :=
  monoid_univalence (gr'_to_monoid (make_gr' X)) (gr'_to_monoid (make_gr' Y)).

Definition gr_univalence_map (X Y : gr) : (X = Y) -> (monoidiso X Y).
Proof.
  intro e. induction e. exact (idmonoidiso X).
Defined.

Lemma gr_univalence_isweq (X Y : gr) : isweq (gr_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (gr_univalence_weq1' X Y)
                   (weqcomp (gr_univalence_weq2 X Y) (gr_univalence_weq3 X Y))).
  - intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque gr_univalence_isweq.

Definition gr_univalence (X Y : gr) : (X = Y) ≃ (monoidiso X Y).
Proof.
  use make_weq.
  - exact (gr_univalence_map X Y).
  - exact (gr_univalence_isweq X Y).
Defined.
Opaque gr_univalence.


(** *** Computation lemmas for groups *)

Definition weqlmultingr (X : gr) (x0 : X) : pr1 X ≃ pr1 X :=
  make_weq _ (isweqlmultingr_is (pr2 X) x0).

Definition weqrmultingr (X : gr) (x0 : X) : pr1 X ≃ pr1 X :=
  make_weq _ (isweqrmultingr_is (pr2 X) x0).

Lemma grlcan (X : gr) {a b : X} (c : X) (e : paths (op c a) (op c b)) : a = b.
Proof. apply (invmaponpathsweq (weqlmultingr X c) _ _ e). Defined.

Lemma grrcan (X : gr) {a b : X} (c : X) (e : paths (op a c) (op b c)) : a = b.
Proof. apply (invmaponpathsweq (weqrmultingr X c) _ _ e). Defined.

Lemma grinvunel (X : gr) : paths (grinv X (unel X)) (unel X).
Proof.
  apply (grrcan X (unel X)).
  rewrite (grlinvax X). rewrite (runax X).
  apply idpath.
Defined.

Lemma grinvinv (X : gr) (a : X) : paths (grinv X (grinv X a)) a.
Proof.
  apply (grlcan X (grinv X a)).
  rewrite (grlinvax X a). rewrite (grrinvax X _).
  apply idpath.
Defined.

Lemma grinvmaponpathsinv (X : gr) {a b : X} (e : paths (grinv X a) (grinv X b)) : a = b.
Proof.
  assert (e' := maponpaths (λ x, grinv X x) e).
  simpl in e'. rewrite (grinvinv X _) in e'.
  rewrite (grinvinv X _) in e'. apply e'.
Defined.

Lemma grinvandmonoidfun (X Y : gr) {f : X -> Y} (is : ismonoidfun f) (x : X) :
  paths (f (grinv X x)) (grinv Y (f x)).
Proof.
  apply (grrcan Y (f x)).
  rewrite (pathsinv0 (pr1 is _ _)). rewrite (grlinvax X).
  rewrite (grlinvax Y).
  apply (pr2 is).
Defined.

Lemma grinvop (Y : gr) :
  ∏ y1 y2 : Y, grinv Y (@op Y y1 y2) = @op Y (grinv Y y2) (grinv Y y1).
Proof.
  intros y1 y2.
  apply (grrcan Y y1).
  rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
  apply (grrcan Y y2).
  rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
  apply idpath.
Qed.


(** *** Relations on groups *)

Lemma isinvbinophrelgr (X : gr) {R : hrel X} (is : isbinophrel R) : isinvbinophrel R.
Proof.
  set (is1 := pr1 is). set (is2 := pr2 is). split.
  - intros a b c r. set (r' := is1 _ _ (grinv X c) r).
    clearbody r'. rewrite (pathsinv0 (assocax X _ _ a)) in r'.
    rewrite (pathsinv0 (assocax X _ _ b)) in r'.
    rewrite (grlinvax X c) in r'.
    rewrite (lunax X a) in r'.
    rewrite (lunax X b) in r'.
    apply r'.
  - intros a b c r. set (r' := is2 _ _ (grinv X c) r).
    clearbody r'. rewrite ((assocax X a _ _)) in r'.
    rewrite ((assocax X b _ _)) in r'.
    rewrite (grrinvax X c) in r'.
    rewrite (runax X a) in r'.
    rewrite (runax X b) in r'.
    apply r'.
Defined.
Opaque isinvbinophrelgr.

Lemma isbinophrelgr (X : gr) {R : hrel X} (is : isinvbinophrel R) : isbinophrel R.
Proof.
  set (is1 := pr1 is). set (is2 := pr2 is). split.
  - intros a b c r. rewrite (pathsinv0 (lunax X a)) in r.
    rewrite (pathsinv0 (lunax X b)) in r.
    rewrite (pathsinv0 (grlinvax X c)) in r.
    rewrite (assocax X _ _ a) in r.
    rewrite (assocax X _ _ b) in r.
    apply (is1 _ _ (grinv X c) r).
  - intros a b c r. rewrite (pathsinv0 (runax X a)) in r.
    rewrite (pathsinv0 (runax X b)) in r.
    rewrite (pathsinv0 (grrinvax X c)) in r.
    rewrite (pathsinv0 (assocax X a _ _)) in r.
    rewrite (pathsinv0 (assocax X b _ _)) in r.
    apply (is2 _ _ (grinv X c) r).
Defined.
Opaque isbinophrelgr.

Lemma grfromgtunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R x (unel X)) :
  R (unel X) (grinv X x).
Proof.
  intros.
  set (r := (pr2 is) _ _ (grinv X x) isg).
  rewrite (grrinvax X x) in r.
  rewrite (lunax X _) in r.
  apply r.
Defined.

Lemma grtogtunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R (unel X) (grinv X x)) :
  R x (unel X).
Proof.
  assert (r := (pr2 is) _ _ x isg).
  rewrite (grlinvax X x) in r.
  rewrite (lunax X _) in r.
  apply r.
Defined.

Lemma grfromltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R (unel X) x) :
  R (grinv X x) (unel X).
Proof.
  assert (r := (pr1 is) _ _ (grinv X x) isg).
  rewrite (grlinvax X x) in r.
  rewrite (runax X _) in r.
  apply r.
Defined.

Lemma grtoltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R (grinv X x) (unel X)) :
  R (unel X) x.
Proof.
  assert (r := (pr1 is) _ _ x isg).
  rewrite (grrinvax X x) in r. rewrite (runax X _) in r.
  apply r.
Defined.


(** *** Subobjects *)

Definition issubgr {X : gr} (A : hsubtype X) : UU :=
  dirprod (issubmonoid A) (∏ x : X, A x -> A (grinv X x)).

Definition make_issubgr {X : gr} {A : hsubtype X} (H1 : issubmonoid A)
           (H2 : ∏ x : X, A x -> A (grinv X x)) : issubgr A := make_dirprod H1 H2.

Lemma isapropissubgr {X : gr} (A : hsubtype X) : isaprop (issubgr A).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropissubmonoid.
  - apply impred. intro x.
    apply impred. intro a.
    apply (pr2 (A (grinv X x))).
Defined.

Definition subgr (X : gr) : UU := total2 (λ A : hsubtype X, issubgr A).

Definition make_subgr {X : gr} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubgr A) t → ∑ A : hsubtype X, issubgr A :=
  tpair (λ A : hsubtype X, issubgr A).

Definition subgrconstr {X : gr} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubgr A) t → ∑ A : hsubtype X, issubgr A :=
  @make_subgr X.

Definition subgrtosubmonoid (X : gr) : subgr X -> submonoid X :=
  λ A : _, make_submonoid (pr1 A) (pr1 (pr2 A)).
Coercion subgrtosubmonoid : subgr >-> submonoid.

Definition totalsubgr (X : gr) : subgr X.
Proof.
  split with (@totalsubtype X).
  split.
  - exact (pr2 (totalsubmonoid X)).
  - exact (fun _ _ => tt).
Defined.

Definition trivialsubgr (X : gr) : subgr X.
Proof.
  exists (λ x, x = @unel X)%set.
  split.
  - exact (pr2 (@trivialsubmonoid X)).
  - intro.
    intro eq_1.
    induction (!eq_1).
    apply grinvunel.
Defined.

Lemma isinvoncarrier {X : gr} (A : subgr X) :
  isinv (@op A) (unel A) (λ a : A, make_carrier _ (grinv X (pr1 a)) (pr2 (pr2 A) (pr1 a) (pr2 a))).
Proof.
  split.
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grlinvax X (pr1 a)).
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grrinvax X (pr1 a)).
Defined.

Definition isgrcarrier {X : gr} (A : subgr X) : isgrop (@op A) :=
  tpair _ (ismonoidcarrier A)
        (tpair _ (λ a : A, make_carrier _ (grinv X (pr1 a)) (pr2 (pr2 A) (pr1 a) (pr2 a)))
               (isinvoncarrier A)).

Definition carrierofasubgr {X : gr} (A : subgr X) : gr.
Proof. split with A. apply (isgrcarrier A). Defined.
Coercion carrierofasubgr : subgr >-> gr.

Lemma intersection_subgr : forall {X : gr} {I : UU} (S : I -> hsubtype X)
                                  (each_is_subgr : ∏ i : I, issubgr (S i)),
    issubgr (subtype_intersection S).
Proof.
  intros.
  use make_issubgr.
  - exact (intersection_submonoid S (λ i, (pr1 (each_is_subgr i)))).
  - exact (λ x x_in_S i, pr2 (each_is_subgr i) x (x_in_S i)).
Qed.

Definition subgr_incl {X : gr} (A : subgr X) : monoidfun A X :=
submonoid_incl A.

(** *** Quotient objects *)

Lemma grquotinvcomp {X : gr} (R : binopeqrel X) : iscomprelrelfun R R (grinv X).
Proof.
  destruct R as [ R isb ].
  set (isc := iscompbinoptransrel _ (eqreltrans _) isb).
  unfold iscomprelrelfun. intros x x' r.
  destruct R as [ R iseq ]. destruct iseq as [ ispo0 symm0 ].
  destruct ispo0 as [ trans0 refl0 ]. unfold isbinophrel in isb.
  set (r0 := isc _ _ _ _ (isc _ _ _ _ (refl0 (grinv X x')) r) (refl0 (grinv X x))).
  rewrite (grlinvax X x') in r0.
  rewrite (assocax X (grinv X x') x (grinv X x)) in r0.
  rewrite (grrinvax X x) in r0. rewrite (lunax X _) in r0.
  rewrite (runax X _) in r0.
  apply (symm0 _ _ r0).
Defined.
Opaque grquotinvcomp.

Definition invongrquot {X : gr} (R : binopeqrel X) : setquot R -> setquot R :=
  setquotfun R R (grinv X) (grquotinvcomp R).

Lemma isinvongrquot {X : gr} (R : binopeqrel X) :
  isinv (@op (setwithbinopquot R)) (setquotpr R (unel X)) (invongrquot R).
Proof.
  split.
  - unfold islinv.
    apply (setquotunivprop
             R (λ x : setwithbinopquot R, eqset
                                             (@op (setwithbinopquot R) (invongrquot R x) x)
                                             (setquotpr R (unel X)))).
    intro x.
    apply (@maponpaths _ _ (setquotpr R) (@op X (grinv X x) x) (unel X)).
    apply (grlinvax X).
  - unfold isrinv.
    apply (setquotunivprop
             R (λ x : setwithbinopquot R, eqset
                                             (@op (setwithbinopquot R) x (invongrquot R x))
                                             (setquotpr R (unel X)))).
    intro x.
    apply (@maponpaths _ _ (setquotpr R) (@op X x (grinv X x)) (unel X)).
    apply (grrinvax X).
Defined.
Opaque isinvongrquot.

Definition isgrquot {X : gr} (R : binopeqrel X) : isgrop (@op (setwithbinopquot R)) :=
  tpair _ (ismonoidquot R) (tpair _ (invongrquot R) (isinvongrquot R)).

Definition grquot {X : gr} (R : binopeqrel X) : gr.
Proof. split with (setwithbinopquot R). apply isgrquot. Defined.

(** *** Cosets *)

Section GrCosets.
  Context {X : gr}.

  Local Open Scope multmonoid.

  Local Lemma isaprop_mult_eq_r (x y : X) : isaprop (∑ z : X, x * z = y).
  Proof.
    apply invproofirrelevance; intros z1 z2.
    apply subtypeEquality.
    { intros x'. apply setproperty. }
    refine (!lunax _ _ @ _ @ lunax _ _).
    refine (maponpaths (λ z, z * _) (!grlinvax X x) @ _ @
            maponpaths (λ z, z * _) (grlinvax X x)).
    refine (assocax _ _ _ _ @ _ @ !assocax _ _ _ _).
    refine (maponpaths _ (pr2 z1) @ _ @ !maponpaths _ (pr2 z2)).
    reflexivity.
  Defined.

  Local Lemma isaprop_mult_eq_l (x y : X) : isaprop (∑ z : X, z * x = y).
  Proof.
    apply invproofirrelevance; intros z1 z2.
    apply subtypeEquality.
    { intros x'. apply setproperty. }
    refine (!runax _ _ @ _ @ runax _ _).
    refine (maponpaths (λ z, _ * z) (!grrinvax X x) @ _ @
            maponpaths (λ z, _ * z) (grrinvax X x)).
    refine (!assocax _ _ _ _ @ _ @ assocax _ _ _ _).
    refine (maponpaths (λ z, z * _) (pr2 z1) @ _ @ !maponpaths (λ z, z * _) (pr2 z2)).
    reflexivity.
  Defined.

  Context (Y : subgr X).

  Lemma isaprop_in_same_left_coset (x1 x2 : X) :
    isaprop (in_same_left_coset Y x1 x2).
  Proof.
    unfold in_same_left_coset.
    apply invproofirrelevance; intros p q.
    apply subtypeEquality.
    { intros x'. apply setproperty. }
    apply subtypeEquality.
    { intros x'. apply propproperty. }
    pose (p' := (pr11 p,, pr2 p) : ∑ y : X, x1 * y = x2).
    pose (q' := (pr11 q,, pr2 q) : ∑ y : X, x1 * y = x2).
    apply (maponpaths pr1 (iscontrpr1 (isaprop_mult_eq_r _ _ p' q'))).
  Defined.

  Lemma isaprop_in_same_right_coset (x1 x2 : X) :
    isaprop (in_same_right_coset Y x1 x2).
  Proof.
    apply invproofirrelevance.
    intros p q.
    apply subtypeEquality'; [|apply setproperty].
    apply subtypeEquality'; [|apply propproperty].
    pose (p' := (pr11 p,, pr2 p) : ∑ y : X, y * x1 = x2).
    pose (q' := (pr11 q,, pr2 q) : ∑ y : X, y * x1 = x2).
    apply (maponpaths pr1 (iscontrpr1 (isaprop_mult_eq_l _ _ p' q'))).
  Defined.

  (** The property of being in the same coset defines an equivalence relation. *)

  Definition in_same_left_coset_prop : X -> X -> hProp.
  Proof.
    intros x1 x2.
    use make_hProp.
    + exact (in_same_left_coset Y x1 x2).
    + apply isaprop_in_same_left_coset.
  Defined.

  Definition in_same_right_coset_prop : X -> X -> hProp.
  Proof.
    intros x1 x2.
    use make_hProp.
    + exact (in_same_right_coset Y x1 x2).
    + apply isaprop_in_same_right_coset.
  Defined.

  Definition in_same_left_coset_eqrel : eqrel X.
    use make_eqrel.
    - exact in_same_left_coset_prop.
    - use iseqrelconstr.
      + (** Transitivity *)
        intros ? ? ?; cbn; intros inxy inyz.
        unfold in_same_left_coset in *.
        use tpair.
        * exists (pr11 inxy * pr11 inyz).
          apply (pr2 Y).
        * cbn.
          refine (_ @ pr2 inyz).
          refine (_ @ maponpaths (λ z, z * _) (pr2 inxy)).
          apply pathsinv0, assocax.
      + (** Reflexivity *)
        intro; cbn.
        use tpair.
        * exists 1; apply (pr2 Y).
        * apply runax.
      + (** Symmetry *)
        intros x y inxy.
        use tpair.
        * exists (grinv X (pr1 (pr1 inxy))).
          apply (pr2 Y).
          exact (pr2 (pr1 inxy)).
        * cbn in *.
          refine (!maponpaths (λ z, z * _) (pr2 inxy) @ _).
          refine (assocax _ _ _ _ @ _).
          refine (maponpaths _ (grrinvax _ _) @ _).
          apply runax.
  Defined.

  (** x₁ and x₂ are in the same Y-coset if and only if x₁⁻¹ * x₂ is in Y.
      (Proposition 4 in Dummit and Foote) *)

  Definition in_same_coset_test (x1 x2 : X) :
             (Y ((grinv _ x1) * x2)) ≃ in_same_left_coset Y x1 x2.
  Proof.
    apply weqimplimpl; unfold in_same_left_coset in *.
    - intros yx1x2.
      exists ((grinv _ x1) * x2,, yx1x2); cbn.
      refine (!assocax X _ _ _ @ _).
      refine (maponpaths (λ z, z * _) (grrinvax X _) @ _).
      apply lunax.
    - intros y.
      use (transportf (pr1 Y)).
      + exact (pr11 y).
      + refine (_ @ maponpaths _ (pr2 y)).
        refine (_ @ assocax _ _ _ _).
        refine (_ @ !maponpaths (λ z, z * _) (grlinvax X _)).
        apply pathsinv0, lunax.
      + exact (pr2 (pr1 y)).
    - apply propproperty.
    - apply isaprop_in_same_left_coset.
  Defined.
End GrCosets.


(** *** Normal Subgroups *)

Section NormalSubGroups.
  Local Open Scope multmonoid.

  Definition isnormalsubgr {X : gr} (N : subgr X) : hProp := ∀ g : X, ∀ n1 : N, N ((g * (pr1 n1)) * (grinv X g)).

  Definition lcoset_in_rcoset {X : gr} (N : subgr X) : UU := ∏ g : X, ∏ n1 : N, ∑ n2 : N, g * (pr1 n1) = (pr1 n2) * g.

  Definition rcoset_in_lcoset {X : gr} (N : subgr X) : UU := ∏ g : X, ∏ n1 : N, ∑ n2 : N, (pr1 n1) * g = g * (pr1 n2).

  Definition lcoset_equal_rcoset {X : gr} (N : subgr X) : UU := lcoset_in_rcoset N × rcoset_in_lcoset N.

  Lemma lcoset_equal_rcoset_impl_normal {X : gr} (N : subgr X) : lcoset_equal_rcoset N -> isnormalsubgr N.
  Proof.
    intros pf.
    unfold isnormalsubgr.
    intros g n1.
    induction ((pr1 pf) g n1) as [n2 eq_n2].
    assert (n2isconjn1 : g * pr1 n1 * (grinv X g) = pr1 n2).
    { apply (grrcan X g).
      rewrite (assocax _ _ _ _).
      rewrite (grlinvax X _).
      rewrite (runax X).
      exact eq_n2.
    }
    induction (!n2isconjn1).
    exact (pr2 n2).
  Defined.

  Definition normalsubgr (X : gr) : UU := ∑ N : subgr X, isnormalsubgr N.

  Definition normalsubgrtosubgr (X : gr) : normalsubgr X -> subgr X := pr1.
  Coercion normalsubgrtosubgr : normalsubgr >-> subgr.

  Definition normalsubgrprop {X : gr} (N : normalsubgr X) : isnormalsubgr N := pr2 N.

  Lemma normal_lcoset_in_rcoset {X : gr} (N : normalsubgr X) : lcoset_in_rcoset N.
  Proof.
    unfold normalsubgr in N.
    induction N as [N normalprop].
    simpl.
    unfold lcoset_in_rcoset.
    intros g n1.
    use tpair.
    - exact (tpair _ (g * (pr1 n1) * (grinv X g)) (normalprop g n1)).
    - simpl.
      rewrite (assocax _ _ _ g).
      rewrite (grlinvax X _).
      rewrite (runax X).
      reflexivity.
  Defined.

  Definition normal_rcoset_in_lcoset {X : gr} (N : normalsubgr X) : rcoset_in_lcoset N.
  Proof.
    induction N as [N normalprop].
    simpl.
    unfold rcoset_in_lcoset.
    intros g n1.
    use tpair.
    - exact (tpair _ ((grinv X g) * (pr1 n1) * (grinv X (grinv X g))) (normalprop (grinv X g) n1)).
    - simpl.
      rewrite (assocax _ (grinv X g) _ _).
      rewrite (!assocax _ g _ _).
      rewrite (grrinvax X).
      rewrite (lunax X).
      rewrite (grinvinv X).
      reflexivity.
  Defined.

  Definition normal_lcoset_equal_rcoset {X : gr} (N : normalsubgr X) : lcoset_equal_rcoset N :=
    (normal_lcoset_in_rcoset N,,normal_rcoset_in_lcoset N).

  Lemma in_same_coset_isbinophrel {X : gr} (N : normalsubgr X) : isbinophrel (in_same_left_coset_eqrel N).
  Proof.
    unfold isbinophrel.
    split.
    - intros a b c.
      unfold in_same_left_coset_eqrel.
      simpl.
      unfold in_same_left_coset.
      intros pf.
      use tpair.
      + exact (pr1 pf).
      + simpl.
        rewrite (assocax _ c _ _).
        apply (maponpaths (λ x, c * x)).
        exact (pr2 pf).
    - intros a b c.
      unfold in_same_left_coset_eqrel.
      simpl.
      unfold in_same_left_coset.
      intros pf1.
      use tpair.
      + exact (pr1 (normal_rcoset_in_lcoset N c (pr1 pf1))).
      + simpl.
        rewrite (grinvinv _).
        rewrite (assocax _ a _ _).
        rewrite (assocax _ (grinv X c) _ _).
        rewrite (!assocax _ c _ _).
        rewrite (grrinvax _).
        rewrite (lunax _).
        rewrite (!assocax _ a _ _).
        apply (maponpaths (λ x, x * c)).
        exact (pr2 pf1).
  Defined.

  Definition in_same_coset_binopeqrel {X : gr} (N : normalsubgr X) : binopeqrel X :=
    tpair _ (in_same_left_coset_eqrel N) (in_same_coset_isbinophrel N).

  Definition grquot_by_normal_subgr (X : gr) (N : normalsubgr X) : gr := grquot (in_same_coset_binopeqrel N).
End NormalSubGroups.

(** *** Direct products *)

Lemma isgrdirprod (X Y : gr) : isgrop (@op (setwithbinopdirprod X Y)).
Proof.
  split with (ismonoiddirprod X Y).
  split with (λ xy : _, make_dirprod (grinv X (pr1 xy)) (grinv Y (pr2 xy))).
  split.
  - intro xy. destruct xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grlinvax X x). apply (grlinvax Y y).
  - intro xy. destruct xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grrinvax X x). apply (grrinvax Y y).
Defined.

Definition grdirprod (X Y : gr) : gr.
Proof. split with (setwithbinopdirprod X Y). apply isgrdirprod. Defined.


(** ** Abelian groups *)

(** *** Basic definitions *)

Definition abgr : UU := total2 (λ X : setwithbinop, isabgrop (@op X)).

Definition make_abgr (X : setwithbinop) (is : isabgrop (@op X)) : abgr :=
  tpair (λ X : setwithbinop,  isabgrop (@op X)) X is.

Definition abgrconstr (X : abmonoid) (inv0 : X -> X) (is : isinv (@op X) (unel X) inv0) : abgr :=
  make_abgr X (make_dirprod (make_isgrop (pr2 X) (tpair _ inv0 is)) (commax X)).

Definition abgrtogr : abgr -> gr := λ X : _, make_gr (pr1 X) (pr1 (pr2 X)).
Coercion abgrtogr : abgr >-> gr.

Definition abgrtoabmonoid : abgr -> abmonoid :=
  λ X : _, make_abmonoid (pr1 X) (make_dirprod (pr1 (pr1 (pr2 X))) (pr2 (pr2 X))).
Coercion abgrtoabmonoid : abgr >-> abmonoid.

Definition abgr_of_gr (X : gr) (H : iscomm (@op X)) : abgr :=
  make_abgr X (make_isabgrop (pr2 X) H).

(* Declare Scope abgr. *)
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

Lemma abgrfuntounit_ismonoidfun (X : abgr) : ismonoidfun (λ x : X, (unel unitabgr)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use isProofIrrelevantUnit.
  - use isProofIrrelevantUnit.
Qed.

Definition abgrfuntounit (X : abgr) : monoidfun X unitabgr :=
  monoidfunconstr (abgrfuntounit_ismonoidfun X).

Lemma abgrfunfromunit_ismonoidfun (X : abgr) : ismonoidfun (λ x : unitabgr, (unel X)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition abgrfunfromunit (X : abgr) : monoidfun unitabgr X :=
  monoidfunconstr (abgrfunfromunit_ismonoidfun X).

Lemma unelabgrfun_ismonoidfun (X Y : abgr) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. use pathsinv0. use lunax.
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
  - use (pathscomp0 (maponpaths (λ y : Y, grinv Y y) (monoidfununel f))).
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
  tpair _ (tpair _ (pr1 X) (dirprod_pr1 (pr2 X))) (dirprod_pr2 (pr2 X)).

Local Definition abgr_univalence_weq1 : abgr ≃ abgr' :=
  weqtotal2asstol (λ Z : setwithbinop, isgrop (@op Z))
                  (fun y : (∑ x : setwithbinop, isgrop (@op x)) => iscomm (@op (pr1 y))).

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

Definition abgr_univalence_map (X Y : abgr) : (X = Y) -> (monoidiso X Y).
Proof.
  intro e. induction e. exact (idmonoidiso X).
Defined.

Lemma abgr_univalence_isweq (X Y : abgr) : isweq (abgr_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (abgr_univalence_weq1' X Y)
                   (weqcomp (abgr_univalence_weq2 X Y) (abgr_univalence_weq3 X Y))).
  - intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque abgr_univalence_isweq.

Definition abgr_univalence (X Y : abgr) : (X = Y) ≃ (monoidiso X Y).
Proof.
  use make_weq.
  - exact (abgr_univalence_map X Y).
  - exact (abgr_univalence_isweq X Y).
Defined.
Opaque abgr_univalence.


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
    Let f : X -> Y be a morphism of abelian groups. A kernel of f is given by the subgroup of X
    consisting of elements x such that [f x = unel Y].
 *)

(** ** Kernel as abelian group *)

Definition abgr_Kernel_subabgr_issubgr {A B : abgr} (f : monoidfun A B) :
  issubgr (abgr_kernel_hsubtype f).
Proof.
  use make_issubgr.
  - apply kernel_issubmonoid.
  - intros x a.
    apply (grrcan B (f x)).
    apply (pathscomp0 (! (binopfunisbinopfun f (grinv A x) x))).
    apply (pathscomp0 (maponpaths (λ a : A, f a) (grlinvax A x))).
    apply (pathscomp0 (monoidfununel f)).
    apply pathsinv0.
    apply (pathscomp0 (lunax B (f x))).
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
      * use (pathscomp0 (binopfunisbinopfun f (pr1 ae) (pr1 a'e))).
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
    + use (pathscomp0 _ (maponpaths (λ bb : B, (grinv B bb)) (pr2 eb))).
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


(** *** Abelian group of fractions of an abelian unitary monoid *)

Section Fractions.
Import UniMath.Algebra.Monoids.AddNotation.
Local Open Scope addmonoid.

Definition hrelabgrdiff (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2,
    hexists (λ x0 : X, paths (((pr1 xa1) + (pr2 xa2)) + x0) (((pr1 xa2) + (pr2 xa1)) + x0)).

Definition abgrdiffphi (X : abmonoid) (xa : dirprod X X) :
  dirprod X (totalsubtype X) := make_dirprod (pr1 xa) (make_carrier (λ x : X, htrue) (pr2 xa) tt).

Definition hrelabgrdiff' (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2, eqrelabmonoidfrac X (totalsubmonoid X) (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqhrelsabgrdiff (X : abmonoid) : hrellogeq (hrelabgrdiff' X) (hrelabgrdiff X).
Proof.
  split. simpl. apply hinhfun. intro t2.
  set (a0 := pr1 (pr1 t2)). split with a0. apply (pr2 t2). simpl.
  apply hinhfun. intro t2. set (x0 := pr1 t2). split with (tpair _ x0 tt).
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
Defined.
Opaque iseqrelabgrdiff.

Definition eqrelabgrdiff (X : abmonoid) : @eqrel (abmonoiddirprod X X) :=
  make_eqrel _ (iseqrelabgrdiff X).

Lemma isbinophrelabgrdiff (X : abmonoid) : @isbinophrel (abmonoiddirprod X X) (hrelabgrdiff X).
Proof.
  apply (@isbinophrellogeqf (abmonoiddirprod X X) _ _ (logeqhrelsabgrdiff X)).
  split. intros a b c r.
  apply (pr1 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (make_dirprod (pr1 c) (make_carrier (λ x : X, htrue) (pr2 c) tt))
             r).
  intros a b c r.
  apply (pr2 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (make_dirprod (pr1 c) (make_carrier (λ x : X, htrue) (pr2 c) tt))
             r).
Defined.
Opaque isbinophrelabgrdiff.

Definition binopeqrelabgrdiff (X : abmonoid) : binopeqrel (abmonoiddirprod X X) :=
  make_binopeqrel (eqrelabgrdiff X) (isbinophrelabgrdiff X).

Definition abgrdiffcarrier (X : abmonoid) : abmonoid := @abmonoidquot (abmonoiddirprod X X)
                                                                      (binopeqrelabgrdiff X).

Definition abgrdiffinvint (X : abmonoid) :  dirprod X X -> dirprod X X :=
  λ xs : _, make_dirprod (pr2 xs) (pr1 xs).

Lemma abgrdiffinvcomp (X : abmonoid) :
  iscomprelrelfun (hrelabgrdiff X) (eqrelabgrdiff X) (abgrdiffinvint X).
Proof.
  unfold iscomprelrelfun. unfold eqrelabgrdiff. unfold hrelabgrdiff.
  unfold eqrelabmonoidfrac. unfold hrelabmonoidfrac. simpl. intros xs xs'.
  apply (hinhfun). intro tt0.
  set (x := pr1 xs). set (s := pr2 xs).
  set (x' := pr1 xs'). set (s' := pr2 xs').
  split with (pr1 tt0).
  destruct tt0 as [ a eq ]. change (paths (s + x' + a) (s' + x + a)).
  apply pathsinv0. simpl.
  set(e := commax X s' x). simpl in e. rewrite e. clear e.
  set (e := commax X s x'). simpl in e. rewrite e. clear e.
  apply eq.
Defined.
Opaque abgrdiffinvcomp.

Definition abgrdiffinv (X : abmonoid) : abgrdiffcarrier X -> abgrdiffcarrier X :=
  setquotfun (hrelabgrdiff X) (eqrelabgrdiff X) (abgrdiffinvint X) (abgrdiffinvcomp X).

Lemma abgrdiffisinv (X : abmonoid) :
  isinv (@op (abgrdiffcarrier X)) (unel (abgrdiffcarrier X)) (abgrdiffinv X).
Proof.
  set (R := eqrelabgrdiff X).
  assert (isl : islinv (@op (abgrdiffcarrier X)) (unel (abgrdiffcarrier X)) (abgrdiffinv X)).
  {
    unfold islinv.
    apply (setquotunivprop
             R (λ x : abgrdiffcarrier X, eqset (abgrdiffinv X x + x) (unel (abgrdiffcarrier X)))).
    intro xs.
    set (x := pr1 xs). set (s := pr2 xs).
    apply (iscompsetquotpr R (@op (abmonoiddirprod X X) (abgrdiffinvint X xs) xs) (unel _)).
    simpl. apply hinhpr. split with (unel X).
    change (paths (s + x + (unel X) + (unel X)) ((unel X) + (x + s) + (unel X))).
    destruct (commax X x s). destruct (commax X (unel X) (x + s)).
    apply idpath.
  }
  apply (make_dirprod isl (weqlinvrinv (@op (abgrdiffcarrier X)) (commax (abgrdiffcarrier X))
                                      (unel (abgrdiffcarrier X)) (abgrdiffinv X) isl)).
Defined.
Opaque abgrdiffisinv.

Definition abgrdiff (X : abmonoid) : abgr := abgrconstr (abgrdiffcarrier X) (abgrdiffinv X)
                                                        (abgrdiffisinv X).

Definition prabgrdiff (X : abmonoid) : X -> X -> abgrdiff X :=
  λ x x' : X, setquotpr (eqrelabgrdiff X) (make_dirprod x x').


(** *** Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrdiffint (X : abmonoid) : weq (X × X) (dirprod X (totalsubtype X)) :=
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

Definition toabgrdiff (X : abmonoid) (x : X) : abgrdiff X := setquotpr _ (make_dirprod x (unel X)).

Lemma isbinopfuntoabgrdiff (X : abmonoid) : isbinopfun (toabgrdiff X).
Proof.
  unfold isbinopfun. intros x1 x2.
  change (paths (setquotpr _ (make_dirprod (x1 + x2) (unel X)))
                (setquotpr (eqrelabgrdiff X) (make_dirprod (x1 + x2) ((unel X) + (unel X))))).
  apply (maponpaths (setquotpr _)).
  apply (@pathsdirprod X X).
  apply idpath.
  apply (pathsinv0 (lunax X 0)).
Defined.

Lemma isunitalfuntoabgrdiff (X : abmonoid) : paths (toabgrdiff X (unel X)) (unel (abgrdiff X)).
Proof. apply idpath. Defined.

Definition ismonoidfuntoabgrdiff (X : abmonoid) : ismonoidfun (toabgrdiff X) :=
  make_dirprod (isbinopfuntoabgrdiff X) (isunitalfuntoabgrdiff X).


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
  isincl (toabgrdiff X) := isinclprabgrdiff X iscanc (unel X).

Lemma isdeceqabgrdiff (X : abmonoid) (iscanc : ∏ x : X, isrcancelable (@op X) x) (is : isdeceq X) :
  isdeceq (abgrdiff X).
Proof.
  intros.
  apply (isdeceqweqf (invweq (weqabgrdiff X))).
  apply (isdeceqabmonoidfrac X (totalsubmonoid X) (λ a : totalsubmonoid X, iscanc (pr1 a)) is).
Defined.


(** *** Relations on the abelian group of fractions *)

Definition abgrdiffrelint (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa yb, hexists (λ c0 : X, L (((pr1 xa) + (pr2 yb)) + c0) (((pr1 yb) + (pr2 xa)) + c0)).

Definition abgrdiffrelint' (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa1 xa2, abmonoidfracrelint _ (totalsubmonoid X) L (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqabgrdiffrelints (X : abmonoid) (L : hrel X) :
  hrellogeq (abgrdiffrelint' X L) (abgrdiffrelint X L).
Proof.
  split. unfold abgrdiffrelint. unfold abgrdiffrelint'.
  simpl. apply hinhfun. intro t2. set (a0 := pr1 (pr1 t2)).
  split with a0. apply (pr2 t2). simpl. apply hinhfun.
  intro t2. set (x0 := pr1 t2). split with (tpair _ x0 tt). apply (pr2 t2).
Defined.

Lemma iscomprelabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrel (eqrelabgrdiff X) (abgrdiffrelint X L).
Proof.
  apply (iscomprelrellogeqf1 _ (logeqhrelsabgrdiff X)).
  apply (iscomprelrellogeqf2 _ (logeqabgrdiffrelints X L)).
  intros x x' x0 x0' r r0.
  apply (iscomprelabmonoidfracrelint
           _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)  _ _ _ _ r r0).
Defined.
Opaque iscomprelabgrdiffrelint.

Definition abgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) :=
  quotrel (iscomprelabgrdiffrelint X is).

Definition abgrdiffrel' (X : abmonoid) {L : hrel X} (is : isbinophrel L) : hrel (abgrdiff X) :=
  λ x x', abmonoidfracrel X (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                           (weqabgrdiff X x) (weqabgrdiff X x').

Definition logeqabgrdiffrels (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  hrellogeq (abgrdiffrel' X is) (abgrdiffrel X is).
Proof.
  intros x1 x2. split.
  - assert (int : ∏ x x', isaprop (abgrdiffrel' X is x x' -> abgrdiffrel X is x x')).
    {
      intros x x'.
      apply impred. intro.
      apply (pr2 _).
    }
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', make_hProp _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint' X L x x')  -> (abgrdiffrelint _ L x x')).
    apply (pr1 (logeqabgrdiffrelints X L x x')).
  - assert (int : ∏ x x', isaprop (abgrdiffrel X is x x' -> abgrdiffrel' X is x x')).
    intros x x'.
    apply impred. intro.
    apply (pr2 _).
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', make_hProp _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint X L x x') -> (abgrdiffrelint' _ L x x')).
    apply (pr2 (logeqabgrdiffrelints X L x x')).
Defined.

Lemma istransabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istrans L) :
  istrans (abgrdiffrelint X L).
Proof.
  apply (istranslogeqf (logeqabgrdiffrelints X L)).
  intros a b c rab rbc.
  apply (istransabmonoidfracrelint
           _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)  isl _ _ _ rab rbc).
Defined.
Opaque istransabgrdiffrelint.

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
Defined.
Opaque issymmabgrdiffrelint.

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
Defined.
Opaque  isantisymmabgrdiffrel.

Lemma isirreflabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isirrefl L) :
  isirrefl (abgrdiffrel X is).
Proof.
  apply (isirrefllogeqf (logeqabgrdiffrels X is)).
  intros a raa.
  apply (isirreflabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                 isl (weqabgrdiff X a) raa).
Defined.
Opaque isirreflabgrdiffrel.

Lemma isasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isasymm L) :
  isasymm (abgrdiffrel X is).
Proof.
  apply (isasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  apply (isasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
Defined.
Opaque isasymmabgrdiffrel.

Lemma iscoasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscoasymm L) :
  iscoasymm (abgrdiffrel X is).
Proof.
  apply (iscoasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab.
  apply (iscoasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) rab).
Defined.
Opaque iscoasymmabgrdiffrel.

Lemma istotalabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istotal L) :
  istotal (abgrdiffrel X is).
Proof.
  apply (istotallogeqf (logeqabgrdiffrels X is)).
  intros a b.
  apply (istotalabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b)).
Defined.
Opaque istotalabgrdiffrel.

Lemma iscotransabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscotrans L) :
  iscotrans (abgrdiffrel X is).
Proof.
  apply (iscotranslogeqf (logeqabgrdiffrels X is)).
  intros a b c.
  apply (iscotransabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) (weqabgrdiff X c)).
Defined.
Opaque iscotransabgrdiffrel.

Lemma abgrdiffrelimpl (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (impl : ∏ x x', L x x' -> L' x x') (x x' : abgrdiff X) (ql : abgrdiffrel X is x x') :
  abgrdiffrel X is' x x'.
Proof.
  generalize ql. refine (quotrelimpl _ _ _ _ _).
  intros x0 x0'. simpl. apply hinhfun. intro t2. split with (pr1 t2).
  apply (impl _ _ (pr2 t2)).
Defined.
Opaque abgrdiffrelimpl.

Lemma abgrdiffrellogeq (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abgrdiff X) :
  (abgrdiffrel X is x x') <-> (abgrdiffrel X is' x x').
Proof.
  refine (quotrellogeq _ _ _ _ _). intros x0 x0'. split.
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr1 (lg _ _) (pr2 t2)).
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr2 (lg _ _) (pr2 t2)).
Defined.
Opaque abgrdiffrellogeq.

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
Defined.
Opaque isbinopabgrdiffrelint.

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
  - apply ii1. unfold abgrdiffrelint. apply hinhpr. split with (unel X).
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
  change (abgrdiffrelint X L (make_dirprod x (unel X)) (make_dirprod x' (unel X))).
  simpl. apply (hinhpr). split with (unel X).
  apply ((pr2 is) _ _ 0). apply ((pr2 is) _ _ 0).
  apply l.
Defined.
Opaque iscomptoabgrdiff.

Close Scope addmonoid_scope.
End Fractions.