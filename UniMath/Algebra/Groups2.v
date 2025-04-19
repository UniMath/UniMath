(**

  Groups

  Contents
  1. Basic definitions
  2. Computation lemmas for groups
  3. Relations on groups
  4. Subobjects
  5. Quotient objects
  6. Cosets
  7. Normal Subgroups
  8. Direct products
  9. Group of invertible elements in a monoid

 *)
Require Import UniMath.MoreFoundations.Subtypes.
Require Export UniMath.Algebra.Monoids2.
Require Export UniMath.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Core.Categories.

Declare Scope gr.
Delimit Scope gr with gr.

Local Open Scope multmonoid.
Local Open Scope gr.

(** * 1. Basic definitions *)

Definition gr : UU := group_category.

Definition make_gr (t : setwithbinop) (H : isgrop (@op t))
  : gr
  := t ,, H.

Definition grtomonoid : gr → monoid := λ X, make_monoid (pr1 X) (pr1 (pr2 X)).
Coercion grtomonoid : gr >-> monoid.

Definition grinv (X : gr) : X → X := pr1 (pr2 (pr2 X)).

Definition grlinvax (X : gr) : islinv (@op X) 1 (grinv X) := pr1 (pr2 (pr2 (pr2 X))).

Definition grrinvax (X : gr) : isrinv (@op X) 1 (grinv X) := pr2 (pr2 (pr2 (pr2 X))).

Definition gr_of_monoid (X : monoid) (H : invstruct (@op X) (pr2 X)) : gr :=
  make_gr X (make_isgrop (pr2 X) H).

Notation "x / y" := (op x (grinv _ y)) : gr.
Notation   "y ^-1" := (grinv _ y) : gr.

Lemma grinv_path_from_op_path {X : gr} {x y : X} (p : x * y = 1) :
  x^-1 = y.
Proof.
  now rewrite <- (lunax X y), <- (grlinvax X x), assocax, p, runax.
Defined.

Definition group_morphism
  (X Y : gr)
  : UU
  := group_category⟦X, Y⟧%cat.

Definition group_morphism_to_monoidfun
  {X Y : gr}
  (f : group_morphism X Y)
  : monoidfun X Y.
Proof.
  use make_monoidfun.
  - exact (pr1 f : binopfun _ _).
  - apply make_ismonoidfun.
    + apply binopfunisbinopfun.
    + exact (pr212 f).
Defined.

Coercion group_morphism_to_monoidfun : group_morphism >-> monoidfun.

Definition group_morphism_inv
  {X Y : gr}
  (f : group_morphism X Y)
  (x : X)
  : f (x^-1) = (f x)^-1
  := pr22 f x.

Lemma binopfun_preserves_unit
  {X Y : gr}
  (f : X → Y)
  (H : isbinopfun f)
  : f 1 = 1.
Proof.
  apply (lcanfromlinv (@op Y) _ _ _ _ ((f 1)^-1 ,, grlinvax Y _)).
  rewrite runax.
  rewrite <- H.
  rewrite runax.
  reflexivity.
Qed.

Lemma binopfun_preserves_inv
  {X Y : gr}
  (f : X → Y)
  (H : isbinopfun f)
  (x : X)
  : f (x^-1) = (f x)^-1.
Proof.
  apply (lcanfromlinv (@op Y) _ _ _ _ ((f x)^-1 ,, grlinvax Y _)).
  rewrite <- (H x (x^-1)).
  rewrite! grrinvax.
  exact (binopfun_preserves_unit _ H).
Qed.

Definition make_group_morphism
  {X Y : gr}
  (f : X → Y)
  (H : isbinopfun f)
  : group_morphism X Y
  := (f ,, H) ,, ((tt ,, binopfun_preserves_unit f H) ,, binopfun_preserves_inv f H).

Definition binopfun_to_group_morphism
  {X Y : gr}
  (f : binopfun X Y)
  : group_morphism X Y
  := make_group_morphism f (binopfunisbinopfun f).

Lemma group_morphism_paths
  {X Y : gr}
  (f g : group_morphism X Y)
  (H : (f : X → Y) = g)
  : f = g.
Proof.
  apply subtypePath.
  {
    refine (λ (h : magma_morphism _ _), _).
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

Definition group_morphism_eq
  {X Y : gr}
  {f g : group_morphism X Y}
  : (f = g) ≃ (∏ x, f x = g x).
Proof.
  use weqimplimpl.
  - intros e x.
    exact (maponpaths (λ (f : group_morphism _ _), f x) e).
  - intro e.
    apply group_morphism_paths, funextfun.
    exact e.
  - abstract apply homset_property.
  - abstract (
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
Defined.

Definition identity_group_morphism
  (X : gr)
  : group_morphism X X
  := identity X.

Definition composite_group_morphism
  {X Y Z : gr}
  (f : group_morphism X Y)
  (g : group_morphism Y Z)
  : group_morphism X Z
  := (f · g)%cat.

(** *** Construction of the trivial group consisting of one element given by unit. *)

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

Definition unelgrfun (X Y : gr) : group_morphism X Y :=
  binopfun_to_group_morphism (unelmonoidfun X Y).


(** * 2. Computation lemmas for groups *)

Definition weqlmultingr (X : gr) (x0 : X) : X ≃ X :=
  make_weq _ (isweqlmultingr_is (pr2 X) x0).

Definition weqrmultingr (X : gr) (x0 : X) : X ≃ X :=
  make_weq _ (isweqrmultingr_is (pr2 X) x0).

Lemma grlcan (X : gr) {a b : X} (c : X) (e : c * a = c * b) : a = b.
Proof. apply (invmaponpathsweq (weqlmultingr X c) _ _ e). Defined.

Lemma grrcan (X : gr) {a b : X} (c : X) (e : a * c = b * c) : a = b.
Proof. apply (invmaponpathsweq (weqrmultingr X c) _ _ e). Defined.

Lemma grinvunel (X : gr) : (1 : X)^-1 = 1.
Proof.
  apply (grrcan X 1).
  rewrite (grlinvax X). rewrite (runax X).
  apply idpath.
Defined.

Lemma grinvinv (X : gr) (a : X) : (a^-1)^-1 = a.
Proof.
  apply (grlcan X a^-1).
  rewrite (grlinvax X a). rewrite (grrinvax X _).
  apply idpath.
Defined.

Lemma grinvmaponpathsinv (X : gr) {a b : X} (e : a^-1 = b^-1) : a = b.
Proof.
  assert (e' := maponpaths (λ x, x^-1) e).
  simpl in e'. rewrite (grinvinv X _) in e'.
  rewrite (grinvinv X _) in e'. apply e'.
Defined.

Lemma group_morphisminvtoinv {X Y : gr} (f : group_morphism X Y) (x : X) :
  f x^-1 = (f x)^-1.
Proof.
  exact (group_morphism_inv f x).
Qed.

Lemma grinvop (Y : gr) :
  ∏ y1 y2 : Y, (y1 * y2)^-1 = y2^-1 * y1^-1.
Proof.
  intros y1 y2.
  apply (grrcan Y y1).
  rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
  apply (grrcan Y y2).
  rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
  apply idpath.
Qed.


(** * 3. Relations on groups *)

Lemma isinvbinophrelgr (X : gr) {R : hrel X} (is : isbinophrel R) : isinvbinophrel R.
Proof.
  set (is1 := pr1 is). set (is2 := pr2 is). split.
  - intros a b c r. set (r' := is1 _ _ c^-1 r).
    clearbody r'. rewrite <- (assocax X _ _ a) in r'.
    rewrite <- (assocax X _ _ b) in r'.
    rewrite (grlinvax X c) in r'.
    rewrite (lunax X a) in r'.
    rewrite (lunax X b) in r'.
    apply r'.
  - intros a b c r. set (r' := is2 _ _ c^-1 r).
    clearbody r'. rewrite ((assocax X a _ _)) in r'.
    rewrite ((assocax X b _ _)) in r'.
    rewrite (grrinvax X c) in r'.
    rewrite (runax X a) in r'.
    rewrite (runax X b) in r'.
    apply r'.
Qed.

Lemma isbinophrelgr (X : gr) {R : hrel X} (is : isinvbinophrel R) : isbinophrel R.
Proof.
  set (is1 := pr1 is). set (is2 := pr2 is). split.
  - intros a b c r. rewrite <- (lunax X a) in r.
    rewrite <- (lunax X b) in r.
    rewrite <- (grlinvax X c) in r.
    rewrite (assocax X _ _ a) in r.
    rewrite (assocax X _ _ b) in r.
    apply (is1 _ _ c^-1 r).
  - intros a b c r. rewrite <- (runax X a) in r.
    rewrite <- (runax X b) in r.
    rewrite <- (grrinvax X c) in r.
    rewrite <- (assocax X a _ _) in r.
    rewrite <- (assocax X b _ _) in r.
    apply (is2 _ _ c^-1 r).
Qed.

Lemma grfromgtunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R x 1) :
  R 1 x^-1.
Proof.
  intros.
  set (r := (pr2 is) _ _ x^-1 isg).
  rewrite (grrinvax X x) in r.
  rewrite (lunax X _) in r.
  apply r.
Defined.

Lemma grtogtunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R 1 x^-1) :
  R x 1.
Proof.
  assert (r := (pr2 is) _ _ x isg).
  rewrite (grlinvax X x) in r.
  rewrite (lunax X _) in r.
  apply r.
Defined.

Lemma grfromltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R 1 x) :
  R x^-1 1.
Proof.
  assert (r := (pr1 is) _ _ x^-1 isg).
  rewrite (grlinvax X x) in r.
  rewrite (runax X _) in r.
  apply r.
Defined.

Lemma grtoltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R x^-1 1) :
  R 1 x.
Proof.
  assert (r := (pr1 is) _ _ x isg).
  rewrite (grrinvax X x) in r. rewrite (runax X _) in r.
  apply r.
Defined.


(** * 4. Subobjects *)

Definition issubgr {X : gr} (A : hsubtype X) : UU :=
  (issubmonoid A) × (∏ x : X, A x → A x^-1).

Definition make_issubgr {X : gr} {A : hsubtype X} (H1 : issubmonoid A)
           (H2 : ∏ x : X, A x → A x^-1) : issubgr A := H1 ,, H2.

Lemma isapropissubgr {X : gr} (A : hsubtype X) : isaprop (issubgr A).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropissubmonoid.
  - apply impred. intro x.
    apply impred. intro a.
    apply (pr2 (A x^-1)).
Defined.

Definition subgr (X : gr) : UU := ∑ (A : hsubtype X), issubgr A.

Definition make_subgr {X : gr} (t : hsubtype X) (H : issubgr t)
    : subgr X
    := t ,, H.

Definition subgrconstr {X : gr} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubgr A) t → ∑ A : hsubtype X, issubgr A :=
  @make_subgr X.

Definition subgrtosubmonoid (X : gr) : subgr X → submonoid X :=
  λ A, make_submonoid (pr1 A) (pr1 (pr2 A)).
Coercion subgrtosubmonoid : subgr >-> submonoid.

Definition totalsubgr (X : gr) : subgr X.
Proof.
  exists (@totalsubtype X).
  split.
  - exact (pr2 (totalsubmonoid X)).
  - exact (λ _ _, tt).
Defined.

Definition trivialsubgr (X : gr) : subgr X.
Proof.
  exists (λ x, x = 1)%logic.
  split.
  - exact (pr2 (@trivialsubmonoid X)).
  - intro.
    intro eq_1.
    induction (!eq_1).
    apply grinvunel.
Defined.

Lemma isinvoncarrier {X : gr} (A : subgr X) :
  isinv (@op A) (unel A) (λ a : A, make_carrier _ ((pr1 a)^-1) (pr2 (pr2 A) (pr1 a) (pr2 a))).
Proof.
  split.
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grlinvax X (pr1 a)).
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grrinvax X (pr1 a)).
Defined.

Definition isgrcarrier {X : gr} (A : subgr X) : isgrop (@op A) :=
  ismonoidcarrier A ,,
  (λ a : A, make_carrier _ ((pr1 a)^-1) (pr2 (pr2 A) (pr1 a) (pr2 a))) ,,
  isinvoncarrier A.

Definition carrierofasubgr {X : gr} (A : subgr X) : gr.
Proof.
  use make_gr.
  - exact A.
  - apply (isgrcarrier A).
Defined.
Coercion carrierofasubgr : subgr >-> gr.

Lemma intersection_subgr : forall {X : gr} {I : UU} (S : I → hsubtype X)
                                  (each_is_subgr : ∏ i : I, issubgr (S i)),
    issubgr (subtype_intersection S).
Proof.
  intros.
  use make_issubgr.
  - exact (intersection_submonoid S (λ i, (pr1 (each_is_subgr i)))).
  - exact (λ x x_in_S i, pr2 (each_is_subgr i) x (x_in_S i)).
Qed.

Definition subgr_incl {X : gr} (A : subgr X) : group_morphism A X :=
  binopfun_to_group_morphism (X := A) (submonoid_incl A).

(** * 5. Quotient objects *)

Lemma grquotinvcomp {X : gr} (R : binopeqrel X) : iscomprelrelfun R R (λ x, x^-1).
Proof.
  induction R as [ R isb ].
  set (isc := iscompbinoptransrel _ (eqreltrans _) isb).
  unfold iscomprelrelfun. intros x x' r.
  induction R as [ R iseq ]. induction iseq as [ ispo0 symm0 ].
  induction ispo0 as [ trans0 refl0 ]. unfold isbinophrel in isb.
  set (r0 := isc _ _ _ _ (isc _ _ _ _ (refl0 x'^-1) r) (refl0 x^-1)).
  rewrite (grlinvax X x') in r0.
  rewrite (assocax X x'^-1 x x^-1) in r0.
  rewrite (grrinvax X x) in r0. rewrite (lunax X _) in r0.
  rewrite (runax X _) in r0.
  apply (symm0 _ _ r0).
Qed.

Definition invongrquot {X : gr} (R : binopeqrel X) : setquot R → setquot R :=
  setquotfun R R (λ x, x^-1) (grquotinvcomp R).

Lemma isinvongrquot {X : gr} (R : binopeqrel X) :
  isinv (@op (setwithbinopquot R)) (setquotpr R 1) (invongrquot R).
Proof.
  split.
  - unfold islinv.
    apply (setquotunivprop R (λ x, _ = _)%logic).
    intro x.
    apply (@maponpaths _ _ (setquotpr R) (x^-1 * x) 1).
    apply (grlinvax X).
  - unfold isrinv.
    apply (setquotunivprop R (λ x, _ = _)%logic).
    intro x.
    apply (@maponpaths _ _ (setquotpr R) (x / x) 1).
    apply (grrinvax X).
Qed.

Definition isgrquot {X : gr} (R : binopeqrel X) : isgrop (@op (setwithbinopquot R)) :=
  ismonoidquot R ,, invongrquot R ,, isinvongrquot R.

Definition grquot {X : gr} (R : binopeqrel X) : gr.
Proof. exists (setwithbinopquot R). apply isgrquot. Defined.

(** * 6. Cosets *)

Section GrCosets.
  Context {X : gr}.

  Local Lemma isaprop_mult_eq_r (x y : X) : isaprop (∑ z : X, x * z = y).
  Proof.
    apply invproofirrelevance; intros z1 z2.
    apply subtypePath.
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
    apply subtypePath.
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
    apply subtypePath.
    { intros x'. apply setproperty. }
    apply subtypePath.
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
    apply subtypePath; [intros x; apply setproperty|].
    apply subtypePath; [intros x; apply propproperty|].
    pose (p' := (pr11 p,, pr2 p) : ∑ y : X, y * x1 = x2).
    pose (q' := (pr11 q,, pr2 q) : ∑ y : X, y * x1 = x2).
    apply (maponpaths pr1 (iscontrpr1 (isaprop_mult_eq_l _ _ p' q'))).
  Defined.

  (** The property of being in the same coset defines an equivalence relation. *)

  Definition in_same_left_coset_prop : X → X → hProp.
  Proof.
    intros x1 x2.
    use make_hProp.
    + exact (in_same_left_coset Y x1 x2).
    + apply isaprop_in_same_left_coset.
  Defined.

  Definition in_same_right_coset_prop : X → X → hProp.
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
          exact (!assocax _ _ _ _).
      + (** Reflexivity *)
        intro; cbn.
        use tpair.
        * exists 1; apply (pr2 Y).
        * apply runax.
      + (** Symmetry *)
        intros x y inxy.
        use tpair.
        * exists ((pr1 (pr1 inxy))^-1).
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
             (Y (x1^-1 * x2)) ≃ in_same_left_coset Y x1 x2.
  Proof.
    apply weqimplimpl; unfold in_same_left_coset in *.
    - intros yx1x2.
      exists (x1^-1 * x2,, yx1x2); cbn.
      refine (!assocax X _ _ _ @ _).
      refine (maponpaths (λ z, z * _) (grrinvax X _) @ _).
      apply lunax.
    - intros y.
      use (transportf (pr1 Y)).
      + exact (pr11 y).
      + refine (_ @ maponpaths _ (pr2 y)).
        refine (_ @ assocax _ _ _ _).
        refine (_ @ !maponpaths (λ z, z * _) (grlinvax X _)).
        exact (!lunax _ _).
      + exact (pr2 (pr1 y)).
    - apply propproperty.
    - apply isaprop_in_same_left_coset.
  Defined.
End GrCosets.


(** * 7. Normal Subgroups *)

Section NormalSubGroups.

  Definition isnormalsubgr {X : gr} (N : subgr X) : hProp :=
    ∀ g : X, ∀ n1 : N, N ((g * (pr1 n1)) / g).

  Definition normalsubgr (X : gr) : UU := ∑ N : subgr X, isnormalsubgr N.

  Definition normalsubgrtosubgr (X : gr) : normalsubgr X → subgr X := pr1.
  Coercion normalsubgrtosubgr : normalsubgr >-> subgr.

  Definition normalsubgrprop {X : gr} (N : normalsubgr X) : isnormalsubgr N := pr2 N.

  Definition lcoset_in_rcoset {X : gr} (N : subgr X) : UU :=
    ∏ g : X, ∏ n1 : N, ∑ n2 : N, g * (pr1 n1) = (pr1 n2) * g.
  Definition lcoset_in_rcoset_witness {X : gr} {N : subgr X} :
    lcoset_in_rcoset N → (X → N → N) := λ H g n1, pr1 (H g n1).
  Definition lcoset_in_rcoset_property {X : gr} {N : subgr X}
      (H : lcoset_in_rcoset N) (g : X) (n1 : N) :
    N (pr1 (lcoset_in_rcoset_witness H g n1)) := pr2 (lcoset_in_rcoset_witness H g n1).
  Definition lcoset_in_rcoset_equation {X : gr} {N : subgr X}
      (H : lcoset_in_rcoset N) (g : X) (n1 : N) :
    g * (pr1 n1) = (pr1 (lcoset_in_rcoset_witness H g n1)) * g := pr2 (H g n1).

  Definition rcoset_in_lcoset {X : gr} (N : subgr X) : UU :=
    ∏ g : X, ∏ n1 : N, ∑ n2 : N, (pr1 n1) * g = g * (pr1 n2).
  Definition rcoset_in_lcoset_witness {X : gr} {N : subgr X} :
    rcoset_in_lcoset N → (X → N → N) := λ H g n1, pr1 (H g n1).
  Definition rcoset_in_lcoset_property {X : gr} {N : subgr X}
      (H : rcoset_in_lcoset N) (g : X) (n1 : N) :
    N (pr1 (rcoset_in_lcoset_witness H g n1)) := pr2 (rcoset_in_lcoset_witness H g n1).
  Definition rcoset_in_lcoset_equation {X : gr} {N : subgr X}
      (H : rcoset_in_lcoset N) (g : X) (n1 : N) :
    (pr1 n1) * g = g * (pr1 (rcoset_in_lcoset_witness H g n1)) := pr2 (H g n1).

  Definition lcoset_equal_rcoset {X : gr} (N : subgr X) : UU :=
    lcoset_in_rcoset N × rcoset_in_lcoset N.

  Lemma lcoset_in_rcoset_impl_normal {X : gr} (N : subgr X) :
    lcoset_in_rcoset N → isnormalsubgr N.
  Proof.
    intros lcinrc.
    unfold isnormalsubgr.
    intros g n1.
    refine (@transportb _ (λ x, N x) _ _ _ _).
    { etrans. { apply maponpaths_2, (lcoset_in_rcoset_equation lcinrc). }
      etrans. { apply assocax. }
      etrans. { apply maponpaths, grrinvax. }
      apply runax.
    }
    apply lcoset_in_rcoset_property.
  Defined.

  Lemma lcoset_equal_rcoset_impl_normal {X : gr} (N : subgr X) :
    lcoset_equal_rcoset N → isnormalsubgr N.
  Proof.
    intros H. apply lcoset_in_rcoset_impl_normal. exact (pr1 H).
  Defined.

  Lemma normal_lcoset_in_rcoset {X : gr} (N : normalsubgr X) : lcoset_in_rcoset N.
  Proof.
    unfold normalsubgr in N.
    induction N as [N normalprop].
    simpl.
    unfold lcoset_in_rcoset.
    intros g n1.
    use tpair.
    - exact (g * pr1 n1 / g ,, normalprop g n1).
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
    - exists (g^-1 * (pr1 n1) / g^-1). use normalprop.
    - simpl.
      rewrite (assocax _ g^-1 _ _).
      rewrite <- (assocax _ g _ _).
      rewrite (grrinvax X).
      rewrite (lunax X).
      rewrite (grinvinv X).
      reflexivity.
  Defined.

  Definition normal_lcoset_equal_rcoset {X : gr} (N : normalsubgr X) : lcoset_equal_rcoset N :=
    (normal_lcoset_in_rcoset N,,normal_rcoset_in_lcoset N).

  Lemma in_same_coset_isbinophrel {X : gr} (N : normalsubgr X) :
    isbinophrel (in_same_left_coset_eqrel N).
  Proof.
    unfold isbinophrel.
    split.
    - intros a b c.
      unfold in_same_left_coset_eqrel.
      simpl.
      unfold in_same_left_coset.
      intros ab_same_lcoset.
      use tpair.
      + exact (pr1 ab_same_lcoset).
      + simpl.
        rewrite (assocax _ c _ _).
        apply maponpaths.
        exact (pr2 ab_same_lcoset).
    - intros a b c.
      unfold in_same_left_coset_eqrel.
      simpl.
      unfold in_same_left_coset.
      intros ab_same_lcoset.
      use tpair.
      + refine (rcoset_in_lcoset_witness _ c (pr1 ab_same_lcoset));
          apply normal_rcoset_in_lcoset.
      + simpl.
        rewrite (grinvinv _).
        rewrite (assocax _ a _ _).
        rewrite (assocax _ c^-1 _ _).
        rewrite <- (assocax _ c _ _).
        rewrite (grrinvax _).
        rewrite (lunax _).
        rewrite <- (assocax _ a _ _).
        apply maponpaths_2.
        exact (pr2 ab_same_lcoset).
  Defined.

  Definition in_same_coset_binopeqrel {X : gr} (N : normalsubgr X) : binopeqrel X :=
    in_same_left_coset_eqrel N ,, in_same_coset_isbinophrel N.

  Definition grquot_by_normal_subgr (X : gr) (N : normalsubgr X) : gr :=
    grquot (in_same_coset_binopeqrel N).

End NormalSubGroups.

(** * 8. Direct products *)

Lemma isgrdirprod (X Y : gr) : isgrop (@op (setwithbinopdirprod X Y)).
Proof.
  exists (ismonoiddirprod X Y).
  exists (λ xy, (pr1 xy)^-1 ,, (pr2 xy)^-1).
  split.
  - intro xy. induction xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grlinvax X x). apply (grlinvax Y y).
  - intro xy. induction xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grrinvax X x). apply (grrinvax Y y).
Defined.

Definition grdirprod (X Y : gr) : gr.
Proof. exists (setwithbinopdirprod X Y). apply isgrdirprod. Defined.

(** * 9. Group of invertible elements in a monoid *)

Definition invertible_submonoid_grop X : isgrop (@op (invertible_submonoid X)).
Proof.
  pose (submon := invertible_submonoid X).
  pose (submon_carrier := ismonoidcarrier submon).

  (** We know that if each element has an inverse, it's a grop *)
  apply (isgropif submon_carrier).

  intros xpair.
  pose (x := pr1 xpair).
  pose (unel := unel_is submon_carrier).

  (** We can use other hProps when proving an hProp (assume it has an inverse) *)
  apply (squash_to_prop (pr2 xpair) (propproperty _)).

  intros xinv.
  unfold haslinv.
  apply hinhpr.
  refine ((pr1 xinv,, inverse_in_submonoid _ x (pr1 xinv) (pr2 xpair) (pr2 xinv)),, _).
  apply subtypePath_prop.
  exact (pr2 (pr2 xinv)).
Defined.

Definition gr_merely_invertible_elements : monoid → gr :=
  λ X, carrierofasubsetwithbinop (submonoidtosubsetswithbinop _ (invertible_submonoid X)) ,,
       invertible_submonoid_grop X.
