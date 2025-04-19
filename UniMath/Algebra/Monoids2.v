(**

  Monoids

  Contents
  1. Basic definitions
  2. Functions between monoids compatible with structures (homomorphisms) and their properties
  3. Subobjects
  4. Kernels
  5. Quotient objects
  6. Cosets
  7. Direct products

 *)

(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Kernel Term Sharing.

Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.MoreFoundations.Sets.

Require Export UniMath.CategoryTheory.Categories.Magma.
Require Export UniMath.CategoryTheory.Core.Categories.

Declare Scope multmonoid.
Delimit Scope multmonoid with multmonoid.

Local Open Scope multmonoid.

(** * 1. Basic definitions *)

Definition monoid
  : UU
  := monoid_category.

Definition make_monoid (t : setwithbinop) (H : ismonoidop (@op t))
  : monoid
  := t ,, H.

Definition pr1monoid : monoid → magma := @pr1 _ _.
Coercion pr1monoid : monoid >-> magma.

Definition assocax (X : monoid) : isassoc (@op X) := pr1 (pr2 X).

Definition unel (X : monoid) : X := pr1 (pr2 (pr2 X)).

Definition lunax (X : monoid) : islunit (@op X) (unel X) := pr1 (pr2 (pr2 (pr2 X))).

Definition runax (X : monoid) : isrunit (@op X) (unel X) := pr2 (pr2 (pr2 (pr2 X))).

Definition unax (X : monoid) : isunit (@op X) (unel X) := lunax X ,, runax X.

Definition isasetmonoid (X : monoid) : isaset X := pr2 (pr1 (pr1 X)).

Notation "x * y" := (op x y) : multmonoid.
Notation "1" := (unel _) : multmonoid.

(** **** Construction of the trivial monoid consisting of one element given by unit. *)

Definition unitmonoid_ismonoid : ismonoidop (λ x : unitset, λ y : unitset, x).
Proof.
  use make_ismonoidop.
  - intros x x' x''. use isProofIrrelevantUnit.
  - use make_isunital.
    + exact tt.
    + use make_isunit.
      * intros x. use isProofIrrelevantUnit.
      * intros x. use isProofIrrelevantUnit.
Qed.

Definition unitmonoid : monoid :=
  make_monoid (make_setwithbinop unitset (λ x : unitset, λ y : unitset, x))
             unitmonoid_ismonoid.


(** * 2. Functions between monoids compatible with structures (homomorphisms) and their properties *)

Definition ismonoidfun {X Y : monoid} (f : X → Y) : UU :=
  isbinopfun f × (f 1 = 1).

Definition make_ismonoidfun {X Y : monoid} {f : X → Y} (H1 : isbinopfun f)
           (H2 : f 1 = 1) : ismonoidfun f := H1 ,, H2.

Definition ismonoidfunisbinopfun {X Y : monoid} {f : X → Y} (H : ismonoidfun f) : isbinopfun f :=
  dirprod_pr1 H.

Definition ismonoidfununel {X Y : monoid} {f : X → Y} (H : ismonoidfun f) : f 1 = 1 :=
  dirprod_pr2 H.

Lemma isapropismonoidfun {X Y : monoid} (f : X → Y) : isaprop (ismonoidfun f).
Proof.
  apply isofhleveldirprod.
  - apply isapropisbinopfun.
  - apply (setproperty Y).
Defined.

Definition monoidfun (X Y : monoid) : UU := monoid_category⟦X, Y⟧%cat.

Definition make_monoidfun {X Y : monoid} {f : X → Y} (is : ismonoidfun f) : monoidfun X Y
  := (f ,, pr1 is) ,, (tt ,, pr2 is).

Definition pr1monoidfun (X Y : monoid) (f : monoidfun X Y) : X → Y := pr11 f.

Definition monoidfuntobinopfun (X Y : monoid) (f : monoidfun X Y) : binopfun X Y :=
  pr1 f.
Coercion monoidfuntobinopfun : monoidfun >-> binopfun.

Definition ismonoidfun_monoidfun
  {X Y : monoid}
  (f : monoidfun X Y)
  : ismonoidfun f
  := pr21 f ,, pr22 f.

Definition monoidfunmul {X Y : monoid} (f : monoidfun X Y) (x x' : X) : f (x * x') = f x * f x' :=
  ismonoidfunisbinopfun (ismonoidfun_monoidfun f) x x'.

Definition monoidfununel {X Y : monoid} (f : monoidfun X Y) : f 1 = 1 := ismonoidfununel (ismonoidfun_monoidfun f).

Definition monoidfun_paths {X Y : monoid} (f g : monoidfun X Y) (e : (f : _ → _) = g) : f = g.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropdirprod.
    - apply isapropunit.
    - apply setproperty.
  }
  apply (subtypePath (isapropisbinopfun)).
  exact e.
Qed.

Definition monoidfun_eq
  {X Y : monoid}
  {f g : monoidfun X Y}
  : (f = g) ≃ (∏ x, f x = g x).
Proof.
  use weqimplimpl.
  - intros e x.
    exact (maponpaths (λ (f : monoidfun _ _), f x) e).
  - intro e.
    apply monoidfun_paths, funextfun.
    exact e.
  - abstract apply homset_property.
  - abstract (
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
Defined.

Lemma isasetmonoidfun (X Y : monoid) : isaset (monoidfun X Y).
Proof.
  apply homset_property.
Defined.

Definition monoidfuncomp {X Y Z : monoid} (f : monoidfun X Y) (g : monoidfun Y Z) :
  monoidfun X Z := (f · g)%cat.

Lemma monoidfunassoc {X Y Z W : monoid} (f : monoidfun X Y) (g : monoidfun Y Z)
      (h : monoidfun Z W) : monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
Proof.
  apply assoc.
Qed.

Lemma unelmonoidfun_ismonoidfun (X Y : monoid) : ismonoidfun (Y := Y) (λ x : X, 1).
Proof.
  use make_ismonoidfun.
  - use make_isbinopfun. intros x x'. exact (!lunax _ _).
  - use idpath.
Qed.

Definition unelmonoidfun (X Y : monoid) : monoidfun X Y :=
  make_monoidfun (unelmonoidfun_ismonoidfun X Y).

Definition monoidmono (X Y : monoid) : UU := ∑ (f : incl X Y), ismonoidfun f.

Definition make_monoidmono {X Y : monoid} (f : incl X Y) (is : ismonoidfun f) :
  monoidmono X Y := f ,, is.

Definition pr1monoidmono (X Y : monoid) : monoidmono X Y → incl X Y := @pr1 _ _.
Coercion pr1monoidmono : monoidmono >-> incl.

Definition monoidincltomonoidfun (X Y : monoid) :
  monoidmono X Y → monoidfun X Y := λ f, make_monoidfun (pr2 f).
Coercion monoidincltomonoidfun : monoidmono >-> monoidfun.

Definition monoidmonotobinopmono (X Y : monoid) : monoidmono X Y → binopmono X Y := λ f, make_binopmono (pr1 f) (pr1 (pr2 f)).
Coercion monoidmonotobinopmono : monoidmono >-> binopmono.

Definition monoidmonocomp {X Y Z : monoid}
           (f : monoidmono X Y) (g : monoidmono Y Z) : monoidmono X Z :=
  make_monoidmono (inclcomp (pr1 f) (pr1 g)) (ismonoidfun_monoidfun (monoidfuncomp f g)).

Definition monoidiso (X Y : monoid) : UU :=
  ∑ (f : X ≃ Y), ismonoidfun f.

Definition make_monoidiso {X Y : monoid} (f : X ≃ Y) (is : ismonoidfun f) :
  monoidiso X Y := f ,, is.

Definition pr1monoidiso (X Y : monoid) : monoidiso X Y → X ≃ Y := @pr1 _ _.
Coercion pr1monoidiso : monoidiso >-> weq.

Definition monoidisotomonoidmono (X Y : monoid) : monoidiso X Y → monoidmono X Y :=
  λ f, make_monoidmono (weqtoincl (pr1 f)) (pr2 f).
Coercion monoidisotomonoidmono : monoidiso >-> monoidmono.

Definition monoidisotobinopiso (X Y : monoid) : monoidiso X Y → binopiso X Y :=
  λ f, make_binopiso (pr1 f) (pr1 (pr2 f)).
Coercion monoidisotobinopiso : monoidiso >-> binopiso.

Definition monoidiso_paths {X Y : monoid} (f g : monoidiso X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropismonoidfun.
Qed.

Lemma ismonoidfuninvmap {X Y : monoid} (f : monoidiso X Y) :
  ismonoidfun (invmap (pr1 f)).
Proof.
  exists (isbinopfuninvmap f).
  apply (invmaponpathsweq (pr1 f)).
  rewrite (homotweqinvweq (pr1 f)).
  apply (!pr2 (pr2 f)).
Qed.

Definition invmonoidiso {X Y : monoid} (f : monoidiso X Y) : monoidiso Y X :=
  make_monoidiso (invweq (pr1 f)) (ismonoidfuninvmap f).

Definition idmonoidiso (X : monoid) : monoidiso X X.
Proof.
  use make_monoidiso.
  - exact (idweq X).
  - use make_dirprod.
    + intros x x'. use idpath.
    + use idpath.
Defined.

Lemma monoidfunidleft {A B : monoid} (f : monoidfun A B) : monoidfuncomp (idmonoidiso A) f = f.
Proof.
  use monoidfun_paths. use idpath.
Qed.

Lemma monoidfunidright {A B : monoid} (f : monoidfun A B) : monoidfuncomp f (idmonoidiso B) = f.
Proof.
  use monoidfun_paths. use idpath.
Qed.


(** * 3. Subobjects *)

Definition issubmonoid {X : monoid} (A : hsubtype X) : UU :=
  (issubsetwithbinop (@op X) A) × (A 1).

Definition make_issubmonoid {X : monoid} {A : hsubtype X} (H1 : issubsetwithbinop (@op X) A)
           (H2 : A 1) : issubmonoid A := H1 ,, H2.

Lemma isapropissubmonoid {X : monoid} (A : hsubtype X) :
  isaprop (issubmonoid A).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropissubsetwithbinop.
  - apply (pr2 (A 1)).
Defined.

Definition submonoid (X : monoid) : UU := ∑ (A : hsubtype X), issubmonoid A.

Definition make_submonoid {X : monoid} (t : hsubtype X) (H : issubmonoid t)
  : submonoid X
  := t ,, H.

Definition pr1submonoid (X : monoid) : submonoid X → hsubtype X := @pr1 _ _.

Lemma isaset_submonoid (A : monoid) : isaset (submonoid A).
Proof.
  apply isaset_total2.
  - apply isasethsubtype.
  - intro P. apply isasetaprop, isapropissubmonoid.
Defined.

Definition totalsubmonoid (X : monoid) : submonoid X.
Proof.
  exists (totalsubtype X). split.
  - intros x x'. apply tt.
  - apply tt.
Defined.

Definition trivialsubmonoid (X : monoid) : @submonoid X.
Proof.
  intros.
  exists (λ x, x = 1)%logic.
  split.
  - intros b c.
    induction b as [x p], c as [y q].
    cbn in *.
    induction (!p), (!q).
    rewrite lunax.
    apply idpath.
  - apply idpath.
Defined.

Definition submonoidtosubsetswithbinop (X : monoid) : submonoid X → @subsetswithbinop X :=
  λ A, make_subsetswithbinop (pr1 A) (pr1 (pr2 A)).
Coercion submonoidtosubsetswithbinop : submonoid >-> subsetswithbinop.

Lemma ismonoidcarrier {X : monoid} (A : submonoid X) : ismonoidop (@op A).
Proof.
  split.
  - intros a a' a''. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (assocax X).
  - exists (make_carrier _ 1 (pr2 (pr2 A))).
    split.
    + simpl. intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply (lunax X).
    + intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply (runax X).
Defined.

Definition carrierofsubmonoid {X : monoid} (A : submonoid X) : monoid.
Proof.
  use make_monoid.
  - exact A.
  - apply ismonoidcarrier.
Defined.
Coercion carrierofsubmonoid : submonoid >-> monoid.

Lemma intersection_submonoid :
  forall {X : monoid} {I : UU} (S : I → hsubtype X)
         (each_is_submonoid : ∏ i : I, issubmonoid (S i)),
    issubmonoid (subtype_intersection S).
Proof.
  intros.
  use make_issubmonoid.
  + intros g h i.
    pose (is_subgr := pr1 (each_is_submonoid i)).
    exact (is_subgr (pr1 g,, (pr2 g) i) (pr1 h,, (pr2 h) i)).
  + exact (λ i, pr2 (each_is_submonoid i)).
Qed.

(* Lemma ismonoidfun_pr1 {X : monoid} (A : submonoid X) : ismonoidfun (pr1submonoid X A). *)
(* ismake_monoidfun _ _. *)

Lemma ismonoidfun_pr1 {X : monoid} (A : submonoid X) : @ismonoidfun A X pr1.
Proof.
  use make_ismonoidfun.
  - intros a a'. reflexivity.
  - reflexivity.
Defined.

Definition submonoid_incl {X : monoid} (A : submonoid X) : monoidfun A X :=
  make_monoidfun (ismonoidfun_pr1 A).

(** Every monoid has a submonoid which is a group, the collection of elements
    with inverses. This is used to construct the automorphism group from the
    endomorphism monoid, for instance. *)

Definition invertible_submonoid (X : monoid) : @submonoid X.
Proof.
  refine (merely_invertible_elements (@op X) (pr2 X),, _).
  split.
  (** This is a similar statement to [grinvop] *)
  - intros xpair ypair.
    apply mere_invop.
    + exact (pr2 xpair).
    + exact (pr2 ypair).
  - apply hinhpr; exact (1 ,, (lunax _ 1) ,, (lunax _ 1)).
Defined.

(** This submonoid is closed under inversion *)
Lemma inverse_in_submonoid (X : monoid) :
  ∏ (x x0 : X), merely_invertible_elements (@op X) (pr2 X) x →
                isinvel (@op X) (pr2 X) x x0 →
                merely_invertible_elements (@op X) (pr2 X) x0.
Proof.
  intros x x0 _ x0isxinv.
  unfold merely_invertible_elements, hasinv.
  apply hinhpr.
  exact (x,, is_inv_inv (@op X) _ _ _ x0isxinv).
Defined.

(** * 4. Kernels *)

(** Kernels
    Let f : X → Y be a morphism of monoids. The kernel of f is
    the submonoid of X consisting of elements x such that [f x = 1].
 *)

Definition monoid_kernel_hsubtype {A B : monoid} (f : monoidfun A B) : hsubtype A.
Proof.
  intros a.
  use make_hProp.
  - exact (f a = 1).
  - apply setproperty.
Defined.

(** Kernel as a monoid *)

Definition kernel_issubmonoid {A B : monoid} (f : monoidfun A B) :
  issubmonoid (monoid_kernel_hsubtype f).
Proof.
  use make_issubmonoid.
  - intros x y.
    refine (monoidfunmul f _ _ @ _).
    refine (maponpaths _ (pr2 y) @ _).
    refine (runax _ _ @ _).
    exact (pr2 x).
  - apply monoidfununel.
Defined.

Definition kernel_submonoid {A B : monoid} (f : monoidfun A B) : @submonoid A :=
  make_submonoid _ (kernel_issubmonoid f).

(** * 5. Quotient objects *)

Lemma isassocquot {X : monoid} (R : binopeqrel X) : isassoc (@op (setwithbinopquot R)).
Proof.
  intros a b c.
  apply (setquotuniv3prop
           R (λ x x' x'' : setwithbinopquot R,
                make_hProp _ (setproperty (setwithbinopquot R) ((x * x') * x'')
                                         (x * (x' * x''))))).
  intros x x' x''.
  apply (maponpaths (setquotpr R) (assocax X x x' x'')).
Qed.

Lemma isunitquot {X : monoid} (R : binopeqrel X) :
  isunit (@op (setwithbinopquot R)) (setquotpr R (pr1 (pr2 (pr2 X)))).
Proof.
  intros.
  set (qun := setquotpr R (pr1 (pr2 (pr2 X)))).
  set (qsetwithop := setwithbinopquot R).
  split.
  - intro x.
    apply (setquotunivprop R (λ x, (@op qsetwithop) qun x = x)%logic).
    simpl. intro x0.
    apply (maponpaths (setquotpr R) (lunax X x0)).
  - intro x.
    apply (setquotunivprop R (λ x, (@op qsetwithop) x qun = x)%logic).
    simpl. intro x0. apply (maponpaths (setquotpr R) (runax X x0)).
Qed.

Definition ismonoidquot {X : monoid} (R : binopeqrel X) : ismonoidop (@op (setwithbinopquot R)) :=
  isassocquot R ,, setquotpr R (pr1 (pr2 (pr2 X))) ,, isunitquot R.

Definition monoidquot {X : monoid} (R : binopeqrel X) : monoid.
Proof. exists (setwithbinopquot R). apply ismonoidquot. Defined.

Lemma ismonoidfun_setquotpr {X : monoid} (R : binopeqrel X) : @ismonoidfun X (monoidquot R) (setquotpr R).
Proof.
  use make_ismonoidfun.
  - intros x y. reflexivity.
  - reflexivity.
Defined.

Definition monoidquotpr {X : monoid} (R : binopeqrel X) : monoidfun X (monoidquot R) :=
  make_monoidfun (ismonoidfun_setquotpr R).

Lemma ismonoidfun_setquotuniv {X Y : monoid} {R : binopeqrel X} (f : monoidfun X Y)
      (H : iscomprelfun R f) : @ismonoidfun (monoidquot R) Y (setquotuniv R Y f H).
Proof.
  use make_ismonoidfun.
  - refine (setquotuniv2prop' _ _ _).
    + intros. apply isasetmonoid.
    + intros. simpl. rewrite setquotfun2comm. rewrite !setquotunivcomm.
      apply monoidfunmul.
  - exact (setquotunivcomm _ _ _ _ _ @ monoidfununel _).
Defined.

(** The universal property of the quotient monoid. If X, Y are monoids, R is a congruence on X, and
    [f : X → Y] is a homomorphism which respects R, then there exists a unique homomorphism
    [f' : X/R → Y] making the following diagram commute:
<<
    X -π-> X/R
     \      |
       f    | ∃! f'
         \  |
          V V
           Y
>>
 *)

Definition monoidquotuniv {X Y : monoid} {R : binopeqrel X} (f : monoidfun X Y)
      (H : iscomprelfun R f) : monoidfun (monoidquot R) Y :=
  make_monoidfun (ismonoidfun_setquotuniv f H).

Definition monoidquotfun {X Y : monoid} {R : binopeqrel X} {S : binopeqrel Y}
  (f : monoidfun X Y) (H : ∏ x x' : X, R x x' → S (f x) (f x')) : monoidfun (monoidquot R) (monoidquot S) :=
monoidquotuniv (monoidfuncomp f (monoidquotpr S)) (λ x x' r, iscompsetquotpr _ _ _ (H _ _ r)).

(** Quotients by the equivalence relation of being in the same fiber.
    This is exactly X / ker f for a homomorphism f. *)

Definition fiber_binopeqrel {X Y : monoid} (f : monoidfun X Y) : binopeqrel X.
Proof.
  use make_binopeqrel.
  - exact (same_fiber_eqrel f).
  - use make_isbinophrel; intros ? ? ? same;
      refine (monoidfunmul _ _ _ @ _ @ !monoidfunmul _ _ _).
    + (** Prove that it's a congruence for left multiplication *)
      apply maponpaths.
      exact same.
    + (** Prove that it's a congruence for right multiplication *)
      apply (maponpaths (λ z, z * f c)).
      exact same.
Defined.

Definition quotient_by_monoidfun {X Y : monoid} (f : monoidfun X Y) : monoid :=
  monoidquot (fiber_binopeqrel f).

(** * 6. Cosets *)

Section Cosets.
  Context {X : monoid} (Y : submonoid X).

  Definition in_same_left_coset (x1 x2 : X) : UU :=
    ∑ y : Y, x1 * (pr1 y) = x2.

  Definition in_same_right_coset (x1 x2 : X) : UU :=
    ∑ y : Y, (pr1 y) * x1 = x2.
End Cosets.

(** * 7. Direct products *)

Lemma isassocdirprod (X Y : monoid) : isassoc (@op (setwithbinopdirprod X Y)).
Proof.
  simpl. intros xy xy' xy''. simpl. apply pathsdirprod.
  - apply (assocax X).
  - apply (assocax Y).
Qed.

Lemma isunitindirprod (X Y : monoid) :
  isunit (@op (setwithbinopdirprod X Y)) (1 ,, 1).
Proof.
  split.
  - intro xy. induction xy as [ x y ]. simpl. apply pathsdirprod.
    apply (lunax X). apply (lunax Y).
  - intro xy. induction xy as [ x y ]. simpl. apply pathsdirprod.
    apply (runax X). apply (runax Y).
Qed.

Definition ismonoiddirprod (X Y : monoid) : ismonoidop (@op (setwithbinopdirprod X Y)) :=
  isassocdirprod X Y ,, (1 ,, 1) ,, isunitindirprod X Y.

Definition monoiddirprod (X Y : monoid) : monoid.
Proof.
  exists (setwithbinopdirprod X Y).
  apply ismonoiddirprod.
Defined.
