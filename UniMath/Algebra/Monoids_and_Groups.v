(** * Algebra I. Part B.  Monoids, abelian monoids groups, abelian groups. Vladimir Voevodsky. Aug. 2011 - . *)
(** ** Contents
- Standard Algebraic Structures
 - Monoids
  - Basics definitions
  - Univalence for monoids
  - Functions between monoids compatible with structures (homomorphisms)
    and their properties
  - Subobjects
  - Quotient objects
  - Direct products
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
 - Groups
  - Basic definitions
  - Univalence for groups
  - Computation lemmas for groups
  - Relations on groups
  - Subobjects
  - Quotient objects
  - Direct products
 - Abelian groups
  - Basic definitions
  - Univalence for abelian groups
  - Subobjects
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


(** ** Preamble *)


(** Settings *)

(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.MoreFoundations.Subtypes.

(** To upstream files *)


(** ** Standard Algebraic Structures *)


(** *** Monoids *)


(** ****  Basic definitions *)

Definition monoid : UU := total2 (λ X : setwithbinop, ismonoidop (@op X)).

Definition monoidpair :
  ∏ (t : setwithbinop), (λ X : setwithbinop, ismonoidop op) t → ∑ X : setwithbinop, ismonoidop op :=
  tpair (λ X : setwithbinop, ismonoidop (@op X)).

Definition monoidconstr :
  ∏ (t : setwithbinop), (λ X : setwithbinop, ismonoidop op) t → ∑ X : setwithbinop, ismonoidop op :=
  monoidpair.

Definition pr1monoid : monoid -> setwithbinop := @pr1 _ _.
Coercion pr1monoid : monoid >-> setwithbinop.

Definition assocax (X : monoid) : isassoc (@op X) := pr1 (pr2 X).

Definition unel (X : monoid) : X := pr1 (pr2 (pr2 X)).

Definition lunax (X : monoid) : islunit (@op X) (unel X) := pr1 (pr2 (pr2 (pr2 X))).

Definition runax (X : monoid) : isrunit (@op X) (unel X) := pr2 (pr2 (pr2 (pr2 X))).

Notation "x + y" := (op x y) : addmonoid_scope.
Notation "0" := (unel _) : addmonoid_scope.

Delimit Scope addmonoid_scope with addmonoid.

Notation "x * y" := (op x y) : multmonoid_scope.
Notation "1" := (unel _) : multmonoid_scope.

Delimit Scope multmonoid_scope with multmonoid.


(** **** Construction of the trivial monoid consisting of one element given by unit. *)

Definition unitmonoid_ismonoid : ismonoidop (λ x : unitset, λ y : unitset, x).
Proof.
  use mk_ismonoidop.
  - intros x x' x''. use isconnectedunit.
  - use isunitalpair.
    + exact tt.
    + use isunitpair.
      * intros x. use isconnectedunit.
      * intros x. use isconnectedunit.
Qed.

Definition unitmonoid : monoid :=
  monoidpair (setwithbinoppair unitset (λ x : unitset, λ y : unitset, x))
             unitmonoid_ismonoid.


(** **** Functions between monoids compatible with structure (homomorphisms) and their properties *)

Definition ismonoidfun {X Y : monoid} (f : X -> Y) : UU :=
  dirprod (isbinopfun f) (f (unel X) = (unel Y)).

Definition mk_ismonoidfun {X Y : monoid} {f : X -> Y} (H1 : isbinopfun f)
           (H2 : f (unel X) = unel Y) : ismonoidfun f := dirprodpair H1 H2.

Definition ismonoidfunisbinopfun {X Y : monoid} {f : X -> Y} (H : ismonoidfun f) : isbinopfun f :=
  dirprod_pr1 H.

Definition ismonoidfununel {X Y : monoid} {f : X -> Y} (H : ismonoidfun f) : f (unel X) = unel Y :=
  dirprod_pr2 H.

Lemma isapropismonoidfun {X Y : monoid} (f : X -> Y) : isaprop (ismonoidfun f).
Proof.
  intros. apply isofhleveldirprod.
  - apply isapropisbinopfun.
  - apply (setproperty Y).
Defined.

Definition monoidfun (X Y : monoid) : UU := total2 (fun f : X -> Y => ismonoidfun f).

Definition monoidfunconstr {X Y : monoid} {f : X -> Y} (is : ismonoidfun f) : monoidfun X Y :=
  tpair _ f is.

Definition pr1monoidfun (X Y : monoid) : monoidfun X Y -> (X -> Y) := @pr1 _ _.

Definition monoidfuntobinopfun (X Y : monoid) : monoidfun X Y -> binopfun X Y :=
  λ f, binopfunpair (pr1 f) (pr1 (pr2 f)).
Coercion monoidfuntobinopfun : monoidfun >-> binopfun.

Definition monoidfununel {X Y : monoid} (f : monoidfun X Y) : f (unel X) = (unel Y) := pr2 (pr2 f).

Definition monoidfun_paths {X Y : monoid} (f g : monoidfun X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  intros X Y f g e.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropismonoidfun.
Defined.
Opaque monoidfun_paths.

Lemma isasetmonoidfun (X Y : monoid) : isaset (monoidfun X Y).
Proof.
  intros. apply (isasetsubset (pr1monoidfun X Y)).
  - change (isofhlevel 2 (X -> Y)).
    apply impred. intro.
    apply (setproperty Y).
  - refine (isinclpr1 _ _). intro.
    apply isapropismonoidfun.
Defined.

Lemma ismonoidfuncomp {X Y Z : monoid} (f : monoidfun X Y) (g : monoidfun Y Z) :
  ismonoidfun (funcomp (pr1 f) (pr1 g)).
Proof.
  intros. split with (isbinopfuncomp f g).
  unfold funcomp. rewrite (pr2 (pr2 f)).
  apply (pr2 (pr2 g)).
Defined.
Opaque ismonoidfuncomp.

Definition monoidfuncomp {X Y Z : monoid} (f : monoidfun X Y) (g : monoidfun Y Z) :
  monoidfun X Z := monoidfunconstr (ismonoidfuncomp f g).

Lemma monoidfunassoc {X Y Z W : monoid} (f : monoidfun X Y) (g : monoidfun Y Z)
      (h : monoidfun Z W) :
  monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
Proof.
  intros X Y Z W f g h. use monoidfun_paths. use idpath.
Qed.

Lemma unelmonoidfun_ismonoidfun (X Y : monoid) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  intros X Y. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Definition unelmonoidfun (X Y : monoid) : monoidfun X Y :=
  monoidfunconstr (unelmonoidfun_ismonoidfun X Y).

Lemma monoidfuntounit_ismonoidfun (X : monoid) : ismonoidfun (λ x : X, (unel unitmonoid)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use isconnectedunit.
  - use isconnectedunit.
Qed.

Definition monoidfuntounit (X : monoid) : monoidfun X unitmonoid :=
  monoidfunconstr (monoidfuntounit_ismonoidfun X).

Lemma monoidfunfromunit_ismonoidfun (X : monoid) : ismonoidfun (λ x : unitmonoid, (unel X)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition monoidfunfromunit (X : monoid) : monoidfun unitmonoid X :=
  monoidfunconstr (monoidfunfromunit_ismonoidfun X).

Definition monoidmono (X Y : monoid) : UU := total2 (λ f : incl X Y, ismonoidfun f).

Definition monoidmonopair {X Y : monoid} (f : incl X Y) (is : ismonoidfun f) :
  monoidmono X Y := tpair _  f is.

Definition pr1monoidmono (X Y : monoid) : monoidmono X Y -> incl X Y := @pr1 _ _.
Coercion pr1monoidmono : monoidmono >-> incl.

Definition monoidincltomonoidfun (X Y : monoid) :
  monoidmono X Y -> monoidfun X Y := λ f, monoidfunconstr (pr2 f).
Coercion monoidincltomonoidfun : monoidmono >-> monoidfun.

Definition monoidmonotobinopmono (X Y : monoid) : monoidmono X Y -> binopmono X Y :=
  λ f, binopmonopair (pr1 f) (pr1 (pr2 f)).
Coercion monoidmonotobinopmono : monoidmono >-> binopmono.

Definition monoidmonocomp {X Y Z : monoid}
           (f : monoidmono X Y) (g : monoidmono Y Z) : monoidmono X Z :=
  monoidmonopair (inclcomp (pr1 f) (pr1 g)) (ismonoidfuncomp f g).

Definition monoidiso (X Y : monoid) : UU := total2 (λ f : X ≃ Y, ismonoidfun f).

Definition monoidisopair {X Y : monoid} (f : X ≃ Y) (is : ismonoidfun f) :
  monoidiso X Y := tpair _  f is.

Definition pr1monoidiso (X Y : monoid) : monoidiso X Y -> X ≃ Y := @pr1 _ _.
Coercion pr1monoidiso : monoidiso >-> weq.

Definition monoidisotomonoidmono (X Y : monoid) : monoidiso X Y -> monoidmono X Y :=
  λ f, monoidmonopair (pr1 f) (pr2 f).
Coercion monoidisotomonoidmono : monoidiso >-> monoidmono.

Definition monoidisotobinopiso (X Y : monoid) : monoidiso X Y -> binopiso X Y :=
  λ f, binopisopair (pr1 f) (pr1 (pr2 f)).
Coercion monoidisotobinopiso : monoidiso >-> binopiso.

Definition monoidiso_paths {X Y : monoid} (f g : monoidiso X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  intros X Y f g e.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropismonoidfun.
Defined.
Opaque monoidiso_paths.

Lemma ismonoidfuninvmap {X Y : monoid} (f : monoidiso X Y) :
  ismonoidfun (invmap (pr1 f)).
Proof.
  intros. split with (isbinopfuninvmap f).
  apply (invmaponpathsweq (pr1 f)).
  rewrite (homotweqinvweq (pr1 f)).
  apply (pathsinv0 (pr2 (pr2 f))).
Defined.
Opaque ismonoidfuninvmap.

Definition invmonoidiso {X Y : monoid} (f : monoidiso X Y) : monoidiso Y X :=
  monoidisopair (invweq (pr1 f)) (ismonoidfuninvmap f).

Definition idmonoidiso (X : monoid) : monoidiso X X.
Proof.
  intros X.
  use monoidisopair.
  - exact (idweq X).
  - use dirprodpair.
    + intros x x'. use idpath.
    + use idpath.
Defined.

Lemma monoidfunidleft {A B : monoid} (f : monoidfun A B) : monoidfuncomp (idmonoidiso A) f = f.
Proof.
  intros A B f. use monoidfun_paths. use idpath.
Qed.

Lemma monoidfunidright {A B : monoid} (f : monoidfun A B) : monoidfuncomp f (idmonoidiso B) = f.
Proof.
  intros A B f. use monoidfun_paths. use idpath.
Qed.


(** **** (X = Y) ≃ (monoidiso X Y)
   The idea here is to use the following composition

                           (X = Y) ≃ (X ╝ Y)
                                   ≃ (monoidiso' X Y)
                                   ≃ (monoidiso X Y).

   The reason why we use monoidiso' is that then we can use univalence for sets with binops,
   [setwithbinop_univalence]. See [monoid_univalence_weq2].
 *)

Local Definition monoidiso' (X Y : monoid) : UU :=
  ∑ g : (∑ f : X ≃ Y, isbinopfun f), (pr1 g) (unel X) = unel Y.

Definition monoid_univalence_weq1 (X Y : monoid) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition monoid_univalence_weq2 (X Y : monoid) : (X ╝ Y) ≃ (monoidiso' X Y).
Proof.
  intros X Y.
  use weqbandf.
  - exact (setwithbinop_univalence X Y).
  - intros e. cbn. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    cbn. induction e. use weqimplimpl.
    + intros i. use proofirrelevance. use isapropismonoidop.
    + intros i. induction i. use idpath.
    + use setproperty.
    + use isapropifcontr. exact (@isapropismonoidop X (pr2 X) Xop Yop).
Defined.
Opaque monoid_univalence_weq2.

Definition monoid_univalence_weq3 (X Y : monoid) : (monoidiso' X Y) ≃ (monoidiso X Y) :=
  weqtotal2asstor (λ w : X ≃ Y, isbinopfun w)
                  (λ y : (∑ w : weq X Y, isbinopfun w), (pr1 y) (unel X) = unel Y).

Definition monoid_univalence_map (X Y : monoid) : X = Y -> monoidiso X Y.
Proof.
  intros X Y e. induction e. exact (idmonoidiso X).
Defined.

Lemma monoid_univalence_isweq (X Y : monoid) :
  isweq (monoid_univalence_map X Y).
Proof.
  intros X Y.
  use isweqhomot.
  - exact (weqcomp (monoid_univalence_weq1 X Y)
                   (weqcomp (monoid_univalence_weq2 X Y) (monoid_univalence_weq3 X Y))).
  - intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque monoid_univalence_isweq.

Definition monoid_univalence (X Y : monoid) : (X = Y) ≃ (monoidiso X Y).
Proof.
  intros X Y.
  use weqpair.
  - exact (monoid_univalence_map X Y).
  - exact (monoid_univalence_isweq X Y).
Defined.
Opaque monoid_univalence.


(** **** Subobjects *)

Definition issubmonoid {X : monoid} (A : hsubtype X) : UU :=
  dirprod (issubsetwithbinop (@op X) A) (A (unel X)).

Definition issubmonoidpair {X : monoid} {A : hsubtype X} (H1 : issubsetwithbinop (@op X) A)
           (H2 : A (unel X)) : issubmonoid A := dirprodpair H1 H2.

Lemma isapropissubmonoid {X : monoid} (A : hsubtype X) :
  isaprop (issubmonoid A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubsetwithbinop.
  - apply (pr2 (A (unel X))).
Defined.

Definition submonoid {X : monoid} : UU := total2 (λ A : hsubtype X, issubmonoid A).

Definition submonoidpair {X : monoid} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubmonoid A) t → ∑ A : hsubtype X, issubmonoid A :=
  tpair (λ A : hsubtype X, issubmonoid A).

Definition submonoidconstr {X : monoid} := @submonoidpair X.

Definition pr1submonoid (X : monoid) : @submonoid X -> hsubtype X := @pr1 _ _.

Definition totalsubmonoid (X : monoid) : @submonoid X.
Proof.
  intro. split with (λ x : _, htrue). split.
  - intros x x'. apply tt.
  - apply tt.
Defined.

Definition submonoidtosubsetswithbinop (X : monoid) : @submonoid X -> @subsetswithbinop X :=
  λ A : _, subsetswithbinoppair (pr1 A) (pr1 (pr2 A)).
Coercion submonoidtosubsetswithbinop : submonoid >-> subsetswithbinop.

Lemma ismonoidcarrier {X : monoid} (A : @submonoid X) : ismonoidop (@op A).
Proof.
  intros. split.
  - intros a a' a''. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (assocax X).
  - split with (carrierpair _ (unel X) (pr2 (pr2 A))).
    split.
    + simpl. intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply (lunax X).
    + intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply (runax X).
Defined.

Definition carrierofsubmonoid {X : monoid} (A : @submonoid X) : monoid.
Proof. intros. split with A. apply ismonoidcarrier. Defined.
Coercion carrierofsubmonoid : submonoid >-> monoid.

Lemma intersection_submonoid :
  forall {X : monoid} {I : UU} (S : I -> hsubtype X)
         (each_is_submonoid : ∏ i : I, issubmonoid (S i)),
    issubmonoid (subtype_intersection S).
Proof.
  intros.
  use issubmonoidpair.
  + intros g h i.
    pose (is_subgr := pr1 (each_is_submonoid i)).
    exact (is_subgr (pr1 g,, (pr2 g) i) (pr1 h,, (pr2 h) i)).
  + exact (λ i, pr2 (each_is_submonoid i)).
Qed.

(** **** Quotient objects *)

Lemma isassocquot {X : monoid} (R : @binopeqrel X) : isassoc (@op (setwithbinopquot R)).
Proof.
  intros. intros a b c.
  apply (setquotuniv3prop
           R (λ x x' x'' : setwithbinopquot R,
                hProppair _ (setproperty (setwithbinopquot R) (op (op x x') x'')
                                         (op x (op x' x''))))).
  intros x x' x''.
  apply (maponpaths (setquotpr R) (assocax X x x' x'')).
Defined.
Opaque isassocquot.

Lemma isunitquot {X : monoid} (R : @binopeqrel X) :
  isunit (@op (setwithbinopquot R)) (setquotpr R (pr1 (pr2 (pr2 X)))).
Proof.
  intros.
  set (qun := setquotpr R (pr1 (pr2 (pr2 X)))).
  set (qsetwithop := setwithbinopquot R).
  split.
  - intro x.
    apply (setquotunivprop R (λ x, @eqset qsetwithop ((@op qsetwithop) qun x) x)).
    simpl. intro x0.
    apply (maponpaths (setquotpr R) (lunax X x0)).
  - intro x.
    apply (setquotunivprop R (λ x, @eqset qsetwithop ((@op qsetwithop) x qun) x)).
    simpl. intro x0. apply (maponpaths (setquotpr R) (runax X x0)).
Defined.
Opaque isunitquot.

Definition ismonoidquot {X : monoid} (R : @binopeqrel X) : ismonoidop (@op (setwithbinopquot R)) :=
  tpair _ (isassocquot R) (tpair _ (setquotpr R (pr1 (pr2 (pr2 X)))) (isunitquot R)).

Definition monoidquot {X : monoid} (R : @binopeqrel X) : monoid.
Proof. intros. split with (setwithbinopquot R). apply ismonoidquot. Defined.


(** **** Direct products *)

Lemma isassocdirprod (X Y : monoid) : isassoc (@op (setwithbinopdirprod X Y)).
Proof.
  intros. simpl. intros xy xy' xy''. simpl. apply pathsdirprod.
  - apply (assocax X).
  - apply (assocax Y).
Defined.
Opaque isassocdirprod.

Lemma isunitindirprod (X Y : monoid) :
  isunit (@op (setwithbinopdirprod X Y)) (dirprodpair (unel X) (unel Y)).
Proof.
  split.
  - intro xy. destruct xy as [ x y ]. simpl. apply pathsdirprod.
    apply (lunax X). apply (lunax Y).
  - intro xy. destruct xy as [ x y ]. simpl. apply pathsdirprod.
    apply (runax X). apply (runax Y).
Defined.
Opaque isunitindirprod.

Definition ismonoiddirprod (X Y : monoid) : ismonoidop (@op (setwithbinopdirprod X Y)) :=
  tpair _ (isassocdirprod X Y) (tpair _ (dirprodpair (unel X) (unel Y)) (isunitindirprod X Y)).

Definition monoiddirprod (X Y : monoid) : monoid.
Proof.
  intros. split with (setwithbinopdirprod X Y).
  apply ismonoiddirprod.
Defined.


(** *** Abelian (commutative) monoids *)

(** **** Basic definitions *)

Definition abmonoid : UU := total2 (λ X : setwithbinop, isabmonoidop (@op X)).

Definition abmonoidpair :
  ∏ (t : setwithbinop), (λ X : setwithbinop, isabmonoidop op) t →
                        ∑ X : setwithbinop, isabmonoidop op :=
  tpair (λ X : setwithbinop, isabmonoidop (@op X)).

Definition abmonoidconstr :
  ∏ (t : setwithbinop), (λ X : setwithbinop, isabmonoidop op) t →
                        ∑ X : setwithbinop, isabmonoidop op := abmonoidpair.

Definition abmonoidtomonoid : abmonoid -> monoid :=
  λ X : _, monoidpair (pr1 X) (pr1 (pr2 X)).
Coercion abmonoidtomonoid : abmonoid >-> monoid.

Definition commax (X : abmonoid) : iscomm (@op X) := pr2 (pr2 X).

Definition abmonoidrer (X : abmonoid) (a b c d : X) :
  paths (op (op a b) (op c d)) (op (op a c) (op b d)) := abmonoidoprer (pr2 X) a b c d.


(** **** Construction of the trivial abmonoid consisting of one element given by unit. *)

Definition unitabmonoid_isabmonoid : isabmonoidop (@op unitmonoid).
Proof.
  use mk_isabmonoidop.
  - exact unitmonoid_ismonoid.
  - intros x x'. use isconnectedunit.
Qed.

Definition unitabmonoid : abmonoid := abmonoidpair unitmonoid unitabmonoid_isabmonoid.

Lemma abmonoidfuntounit_ismonoidfun (X : abmonoid) : ismonoidfun (λ x : X, (unel unitabmonoid)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use isconnectedunit.
  - use isconnectedunit.
Qed.

Definition abmonoidfuntounit (X : abmonoid) : monoidfun X unitabmonoid :=
  monoidfunconstr (abmonoidfuntounit_ismonoidfun X).

Lemma abmonoidfunfromunit_ismonoidfun (X : abmonoid) : ismonoidfun (λ x : unitabmonoid, (unel X)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition abmonoidfunfromunit (X : abmonoid) : monoidfun unitabmonoid X :=
  monoidfunconstr (abmonoidfunfromunit_ismonoidfun X).

Lemma unelabmonoidfun_ismonoidfun (X Y : abmonoid) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  intros X Y. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Definition unelabmonoidfun (X Y : abmonoid) : monoidfun X Y :=
  monoidfunconstr (unelabmonoidfun_ismonoidfun X Y).


(** **** Abelian monoid structure on homsets
    If f g : X -> Y are morphisms of abelian monoids, then we define f + g to be the morphism
    (f + g)(x) = f(x) + g(x).
 *)

Lemma abmonoidshombinop_ismonoidfun {X Y : abmonoid} (f g : monoidfun X Y) :
  @ismonoidfun X Y (λ x : pr1 X, (pr1 f x * pr1 g x)%multmonoid).
Proof.
  intros X Y f g.
  use mk_ismonoidfun.
  - use mk_isbinopfun.
    intros x x'. cbn. rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
    rewrite (assocax Y). rewrite (assocax Y). use maponpaths.
    rewrite <- (assocax Y). rewrite <- (assocax Y).
    use (maponpaths (λ y : Y, (y * (pr1 g x'))%multmonoid)).
    use (commax Y).
  - use (pathscomp0 (maponpaths (λ h : Y, (pr1 f (unel X) * h)%multmonoid)
                                (monoidfununel g))).
    rewrite runax. exact (monoidfununel f).
Qed.

Definition abmonoidshombinop {X Y : abmonoid} : binop (monoidfun X Y) :=
  (λ f g, monoidfunconstr (abmonoidshombinop_ismonoidfun f g)).

Lemma abmonoidsbinop_runax {X Y : abmonoid} (f : monoidfun X Y) :
  abmonoidshombinop f (unelmonoidfun X Y) = f.
Proof.
  intros X Y f. use monoidfun_paths. use funextfun. intros x. use (runax Y).
Qed.

Lemma abmonoidsbinop_lunax {X Y : abmonoid} (f : monoidfun X Y) :
  abmonoidshombinop (unelmonoidfun X Y) f = f.
Proof.
  intros X Y f. use monoidfun_paths. use funextfun. intros x. use (lunax Y).
Qed.

Lemma abmonoidshombinop_assoc {X Y : abmonoid} (f g h : monoidfun X Y) :
  abmonoidshombinop (abmonoidshombinop f g) h = abmonoidshombinop f (abmonoidshombinop g h).
Proof.
  intros X Y f g h. use monoidfun_paths. use funextfun. intros x. use assocax.
Qed.

Lemma abmonoidshombinop_comm {X Y : abmonoid} (f g : monoidfun X Y) :
  abmonoidshombinop f g = abmonoidshombinop g f.
Proof.
  intros X Y f g. use monoidfun_paths. use funextfun. intros x. use (commax Y).
Qed.

Lemma abmonoidshomabmonoid_ismonoidop (X Y : abmonoid) :
  @ismonoidop (hSetpair (monoidfun X Y) (isasetmonoidfun X Y))
              (λ f g : monoidfun X Y, abmonoidshombinop f g).
Proof.
  intros X Y.
  use mk_ismonoidop.
  - intros f g h. exact (abmonoidshombinop_assoc f g h).
  - use isunitalpair.
    + exact (unelmonoidfun X Y).
    + use isunitpair.
      * intros f. exact (abmonoidsbinop_lunax f).
      * intros f. exact (abmonoidsbinop_runax f).
Defined.

Lemma abmonoidshomabmonoid_isabmonoid (X Y : abmonoid) :
  @isabmonoidop (hSetpair (monoidfun X Y) (isasetmonoidfun X Y))
                (λ f g : monoidfun X Y, abmonoidshombinop f g).
Proof.
  intros X Y.
  use mk_isabmonoidop.
  - exact (abmonoidshomabmonoid_ismonoidop X Y).
  - intros f g. exact (abmonoidshombinop_comm f g).
Defined.

Definition abmonoidshomabmonoid (X Y : abmonoid) : abmonoid.
Proof.
  intros X Y.
  - use abmonoidpair.
    + use setwithbinoppair.
      * use hSetpair.
        -- exact (monoidfun X Y).
        -- exact (isasetmonoidfun X Y).
      * intros f g. exact (abmonoidshombinop f g).
    + exact (abmonoidshomabmonoid_isabmonoid X Y).
Defined.


(** **** (X = Y) ≃ (monoidiso X Y)
    We use the following composition

                      (X = Y) ≃ ((mk_abmonoid' X) = (mk_abmonoid' Y))
                              ≃ ((pr1 (mk_abmonoid' X)) = (pr1 (mk_abmonoid' Y)))
                              ≃ (monoidiso X Y)

    where the third weak equivalence is given by univalence for monoids, [monoid_univalence].
*)

Local Definition abmonoid' : UU := ∑ m : monoid, iscomm (@op m).

Local Definition mk_abmonoid' (X : abmonoid) : abmonoid' :=
  tpair _ (tpair _ (pr1 X) (dirprod_pr1 (pr2 X))) (dirprod_pr2 (pr2 X)).

Definition abmonoid_univalence_weq1 : abmonoid ≃ abmonoid' :=
  weqtotal2asstol (λ X : setwithbinop, ismonoidop (@op X))
                  (fun y : (∑ X : setwithbinop, ismonoidop op) => iscomm (@op (pr1 y))).

Definition abmonoid_univalence_weq1' (X Y : abmonoid) :
  (X = Y) ≃ ((mk_abmonoid' X) = (mk_abmonoid' Y)) :=
  weqpair _ (@isweqmaponpaths abmonoid abmonoid' abmonoid_univalence_weq1 X Y).

Definition abmonoid_univalence_weq2 (X Y : abmonoid) :
  ((mk_abmonoid' X) = (mk_abmonoid' Y)) ≃ ((pr1 (mk_abmonoid' X)) = (pr1 (mk_abmonoid' Y))).
Proof.
  intros X Y.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque abmonoid_univalence_weq2.

Definition abmonoid_univalence_weq3 (X Y : abmonoid) :
  ((pr1 (mk_abmonoid' X)) = (pr1 (mk_abmonoid' Y))) ≃ (monoidiso X Y) :=
  monoid_univalence (pr1 (mk_abmonoid' X)) (pr1 (mk_abmonoid' Y)).

Definition abmonoid_univalence_map (X Y : abmonoid) : (X = Y) -> (monoidiso X Y).
Proof.
  intros X Y e. induction e. exact (idmonoidiso X).
Defined.

Lemma abmonoid_univalence_isweq (X Y : abmonoid) : isweq (abmonoid_univalence_map X Y).
Proof.
  intros X Y.
  use isweqhomot.
  - exact (weqcomp (abmonoid_univalence_weq1' X Y)
                   (weqcomp (abmonoid_univalence_weq2 X Y) (abmonoid_univalence_weq3 X Y))).
  - intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque abmonoid_univalence_isweq.

Definition abmonoid_univalence (X Y : abmonoid) : (X = Y) ≃ (monoidiso X Y).
Proof.
  intros X Y.
  use weqpair.
  - exact (abmonoid_univalence_map X Y).
  - exact (abmonoid_univalence_isweq X Y).
Defined.
Opaque abmonoid_univalence.


(** **** Subobjects *)

Definition subabmonoid {X : abmonoid} := @submonoid X.
Identity Coercion id_subabmonoid : subabmonoid >-> submonoid.

Lemma iscommcarrier {X : abmonoid} (A : @submonoid X) : iscomm (@op A).
Proof.
  intros. intros a a'.
  apply (invmaponpathsincl _ (isinclpr1carrier A)).
  simpl. apply (pr2 (pr2 X)).
Defined.
Opaque iscommcarrier.

Definition isabmonoidcarrier {X : abmonoid} (A : @submonoid X) :
  isabmonoidop (@op A) := dirprodpair (ismonoidcarrier A) (iscommcarrier A).

Definition carrierofsubabmonoid {X : abmonoid} (A : @subabmonoid X) : abmonoid.
Proof.
  intros. unfold subabmonoid in A. split with A. apply isabmonoidcarrier.
Defined.
Coercion carrierofsubabmonoid : subabmonoid >-> abmonoid.


(** **** Quotient objects *)

Lemma iscommquot {X : abmonoid} (R : @binopeqrel X) : iscomm (@op (setwithbinopquot R)).
Proof.
  intros.
  set (X0 := setwithbinopquot R).
  intros x x'.
  apply (setquotuniv2prop R (λ x x' : X0, hProppair _ (setproperty X0 (op x x') (op x' x)))).
  intros x0 x0'.
  apply (maponpaths (setquotpr R) ((commax X) x0 x0')).
Defined.
Opaque iscommquot.

Definition isabmonoidquot {X : abmonoid} (R : @binopeqrel X) :
  isabmonoidop (@op (setwithbinopquot R)) := dirprodpair (ismonoidquot R) (iscommquot R).

Definition abmonoidquot {X : abmonoid} (R : @binopeqrel X) : abmonoid.
Proof. intros. split with (setwithbinopquot R). apply isabmonoidquot. Defined.


(** **** Direct products *)

Lemma iscommdirprod (X Y : abmonoid) : iscomm (@op (setwithbinopdirprod X Y)).
Proof.
  intros. intros xy xy'.
  destruct xy as [ x y ]. destruct xy' as [ x' y' ]. simpl.
  apply pathsdirprod.
  - apply (commax X).
  - apply (commax Y).
Defined.
Opaque iscommdirprod.

Definition isabmonoiddirprod (X Y : abmonoid) : isabmonoidop (@op (setwithbinopdirprod X Y)) :=
  dirprodpair (ismonoiddirprod X Y) (iscommdirprod X Y).

Definition abmonoiddirprod (X Y : abmonoid) : abmonoid.
Proof. intros. split with (setwithbinopdirprod X Y). apply isabmonoiddirprod. Defined.


(** **** Monoid of fractions of an abelian monoid

Note : the following construction uses onbly associativity and commutativity
of the [abmonoid] operations but does not use the unit element. *)

Open Scope addmonoid_scope.

Definition abmonoidfracopint (X : abmonoid) (A : @submonoid X) :
  binop (X × A) := @op (setwithbinopdirprod X A).

Definition hrelabmonoidfrac (X : abmonoid) (A : @submonoid X) : hrel (setwithbinopdirprod X A) :=
  λ xa yb : dirprod X A, hexists (λ a0 : A, paths (((pr1 xa) + (pr1 (pr2 yb))) + (pr1 a0))
                                                    (((pr1 yb) + (pr1 (pr2 xa)) + (pr1 a0)))).

Lemma iseqrelabmonoidfrac (X : abmonoid) (A : @submonoid X) : iseqrel (hrelabmonoidfrac X A).
Proof.
  intros.
  set (assoc := assocax X). set (comm := commax X).
  set (R := hrelabmonoidfrac X A).
  assert (symm : issymm R).
  {
    intros xa yb. unfold R. simpl. apply hinhfun. intro eq1.
    destruct eq1 as [ x1 eq1 ]. split with x1. destruct x1 as [ x1 isx1 ].
    simpl. apply (pathsinv0 eq1).
  }
  assert (trans : istrans R).
  {
    unfold istrans. intros ab cd ef. simpl. apply hinhfun2.
    destruct ab as [ a b ]. destruct cd as [ c d ]. destruct ef as [ e f ].
    destruct b as [ b isb ]. destruct d as [ d isd ].  destruct f as [ f isf ].
    intros eq1 eq2. destruct eq1 as [ x1 eq1 ]. destruct eq2 as [ x2 eq2 ].
    simpl in *. split with (@op A (tpair _ d isd) (@op A x1 x2)).
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
  }
  assert (refl : isrefl R).
  {
    intro xa. simpl. apply hinhpr. split with (pr2 xa). apply idpath.
  }
  apply (iseqrelconstr trans refl symm).
Defined.
Opaque iseqrelabmonoidfrac.

Definition eqrelabmonoidfrac (X : abmonoid) (A : @submonoid X) : eqrel (setwithbinopdirprod X A) :=
  eqrelpair (hrelabmonoidfrac X A) (iseqrelabmonoidfrac X A).

Lemma isbinophrelabmonoidfrac (X : abmonoid) (A : @submonoid X) :
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
Defined.
Opaque isbinophrelabmonoidfrac.

Definition abmonoidfracop (X : abmonoid) (A : @submonoid X) :
  binop (setquot (hrelabmonoidfrac X A)) :=
  setquotfun2 (hrelabmonoidfrac X A) (eqrelabmonoidfrac X A) (abmonoidfracopint X A)
              ((iscompbinoptransrel _ (eqreltrans _) (isbinophrelabmonoidfrac X A))).

Definition binopeqrelabmonoidfrac (X : abmonoid) (A : @subabmonoid X) :
  @binopeqrel (abmonoiddirprod X A) :=
  @binopeqrelpair (setwithbinopdirprod X A) (eqrelabmonoidfrac X A) (isbinophrelabmonoidfrac X A).

Definition abmonoidfrac (X : abmonoid) (A : @submonoid X) : abmonoid :=
  abmonoidquot (binopeqrelabmonoidfrac X A).

Definition prabmonoidfrac (X : abmonoid) (A : @submonoid X) : X -> A -> abmonoidfrac X A :=
  fun (x : X) (a : A) => setquotpr (eqrelabmonoidfrac X A) (dirprodpair x a).

(* ??? could the use of [issubabmonoid] in [binopeqrelabmonoidfrac] and
 [submonoid] in [abmonoidfrac] lead to complications for the unification
 machinery? See also [abmonoidfracisbinoprelint] below. *)

Lemma invertibilityinabmonoidfrac (X : abmonoid) (A : @submonoid X) :
  ∏ a a' : A, isinvertible (@op (abmonoidfrac X A)) (prabmonoidfrac X A (pr1 a) a').
Proof.
  intros. set (R := eqrelabmonoidfrac X A). unfold isinvertible.
  assert (isl : islinvertible (@op (abmonoidfrac X A))
                              (prabmonoidfrac X A (pr1 a) a')).
  {
    unfold islinvertible.
    set (f := λ x0 : abmonoidfrac X A, prabmonoidfrac X A (pr1 a) a' + x0).
    set (g := λ x0 : abmonoidfrac X A, prabmonoidfrac X A (pr1 a') a + x0).
    assert (egf : ∏ x0 : _, paths (g (f x0)) x0).
    {
      apply (setquotunivprop R (λ x0 : abmonoidfrac X A, eqset (g (f x0)) x0)).
      intro xb. simpl.
      apply (iscompsetquotpr
               R (@dirprodpair X A ((pr1 a') + ((pr1 a) + (pr1 xb)))
                               ((@op A) a ((@op A) a' (pr2 xb))))).
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
    assert (efg : ∏ x0 : _, paths (f (g x0)) x0).
    {
      apply (setquotunivprop R (λ x0 : abmonoidfrac X A, eqset (f (g x0)) x0)).
      intro xb. simpl.
      apply (iscompsetquotpr
               R (@dirprodpair X A ((pr1 a) + ((pr1 a') + (pr1 xb)))
                               ((@op A) a' ((@op A) a (pr2 xb))))).
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
    apply (gradth _ _ egf efg).
  }
  apply (dirprodpair isl (weqlinvertiblerinvertible (@op (abmonoidfrac X A))
                                                    (commax (abmonoidfrac X A))
                                                    (prabmonoidfrac X A (pr1 a) a') isl)).
Defined.


(** **** Canonical homomorphism to the monoid of fractions *)

Definition toabmonoidfrac (X : abmonoid) (A : @submonoid X) (x : X) : abmonoidfrac X A :=
  setquotpr _ (dirprodpair x (unel A)).

Lemma isbinopfuntoabmonoidfrac (X : abmonoid) (A : @submonoid X) : isbinopfun (toabmonoidfrac X A).
Proof.
  intros. unfold isbinopfun. intros x1 x2.
  change (paths (setquotpr _ (dirprodpair (x1 + x2) (@unel A)))
                (setquotpr (eqrelabmonoidfrac X A) (dirprodpair (x1 + x2) ((unel A) + (unel A))))).
  apply (maponpaths (setquotpr _)).
  apply (@pathsdirprod X A).
  apply idpath.
  apply (pathsinv0 (lunax A 0)).
Defined.

Lemma isunitalfuntoabmonoidfrac (X : abmonoid) (A : @submonoid X) :
  paths (toabmonoidfrac X A (unel X)) (unel (abmonoidfrac X A)).
Proof. intros. apply idpath. Defined.

Definition ismonoidfuntoabmonoidfrac (X : abmonoid) (A : @submonoid X) :
  ismonoidfun (toabmonoidfrac X A) :=
  dirprodpair (isbinopfuntoabmonoidfrac X A) (isunitalfuntoabmonoidfrac X A).


(** **** Abelian monoid of fractions in the case when elements of the localziation submonoid are cancelable *)

Definition hrel0abmonoidfrac (X : abmonoid) (A : @submonoid X) : hrel (X × A) :=
  λ xa yb : setdirprod X A, eqset ((pr1 xa) + (pr1 (pr2 yb))) ((pr1 yb) + (pr1 (pr2 xa))).

Lemma weqhrelhrel0abmonoidfrac (X : abmonoid) (A : @submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a))
      (xa xa' : dirprod X A) : (eqrelabmonoidfrac X A xa xa') ≃ (hrel0abmonoidfrac X A xa xa').
Proof.
  intros. unfold eqrelabmonoidfrac. unfold hrelabmonoidfrac. simpl.
  apply weqimplimpl.
  apply (@hinhuniv _ (eqset (pr1 xa + pr1 (pr2 xa')) (pr1 xa' + pr1 (pr2 xa)))).
  intro ae. destruct ae as [ a eq ].
  apply (invmaponpathsincl _ (iscanc a) _ _ eq).
  intro eq. apply hinhpr. split with (unel A). rewrite (runax X).
  rewrite (runax X). apply eq. apply (isapropishinh _).
  apply (setproperty X).
Defined.

Lemma isinclprabmonoidfrac (X : abmonoid) (A : @submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) :
  ∏ a' : A, isincl (λ x, prabmonoidfrac X A x a').
Proof.
  intros. apply isinclbetweensets.
  - apply (setproperty X).
  - apply (setproperty (abmonoidfrac X A)).
  - intros x x'. intro e.
    set (e' := invweq (weqpathsinsetquot (eqrelabmonoidfrac X A) (dirprodpair x a')
                                         (dirprodpair x' a')) e).
    set (e'' := weqhrelhrel0abmonoidfrac X A iscanc (dirprodpair _ _) (dirprodpair _ _) e').
    simpl in e''.
    apply (invmaponpathsincl _ (iscanc a')).
    apply e''.
Defined.

Definition isincltoabmonoidfrac (X : abmonoid) (A : @submonoid X)
           (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) :
  isincl (toabmonoidfrac X A) := isinclprabmonoidfrac X A iscanc (unel A).

Lemma isdeceqabmonoidfrac (X : abmonoid) (A : @submonoid X)
      (iscanc : ∏ a : A, isrcancelable (@op X) (pr1carrier _ a)) (is : isdeceq X) :
  isdeceq (abmonoidfrac X A).
Proof.
  intros. apply (isdeceqsetquot (eqrelabmonoidfrac X A)). intros xa xa'.
  apply (isdecpropweqb (weqhrelhrel0abmonoidfrac X A iscanc xa xa')).
  apply isdecpropif. unfold isaprop. simpl.
  set (int := setproperty X (pr1 xa + pr1 (pr2 xa')) (pr1 xa' + pr1 (pr2 xa))).
  simpl in int. apply int. unfold hrel0abmonoidfrac. unfold eqset.
  simpl. apply (is _ _).
Defined.


(** **** Relations on the abelian monoid of fractions *)

Definition abmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) (L : hrel X) :
  hrel (setwithbinopdirprod X A) :=
  λ xa yb, hexists (λ c0 : A, L (((pr1 xa) + (pr1 (pr2 yb))) + (pr1 c0))
                                  (((pr1 yb) + (pr1 (pr2 xa))) + (pr1 c0))).

Lemma iscomprelabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) : iscomprelrel (eqrelabmonoidfrac X A) (abmonoidfracrelint X A L).
Proof.
  intros. set (assoc := (assocax X) : isassoc (@op X)).
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
    change (paths (x + a' + c1) (x' + a + c1)) in e.
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
    change (paths (y + b' + c1) (y' + b + c1)) in e.
    rewrite (rer y' _ _ c0).
    destruct (assoc y' b c1). destruct e.
    rewrite (assoc y b' c1).  rewrite (rer y _ _ c0).
    rewrite (assoc b c1 c0). rewrite (rer _ b' b _).
    rewrite (assoc b' c1 c0). rewrite (comm b' _).
    rewrite (comm c1 _). rewrite (assoc  c0 c1 b').
    destruct (assoc (x + b) c0 (@op X c1 b')).
    destruct (assoc (y + a) c0 (@op X c1 b')).
    apply ((pr2 is) _ _ _ (pr2 (@op A c1a (pr2 yb'))) l).
Defined.
Opaque iscomprelabmonoidfracrelint.

Definition abmonoidfracrel (X : abmonoid) (A : @submonoid X) {L : hrel X}
           (is : ispartbinophrel A L) := quotrel (iscomprelabmonoidfracrelint X A is).

Lemma istransabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
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
  assert (e : paths (x2 + a1 + c1 + (c2 + a3))
                    (x2 + a3 + c2 + (a1 + c1))).
  {
    rewrite (assoc (x2 + a1) c1 _). rewrite (assoc (x2 + a3) c2 _).
    rewrite (assoc x2 a1 _). rewrite (assoc x2 a3 _).
    destruct (assoc a1 c1 (c2 + a3)). destruct (assoc a3 c2 (a1 + c1)).
    destruct (comm (c2 + a3) (a1 + c1)).
    rewrite (comm a3 c2). apply idpath.
  }
  destruct e. apply (isl _ _ _ ll1 ll2).
Defined.
Opaque istransabmonoidfracrelint.

Lemma istransabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istrans L) : istrans (abmonoidfracrel X A is).
Proof.
  intros. apply istransquotrel. apply istransabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma issymmabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : issymm L) : issymm (abmonoidfracrelint X A L).
Proof.
  intros. intros xa1 xa2. unfold abmonoidfracrelint. simpl.
  apply hinhfun. intros t2l1.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  split with (c1a). apply (isl _ _ l1).
Defined.
Opaque issymmabmonoidfracrelint.

Lemma issymmabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : issymm L) : issymm (abmonoidfracrel X A is).
Proof.
  intros. apply issymmquotrel. apply issymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isreflabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isrefl L) : isrefl (abmonoidfracrelint X A L).
Proof.
  intros. intro xa. unfold abmonoidfracrelint. simpl. apply hinhpr.
  split with (unel A). apply (isl _).
Defined.

Lemma isreflabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isrefl L) : isrefl (abmonoidfracrel X A is).
Proof.
  intros. apply isreflquotrel. apply isreflabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma ispoabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : ispreorder L) : ispreorder (abmonoidfracrelint X A L).
Proof.
  intros. split with (istransabmonoidfracrelint X A is (pr1 isl)).
  apply (isreflabmonoidfracrelint X A is (pr2 isl)).
Defined.

Lemma ispoabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : ispreorder L) : ispreorder (abmonoidfracrel X A is).
Proof.
  intros. apply ispoquotrel. apply ispoabmonoidfracrelint.
  apply is. apply isl.
Defined.

Lemma iseqrelabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iseqrel L) : iseqrel (abmonoidfracrelint X A L).
Proof.
  intros. split with (ispoabmonoidfracrelint X A is (pr1 isl)).
  apply (issymmabmonoidfracrelint X A is (pr2 isl)).
Defined.

Lemma iseqrelabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iseqrel L) : iseqrel (abmonoidfracrel X A is).
Proof.
  intros. apply iseqrelquotrel. apply iseqrelabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isirreflabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isirrefl L) : isirrefl (abmonoidfracrelint X A L).
Proof.
  intros. unfold isirrefl. intro xa. unfold abmonoidfracrelint. simpl.
  unfold neg. apply (@hinhuniv _ (hProppair _ isapropempty)).
  intro t2. apply (isl _ (pr2 t2)).
Defined.

Lemma isirreflabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isirrefl L) : isirrefl (abmonoidfracrel X A is).
Proof.
  intros. apply isirreflquotrel. apply isirreflabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isasymmabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isasymm L) : isasymm (abmonoidfracrelint X A L).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)).
  unfold isassoc in assoc. set (comm := commax X).
  unfold iscomm in comm. unfold isasymm.
  intros xa1 xa2. unfold abmonoidfracrelint. simpl.
  apply (@hinhuniv2 _ _ (hProppair _ isapropempty)).
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
Defined.
Opaque isasymmabmonoidfracrelint.

Lemma isasymmabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isasymm L) : isasymm (abmonoidfracrel X A is).
Proof.
  intros. apply isasymmquotrel. apply isasymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iscoasymmabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
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
Defined.
Opaque isasymmabmonoidfracrelint.

Lemma iscoasymmabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscoasymm L) : iscoasymm (abmonoidfracrel X A is).
Proof.
  intros. apply iscoasymmquotrel. apply iscoasymmabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma istotalabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istotal L) : istotal (abmonoidfracrelint X A L).
Proof.
  intros. unfold istotal. intros x1 x2. unfold abmonoidfracrelint.
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

Lemma istotalabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : istotal L) : istotal (abmonoidfracrel X A is).
Proof.
  intros. apply istotalquotrel. apply istotalabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iscotransabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
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
    rewrite (pathsinv0 (assoc _ _ a2)).
    rewrite (pathsinv0 (assoc _ _ a2)).
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
Defined.
Opaque iscotransabmonoidfracrelint.

Lemma iscotransabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : iscotrans L) : iscotrans (abmonoidfracrel X A is).
Proof.
  intros. apply iscotransquotrel. apply iscotransabmonoidfracrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isStrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : hrel X)
      (Hgt : ispartbinophrel Y gt) :
  isStrongOrder gt → isStrongOrder (abmonoidfracrel X Y Hgt).
Proof.
  intros X Y gt Hgt H.
  split ; [ | split].
  - apply istransabmonoidfracrel, (istrans_isStrongOrder H).
  - apply iscotransabmonoidfracrel, (iscotrans_isStrongOrder H).
  - apply isirreflabmonoidfracrel, (isirrefl_isStrongOrder H).
Defined.
Definition StrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : StrongOrder X)
           (Hgt : ispartbinophrel Y gt) : StrongOrder (abmonoidfrac X Y) :=
  abmonoidfracrel X Y Hgt,, isStrongOrder_abmonoidfrac Y gt Hgt (pr2 gt).

Lemma isantisymmnegabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isantisymmneg L) : isantisymmneg (abmonoidfracrel X A is).
Proof.
  intros.
  assert (int : ∏ x1 x2, isaprop (neg (abmonoidfracrel X A is x1 x2) ->
                                  neg (abmonoidfracrel X A is x2 x1) ->
                                  x1 = x2)).
  {
    intros x1 x2.
    apply impred. intro.
    apply impred. intro.
    apply (isasetsetquot _ x1 x2).
  }
  unfold isantisymmneg.
  apply (setquotuniv2prop _ (λ x1 x2, hProppair _ (int x1 x2))).
  intros xa1 xa2. intros r r'. apply (weqpathsinsetquot _).
  generalize r r'. clear r r'.
  change (neg (abmonoidfracrelint X A L xa1 xa2) ->
          neg (abmonoidfracrelint X A L xa2 xa1) ->
          (eqrelabmonoidfrac X A xa1 xa2)).
  intros nr12 nr21.
  set (nr12' := neghexisttoforallneg _ nr12 (unel A)).
  set (nr21' := neghexisttoforallneg _ nr21 (unel A)).
  set (int' := isl _ _ nr12' nr21').
  simpl. apply hinhpr. split with (unel A). apply int'.
Defined.
Opaque isantisymmnegabmonoidfracrel.

Lemma isantisymmabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (isl : isantisymm L) : isantisymm (abmonoidfracrel X A is).
Proof.
  intros.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm. unfold isantisymm.
  assert (int : ∏ x1 x2, isaprop ((abmonoidfracrel X A is x1 x2) ->
                                  (abmonoidfracrel X A is x2 x1) ->
                                  x1 = x2)).
  {
    intros x1 x2.
    apply impred. intro.
    apply impred. intro.
    apply (isasetsetquot _ x1 x2).
  }
  apply (setquotuniv2prop _ (λ x1 x2, hProppair _ (int x1 x2))).
  intros xa1 xa2. intros r r'. apply (weqpathsinsetquot _).
  generalize r r'. clear r r'.
  change ((abmonoidfracrelint X A L xa1 xa2) ->
          (abmonoidfracrelint X A L xa2 xa1) ->
          (eqrelabmonoidfrac X A xa1 xa2)).
  unfold abmonoidfracrelint. unfold eqrelabmonoidfrac. simpl.
  apply hinhfun2. intros t2l1 t2l2.
  set (c1a := pr1 t2l1). set (l1 := pr2 t2l1).
  set (c2a := pr1 t2l2). set (l2 := pr2 t2l2).
  set (c1 := pr1 c1a). set (c2 := pr1 c2a).
  split with (@op A c1a c2a).
  set (x1 := pr1 xa1). set (a1 := pr1 (pr2 xa1)).
  set (x2 := pr1 xa2). set (a2 := pr1 (pr2 xa2)).
  change (paths (x1 + a2 + (@op X c1 c2)) (x2 + a1 + (@op X c1 c2))).
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
Defined.
Opaque isantisymmabmonoidfracrel.

Lemma ispartbinopabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
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
  apply ((pr1 is) _ _ _ (pr2 (@op A (carrierpair A z s) (pr2 zc)))).
  apply l.
Defined.
Opaque ispartbinopabmonoidfracrelint.

(* ??? Coq 8.4-8.5 trunk hangs here on the following line:

Axiom ispartlbinopabmonoidfracrel : ∏ (X : abmonoid) (A : @subabmonoid X)
 {L : hrel X} (is : ispartbinophrel A L) (aa aa' : A)
 (z z' : abmonoidfrac X A) (l : abmonoidfracrel X A is z z'),
abmonoidfracrel X A is ((prabmonoidfrac X A (pr1 aa) aa') + z)
                       ((prabmonoidfrac X A (pr1 aa) aa') + z').

*)

Lemma ispartlbinopabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (aa aa' : A) (z z' : abmonoidfrac X A)
      (l : abmonoidfracrel X A is z z') :
  abmonoidfracrel X A is
                  ((prabmonoidfrac X A (pr1 aa) aa') + z) ((prabmonoidfrac X A (pr1 aa) aa') + z').
Proof.
  intros X A L is aa aa'.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X).
  assert (int : ∏ z z', isaprop (abmonoidfracrel X A is z z' ->
                                 abmonoidfracrel
                                   X A is (prabmonoidfrac X A (pr1 aa) aa' + z)
                                   (prabmonoidfrac X A (pr1 aa) aa' + z'))).
  {
    intros z z'.
    apply impred. intro.
    apply (pr2 (abmonoidfracrel _ _ _ _ _)).
  }
  apply (setquotuniv2prop _ (λ z z', hProppair _ (int z z'))).
  intros xa1 xa2.
  change (abmonoidfracrelint X A L xa1 xa2 ->
          abmonoidfracrelint X A L
                             (@op (abmonoiddirprod X A) (dirprodpair (pr1 aa) aa') xa1)
                             (@op (abmonoiddirprod X A) (dirprodpair (pr1 aa) aa') xa2)).
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
Defined.
Opaque ispartlbinopabmonoidfracrel.

Lemma ispartrbinopabmonoidfracrel (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
      (is : ispartbinophrel A L) (aa aa' : A) (z z' : abmonoidfrac X A)
      (l : abmonoidfracrel X A is z z') :
  abmonoidfracrel X A is
                  (z + (prabmonoidfrac X A (pr1 aa) aa')) (z' + (prabmonoidfrac X A (pr1 aa) aa')).
Proof.
  intros X A L is aa aa'.
  set (assoc := (assocax X) : isassoc (@op X)). unfold isassoc in assoc.
  set (comm := commax X). unfold iscomm in comm.
  set (rer := abmonoidrer X).
  assert (int : ∏ (z z' : abmonoidfrac X A),
                isaprop (abmonoidfracrel X A is z z' ->
                         abmonoidfracrel X A is
                                         (z + (prabmonoidfrac X A (pr1 aa) aa'))
                                         (z' + prabmonoidfrac X A (pr1 aa) aa'))).
  {
    intros z z'.
    apply impred. intro.
    apply (pr2 (abmonoidfracrel _ _ _ _ _)).
  }
  apply (setquotuniv2prop _ (λ z z', hProppair _ (int z z'))).
  intros xa1 xa2.
  change (abmonoidfracrelint X A L xa1 xa2 ->
          abmonoidfracrelint X A L
                             (@op (abmonoiddirprod X A) xa1 (dirprodpair (pr1 aa) aa'))
                             (@op (abmonoiddirprod X A) xa2 (dirprodpair (pr1 aa) aa'))).
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
Defined.
Opaque ispartrbinopabmonoidfracrel.

Lemma abmonoidfracrelimpl (X : abmonoid) (A : @subabmonoid X) {L L' : hrel X}
      (is : ispartbinophrel A L) (is' : ispartbinophrel A L')
      (impl : ∏ x x', L x x' -> L' x x') (x x' : abmonoidfrac X A)
      (ql : abmonoidfracrel X A is x x') : abmonoidfracrel X A is' x x'.
Proof.
  intros. generalize ql. apply quotrelimpl. intros x0 x0'.
  unfold abmonoidfracrelint. simpl. apply hinhfun.
  intro t2. split with (pr1 t2). apply (impl _ _ (pr2 t2)).
Defined.
Opaque abmonoidfracrelimpl.

Lemma abmonoidfracrellogeq (X : abmonoid) (A : @subabmonoid X) {L L' : hrel X}
      (is : ispartbinophrel A L) (is' : ispartbinophrel A L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abmonoidfrac X A) :
  (abmonoidfracrel X A is x x') <-> (abmonoidfracrel X A is' x x').
Proof.
  intros. apply quotrellogeq. intros x0 x0'. split.
  - unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2.
    split with (pr1 t2). apply (pr1 (lg _ _) (pr2 t2)).
  - unfold abmonoidfracrelint. simpl. apply hinhfun. intro t2.
    split with (pr1 t2). apply (pr2 (lg _ _) (pr2 t2)).
Defined.
Opaque abmonoidfracrellogeq.

Definition isdecabmonoidfracrelint (X : abmonoid) (A : @subabmonoid X) {L : hrel X}
           (is : ispartinvbinophrel A L) (isl : isdecrel L) : isdecrel (abmonoidfracrelint X A L).
Proof.
  intros. intros xa1 xa2.
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
    apply (@hinhuniv _ (hProppair _ (pr2 (L _ _)))).
    intro t2l. destruct t2l as [ c0a l ].
    simpl.
    apply ((pr2 is) _ _ _ (pr2 c0a) l).
Defined.

Definition isdecabmonoidfracrel (X : abmonoid) (A : @submonoid X) {L : hrel X}
           (is : ispartbinophrel A L) (isi : ispartinvbinophrel A L)
           (isl : isdecrel L) : isdecrel (abmonoidfracrel X A is).
Proof.
  intros. apply isdecquotrel. apply isdecabmonoidfracrelint.
  - apply isi.
  - apply isl.
Defined.


(** **** Relations and the canonical homomorphism to [abmonoidfrac] *)

Lemma iscomptoabmonoidfrac (X : abmonoid) (A : @submonoid X) {L : hrel X}
      (is : ispartbinophrel A L) : iscomprelrelfun L (abmonoidfracrel X A is) (toabmonoidfrac X A).
Proof.
  intros. unfold iscomprelrelfun. intros x x' l.
  change (abmonoidfracrelint X A L (dirprodpair x (unel A)) (dirprodpair x' (unel A))).
  simpl. apply (hinhpr). split with (unel A). apply ((pr2 is) _ _ 0).
  apply (pr2 (unel A)). apply ((pr2 is) _ _ 0). apply (pr2 (unel A)).
  apply l.
Defined.
Opaque iscomptoabmonoidfrac.

Close Scope addmonoid_scope.


(** *** Groups *)

(** **** Basic definitions *)

Definition gr : UU := total2 (λ X : setwithbinop, isgrop (@op X)).

Definition grpair :
  ∏ (t : setwithbinop), (λ X : setwithbinop, isgrop op) t → ∑ X : setwithbinop, isgrop op :=
  tpair (λ X : setwithbinop, isgrop (@op X)).

Definition grconstr :
  ∏ (t : setwithbinop), (λ X : setwithbinop, isgrop op) t → ∑ X : setwithbinop, isgrop op :=
  grpair.

Definition grtomonoid : gr -> monoid := λ X : _, monoidpair (pr1 X) (pr1 (pr2 X)).
Coercion grtomonoid : gr >-> monoid.

Definition grinv (X : gr) : X -> X := pr1 (pr2 (pr2 X)).

Definition grlinvax (X : gr) : islinv (@op X) (unel X) (grinv X) := pr1 (pr2 (pr2 (pr2 X))).

Definition grrinvax (X : gr) : isrinv (@op X) (unel X) (grinv X) := pr2 (pr2 (pr2 (pr2 X))).

Lemma monoidfuninvtoinv {X Y : gr} (f : monoidfun X Y) (x : X) :
  paths (f (grinv X x)) (grinv Y (f x)).
Proof.
  intros.
  apply (invmaponpathsweq (weqpair _ (isweqrmultingr_is (pr2 Y) (f x)))).
  simpl.
  change (paths (op (pr1 f (grinv X x)) (pr1 f x)) (op (grinv Y (pr1 f x)) (pr1 f x))).
  rewrite (grlinvax Y (pr1 f x)).
  destruct (pr1 (pr2 f) (grinv X x) x).
  rewrite (grlinvax X x).
  apply (pr2 (pr2 f)).
Defined.


(** **** Construction of the trivial abmonoid consisting of one element given by unit. *)

Definition unitgr_isgrop : isgrop (@op unitmonoid).
Proof.
  use mk_isgrop.
  - exact unitmonoid_ismonoid.
  - use mk_invstruct.
    + intros i. exact i.
    + use mk_isinv.
      * intros x. use isconnectedunit.
      * intros x. use isconnectedunit.
Qed.

Definition unitgr : gr := grpair unitmonoid unitgr_isgrop.

Lemma grfuntounit_ismonoidfun (X : gr) : ismonoidfun (λ x : X, (unel unitgr)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use isconnectedunit.
  - use isconnectedunit.
Qed.

Definition grfuntounit (X : gr) : monoidfun X unitgr := monoidfunconstr (grfuntounit_ismonoidfun X).

Lemma grfunfromunit_ismonoidfun (X : gr) : ismonoidfun (λ x : unitgr, (unel X)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition grfunfromunit (X : gr) : monoidfun unitmonoid X :=
  monoidfunconstr (monoidfunfromunit_ismonoidfun X).

Lemma unelgrfun_ismonoidfun (X Y : gr) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  intros X Y. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Definition unelgrfun (X Y : gr) : monoidfun X Y :=
  monoidfunconstr (unelgrfun_ismonoidfun X Y).


(** **** (X = Y) ≃ (monoidiso X Y)
   The idea is to use the composition

            (X = Y) ≃ (mk_gr' X = mk_gr' Y)
                    ≃ ((gr'_to_monoid (mk_gr' X)) = (gr'_to_monoid (mk_gr' Y)))
                    ≃ (monoidiso X Y).

   The reason why we use gr' is that then we can use univalence for monoids. See
   [gr_univalence_weq3].
*)

Local Definition gr' : UU :=
  ∑ g : (∑ X : setwithbinop, ismonoidop (@op X)), invstruct (@op (pr1 g)) (pr2 g).

Local Definition mk_gr' (X : gr) : gr' := tpair _ (tpair _ (pr1 X) (pr1 (pr2 X))) (pr2 (pr2 X)).

Local Definition gr'_to_monoid (X : gr') : monoid := pr1 X.

Definition gr_univalence_weq1 : gr ≃ gr' :=
  weqtotal2asstol
    (λ Z : setwithbinop, ismonoidop (@op Z))
    (fun y : (∑ (x : setwithbinop), ismonoidop (@op x)) => invstruct (@op (pr1 y)) (pr2 y)).

Definition gr_univalence_weq1' (X Y : gr) : (X = Y) ≃ (mk_gr' X = mk_gr' Y) :=
  weqpair _ (@isweqmaponpaths gr gr' gr_univalence_weq1 X Y).

Definition gr_univalence_weq2 (X Y : gr) :
  ((mk_gr' X) = (mk_gr' Y)) ≃ ((gr'_to_monoid (mk_gr' X)) = (gr'_to_monoid (mk_gr' Y))).
Proof.
  intros X Y.
  use subtypeInjectivity.
  intros w. use isapropinvstruct.
Defined.
Opaque gr_univalence_weq2.

Definition gr_univalence_weq3 (X Y : gr) :
  ((gr'_to_monoid (mk_gr' X)) = (gr'_to_monoid (mk_gr' Y))) ≃ (monoidiso X Y) :=
  monoid_univalence (gr'_to_monoid (mk_gr' X)) (gr'_to_monoid (mk_gr' Y)).

Definition gr_univalence_map (X Y : gr) : (X = Y) -> (monoidiso X Y).
Proof.
  intros X Y e. induction e. exact (idmonoidiso X).
Defined.

Lemma gr_univalence_isweq (X Y : gr) : isweq (gr_univalence_map X Y).
Proof.
  intros X Y.
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
  intros X Y.
  use weqpair.
  - exact (gr_univalence_map X Y).
  - exact (gr_univalence_isweq X Y).
Defined.
Opaque gr_univalence.


(** **** Computation lemmas for groups *)

Definition weqlmultingr (X : gr) (x0 : X) : pr1 X ≃ pr1 X :=
  weqpair _ (isweqlmultingr_is (pr2 X) x0).

Definition weqrmultingr (X : gr) (x0 : X) : pr1 X ≃ pr1 X :=
  weqpair _ (isweqrmultingr_is (pr2 X) x0).

Lemma grlcan (X : gr) {a b : X} (c : X) (e : paths (op c a) (op c b)) : a = b.
Proof. intros. apply (invmaponpathsweq (weqlmultingr X c) _ _ e). Defined.

Lemma grrcan (X : gr) {a b : X} (c : X) (e : paths (op a c) (op b c)) : a = b.
Proof. intros. apply (invmaponpathsweq (weqrmultingr X c) _ _ e). Defined.

Lemma grinvunel (X : gr) : paths (grinv X (unel X)) (unel X).
Proof.
  intro. apply (grrcan X (unel X)).
  rewrite (grlinvax X). rewrite (runax X).
  apply idpath.
Defined.

Lemma grinvinv (X : gr) (a : X) : paths (grinv X (grinv X a)) a.
Proof.
  intros. apply (grlcan X (grinv X a)).
  rewrite (grlinvax X a). rewrite (grrinvax X _).
  apply idpath.
Defined.

Lemma grinvmaponpathsinv (X : gr) {a b : X} (e : paths (grinv X a) (grinv X b)) : a = b.
Proof.
  intros. assert (e' := maponpaths (λ x, grinv X x) e).
  simpl in e'. rewrite (grinvinv X _) in e'.
  rewrite (grinvinv X _) in e'. apply e'.
Defined.

Lemma grinvandmonoidfun (X Y : gr) {f : X -> Y} (is : ismonoidfun f) (x : X) :
  paths (f (grinv X x)) (grinv Y (f x)).
Proof.
  intros. apply (grrcan Y (f x)).
  rewrite (pathsinv0 (pr1 is _ _)). rewrite (grlinvax X).
  rewrite (grlinvax Y).
  apply (pr2 is).
Defined.

Lemma grinvop (Y : gr) :
  ∏ y1 y2 : Y, grinv Y (@op Y y1 y2) = @op Y (grinv Y y2) (grinv Y y1).
Proof.
  intros Y y1 y2.
  apply (grrcan Y y1).
  rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
  apply (grrcan Y y2).
  rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
  apply idpath.
Qed.


(** **** Relations on groups *)

Lemma isinvbinophrelgr (X : gr) {R : hrel X} (is : isbinophrel R) : isinvbinophrel R.
Proof.
  intros. set (is1 := pr1 is). set (is2 := pr2 is). split.
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
  intros. set (is1 := pr1 is). set (is2 := pr2 is). split.
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
  intros. assert (r := (pr2 is) _ _ x isg).
  rewrite (grlinvax X x) in r.
  rewrite (lunax X _) in r.
  apply r.
Defined.

Lemma grfromltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R (unel X) x) :
  R (grinv X x) (unel X).
Proof.
  intros. assert (r := (pr1 is) _ _ (grinv X x) isg).
  rewrite (grlinvax X x) in r.
  rewrite (runax X _) in r.
  apply r.
Defined.

Lemma grtoltunel (X : gr) {R : hrel X} (is : isbinophrel R) {x : X} (isg : R (grinv X x) (unel X)) :
  R (unel X) x.
Proof.
  intros. assert (r := (pr1 is) _ _ x isg).
  rewrite (grrinvax X x) in r. rewrite (runax X _) in r.
  apply r.
Defined.


(** **** Subobjects *)

Definition issubgr {X : gr} (A : hsubtype X) : UU :=
  dirprod (issubmonoid A) (∏ x : X, A x -> A (grinv X x)).

Definition issubgrpair {X : gr} {A : hsubtype X} (H1 : issubmonoid A)
           (H2 : ∏ x : X, A x -> A (grinv X x)) : issubgr A := dirprodpair H1 H2.

Lemma isapropissubgr {X : gr} (A : hsubtype X) : isaprop (issubgr A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubmonoid.
  - apply impred. intro x.
    apply impred. intro a.
    apply (pr2 (A (grinv X x))).
Defined.

Definition subgr {X : gr} : UU := total2 (λ A : hsubtype X, issubgr A).

Definition subgrpair {X : gr} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubgr A) t → ∑ A : hsubtype X, issubgr A :=
  tpair (λ A : hsubtype X, issubgr A).

Definition subgrconstr {X : gr} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubgr A) t → ∑ A : hsubtype X, issubgr A :=
  @subgrpair X.

Definition subgrtosubmonoid (X : gr) : @subgr X -> @submonoid X :=
  λ A : _, submonoidpair (pr1 A) (pr1 (pr2 A)).
Coercion subgrtosubmonoid : subgr >-> submonoid.

Lemma isinvoncarrier {X : gr} (A : @subgr X) :
  isinv (@op A) (unel A) (λ a : A, carrierpair _ (grinv X (pr1 a)) (pr2 (pr2 A) (pr1 a) (pr2 a))).
Proof.
  intros. split.
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grlinvax X (pr1 a)).
  - intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
    simpl. apply (grrinvax X (pr1 a)).
Defined.

Definition isgrcarrier {X : gr} (A : @subgr X) : isgrop (@op A) :=
  tpair _ (ismonoidcarrier A)
        (tpair _ (λ a : A, carrierpair _ (grinv X (pr1 a)) (pr2 (pr2 A) (pr1 a) (pr2 a)))
               (isinvoncarrier A)).

Definition carrierofasubgr {X : gr} (A : @subgr X) : gr.
Proof. intros. split with A. apply (isgrcarrier A). Defined.
Coercion carrierofasubgr : subgr >-> gr.

Lemma intersection_subgr : forall {X : gr} {I : UU} (S : I -> hsubtype X)
                                  (each_is_subgr : ∏ i : I, issubgr (S i)),
    issubgr (subtype_intersection S).
Proof.
  intros.
  use issubgrpair.
  - exact (intersection_submonoid S (λ i, (pr1 (each_is_subgr i)))).
  - exact (λ x x_in_S i, pr2 (each_is_subgr i) x (x_in_S i)).
Qed.


(** **** Quotient objects *)

Lemma grquotinvcomp {X : gr} (R : @binopeqrel X) : iscomprelrelfun R R (grinv X).
Proof.
  intros. destruct R as [ R isb ].
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

Definition invongrquot {X : gr} (R : @binopeqrel X) : setquot R -> setquot R :=
  setquotfun R R (grinv X) (grquotinvcomp R).

Lemma isinvongrquot {X : gr} (R : @binopeqrel X) :
  isinv (@op (setwithbinopquot R)) (setquotpr R (unel X)) (invongrquot R).
Proof.
  intros. split.
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

Definition isgrquot {X : gr} (R : @binopeqrel X) : isgrop (@op (setwithbinopquot R)) :=
  tpair _ (ismonoidquot R) (tpair _ (invongrquot R) (isinvongrquot R)).

Definition grquot {X : gr} (R : @binopeqrel X) : gr.
Proof. intros. split with (setwithbinopquot R). apply isgrquot. Defined.


(** **** Direct products *)

Lemma isgrdirprod (X Y : gr) : isgrop (@op (setwithbinopdirprod X Y)).
Proof.
  intros. split with (ismonoiddirprod X Y).
  split with (λ xy : _, dirprodpair (grinv X (pr1 xy)) (grinv Y (pr2 xy))).
  split.
  - intro xy. destruct xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grlinvax X x). apply (grlinvax Y y).
  - intro xy. destruct xy as [ x y ].
    unfold unel_is. simpl. apply pathsdirprod.
    apply (grrinvax X x). apply (grrinvax Y y).
Defined.

Definition grdirprod (X Y : gr) : gr.
Proof. intros. split with (setwithbinopdirprod X Y). apply isgrdirprod. Defined.


(** *** Abelian groups *)

(** **** Basic definitions *)

Definition abgr : UU := total2 (λ X : setwithbinop, isabgrop (@op X)).

Definition abgrpair (X : setwithbinop) (is : isabgrop (@op X)) : abgr :=
  tpair (λ X : setwithbinop,  isabgrop (@op X)) X is.

Definition abgrconstr (X : abmonoid) (inv0 : X -> X) (is : isinv (@op X) (unel X) inv0) : abgr :=
  abgrpair X (dirprodpair (isgroppair (pr2 X) (tpair _ inv0 is)) (commax X)).

Definition abgrtogr : abgr -> gr := λ X : _, grpair (pr1 X) (pr1 (pr2 X)).
Coercion abgrtogr : abgr >-> gr.

Definition abgrtoabmonoid : abgr -> abmonoid :=
  λ X : _, abmonoidpair (pr1 X) (dirprodpair (pr1 (pr1 (pr2 X))) (pr2 (pr2 X))).
Coercion abgrtoabmonoid : abgr >-> abmonoid.


(** **** Construction of the trivial abgr consisting of one element given by unit. *)

Definition unitabgr_isabgrop : isabgrop (@op unitabmonoid).
Proof.
  use mk_isabgrop.
  - exact unitgr_isgrop.
  - exact (commax unitabmonoid).
Qed.

Definition unitabgr : abgr := abgrpair unitabmonoid unitabgr_isabgrop.

Lemma abgrfuntounit_ismonoidfun (X : abgr) : ismonoidfun (λ x : X, (unel unitabgr)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use isconnectedunit.
  - use isconnectedunit.
Qed.

Definition abgrfuntounit (X : abgr) : monoidfun X unitabgr :=
  monoidfunconstr (abgrfuntounit_ismonoidfun X).

Lemma abgrfunfromunit_ismonoidfun (X : abgr) : ismonoidfun (λ x : unitabgr, (unel X)).
Proof.
  intros X. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use (runax X).
  - use idpath.
Qed.

Definition abgrfunfromunit (X : abgr) : monoidfun unitabgr X :=
  monoidfunconstr (abgrfunfromunit_ismonoidfun X).

Lemma unelabgrfun_ismonoidfun (X Y : abgr) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  intros X Y. use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Definition unelabgrfun (X Y : abgr) : monoidfun X Y :=
  monoidfunconstr (unelgrfun_ismonoidfun X Y).


(** **** Abelian group structure on morphism between abelian groups *)

Definition abgrshombinop_inv_ismonoidfun {X Y : abgr} (f : monoidfun X Y) :
  ismonoidfun (λ x : X, grinv Y (pr1 f x)).
Proof.
  intros X Y f.
  use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 Y)). use (grinvop Y).
  - use (pathscomp0 (maponpaths (λ y : Y, grinv Y y) (monoidfununel f))).
    use grinvunel.
Qed.

Definition abgrshombinop_inv {X Y : abgr} (f : monoidfun X Y) : monoidfun X Y :=
  monoidfunconstr (abgrshombinop_inv_ismonoidfun f).

Definition abgrshombinop_linvax {X Y : abgr} (f : monoidfun X Y) :
  @abmonoidshombinop X Y (abgrshombinop_inv f) f = unelmonoidfun X Y.
Proof.
  intros X Y f. use monoidfun_paths. use funextfun. intros x. use (@grlinvax Y).
Qed.

Definition abgrshombinop_rinvax {X Y : abgr} (f : monoidfun X Y) :
  @abmonoidshombinop X Y f (abgrshombinop_inv f) = unelmonoidfun X Y.
Proof.
  intros X Y f. use monoidfun_paths. use funextfun. intros x. use (grrinvax Y).
Qed.

Lemma abgrshomabgr_isabgrop (X Y : abgr) :
  @isabgrop (abmonoidshomabmonoid X Y) (λ f g : monoidfun X Y, @abmonoidshombinop X Y f g).
Proof.
  intros X Y.
  use mk_isabgrop.
  - use mk_isgrop.
    + exact (abmonoidshomabmonoid_ismonoidop X Y).
    + use mk_invstruct.
      * intros f. exact (abgrshombinop_inv f).
      * use mk_isinv.
        -- intros f. exact (abgrshombinop_linvax f).
        -- intros f. exact (abgrshombinop_rinvax f).
  - intros f g. exact (abmonoidshombinop_comm f g).
Defined.

Definition abgrshomabgr (X Y : abgr) : abgr.
Proof.
  intros X Y. use abgrpair.
  - exact (abmonoidshomabmonoid X Y).
  - exact (abgrshomabgr_isabgrop X Y).
Defined.


(** **** (X = Y) ≃ (monoidiso X Y)
   The idea is to use the following composition

        (X = Y) ≃ (mk_abgr' X = mk_abgr' Y)
                ≃ (pr1 (mk_abgr' X) = pr1 (mk_abgr' Y))
                ≃ (monoidiso X Y)

    We use abgr' so that we can use univalence for groups, [gr_univalence]. See
    [abgr_univalence_weq3].
 *)

Local Definition abgr' : UU :=
  ∑ g : (∑ X : setwithbinop, isgrop (@op X)), iscomm (pr2 (pr1 g)).

Local Definition mk_abgr' (X : abgr) : abgr' :=
  tpair _ (tpair _ (pr1 X) (dirprod_pr1 (pr2 X))) (dirprod_pr2 (pr2 X)).

Local Definition abgr_univalence_weq1 : abgr ≃ abgr' :=
  weqtotal2asstol (λ Z : setwithbinop, isgrop (@op Z))
                  (fun y : (∑ x : setwithbinop, isgrop (@op x)) => iscomm (@op (pr1 y))).

Definition abgr_univalence_weq1' (X Y : abgr) : (X = Y) ≃ (mk_abgr' X = mk_abgr' Y) :=
  weqpair _ (@isweqmaponpaths abgr abgr' abgr_univalence_weq1 X Y).

Definition abgr_univalence_weq2 (X Y : abgr) :
  (mk_abgr' X = mk_abgr' Y) ≃ (pr1 (mk_abgr' X) = pr1 (mk_abgr' Y)).
Proof.
  intros X Y.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque abgr_univalence_weq2.

Definition abgr_univalence_weq3 (X Y : abgr) :
  (pr1 (mk_abgr' X) = pr1 (mk_abgr' Y)) ≃ (monoidiso X Y) :=
  gr_univalence (pr1 (mk_abgr' X)) (pr1 (mk_abgr' Y)).

Definition abgr_univalence_map (X Y : abgr) : (X = Y) -> (monoidiso X Y).
Proof.
  intros X Y e. induction e. exact (idmonoidiso X).
Defined.

Lemma abgr_univalence_isweq (X Y : abgr) : isweq (abgr_univalence_map X Y).
Proof.
  intros X Y.
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
  intros X Y.
  use weqpair.
  - exact (abgr_univalence_map X Y).
  - exact (abgr_univalence_isweq X Y).
Defined.
Opaque abgr_univalence.


(** **** Subobjects *)

Definition subabgr {X : abgr} := @subgr X.
Identity Coercion id_subabgr : subabgr >-> subgr.

Lemma isabgrcarrier {X : abgr} (A : @subgr X) : isabgrop (@op A).
Proof.
  intros. split with (isgrcarrier A).
  apply (pr2 (@isabmonoidcarrier X A)).
Defined.

Definition carrierofasubabgr {X : abgr} (A : @subabgr X) : abgr.
Proof. intros. split with A. apply isabgrcarrier. Defined.
Coercion carrierofasubabgr : subabgr >-> abgr.


(** **** Quotient objects *)

Lemma isabgrquot {X : abgr} (R : @binopeqrel X) : isabgrop (@op (setwithbinopquot R)).
Proof.
  intros. split with (isgrquot R).
  apply (pr2 (@isabmonoidquot X R)).
Defined.
Global Opaque isabgrquot.

Definition abgrquot {X : abgr} (R : @binopeqrel X) : abgr.
Proof. intros. split with (setwithbinopquot R). apply isabgrquot. Defined.


(** **** Direct products *)

Lemma isabgrdirprod (X Y : abgr) : isabgrop (@op (setwithbinopdirprod X Y)).
Proof.
  intros. split with (isgrdirprod X Y).
  apply (pr2 (isabmonoiddirprod X Y)).
Defined.

Definition abgrdirprod (X Y : abgr) : abgr.
Proof.
  intros. split with (setwithbinopdirprod X Y).
  apply isabgrdirprod.
Defined.


(** **** Abelian group of fractions of an abelian unitary monoid *)

Open Scope addmonoid_scope.

Definition hrelabgrdiff (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2,
    hexists (λ x0 : X, paths (((pr1 xa1) + (pr2 xa2)) + x0) (((pr1 xa2) + (pr2 xa1)) + x0)).

Definition abgrdiffphi (X : abmonoid) (xa : dirprod X X) :
  dirprod X (totalsubtype X) := dirprodpair (pr1 xa) (carrierpair (λ x : X, htrue) (pr2 xa) tt).

Definition hrelabgrdiff' (X : abmonoid) : hrel (X × X) :=
  λ xa1 xa2, eqrelabmonoidfrac X (totalsubmonoid X) (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqhrelsabgrdiff (X : abmonoid) : hrellogeq (hrelabgrdiff' X) (hrelabgrdiff X).
Proof.
  intros. split. simpl. apply hinhfun. intro t2.
  set (a0 := pr1 (pr1 t2)). split with a0. apply (pr2 t2). simpl.
  apply hinhfun. intro t2. set (x0 := pr1 t2). split with (tpair _ x0 tt).
  apply (pr2 t2).
Defined.

Lemma iseqrelabgrdiff (X : abmonoid) : iseqrel (hrelabgrdiff X).
Proof.
  intro.
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
  eqrelpair _ (iseqrelabgrdiff X).

Lemma isbinophrelabgrdiff (X : abmonoid) : @isbinophrel (abmonoiddirprod X X) (hrelabgrdiff X).
Proof.
  intro.
  apply (@isbinophrellogeqf (abmonoiddirprod X X) _ _ (logeqhrelsabgrdiff X)).
  split. intros a b c r.
  apply (pr1 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (dirprodpair (pr1 c) (carrierpair (λ x : X, htrue) (pr2 c) tt))
             r).
  intros a b c r.
  apply (pr2 (isbinophrelabmonoidfrac X (totalsubmonoid X)) _ _
             (dirprodpair (pr1 c) (carrierpair (λ x : X, htrue) (pr2 c) tt))
             r).
Defined.
Opaque isbinophrelabgrdiff.

Definition binopeqrelabgrdiff (X : abmonoid) : @binopeqrel (abmonoiddirprod X X) :=
  binopeqrelpair (eqrelabgrdiff X) (isbinophrelabgrdiff X).

Definition abgrdiffcarrier (X : abmonoid) : abmonoid := @abmonoidquot (abmonoiddirprod X X)
                                                                      (binopeqrelabgrdiff X).

Definition abgrdiffinvint (X : abmonoid) :  dirprod X X -> dirprod X X :=
  λ xs : _, dirprodpair (pr2 xs) (pr1 xs).

Lemma abgrdiffinvcomp (X : abmonoid) :
  iscomprelrelfun (hrelabgrdiff X) (eqrelabgrdiff X) (abgrdiffinvint X).
Proof.
  intros. unfold iscomprelrelfun. unfold eqrelabgrdiff. unfold hrelabgrdiff.
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
  intros. set (R := eqrelabgrdiff X).
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
  apply (dirprodpair isl (weqlinvrinv (@op (abgrdiffcarrier X)) (commax (abgrdiffcarrier X))
                                      (unel (abgrdiffcarrier X)) (abgrdiffinv X) isl)).
Defined.
Opaque abgrdiffisinv.

Definition abgrdiff (X : abmonoid) : abgr := abgrconstr (abgrdiffcarrier X) (abgrdiffinv X)
                                                        (abgrdiffisinv X).

Definition prabgrdiff (X : abmonoid) : X -> X -> abgrdiff X :=
  λ x x' : X, setquotpr (eqrelabgrdiff X) (dirprodpair x x').


(** **** Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrdiffint (X : abmonoid) : weq (X × X) (dirprod X (totalsubtype X)) :=
  weqdirprodf (idweq X) (invweq (weqtotalsubtype X)).

Definition weqabgrdiff (X : abmonoid) : weq (abgrdiff X) (abmonoidfrac X (totalsubmonoid X)).
Proof.
  intros.
  apply (weqsetquotweq (eqrelabgrdiff X)
                       (eqrelabmonoidfrac X (totalsubmonoid X)) (weqabgrdiffint X)).
  - simpl. intros x x'. destruct x as [ x1 x2 ]. destruct x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. destruct tt0 as [ xx0 is0 ].
    split with (carrierpair (λ x : X, htrue) xx0 tt). apply is0.
  - simpl. intros x x'. destruct x as [ x1 x2 ]. destruct x' as [ x1' x2' ].
    simpl in *. apply hinhfun. intro tt0. destruct tt0 as [ xx0 is0 ].
    split with (pr1 xx0). apply is0.
Defined.


(** **** Canonical homomorphism to the abelian group of fractions *)

Definition toabgrdiff (X : abmonoid) (x : X) : abgrdiff X := setquotpr _ (dirprodpair x (unel X)).

Lemma isbinopfuntoabgrdiff (X : abmonoid) : isbinopfun (toabgrdiff X).
Proof.
  intros. unfold isbinopfun. intros x1 x2.
  change (paths (setquotpr _ (dirprodpair (x1 + x2) (unel X)))
                (setquotpr (eqrelabgrdiff X) (dirprodpair (x1 + x2) ((unel X) + (unel X))))).
  apply (maponpaths (setquotpr _)).
  apply (@pathsdirprod X X).
  apply idpath.
  apply (pathsinv0 (lunax X 0)).
Defined.

Lemma isunitalfuntoabgrdiff (X : abmonoid) : paths (toabgrdiff X (unel X)) (unel (abgrdiff X)).
Proof. intros. apply idpath. Defined.

Definition ismonoidfuntoabgrdiff (X : abmonoid) : ismonoidfun (toabgrdiff X) :=
  dirprodpair (isbinopfuntoabgrdiff X) (isunitalfuntoabgrdiff X).


(** **** Abelian group of fractions in the case when all elements are cancelable *)

Lemma isinclprabgrdiff (X : abmonoid) (iscanc : ∏ x : X, isrcancelable (@op X) x) :
  ∏ x' : X, isincl (λ x, prabgrdiff X x x').
Proof.
  intros.
  set (int := isinclprabmonoidfrac X (totalsubmonoid X) (λ a : totalsubmonoid X, iscanc (pr1 a))
                                   (carrierpair (λ x : X, htrue) x' tt)).
  set (int1 := isinclcomp (inclpair _ int) (invweq (weqabgrdiff X))).
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


(** **** Relations on the abelian group of fractions *)

Definition abgrdiffrelint (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa yb, hexists (λ c0 : X, L (((pr1 xa) + (pr2 yb)) + c0) (((pr1 yb) + (pr2 xa)) + c0)).

Definition abgrdiffrelint' (X : abmonoid) (L : hrel X) : hrel (setwithbinopdirprod X X) :=
  λ xa1 xa2, abmonoidfracrelint _ (totalsubmonoid X) L (abgrdiffphi X xa1) (abgrdiffphi X xa2).

Lemma logeqabgrdiffrelints (X : abmonoid) (L : hrel X) :
  hrellogeq (abgrdiffrelint' X L) (abgrdiffrelint X L).
Proof.
  intros. split. unfold abgrdiffrelint. unfold abgrdiffrelint'.
  simpl. apply hinhfun. intro t2. set (a0 := pr1 (pr1 t2)).
  split with a0. apply (pr2 t2). simpl. apply hinhfun.
  intro t2. set (x0 := pr1 t2). split with (tpair _ x0 tt). apply (pr2 t2).
Defined.

Lemma iscomprelabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrel (eqrelabgrdiff X) (abgrdiffrelint X L).
Proof.
  intros. apply (iscomprelrellogeqf1 _ (logeqhrelsabgrdiff X)).
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
  intros X L is x1 x2. split.
  - assert (int : ∏ x x', isaprop (abgrdiffrel' X is x x' -> abgrdiffrel X is x x')).
    {
      intros x x'.
      apply impred. intro.
      apply (pr2 _).
    }
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', hProppair _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint' X L x x')  -> (abgrdiffrelint _ L x x')).
    apply (pr1 (logeqabgrdiffrelints X L x x')).
  - assert (int : ∏ x x', isaprop (abgrdiffrel X is x x' -> abgrdiffrel' X is x x')).
    intros x x'.
    apply impred. intro.
    apply (pr2 _).
    generalize x1 x2. clear x1 x2.
    apply (setquotuniv2prop _ (λ x x', hProppair _ (int x x'))).
    intros x x'.
    change ((abgrdiffrelint X L x x') -> (abgrdiffrelint' _ L x x')).
    apply (pr2 (logeqabgrdiffrelints X L x x')).
Defined.

Lemma istransabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istrans L) :
  istrans (abgrdiffrelint X L).
Proof.
  intros. apply (istranslogeqf (logeqabgrdiffrelints X L)).
  intros a b c rab rbc.
  apply (istransabmonoidfracrelint
           _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)  isl _ _ _ rab rbc).
Defined.
Opaque istransabgrdiffrelint.

Lemma istransabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istrans L) :
  istrans (abgrdiffrel X is).
Proof.
  intros. refine (istransquotrel _ _). apply istransabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma issymmabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : issymm L) :
  issymm (abgrdiffrelint X L).
Proof.
  intros. apply (issymmlogeqf (logeqabgrdiffrelints X L)).
  intros a b rab.
  apply (issymmabmonoidfracrelint _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is) isl _ _ rab).
Defined.
Opaque issymmabgrdiffrelint.

Lemma issymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : issymm L) :
  issymm (abgrdiffrel X is).
Proof.
  intros. refine (issymmquotrel _ _). apply issymmabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isreflabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isrefl L) :
  isrefl (abgrdiffrelint X L).
Proof.
  intros. intro xa. unfold abgrdiffrelint. simpl.
  apply hinhpr. split with (unel X). apply (isl _).
Defined.

Lemma isreflabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isrefl L) :
  isrefl (abgrdiffrel X is).
Proof.
  intros. refine (isreflquotrel _ _). apply isreflabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma ispoabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : ispreorder L) :
  ispreorder (abgrdiffrelint X L).
Proof.
  intros. split with (istransabgrdiffrelint X is (pr1 isl)).
  apply (isreflabgrdiffrelint X is (pr2 isl)).
Defined.

Lemma ispoabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : ispreorder L) :
  ispreorder (abgrdiffrel X is).
Proof.
  intros. refine (ispoquotrel _ _). apply ispoabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma iseqrelabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iseqrel L) :
  iseqrel (abgrdiffrelint X L).
Proof.
  intros. split with (ispoabgrdiffrelint X is (pr1 isl)).
  apply (issymmabgrdiffrelint X is (pr2 isl)).
Defined.

Lemma iseqrelabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iseqrel L) :
  iseqrel (abgrdiffrel X is).
Proof.
  intros. refine (iseqrelquotrel _ _). apply iseqrelabgrdiffrelint.
  - apply is.
  - apply isl.
Defined.

Lemma isantisymmnegabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L)
      (isl : isantisymmneg L) : isantisymmneg (abgrdiffrel X is).
Proof.
  intros. apply (isantisymmneglogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  set (int := isantisymmnegabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                           isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
  apply (invmaponpathsweq _ _ _ int).
Defined.

Lemma isantisymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isantisymm L) :
  isantisymm (abgrdiffrel X is).
Proof.
  intros. apply (isantisymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  set (int := isantisymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                        isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
  apply (invmaponpathsweq _ _ _ int).
Defined.
Opaque  isantisymmabgrdiffrel.

Lemma isirreflabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isirrefl L) :
  isirrefl (abgrdiffrel X is).
Proof.
  intros. apply (isirrefllogeqf (logeqabgrdiffrels X is)).
  intros a raa.
  apply (isirreflabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                 isl (weqabgrdiff X a) raa).
Defined.
Opaque isirreflabgrdiffrel.

Lemma isasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : isasymm L) :
  isasymm (abgrdiffrel X is).
Proof.
  intros. apply (isasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab rba.
  apply (isasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b) rab rba).
Defined.
Opaque isasymmabgrdiffrel.

Lemma iscoasymmabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscoasymm L) :
  iscoasymm (abgrdiffrel X is).
Proof.
  intros. apply (iscoasymmlogeqf (logeqabgrdiffrels X is)).
  intros a b rab.
  apply (iscoasymmabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) rab).
Defined.
Opaque iscoasymmabgrdiffrel.

Lemma istotalabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : istotal L) :
  istotal (abgrdiffrel X is).
Proof.
  intros. apply (istotallogeqf (logeqabgrdiffrels X is)).
  intros a b.
  apply (istotalabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                isl (weqabgrdiff X a) (weqabgrdiff X b)).
Defined.
Opaque istotalabgrdiffrel.

Lemma iscotransabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L) (isl : iscotrans L) :
  iscotrans (abgrdiffrel X is).
Proof.
  intros. apply (iscotranslogeqf (logeqabgrdiffrels X is)).
  intros a b c.
  apply (iscotransabmonoidfracrel _ (totalsubmonoid X) (isbinoptoispartbinop _ _ is)
                                  isl (weqabgrdiff X a) (weqabgrdiff X b) (weqabgrdiff X c)).
Defined.
Opaque iscotransabgrdiffrel.

Lemma isStrongOrder_abgrdiff {X : abmonoid} (gt : hrel X)
      (Hgt : isbinophrel gt) :
  isStrongOrder gt → isStrongOrder (abgrdiffrel X Hgt).
Proof.
  intros X gt Hgt H.
  split ; [ | split].
  - apply istransabgrdiffrel, (istrans_isStrongOrder H).
  - apply iscotransabgrdiffrel, (iscotrans_isStrongOrder H).
  - apply isirreflabgrdiffrel, (isirrefl_isStrongOrder H).
Defined.
Definition StrongOrder_abgrdiff {X : abmonoid} (gt : StrongOrder X)
           (Hgt : isbinophrel gt) : StrongOrder (abgrdiff X) :=
  abgrdiffrel X Hgt,, isStrongOrder_abgrdiff gt Hgt (pr2 gt).


Lemma abgrdiffrelimpl (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (impl : ∏ x x', L x x' -> L' x x') (x x' : abgrdiff X) (ql : abgrdiffrel X is x x') :
  abgrdiffrel X is' x x'.
Proof.
  intros. generalize ql. refine (quotrelimpl _ _ _ _ _).
  intros x0 x0'. simpl. apply hinhfun. intro t2. split with (pr1 t2).
  apply (impl _ _ (pr2 t2)).
Defined.
Opaque abgrdiffrelimpl.

Lemma abgrdiffrellogeq (X : abmonoid) {L L' : hrel X} (is : isbinophrel L) (is' : isbinophrel L')
      (lg : ∏ x x', L x x' <-> L' x x') (x x' : abgrdiff X) :
  (abgrdiffrel X is x x') <-> (abgrdiffrel X is' x x').
Proof.
  intros. refine (quotrellogeq _ _ _ _ _). intros x0 x0'. split.
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr1 (lg _ _) (pr2 t2)).
  - simpl. apply hinhfun. intro t2. split with (pr1 t2).
    apply (pr2 (lg _ _) (pr2 t2)).
Defined.
Opaque abgrdiffrellogeq.

Lemma isbinopabgrdiffrelint (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  @isbinophrel (setwithbinopdirprod X X) (abgrdiffrelint X L).
Proof.
  intros. apply (isbinophrellogeqf (logeqabgrdiffrelints X L)). split.
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
  intros. intros xa1 xa2.
  set (x1 := pr1 xa1). set (a1 := pr2 xa1).
  set (x2 := pr1 xa2). set (a2 := pr2 xa2).
  assert (int : coprod (L (x1 + a2) (x2 + a1)) (neg (L (x1 + a2) (x2 + a1)))) by apply (isl _ _).
  destruct int as [ l | nl ].
  - apply ii1. unfold abgrdiffrelint. apply hinhpr. split with (unel X).
    rewrite (runax X _). rewrite (runax X _). apply l.
  - apply ii2. generalize nl. clear nl. apply negf. unfold abgrdiffrelint.
    simpl. apply (@hinhuniv _ (hProppair _ (pr2 (L _ _)))).
    intro t2l. destruct t2l as [ c0a l ]. simpl. apply ((pr2 is) _ _ c0a l).
Defined.

Definition isdecabgrdiffrel (X : abmonoid) {L : hrel X} (is : isbinophrel L)
           (isi : isinvbinophrel L) (isl : isdecrel L) : isdecrel (abgrdiffrel X is).
Proof.
  intros. refine (isdecquotrel _ _). apply isdecabgrdiffrelint.
  - apply isi.
  - apply isl.
Defined.


(** **** Relations and the canonical homomorphism to [ abgrdiff ] *)

Lemma iscomptoabgrdiff (X : abmonoid) {L : hrel X} (is : isbinophrel L) :
  iscomprelrelfun L (abgrdiffrel X is) (toabgrdiff X).
Proof.
  intros. unfold iscomprelrelfun.
  intros x x' l.
  change (abgrdiffrelint X L (dirprodpair x (unel X)) (dirprodpair x' (unel X))).
  simpl. apply (hinhpr). split with (unel X).
  apply ((pr2 is) _ _ 0). apply ((pr2 is) _ _ 0).
  apply l.
Defined.
Opaque iscomptoabgrdiff.

Close Scope addmonoid_scope.

(** simple examples *)

Require Export UniMath.Foundations.NaturalNumbers.

Definition nat_add_abmonoid : abmonoid :=
  (natset,, Nat.add),, (natplusassoc,, 0,, natplusl0,, natplusr0),, natpluscomm.

Definition nat_mul_abmonoid : abmonoid :=
  (natset,, mul),, (natmultassoc,, 1,, natmultl1,, natmultr1),, natmultcomm.

(* End of the file algebra1b.v *)
