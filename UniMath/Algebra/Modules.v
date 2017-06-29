(** Anthony Bordg, February-March 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Foundations.PartD.


Local Open Scope addmonoid_scope.

(** * The ring of endomorphisms of an abelian group *)

(** Two binary operations on the set of endomorphisms of an abelian group *)

Definition monoidfun_to_isbinopfun {G : abgr} (f : monoidfun G G) : isbinopfun f := pr1 (pr2 f).

Definition rngofendabgr_op1 {G: abgr} : binop (monoidfun G G).
Proof.
  intros f g.
  apply (@monoidfunconstr _ _ (λ x : G, f x + g x)).
  apply tpair.
  - intros x x'.
    rewrite (monoidfun_to_isbinopfun f).
    rewrite (monoidfun_to_isbinopfun g).
    apply (abmonoidrer G).
  - rewrite (monoidfununel f).
    rewrite (monoidfununel g).
    rewrite (lunax G).
    reflexivity.
Defined.

Definition rngofendabgr_op2 {G : abgr} : binop (monoidfun G G).
Proof.
  intros f g.
  apply (monoidfuncomp f g).
Defined.

Notation "f + g" := (rngofendabgr_op1 f g) : abgr_scope.

(** the composition below uses the diagrammatic order following the general convention used in UniMath *)

Notation "f ∘ g" := (rngofendabgr_op2 f g) : abgr_scope.

(** The underlying set of the ring of endomorphisms of an abelian group *)

Definition setofendabgr (G : abgr) : hSet :=
   hSetpair (monoidfun G G) (isasetmonoidfun G G).

(** A few access functions *)

Definition pr1setofendabgr {G : abgr} (f : setofendabgr G) : G -> G := pr1 f.

Definition pr2setofendabgr {G : abgr} (f : setofendabgr G) : ismonoidfun (pr1 f) := pr2 f.

Definition setofendabgr_to_isbinopfun {G : abgr} (f : setofendabgr G) : isbinopfun (pr1setofendabgr f) := pr1 (pr2 f).

Definition setofendabgr_to_unel {G : abgr} (f : setofendabgr G) : pr1setofendabgr f 0 = 0 := pr2 (pr2setofendabgr f).

(** We endow setofendabgr with the two binary operations defined above *)

Definition setwith2binopofendabgr (G : abgr) : setwith2binop :=
   setwith2binoppair (setofendabgr G) (dirprodpair (rngofendabgr_op1) (rngofendabgr_op2)).

(** rngofendabgr_op1 G and rngofendabgr_op2 G are ring operations *)

(** rngofendabgr_op1 is a monoid operation *)

Local Open Scope abgr_scope.

Definition isassoc_rngofendabgr_op1 {G : abgr} : isassoc (@rngofendabgr_op1 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro.
     apply (pr2 G).
   - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un0 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).
   apply dirprodpair.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
Defined.

Definition islunit_setofendabgr_un0 {G : abgr} : islunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (lunax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Definition isrunit_setofendabgr_un0 {G : abgr} : isrunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (runax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Definition isunit_setofendabgr_un0 {G : abgr} : isunit (@rngofendabgr_op1 G) setofendabgr_un0 :=
  isunitpair islunit_setofendabgr_un0 isrunit_setofendabgr_un0.

Definition isunital_rngofendabgr_op1 {G : abgr} : isunital (@rngofendabgr_op1 G) :=
  isunitalpair setofendabgr_un0 isunit_setofendabgr_un0.

Definition ismonoidop_rngofendabgr_op1 {G : abgr} : ismonoidop (@rngofendabgr_op1 G) :=
   mk_ismonoidop isassoc_rngofendabgr_op1 isunital_rngofendabgr_op1.

Local Close Scope abgr_scope.

(** rngofendabgr_op1 is a group operation *)

Definition setofendabgr_inv {G : abgr} : monoidfun G G -> monoidfun G G.
Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1setofendabgr f x))).
   apply dirprodpair.
   - intros x x'.
     rewrite (setofendabgr_to_isbinopfun f).
     rewrite (grinvop G).
     apply (commax G).
   - rewrite (setofendabgr_to_unel f).
     apply (grinvunel G).
Defined.

Local Open Scope abgr_scope.

Definition islinv_setofendabgr_inv {G : abgr} : islinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grlinvax G).
   - apply isapropismonoidfun.
Defined.

Definition isrinv_setofendabgr_inv {G : abgr} : isrinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grrinvax G).
   - apply isapropismonoidfun.
Defined.

Definition isinv_setofendabgr_inv {G : abgr} : isinv (@rngofendabgr_op1 G) (unel_is (@ismonoidop_rngofendabgr_op1 G)) setofendabgr_inv :=
  mk_isinv islinv_setofendabgr_inv isrinv_setofendabgr_inv.

Definition invstruct_setofendabgr_inv {G : abgr} : invstruct (@rngofendabgr_op1 G) ismonoidop_rngofendabgr_op1 :=
   mk_invstruct (@setofendabgr_inv G) (@isinv_setofendabgr_inv G).

Definition isgrop_rngofendabgr_op1 {G : abgr} : isgrop (@rngofendabgr_op1 G) :=
   isgroppair ismonoidop_rngofendabgr_op1 invstruct_setofendabgr_inv.

Definition iscomm_rngofendabgr_op1 {G : abgr} : iscomm (@rngofendabgr_op1 G).
Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (commax G).
   - apply (isapropismonoidfun).
Defined.

Definition isabgrop_rngofendabgr_op1 {G : abgr} : isabgrop (@rngofendabgr_op1 G) :=
  mk_isabgrop isgrop_rngofendabgr_op1 iscomm_rngofendabgr_op1.

(** rngofendabgr_op2 is a monoid operation *)

Definition isassoc_rngofendabgr_op2 {G : abgr} : isassoc (@rngofendabgr_op2 G).
Proof.
  intros f g h.
  use total2_paths_f.
  - apply funcomp_assoc.
  - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un1 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (idfun G)).
   apply dirprodpair.
   - intros x x'. reflexivity.
   - reflexivity.
Defined.

Definition islunit_setofendabgr_un1 {G : abgr} : islunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isrunit_setofendabgr_un1 {G : abgr} : isrunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isunit_setofendabgr_un1 {G : abgr} : isunit (@rngofendabgr_op2 G) setofendabgr_un1 :=
  isunitpair islunit_setofendabgr_un1 isrunit_setofendabgr_un1.

Definition isunital_rngofendabgr_op2 {G : abgr} : isunital (@rngofendabgr_op2 G) :=
  isunitalpair setofendabgr_un1 isunit_setofendabgr_un1.

Definition ismonoidop_rngofendabgr_op2 {G : abgr} : ismonoidop (@rngofendabgr_op2 G) :=
   mk_ismonoidop isassoc_rngofendabgr_op2 isunital_rngofendabgr_op2.

(** rngofendabgr_op2 is distributive over rngofendabgr_op1 *)

Definition isldistr_setofendabgr_op {G : abgr} : isldistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isrdistr_setofendabgr_op {G : abgr} : isrdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (setofendabgr_to_isbinopfun h).
   - apply isapropismonoidfun.
Defined.

Definition isdistr_setofendabgr_op {G : abgr} : isdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G) :=
   dirprodpair isldistr_setofendabgr_op isrdistr_setofendabgr_op.

Definition isrngops_setofendabgr_op {G : abgr} : isrngops (@rngofendabgr_op1 G) (@rngofendabgr_op2 G) :=
   mk_isrngops isabgrop_rngofendabgr_op1 ismonoidop_rngofendabgr_op2 isdistr_setofendabgr_op.

(** The set of endomorphisms of an abelian group is a ring *)

Definition rngofendabgr (G : abgr) : rng :=
   @rngpair (setwith2binopofendabgr G) (@isrngops_setofendabgr_op G).


(** ** The definition of the small type of (left) R-modules over a ring R *)

Definition module_struct (R : rng) (G : abgr) : UU := rngfun R (rngofendabgr G).

Definition module (R : rng) : UU := ∑ G, module_struct R G.

Definition pr1module {R : rng} (M : module R) : abgr := pr1 M.

Coercion pr1module : module >-> abgr.

Definition pr2module {R : rng} (M : module R) : module_struct R (pr1module M) := pr2 M.

Identity Coercion id_module_struct : module_struct >-> rngfun.

Definition modulepair {R : rng} (G : abgr) (f : module_struct R G) : module R := tpair _ G f.

(** The multiplication defined from a module *)

Definition module_mult {R : rng} (M : module R) : R -> M -> M := λ r : R, λ x : M, (pr1setofendabgr (pr2module M r) x).

Notation "r * x" := (module_mult _ r x) : module_scope.

Delimit Scope module_scope with module.

Local Open Scope rig_scope.

Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f 0 = 0 := pr2 (pr1 (pr2 f)).

Local Close Scope rig_scope.

Local Open Scope module.

Definition module_mult_0_to_0 {R : rng} {M : module R} (x : M) : rngunel1 * x = @unel M.
Proof.
   unfold module_mult. cbn.
   assert (pr2module M rngunel1 = @rngunel1 (rngofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2module M)).
   - rewrite X.
     reflexivity.
Defined.

(** To construct a module from a left action satisfying four axioms *)

Local Open Scope addmonoid.

Definition mult_isldistr_wrt_grop {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r : R, ∏ x y : G, m r (x + y) = (m r x) + (m r y).

Definition mult_isrdistr_wrt_rngop1 {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r s : R, ∏ x : G, m (op1 r s) x = (m r x) + (m s x).

Definition mult_isrdistr_wrt_rngop2 {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r s : R, ∏ x : G, m (op2 r s) x = m s (m r x).

Definition mult_unel {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ x : G, m rngunel2 x = x.

Local Close Scope addmonoid.

Definition mult_to_rngofendabgr {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (r : R) : rngofendabgr G.
Proof.
    use monoidfunconstr.
    intro x. exact (m r x).
    apply dirprodpair.
    + intros x y. apply ax1.
    + apply (grlcan G (m r (unel G))).
      rewrite runax.
      rewrite <- (ax1 r (unel G) (unel G)).
      rewrite runax.
      apply idpath.
Defined.

Definition mult_to_module_struct {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_rngop1 m)
  (ax3 : mult_isrdistr_wrt_rngop2 m) (ax4 : mult_unel m) : module_struct R G.
Proof.
  split with (λ r : R, mult_to_rngofendabgr ax1 r).
  apply dirprodpair.
  - apply dirprodpair.
    + intros r s.
      use total2_paths2_f.
      * apply funextfun. intro x. apply ax2.
      * apply isapropismonoidfun.
    + use total2_paths2_f.
      * apply funextfun. intro x. change (m rngunel1 x = unel G). apply (grlcan G (m (rngunel1) x)). rewrite runax.
        rewrite <- (ax2 rngunel1 rngunel1 x). rewrite rngrunax1. apply idpath.
      * apply isapropismonoidfun.
  -  apply dirprodpair.
     + intros r s.
       use total2_paths2_f.
       * apply funextfun. intro x. apply ax3.
       * apply isapropismonoidfun.
     + use total2_paths2_f.
       * apply funextfun. intro x. apply ax4.
       * apply isapropismonoidfun.
Defined.

Definition mult_to_module {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_rngop1 m)
  (ax3 : mult_isrdistr_wrt_rngop2 m) (ax4 : mult_unel m) : module R := modulepair G (mult_to_module_struct ax1 ax2 ax3 ax4).

(** (left) R-module homomorphism *)

Definition islinear {R : rng} {M N : module R} (f : M -> N) :=
  ∏ r : R, ∏ x : M, f (r * x) = r * (f x).

Definition linearfun {R : rng} (M N : module R) : UU := ∑ f : M -> N, islinear f.

Definition linearfunpair {R : rng} {M N : module R} (f : M -> N) (is : islinear f) : linearfun M N := tpair _ f is.

Definition pr1linearfun {R : rng} {M N : module R} (f : linearfun M N) : M -> N := pr1 f.

Coercion pr1linearfun : linearfun >-> Funclass.

Definition islinearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) : islinear (funcomp (pr1 f) (pr1 g)).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (pr2 f).
  rewrite (pr2 g).
  apply idpath.
Defined.

Definition linearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) : linearfun M P :=
  tpair _ (funcomp f g) (islinearfuncomp f g).

Definition ismodulefun {R : rng} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (islinear f).

Lemma isapropismodulefun {R : rng} {M N : module R} (f : M -> N) : isaprop (ismodulefun f).
Proof.
   refine (@isofhleveldirprod 1 (isbinopfun f) (islinear f) _ _).
   exact (isapropisbinopfun f).
   apply (impred 1 _). intro r.
   apply (impred 1 _). intro x.
   apply (setproperty N).
Defined.

Definition modulefun {R : rng} (M N : module R) : UU := ∑ f : M -> N, ismodulefun f.

Definition modulefunpair {R : rng} {M N : module R} (f : M -> N) (is : ismodulefun f) : modulefun M N :=
   tpair _ f is.

Definition pr1modulefun {R : rng} {M N : module R} (f : modulefun M N) : M -> N := pr1 f.

Coercion pr1modulefun : modulefun >-> Funclass.

Definition modulefun_to_isbinopfun {R : rng} {M N : module R} (f : modulefun M N) : isbinopfun (pr1modulefun f) := pr1 (pr2 f).

Definition modulefun_to_binopfun {R : rng} {M N : module R} (f : modulefun M N) : binopfun M N :=
  binopfunpair (pr1modulefun f) (modulefun_to_isbinopfun f).

Definition modulefun_to_islinear {R : rng} {M N : module R} (f : modulefun M N): islinear (pr1modulefun f) := pr2 (pr2 f).

Definition modulefun_to_linearfun {R : rng} {M N : module R} (f : modulefun M N) : linearfun M N :=
  linearfunpair f (modulefun_to_islinear f).

Definition modulefun_unel {R : rng} {M N : module R} (f : modulefun M N) : f (unel M) = unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (unel M)).
   rewrite ((modulefun_to_islinear f) rngunel1 (unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.
