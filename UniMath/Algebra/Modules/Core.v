(** Authors Anthony Bordg and Floris van Doorn, February-December 2017 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Monoids.

(** ** Contents
- The ring of endomorphisms of an abelian group
- Modules (the definition of the small type of R-modules over a ring R)
 - R-module morphisms
  - Linearity
  - [modulefun]
  - R-module homomorphisms form an R-module
  - Isomorphisms ([moduleiso])
*)

Local Open Scope addmonoid_scope.
Import UniMath.Algebra.Monoids.AddNotation.

(** ** The ring of endomorphisms of an abelian group *)

(** Two binary operations on the set of endomorphisms of an abelian group *)

Definition monoidfun_to_isbinopfun {G : abgr} (f : monoidfun G G) : isbinopfun f := pr1 (pr2 f).

Definition ringofendabgr_op1 {G: abgr} : binop (monoidfun G G).
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

Definition ringofendabgr_op2 {G : abgr} : binop (monoidfun G G).
Proof.
  intros f g.
  apply (monoidfuncomp g f).
Defined.

(* Declare Scope abgr_scope. *)
Notation "f + g" := (ringofendabgr_op1 f g) : abgr_scope.

(** The underlying set of the ring of endomorphisms of an abelian group *)

Definition setofendabgr (G : abgr) : hSet :=
   make_hSet (monoidfun G G) (isasetmonoidfun G G).

(** A few access functions *)

Definition pr1setofendabgr {G : abgr} (f : setofendabgr G) : G -> G := pr1 f.

Definition pr2setofendabgr {G : abgr} (f : setofendabgr G) : ismonoidfun (pr1 f) := pr2 f.

Definition setofendabgr_to_isbinopfun {G : abgr} (f : setofendabgr G) :
  isbinopfun (pr1setofendabgr f) := pr1 (pr2 f).

Definition setofendabgr_to_unel {G : abgr} (f : setofendabgr G) : pr1setofendabgr f 0 = 0 :=
  pr2 (pr2setofendabgr f).

(** We endow setofendabgr with the two binary operations defined above *)

Definition setwith2binopofendabgr (G : abgr) : setwith2binop :=
   make_setwith2binop (setofendabgr G) (make_dirprod (ringofendabgr_op1) (ringofendabgr_op2)).

(** ringofendabgr_op1 G and ringofendabgr_op2 G are ring operations *)

(** ringofendabgr_op1 is a monoid operation *)

Local Open Scope abgr_scope.

Lemma isassoc_ringofendabgr_op1 {G : abgr} : isassoc (@ringofendabgr_op1 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro.
     apply (pr2 G).
   - apply isapropismonoidfun.
Defined.

Lemma setofendabgr_un0 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).
   apply make_dirprod.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
Defined.

Lemma islunit_setofendabgr_un0 {G : abgr} : islunit (@ringofendabgr_op1 G) setofendabgr_un0.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (lunax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Lemma isrunit_setofendabgr_un0 {G : abgr} : isrunit (@ringofendabgr_op1 G) setofendabgr_un0.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (runax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Lemma isunit_setofendabgr_un0 {G : abgr} : isunit (@ringofendabgr_op1 G) setofendabgr_un0.
Proof. exact (make_isunit islunit_setofendabgr_un0 isrunit_setofendabgr_un0). Defined.

Lemma isunital_ringofendabgr_op1 {G : abgr} : isunital (@ringofendabgr_op1 G).
Proof. exact (make_isunital setofendabgr_un0 isunit_setofendabgr_un0). Defined.

Lemma ismonoidop_ringofendabgr_op1 {G : abgr} : ismonoidop (@ringofendabgr_op1 G).
Proof. exact (make_ismonoidop isassoc_ringofendabgr_op1 isunital_ringofendabgr_op1). Defined.

Local Close Scope abgr_scope.

(** ringofendabgr_op1 is a group operation *)

Definition setofendabgr_inv {G : abgr} : monoidfun G G -> monoidfun G G.
Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1setofendabgr f x))).
   apply make_dirprod.
   - intros x x'.
     rewrite (setofendabgr_to_isbinopfun f).
     rewrite (grinvop G).
     apply (commax G).
   - rewrite (setofendabgr_to_unel f).
     apply (grinvunel G).
Defined.

Local Open Scope abgr_scope.

Lemma islinv_setofendabgr_inv {G : abgr} :
  islinv (@ringofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grlinvax G).
   - apply isapropismonoidfun.
Defined.

Lemma isrinv_setofendabgr_inv {G : abgr} :
  isrinv (@ringofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grrinvax G).
   - apply isapropismonoidfun.
Defined.

Lemma isinv_setofendabgr_inv {G : abgr} :
  isinv (@ringofendabgr_op1 G) (unel_is (@ismonoidop_ringofendabgr_op1 G)) setofendabgr_inv.
Proof. exact (make_isinv islinv_setofendabgr_inv isrinv_setofendabgr_inv). Defined.

Definition invstruct_setofendabgr_inv {G : abgr} :
  invstruct (@ringofendabgr_op1 G) ismonoidop_ringofendabgr_op1.
Proof. exact (make_invstruct (@setofendabgr_inv G) (@isinv_setofendabgr_inv G)). Defined.

Lemma isgrop_ringofendabgr_op1 {G : abgr} : isgrop (@ringofendabgr_op1 G).
Proof. exact (make_isgrop ismonoidop_ringofendabgr_op1 invstruct_setofendabgr_inv). Defined.

Lemma iscomm_ringofendabgr_op1 {G : abgr} : iscomm (@ringofendabgr_op1 G).
Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (commax G).
   - apply (isapropismonoidfun).
Defined.

Lemma isabgrop_ringofendabgr_op1 {G : abgr} : isabgrop (@ringofendabgr_op1 G).
Proof. exact (make_isabgrop isgrop_ringofendabgr_op1 iscomm_ringofendabgr_op1). Defined.

(** ringofendabgr_op2 is a monoid operation *)

Lemma isassoc_ringofendabgr_op2 {G : abgr} : isassoc (@ringofendabgr_op2 G).
Proof.
  intros f g h.
  use total2_paths_f.
  - apply funcomp_assoc.
  - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un1 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (idfun G)).
   apply make_dirprod.
   - intros x x'. reflexivity.
   - reflexivity.
Defined.

Lemma islunit_setofendabgr_un1 {G : abgr} : islunit (@ringofendabgr_op2 G) setofendabgr_un1.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isrunit_setofendabgr_un1 {G : abgr} : isrunit (@ringofendabgr_op2 G) setofendabgr_un1.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isunit_setofendabgr_un1 {G : abgr} : isunit (@ringofendabgr_op2 G) setofendabgr_un1.
Proof. exact (make_isunit islunit_setofendabgr_un1 isrunit_setofendabgr_un1). Defined.

Lemma isunital_ringofendabgr_op2 {G : abgr} : isunital (@ringofendabgr_op2 G).
Proof. exact (make_isunital setofendabgr_un1 isunit_setofendabgr_un1). Defined.

Lemma ismonoidop_ringofendabgr_op2 {G : abgr} : ismonoidop (@ringofendabgr_op2 G).
Proof. exact (make_ismonoidop isassoc_ringofendabgr_op2 isunital_ringofendabgr_op2). Defined.

(** ringofendabgr_op2 is distributive over ringofendabgr_op1 *)

Lemma isldistr_setofendabgr_op {G : abgr} :
  isldistr (@ringofendabgr_op1 G) (@ringofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (setofendabgr_to_isbinopfun h).
   - apply isapropismonoidfun.
Defined.

Lemma isrdistr_setofendabgr_op {G : abgr} :
  isrdistr (@ringofendabgr_op1 G) (@ringofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isdistr_setofendabgr_op {G : abgr} :
  isdistr (@ringofendabgr_op1 G) (@ringofendabgr_op2 G).
Proof. exact (make_dirprod isldistr_setofendabgr_op isrdistr_setofendabgr_op). Defined.

Lemma isringops_setofendabgr_op {G : abgr} :
  isringops (@ringofendabgr_op1 G) (@ringofendabgr_op2 G).
Proof.
  exact (make_isringops isabgrop_ringofendabgr_op1 ismonoidop_ringofendabgr_op2 isdistr_setofendabgr_op).
Defined.

(** The set of endomorphisms of an abelian group is a ring *)

Definition ringofendabgr (G : abgr) : ring :=
  @make_ring (setwith2binopofendabgr G) (@isringops_setofendabgr_op G).


(** ** Modules: the definition of the small type of R-modules over a ring R  *)

(** A module over R may be defined as a ring homomorphism from R to the ring of
    endomorphisms of an Abelian group (in other words, a ring action on the
    abelian group). An equivalence with the more common axiomatic definition is
    established below.

    In this development, we concern ourselves with left modules. Recall that a
    right module is equivalent to a left module over the opposite ring.
 *)

Definition module_struct (R : ring) (G : abgr) : UU := ringfun R (ringofendabgr G).

Definition module (R : ring) : UU := ∑ G, module_struct R G.

Definition pr1module {R : ring} (M : module R) : abgr := pr1 M.

Coercion pr1module : module >-> abgr.

Definition pr2module {R : ring} (M : module R) : module_struct R (pr1module M) := pr2 M.

Identity Coercion id_module_struct : module_struct >-> ringfun.

Definition make_module {R : ring} (G : abgr) (f : module_struct R G) : module R := tpair _ G f.

Lemma isasetmodule {R : ring} (M : module R) : isaset M.
Proof.
  exact (pr2 (pr1 (pr1 (pr1 M)))).
Defined.

(** The ring action gives rise to a notion of multiplication. *)

Definition module_mult {R : ring} (M : module R) : R -> M -> M :=
  λ r : R, λ x : M, (pr1setofendabgr (pr2module M r) x).

(* Declare Scope module_scope. *)
Notation "r * x" := (module_mult _ r x) : module_scope.

Delimit Scope module_scope with module.

Local Open Scope module.

Lemma module_mult_0_to_0 {R : ring} {M : module R} (x : M) : ringunel1 * x = @unel M.
Proof.
   unfold module_mult. cbn.
   assert (pr2module M ringunel1 = @ringunel1 (ringofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2module M)).
   - rewrite X.
     reflexivity.
Defined.

Local Open Scope addmonoid.

Lemma module_mult_is_ldistr {R : ring} {M : module R} (r : R) (x y : M) :
  r * (x + y) = r * x + r * y.
Proof. exact (pr1 (pr2 (pr2module M r)) x y). Defined.

Lemma module_mult_is_rdistr {R : ring} {M : module R} (r s : R) (x : M) :
  (op1 r s) * x = r * x + s * x.
Proof. exact (maponpaths (λ r, pr1setofendabgr r x) (pr1 (pr1 (pr2 (pr2module M))) r s)). Defined.

Lemma module_mult_assoc {R : ring} {M : module R} (r s : R) (x : M) :
  (op2 r s) * x = r * (s * x).
Proof. exact (maponpaths (λ r, pr1setofendabgr r x) (pr1 (pr2 (pr2 (pr2module M))) r s)). Defined.

Lemma module_mult_1 {R : ring} {M : module R} (r : R) : r * unel M = unel M.
Proof. exact (pr2 (pr2 (pr2module M r))). Defined.

Lemma module_mult_unel2 {R : ring} {M : module R} (m : M) : ringunel2 * m = m.
Proof. exact (maponpaths (λ r, pr1setofendabgr r m) (pr2 (pr2 (pr2 (pr2module M))))). Defined.

Lemma module_inv_mult {R : ring} {M : module R} (r : R) (x : M) :
  @grinv _ (r * x) = r * @grinv _ x.
Proof.
  apply grinv_path_from_op_path. now rewrite <- module_mult_is_ldistr, grrinvax, module_mult_1.
Defined.

Lemma module_mult_neg1 {R : ring} {M : module R} (x : M) : ringminus1 * x = @grinv _ x.
Proof.
  apply pathsinv0. apply grinv_path_from_op_path.
  refine (maponpaths (λ y, y * ((_ * x)%module))%multmonoid (!(module_mult_unel2 x)) @ _).
  now rewrite <- module_mult_is_rdistr, ringrinvax1, module_mult_0_to_0.
Defined.

Lemma module_inv_mult_to_inv1 {R : ring} {M : module R} (r : R) (x : M) :
  @grinv _ (r * x) = ringinv1 r * x.
Proof.
  apply grinv_path_from_op_path.
  now rewrite <- module_mult_is_rdistr, ringrinvax1, module_mult_0_to_0.
Defined.

Lemma module_mult_inv_to_inv1 {R : ring} {M : module R} (r : R) (x : M) :
  r * @grinv _ x = ringinv1 r * x.
Proof.
  now rewrite <- module_inv_mult_to_inv1, module_inv_mult.
Defined.

(** To construct a module from a left action satisfying four axioms *)

Definition mult_isldistr_wrt_grop {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r : R, ∏ x y : G, m r (x + y) = (m r x) + (m r y).

Definition mult_isrdistr_wrt_ringop1 {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (op1 r s) x = (m r x) + (m s x).

Definition mult_isrdistr_wrt_ringop2 {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (op2 r s) x = m r (m s x).

Definition mult_unel {R : ring} {G : abgr} (m : R -> G -> G) : UU := ∏ x : G, m ringunel2 x = x.

Local Close Scope addmonoid.

Definition mult_to_ringofendabgr {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (r : R) : ringofendabgr G.
Proof.
    use monoidfunconstr.
    intro x. exact (m r x).
    apply make_dirprod.
    + intros x y. apply ax1.
    + apply (grlcan G (m r (unel G))).
      rewrite runax.
      rewrite <- (ax1 r (unel G) (unel G)).
      rewrite runax.
      apply idpath.
Defined.

Definition mult_to_module_struct {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_ringop1 m)
           (ax3 : mult_isrdistr_wrt_ringop2 m) (ax4 : mult_unel m) : module_struct R G.
Proof.
  split with (λ r : R, mult_to_ringofendabgr ax1 r).
  apply make_dirprod.
  - apply make_dirprod.
    + intros r s.
      use total2_paths2_f.
      * apply funextfun. intro x. apply ax2.
      * apply isapropismonoidfun.
    + use total2_paths2_f.
      * apply funextfun. intro x. change (m ringunel1 x = unel G). apply (grlcan G (m (ringunel1) x)).
        rewrite runax. rewrite <- (ax2 ringunel1 ringunel1 x). rewrite ringrunax1. apply idpath.
      * apply isapropismonoidfun.
  -  apply make_dirprod.
     + intros r s.
       use total2_paths2_f.
       * apply funextfun. intro x. apply ax3.
       * apply isapropismonoidfun.
     + use total2_paths2_f.
       * apply funextfun. intro x. apply ax4.
       * apply isapropismonoidfun.
Defined.

Definition mult_to_module {R : ring} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m)
           (ax2 : mult_isrdistr_wrt_ringop1 m) (ax3 : mult_isrdistr_wrt_ringop2 m)
           (ax4 : mult_unel m) : module R := make_module G (mult_to_module_struct ax1 ax2 ax3 ax4).

(** *** R-module morphisms *)

(** **** Linearity *)

Definition islinear {R : ring} {M N : module R} (f : M -> N) :=
  ∏ r : R, ∏ x : M, f (r * x) = r * (f x).

Definition linearfun {R : ring} (M N : module R) : UU := ∑ f : M -> N, islinear f.

Definition make_linearfun {R : ring} {M N : module R} (f : M -> N) (is : islinear f) :
  linearfun M N := tpair _ f is.

Definition pr1linearfun {R : ring} {M N : module R} (f : linearfun M N) : M -> N := pr1 f.

Coercion pr1linearfun : linearfun >-> Funclass.

Definition linearfun_islinear {R} {M N : module R} (f : linearfun M N) :
  islinear f := pr2 f.

Lemma islinearfuncomp {R : ring} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  islinear (funcomp f g).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (linearfun_islinear f).
  rewrite (linearfun_islinear g).
  apply idpath.
Defined.

Definition linearfuncomp {R : ring} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  linearfun M P := tpair _ (funcomp f g) (islinearfuncomp f g).

Lemma isapropislinear {R : ring} {M N : module R} (f : M -> N) :
  isaprop (islinear f).
Proof.
   apply (impred 1 _). intro r.
   apply (impred 1 _). intro x.
   apply (setproperty N).
Defined.

(** The type of linear functions M -> N is a set. *)
Lemma isasetlinearfun {R : ring} (M N : module R) : isaset (linearfun M N).
Proof.
  intros. apply (isasetsubset (@pr1linearfun R M N)).
  - change (isofhlevel 2 (M -> N)).
    apply impred.
    exact (fun x => setproperty N).
  - refine (isinclpr1 _ _).
    intro.
    apply isapropislinear.
Defined.

(** **** [modulefun] *)

Definition ismodulefun {R : ring} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (islinear f).

Definition make_ismodulefun {R : ring} {M N : module R} {f : M -> N}
           (H1 : isbinopfun f) (H2 : islinear f) : ismodulefun f :=
  tpair _ H1 H2.

Lemma isapropismodulefun {R : ring} {M N : module R} (f : M -> N) :
  isaprop (ismodulefun f).
Proof.
  exact (@isofhleveldirprod 1 (isbinopfun f) (islinear f)
                            (isapropisbinopfun f) (isapropislinear f)).
Defined.

Definition modulefun {R : ring} (M N : module R) : UU := ∑ f : M -> N, ismodulefun f.

Definition make_modulefun {R : ring} {M N : module R} (f : M -> N) (is : ismodulefun f) :
  modulefun M N := tpair _ f is.

Local Notation "R-mod( M , N )" := (modulefun M N) : module_scope.

Section accessors.
  Context {R : ring} {M N : module R} (f : R-mod(M, N)).

  Definition pr1modulefun : M -> N := pr1 f.

  Definition modulefun_ismodulefun : ismodulefun pr1modulefun := pr2 f.

  Definition modulefun_to_isbinopfun : isbinopfun pr1modulefun :=
    pr1 modulefun_ismodulefun.

  Definition modulefun_to_binopfun : binopfun M N :=
    make_binopfun pr1modulefun modulefun_to_isbinopfun.

  Definition modulefun_to_islinear : islinear pr1modulefun := pr2 modulefun_ismodulefun.

  Definition modulefun_to_linearfun : linearfun M N :=
    make_linearfun pr1modulefun modulefun_to_islinear.
End accessors.

Coercion pr1modulefun : modulefun >-> Funclass.

Lemma ismodulefun_comp {R} {M N P : module R} (f : R-mod(M,N)) (g : R-mod(N,P)) :
  ismodulefun (g ∘ f)%functions.
Proof.
  exact (make_dirprod (isbinopfuncomp (modulefun_to_binopfun f)
                                     (modulefun_to_binopfun g))
                     (islinearfuncomp (modulefun_to_linearfun f)
                                      (modulefun_to_linearfun g))).
Defined.

Definition modulefun_comp
  {R} {M N P : module R} (f : R-mod(M, N)) (g : R-mod(N,P)) : R-mod(M,P) :=
  (funcomp f g,, ismodulefun_comp f g).

Lemma modulefun_unel {R : ring} {M N : module R} (f : R-mod(M, N)) : f (unel M) = unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (unel M)).
   rewrite ((modulefun_to_islinear f) ringunel1 (unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.

Definition moduletomonoid  {R : ring} (M : module R) : abmonoid := abgrtoabmonoid (pr1module M).

Definition modulefun_to_monoidfun {R : ring} {M N : module R} (f : R-mod(M, N)) :
  monoidfun (moduletomonoid M) (moduletomonoid N) :=
  tpair _ (pr1 f) (tpair _ (pr1 (pr2 f)) (modulefun_unel f)).

Definition modulefun_from_monoidfun {R : ring} {M N : module R} (f : R-mod(M, N))
           (H : islinear (pr1 f)) : R-mod(M, N) :=
  make_modulefun (pr1 f) (make_ismodulefun (pr1 (pr2 f)) H).

Lemma modulefun_paths {R : ring} {M N : module R} {f g : R-mod(M, N)} (p : pr1 f = pr1 g) :
  f = g.
Proof.
  use total2_paths_f.
  - exact p.
  - use proofirrelevance. use isapropismodulefun.
Defined.

Lemma modulefun_paths2 {R : ring} {M N : module R} {f g : modulefun M N} (p : pr1 f ~ pr1 g) :
  f = g.
Proof. exact (modulefun_paths (funextfun _ _ p)). Defined.

Lemma isasetmodulefun {R : ring} (M N : module R) : isaset (R-mod(M, N)).
Proof.
  intros. apply (isasetsubset (@pr1modulefun R M N)).
  - change (isofhlevel 2 (M -> N)).
    apply impred. intro.
    apply (setproperty N).
  - refine (isinclpr1 _ _). intro.
    apply isapropismodulefun.
Defined.

(* module structure of morphisms between modules *)
Lemma modulehombinop_ismodulefun {R : ring} {M N : module R} (f g : R-mod(M, N)) :
  @ismodulefun R M N (λ x : pr1 M, (pr1 f x * pr1 g x)%multmonoid).
Proof.
  use make_ismodulefun.
  -  exact (pr1 (abmonoidshombinop_ismonoidfun (modulefun_to_monoidfun f)
                                              (modulefun_to_monoidfun g))).
  - intros r m. rewrite (modulefun_to_islinear f). rewrite (modulefun_to_islinear g).
    rewrite <- module_mult_is_ldistr. reflexivity.
Defined.

Definition modulehombinop {R : ring} {M N : module R} : binop (R-mod(M, N)) :=
  (λ f g, make_modulefun _ (modulehombinop_ismodulefun f g)).

Lemma unelmodulefun_ismodulefun {R : ring} (M N : module R) : ismodulefun (λ x : M, (unel N)).
Proof.
  use make_ismodulefun.
  - use make_isbinopfun. intros m m'. use pathsinv0. use lunax.
  - intros r m. rewrite module_mult_1. reflexivity.
Qed.

Definition unelmodulefun {R : ring} (M N : module R) : R-mod(M, N) :=
  make_modulefun _ (unelmodulefun_ismodulefun M N).

Lemma modulebinop_runax {R : ring} {M N : module R} (f : R-mod(M, N)) :
  modulehombinop f (unelmodulefun M N) = f.
Proof.
  use modulefun_paths2. intros x. use (runax N).
Qed.

Lemma modulebinop_lunax {R : ring} {M N : module R} (f : R-mod(M, N)) :
  modulehombinop (unelmodulefun M N) f = f.
Proof.
  use modulefun_paths2. intros x. use (lunax N).
Qed.

Lemma modulehombinop_assoc {R : ring} {M N : module R} (f g h : R-mod(M, N)) :
  modulehombinop (modulehombinop f g) h = modulehombinop f (modulehombinop g h).
Proof.
  use modulefun_paths2. intros x. use assocax.
Qed.

Lemma modulehombinop_comm {R : ring} {M N : module R} (f g : R-mod(M, N)) :
  modulehombinop f g = modulehombinop g f.
Proof.
  use modulefun_paths2. intros x. use (commax N).
Qed.

Lemma modulehomabmodule_ismoduleop {R : ring} {M N : module R} :
  ismonoidop (λ f g : R-mod(M, N), modulehombinop f g).
Proof.
  use make_ismonoidop.
  - intros f g h. exact (modulehombinop_assoc f g h).
  - use make_isunital.
    + exact (unelmodulefun M N).
    + use make_isunit.
      * intros f. exact (modulebinop_lunax f).
      * intros f. exact (modulebinop_runax f).
Defined.

Lemma modulehombinop_inv_ismodulefun {R : ring} {M N : module R} (f : R-mod(M, N)) :
  ismodulefun (λ m : M, grinv N (pr1 f m)).
Proof.
  use tpair.
  - use make_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 (pr1module N))). use (grinvop N).
  - intros r m. rewrite <- module_inv_mult. apply maponpaths.
    apply (pr2 f).
Qed.

Definition modulehombinop_inv {R : ring} {M N : module R} (f : R-mod(M, N)) : R-mod(M, N) :=
  tpair _ _ (modulehombinop_inv_ismodulefun f).

Lemma modulehombinop_linvax {R : ring} {M N : module R} (f : R-mod(M, N)) :
  modulehombinop (modulehombinop_inv f) f = unelmodulefun M N.
Proof.
  use modulefun_paths2. intros x. use (@grlinvax N).
Qed.

Lemma modulehombinop_rinvax {R : ring} {M N : module R} (f : R-mod(M, N)) :
  modulehombinop f (modulehombinop_inv f) = unelmodulefun M N.
Proof.
  use modulefun_paths2. intros x. use (grrinvax N).
Qed.

Lemma modulehomabgr_isabgrop {R : ring} (M N : module R) :
  isabgrop (λ f g : R-mod(M, N), modulehombinop f g).
Proof.
  use make_isabgrop.
  use make_isgrop.
  - use modulehomabmodule_ismoduleop.
  - use make_invstruct.
    + intros f. exact (modulehombinop_inv f).
    + use make_isinv.
      * intros f. exact (modulehombinop_linvax f).
      * intros f. exact (modulehombinop_rinvax f).
  - intros f g. exact (modulehombinop_comm f g).
Defined.

Definition modulehomabgr {R : ring} (M N : module R) : abgr.
Proof.
  use make_abgr.
  use make_setwithbinop.
  use make_hSet.
  - exact (R-mod(M, N)).
  - exact (isasetmodulefun M N).
  - exact (@modulehombinop R M N).
  - exact (modulehomabgr_isabgrop M N).
Defined.

Definition modulehombinop_scalar_ismodulefun {R : commring} {M N : module R} (r : R)
           (f : R-mod(M, N)) : ismodulefun (λ m : M, r * (pr1 f m)).
Proof.
  use tpair.
  - use make_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite module_mult_is_ldistr. reflexivity.
  - intros r0 m. rewrite (modulefun_to_islinear f). do 2 rewrite <- module_mult_assoc.
    rewrite ringcomm2. reflexivity.
Qed.

Definition modulehombinop_smul {R : commring} {M N : module R} (r : R) (f : R-mod(M, N)) :
  modulefun M N :=
  make_modulefun _ (modulehombinop_scalar_ismodulefun r f).

Definition modulehommodule {R : commring} (M N : module R) : module R.
Proof.
  use make_module.
  use (modulehomabgr M N).
  use mult_to_module_struct.
  exact modulehombinop_smul.
  - intros r f g. use modulefun_paths2. intros x. apply module_mult_is_ldistr.
  - intros r r0 f. use modulefun_paths2. intros x. apply module_mult_is_rdistr.
  - intros r r0 f. use modulefun_paths2. intros x. apply module_mult_assoc.
  - intros f. use modulefun_paths2. intros x. cbn. apply module_mult_unel2.
Defined.

(** **** Isomorphisms ([moduleiso]) *)

Definition moduleiso {R : ring} (M N : module R) : UU :=
  ∑ w : pr1module M ≃ pr1module N, ismodulefun w.

Section accessors_moduleiso.
  Context {R : ring} {M N : module R} (f : moduleiso M N).

  Definition moduleiso_to_weq : (pr1module M) ≃ (pr1module N) := pr1 f.
  Definition moduleiso_ismodulefun : ismodulefun moduleiso_to_weq := pr2 f.
  Definition moduleiso_to_modulefun : R-mod(M, N) :=
    (tpair _ (pr1weq moduleiso_to_weq) (pr2 f)).
End accessors_moduleiso.

Coercion moduleiso_to_weq : moduleiso >-> weq.
Coercion moduleiso_to_modulefun : moduleiso >-> modulefun.

Definition make_moduleiso {R} {M N : module R} f is : moduleiso M N := tpair _ f is.

Lemma isbinopfuninvmap {R} {M N : module R} (f : moduleiso M N) :
  isbinopfun (invmap f).
Proof.
   intros x y.
   apply (invmaponpathsweq f).
   rewrite (homotweqinvweq f (op x y)).
   apply pathsinv0.
   transitivity (op ((moduleiso_to_weq f) (invmap f x)) ((moduleiso_to_weq f) (invmap f y))).
   apply (modulefun_to_isbinopfun f (invmap f x) (invmap f y)).
   rewrite 2 (homotweqinvweq f).
   apply idpath.
Defined.

Lemma islinearinvmap {R} {M N : module R} (f : moduleiso M N) : islinear (invmap f).
Proof.
   intros r x.
   apply (invmaponpathsweq f).
   transitivity (module_mult N r x).
   exact (homotweqinvweq f (module_mult N r x)).
   transitivity (module_mult N r (moduleiso_to_weq f (invmap (moduleiso_to_weq f) x))).
   rewrite (homotweqinvweq (moduleiso_to_weq f) x).
   apply idpath.
   apply pathsinv0.
   apply (pr2 (moduleiso_ismodulefun f) r (invmap f x)).
Defined.

Definition invmoduleiso {R} {M N : module R} (f : moduleiso M N) : moduleiso N M.
Proof.
   use make_moduleiso.
   - exact (invweq f).
   - apply make_dirprod.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
Defined.

Definition moduleiso' {R} (M N : module R) : UU :=
  ∑ w : monoidiso (pr1module M) (pr1module N), islinear w.

Lemma moduleiso_to_moduleiso' {R} (M N : module R) :
  moduleiso M N -> moduleiso' M N.
Proof.
   intro w.
   use tpair.
   - use tpair.
     + exact w.
     + use tpair.
       * exact (modulefun_to_isbinopfun w).
       * apply (modulefun_unel w).
   - exact (modulefun_to_islinear w).
Defined.

Lemma moduleiso'_to_moduleiso {R} (M N : module R) :
  moduleiso' M N -> moduleiso M N.
Proof.
   intro w.
   use tpair.
   - exact (pr1 w).
   - apply make_dirprod.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
Defined.

Lemma moduleiso'_to_moduleisweq_iso {R} (M N : module R) :
  isweq (moduleiso'_to_moduleiso M N).
Proof.
  use (isweq_iso _ (moduleiso_to_moduleiso' M N)).
  - intro w.
    unfold moduleiso'_to_moduleiso, moduleiso_to_moduleiso'. cbn.
    induction w as [w1 w2]; cbn.
    use total2_paths_f; cbn.
    * use total2_paths_f; cbn.
      + reflexivity.
      + apply isapropismonoidfun.
    * apply isapropislinear.
 - reflexivity.
Defined.

Definition moduleiso'_to_moduleweq_iso {R} (M N : module R) : (moduleiso' M N) ≃ (moduleiso M N) :=
   make_weq (moduleiso'_to_moduleiso M N) (moduleiso'_to_moduleisweq_iso M N).