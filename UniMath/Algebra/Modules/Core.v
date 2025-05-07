(**

  Ring Modules

  This file defines the small type of R-modules over a ring R as a ring homomorphism from R to the
  ring of endomorphisms of an abelian group (in other words, a ring action on the abelian group).
  Accessors and a constructor are given to and from the more common axiomatic definition.
  Because a right module is equivalent to a left module over the opposite ring, we restrict
  ourselves to left modules in this file.

  Contents
  1. Modules [module]
  1.1. A module constructor that takes a left action satisfying four axioms [mult_to_module]
  2. R-module morphisms
  2.1 Linearity [islinear] [linearfun]
  2.2 Module morphisms [modulefun]
  2.3 R-module homomorphisms form an R-module [modulehommodule]
  2.4 Isomorphisms [moduleiso]

  Originally written by Anthony Bordg and Floris van Doorn, February-December 2017

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.ModuleCore.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.

Local Open Scope addmonoid.
Local Open Scope abgr.

(** * 1. Modules *)

Definition module_struct (R : ring) (G : abgr) : UU := ringfun R (group_endomorphism_ring G).

Definition module (R : ring) : UU := module_category R.

Coercion pr1module {R : ring} (M : module R) : abgr := pr1 M.

Definition pr2module {R : ring} (M : module R) : module_struct R M := pr2 M.

Identity Coercion id_module_struct : module_struct >-> ringfun.

Definition make_module {R : ring} (G : abgr) (f : module_struct R G) : module R := G ,, f.

(** The ring action gives rise to a notion of multiplication. *)

Definition module_mult {R : ring} (M : module R) : R -> M -> M :=
  λ r : R, λ x : M, (pr2module M r : abelian_group_morphism _ _) x.

Declare Scope module_scope.
Notation "r * x" := (module_mult _ r x) : module_scope.

Delimit Scope module_scope with module.

Local Open Scope module.

Lemma module_mult_0_to_0 {R : ring} {M : module R} (x : M) : ringunel1 * x = @unel M.
Proof.
   unfold module_mult. cbn.
   assert (pr2module M ringunel1 = @ringunel1 (group_endomorphism_ring M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2module M)).
   - rewrite X.
     reflexivity.
Defined.

Local Open Scope addmonoid.

Lemma module_mult_is_ldistr {R : ring} {M : module R} (r : R) (x y : M) :
  r * (x + y) = r * x + r * y.
Proof. exact (monoidfunmul (pr2module M r : abelian_group_morphism _ _) x y). Defined.

Lemma module_mult_is_rdistr {R : ring} {M : module R} (r s : R) (x : M) :
  (r + s)%ring * x = r * x + s * x.
Proof.
  exact (abelian_group_morphism_eq (binopfunisbinopfun (rigaddfun (pr2module M : ringfun _ _)) r s) x).
Defined.

Lemma module_mult_assoc {R : ring} {M : module R} (r s : R) (x : M) :
  (r * s)%ring * x = r * (s * x).
Proof.
  exact (abelian_group_morphism_eq (binopfunisbinopfun (rigmultfun (pr2module M : ringfun _ _)) r s) x).
Defined.

Lemma module_mult_1 {R : ring} {M : module R} (r : R) : r * unel M = unel M.
Proof.
  exact (monoidfununel (pr2module M r : abelian_group_morphism _ _)).
Defined.

Lemma module_mult_unel2 {R : ring} {M : module R} (m : M) : ringunel2 * m = m.
Proof.
  exact (abelian_group_morphism_eq (monoidfununel (rigmultfun (pr2module M : ringfun _ _))) m).
Defined.

Lemma module_inv_mult {R : ring} {M : module R} (r : R) (x : M) :
  -(r * x) = r * -x.
Proof.
  apply grinv_path_from_op_path. now rewrite <- module_mult_is_ldistr, grrinvax, module_mult_1.
Defined.

Lemma module_mult_neg1 {R : ring} {M : module R} (x : M) : ringminus1 * x = -x.
Proof.
  apply pathsinv0. apply grinv_path_from_op_path.
  refine (maponpaths (λ y, y * ((_ * x)%module))%multmonoid (!(module_mult_unel2 x)) @ _).
  now rewrite <- module_mult_is_rdistr, ringrinvax1, module_mult_0_to_0.
Defined.

Lemma module_inv_mult_to_inv1 {R : ring} {M : module R} (r : R) (x : M) :
  -(r * x) = (-r)%ring * x.
Proof.
  apply grinv_path_from_op_path.
  now rewrite <- module_mult_is_rdistr, ringrinvax1, module_mult_0_to_0.
Defined.

Lemma module_mult_inv_to_inv1 {R : ring} {M : module R} (r : R) (x : M) :
  r * -x = (-r)%ring * x.
Proof.
  now rewrite <- module_inv_mult_to_inv1, module_inv_mult.
Defined.

(** ** 1.1. A module constructor that takes a left action satisfying four axioms *)

Definition mult_isldistr_wrt_grop {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r : R, ∏ x y : G, m r (x + y) = (m r x) + (m r y).

Definition mult_isrdistr_wrt_ringop1 {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (r + s)%ring x = (m r x) + (m s x).

Definition mult_isrdistr_wrt_ringop2 {R : ring} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (r * s)%ring x = m r (m s x).

Definition mult_unel {R : ring} {G : abgr} (m : R -> G -> G) : UU := ∏ x : G, m ringunel2 x = x.

Local Close Scope addmonoid.

Definition mult_to_group_endomorphism_ring {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (r : R) : group_endomorphism_ring G.
Proof.
  apply (make_abelian_group_morphism (λ x, m r x)).
  intros x y. apply ax1.
Defined.

Definition mult_to_module_struct_fun {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m)
           : R → group_endomorphism_ring G
           := mult_to_group_endomorphism_ring ax1.

Lemma mult_to_module_struct_ismonoidfun {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_ringop1 m)
           (ax3 : mult_isrdistr_wrt_ringop2 m) (ax4 : mult_unel m)
  : isrigfun (X := R) (Y := group_endomorphism_ring G) (mult_to_module_struct_fun ax1).
Proof.
  apply make_isrigfun.
  - apply make_ismonoidfun.
    + intros r s.
      apply abelian_group_morphism_eq.
      intro x. apply ax2.
    + apply abelian_group_morphism_eq.
      intro x. change (m ringunel1 x = unel G). apply (grlcan G (m (ringunel1) x)).
      rewrite runax. rewrite <- (ax2 ringunel1 ringunel1 x). rewrite ringrunax1. apply idpath.
  - apply make_ismonoidfun.
    + intros r s.
      apply abelian_group_morphism_eq.
      intro x. apply ax3.
    + apply abelian_group_morphism_eq.
      intro x. apply ax4.
Qed.

Definition mult_to_module_struct {R : ring} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_ringop1 m)
           (ax3 : mult_isrdistr_wrt_ringop2 m) (ax4 : mult_unel m)
  : module_struct R G
  := mult_to_module_struct_fun ax1 ,, mult_to_module_struct_ismonoidfun ax1 ax2 ax3 ax4.

Definition mult_to_module {R : ring} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m)
           (ax2 : mult_isrdistr_wrt_ringop1 m) (ax3 : mult_isrdistr_wrt_ringop2 m)
           (ax4 : mult_unel m) : module R := make_module G (mult_to_module_struct ax1 ax2 ax3 ax4).

(** * 2. R-module morphisms *)

(** ** 2.1. Linearity *)

Definition islinear {R : ring} {M N : module R} (f : M -> N) :=
  ∏ r : R, ∏ x : M, f (r * x) = r * (f x).

Definition linearfun {R : ring} (M N : module R) : UU := ∑ f : M -> N, islinear f.

Definition make_linearfun {R : ring} {M N : module R} (f : M -> N) (is : islinear f) :
  linearfun M N := f ,, is.

Definition pr1linearfun {R : ring} {M N : module R} (f : linearfun M N) : M -> N := pr1 f.

Coercion pr1linearfun : linearfun >-> Funclass.

Definition linearfun_islinear {R} {M N : module R} (f : linearfun M N) :
  islinear f := pr2 f.

Lemma islinearfuncomp {R : ring} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  islinear (funcomp f g).
Proof.
  intros r x; simpl.
  rewrite (linearfun_islinear f).
  rewrite (linearfun_islinear g).
  apply idpath.
Defined.

Definition linearfuncomp {R : ring} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  linearfun M P := make_linearfun (funcomp f g) (islinearfuncomp f g).

Lemma isapropislinear {R : ring} {M N : module R} (f : M -> N) :
  isaprop (islinear f).
Proof.
   apply (impred 1 _). intro r.
   apply (impred 1 _). intro x.
   apply (setproperty N).
Defined.

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

(** ** 2.2. Module morphisms *)

Definition ismodulefun {R : ring} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (islinear f).

Definition make_ismodulefun {R : ring} {M N : module R} {f : M -> N}
           (H1 : isbinopfun f) (H2 : islinear f) : ismodulefun f :=
  make_dirprod H1 H2.

Lemma isapropismodulefun {R : ring} {M N : module R} (f : M -> N) :
  isaprop (ismodulefun f).
Proof.
  exact (@isofhleveldirprod 1 (isbinopfun f) (islinear f)
                            (isapropisbinopfun f) (isapropislinear f)).
Defined.

Definition modulefun {R : ring} (M N : module R) : UU := module_category R⟦M, N⟧%cat.

Definition make_modulefun {R : ring} {M N : module R} (f : M -> N) (is : ismodulefun f)
  : modulefun M N.
Proof.
  exists (make_abelian_group_morphism f (pr1 is)).
  abstract (
    intro r;
    apply abelian_group_morphism_eq;
    exact (pr2 is r)
  ).
Defined.

Local Notation "R-mod( M , N )" := (modulefun M N) : module_scope.

Section accessors.
  Context {R : ring} {M N : module R} (f : R-mod(M, N)).

  Definition modulefun_to_abelian_group_morphism : abelian_group_morphism M N := pr1 f.

  Definition modulefun_to_binopfun : binopfun M N := modulefun_to_abelian_group_morphism.

  Definition pr1modulefun : M → N := modulefun_to_binopfun.

  Definition modulefun_to_isbinopfun : isbinopfun pr1modulefun :=
    binopfunisbinopfun modulefun_to_binopfun.

  Lemma modulefun_to_islinear : islinear pr1modulefun.
  Proof.
    intro r.
    exact (abelian_group_morphism_eq (pr2 f r)).
  Qed.

  Definition modulefun_to_linearfun : linearfun M N :=
    make_linearfun pr1modulefun modulefun_to_islinear.

  Definition modulefun_ismodulefun : ismodulefun pr1modulefun
    := make_ismodulefun modulefun_to_isbinopfun modulefun_to_islinear.

End accessors.

Coercion pr1modulefun : modulefun >-> Funclass.

Definition composite_modulefun
  {R} {M N P : module R} (f : R-mod(M, N)) (g : R-mod(N,P)) : R-mod(M,P) := (f · g)%cat.

Definition identity_modulefun
  {R} (M : module R) : R-mod(M, M) := identity M.

Lemma modulefun_unel {R : ring} {M N : module R} (f : R-mod(M, N)) : f (unel M) = unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (unel M)).
   rewrite ((modulefun_to_islinear f) ringunel1 (unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.

Definition moduletomonoid  {R : ring} (M : module R) : abmonoid := abgrtoabmonoid M.

Definition modulefun_to_monoidfun {R : ring} {M N : module R} (f : R-mod(M, N)) :
  monoidfun (moduletomonoid M) (moduletomonoid N) := modulefun_to_abelian_group_morphism f.

Definition modulefun_from_monoidfun {R : ring} {M N : module R} (f : monoidfun M N)
           (H : islinear f) : R-mod(M, N) :=
  make_modulefun f (make_ismodulefun (binopfunisbinopfun f) H).

Lemma modulefun_paths {R : ring} {M N : module R} {f g : R-mod(M, N)} (p : (f : _ → _) = g) :
  f = g.
Proof.
  apply subtypePath.
  {
    intro.
    apply impred_isaprop.
    intro.
    apply homset_property.
  }
  apply abelian_group_morphism_paths.
  exact p.
Qed.

Lemma modulefun_paths2 {R : ring} {M N : module R} {f g : modulefun M N} (p : f ~ g) :
  f = g.
Proof. exact (modulefun_paths (funextfun _ _ p)). Qed.

(** ** 2.3 R-module homomorphisms form an R-module *)

Lemma modulehombinop_ismodulefun {R : ring} {M N : module R} (f g : R-mod(M, N)) :
  @ismodulefun R M N (λ x : M, (f x * g x)%multmonoid).
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
  ismodulefun (λ m : M, -(f m)).
Proof.
  apply make_ismodulefun.
  - apply make_isbinopfun. intros x x'. cbn.
    rewrite binopfunisbinopfun.
    rewrite (commax N).
    apply (grinvop N).
  - intros r m. rewrite <- module_inv_mult. apply maponpaths.
    apply modulefun_to_islinear.
Qed.

Definition modulehombinop_inv {R : ring} {M N : module R} (f : R-mod(M, N)) : R-mod(M, N) :=
  make_modulefun _ (modulehombinop_inv_ismodulefun f).

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
  - exact (homset_property _ M N).
  - exact (@modulehombinop R M N).
  - exact (modulehomabgr_isabgrop M N).
Defined.

Definition modulehombinop_scalar_ismodulefun {R : commring} {M N : module R} (r : R)
           (f : R-mod(M, N)) : ismodulefun (λ m : M, r * f m).
Proof.
  apply make_ismodulefun.
  - apply make_isbinopfun. intros x x'.
    rewrite modulefun_to_isbinopfun. rewrite module_mult_is_ldistr. reflexivity.
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

(** ** 2.4. Isomorphisms *)

Definition moduleiso {R : ring} (M N : module R) : UU :=
  ∑ w : M ≃ N, ismodulefun w.

Section accessors_moduleiso.
  Context {R : ring} {M N : module R} (f : moduleiso M N).

  Definition moduleiso_to_weq : (pr1module M) ≃ (pr1module N) := pr1 f.
  Definition moduleiso_ismodulefun : ismodulefun moduleiso_to_weq := pr2 f.
  Definition moduleiso_to_modulefun : R-mod(M, N) :=
    make_modulefun _ moduleiso_ismodulefun.
End accessors_moduleiso.

Coercion moduleiso_to_weq : moduleiso >-> weq.
Coercion moduleiso_to_modulefun : moduleiso >-> modulefun.

Definition make_moduleiso {R} {M N : module R} f is : moduleiso M N := f ,, is.

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
Qed.

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
  apply (modulefun_to_islinear f).
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
  - use make_monoidiso.
    + exact w.
    + use make_ismonoidfun.
      * exact (modulefun_to_isbinopfun w).
      * apply (modulefun_unel w).
  - exact (modulefun_to_islinear w).
Defined.

Lemma moduleiso'_to_moduleiso {R} (M N : module R) :
  moduleiso' M N -> moduleiso M N.
Proof.
  intro w.
  use make_moduleiso.
  - exact (pr1 w).
  - apply make_dirprod.
    + exact (pr121 w).
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
 - intro y.
  apply (maponpaths (λ x, _ ,, x)).
  apply isapropismodulefun.
Defined.

Definition moduleiso'_to_moduleweq_iso {R} (M N : module R) : (moduleiso' M N) ≃ (moduleiso M N) :=
   make_weq (moduleiso'_to_moduleiso M N) (moduleiso'_to_moduleisweq_iso M N).
