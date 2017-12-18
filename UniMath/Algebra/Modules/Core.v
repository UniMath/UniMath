(** Authors Anthony Bordg and Floris van Doorn, February-December 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Foundations.PartD.

(** ** Contents
- The ring of endomorphisms of an abelian group
- Modules (the definition of the small type of R-modules over a ring R)
 - R-module morphisms
  - Linearity
  - [modulefun]
  - Isomorphisms ([moduleiso])
*)

Local Open Scope addmonoid_scope.

(** ** The ring of endomorphisms of an abelian group *)

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
  apply (monoidfuncomp g f).
Defined.

Notation "f + g" := (rngofendabgr_op1 f g) : abgr_scope.

(** The underlying set of the ring of endomorphisms of an abelian group *)

Definition setofendabgr (G : abgr) : hSet :=
   hSetpair (monoidfun G G) (isasetmonoidfun G G).

(** A few access functions *)

Definition pr1setofendabgr {G : abgr} (f : setofendabgr G) : G -> G := pr1 f.

Definition pr2setofendabgr {G : abgr} (f : setofendabgr G) : ismonoidfun (pr1 f) := pr2 f.

Definition setofendabgr_to_isbinopfun {G : abgr} (f : setofendabgr G) :
  isbinopfun (pr1setofendabgr f) := pr1 (pr2 f).

Definition setofendabgr_to_unel {G : abgr} (f : setofendabgr G) : pr1setofendabgr f 0 = 0 :=
  pr2 (pr2setofendabgr f).

(** We endow setofendabgr with the two binary operations defined above *)

Definition setwith2binopofendabgr (G : abgr) : setwith2binop :=
   setwith2binoppair (setofendabgr G) (dirprodpair (rngofendabgr_op1) (rngofendabgr_op2)).

(** rngofendabgr_op1 G and rngofendabgr_op2 G are ring operations *)

(** rngofendabgr_op1 is a monoid operation *)

Local Open Scope abgr_scope.

Lemma isassoc_rngofendabgr_op1 {G : abgr} : isassoc (@rngofendabgr_op1 G).
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
   apply dirprodpair.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
Defined.

Lemma islunit_setofendabgr_un0 {G : abgr} : islunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (lunax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Lemma isrunit_setofendabgr_un0 {G : abgr} : isrunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (runax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Lemma isunit_setofendabgr_un0 {G : abgr} : isunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof. exact (isunitpair islunit_setofendabgr_un0 isrunit_setofendabgr_un0). Defined.

Lemma isunital_rngofendabgr_op1 {G : abgr} : isunital (@rngofendabgr_op1 G).
Proof. exact (isunitalpair setofendabgr_un0 isunit_setofendabgr_un0). Defined.

Lemma ismonoidop_rngofendabgr_op1 {G : abgr} : ismonoidop (@rngofendabgr_op1 G).
Proof. exact (mk_ismonoidop isassoc_rngofendabgr_op1 isunital_rngofendabgr_op1). Defined.

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

Lemma islinv_setofendabgr_inv {G : abgr} :
  islinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grlinvax G).
   - apply isapropismonoidfun.
Defined.

Lemma isrinv_setofendabgr_inv {G : abgr} :
  isrinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grrinvax G).
   - apply isapropismonoidfun.
Defined.

Lemma isinv_setofendabgr_inv {G : abgr} :
  isinv (@rngofendabgr_op1 G) (unel_is (@ismonoidop_rngofendabgr_op1 G)) setofendabgr_inv.
Proof. exact (mk_isinv islinv_setofendabgr_inv isrinv_setofendabgr_inv). Defined.

Definition invstruct_setofendabgr_inv {G : abgr} :
  invstruct (@rngofendabgr_op1 G) ismonoidop_rngofendabgr_op1.
Proof. exact (mk_invstruct (@setofendabgr_inv G) (@isinv_setofendabgr_inv G)). Defined.

Lemma isgrop_rngofendabgr_op1 {G : abgr} : isgrop (@rngofendabgr_op1 G).
Proof. exact (isgroppair ismonoidop_rngofendabgr_op1 invstruct_setofendabgr_inv). Defined.

Lemma iscomm_rngofendabgr_op1 {G : abgr} : iscomm (@rngofendabgr_op1 G).
Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (commax G).
   - apply (isapropismonoidfun).
Defined.

Lemma isabgrop_rngofendabgr_op1 {G : abgr} : isabgrop (@rngofendabgr_op1 G).
Proof. exact (mk_isabgrop isgrop_rngofendabgr_op1 iscomm_rngofendabgr_op1). Defined.

(** rngofendabgr_op2 is a monoid operation *)

Lemma isassoc_rngofendabgr_op2 {G : abgr} : isassoc (@rngofendabgr_op2 G).
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

Lemma islunit_setofendabgr_un1 {G : abgr} : islunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isrunit_setofendabgr_un1 {G : abgr} : isrunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isunit_setofendabgr_un1 {G : abgr} : isunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof. exact (isunitpair islunit_setofendabgr_un1 isrunit_setofendabgr_un1). Defined.

Lemma isunital_rngofendabgr_op2 {G : abgr} : isunital (@rngofendabgr_op2 G).
Proof. exact (isunitalpair setofendabgr_un1 isunit_setofendabgr_un1). Defined.

Lemma ismonoidop_rngofendabgr_op2 {G : abgr} : ismonoidop (@rngofendabgr_op2 G).
Proof. exact (mk_ismonoidop isassoc_rngofendabgr_op2 isunital_rngofendabgr_op2). Defined.

(** rngofendabgr_op2 is distributive over rngofendabgr_op1 *)

Lemma isldistr_setofendabgr_op {G : abgr} :
  isldistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (setofendabgr_to_isbinopfun h).
   - apply isapropismonoidfun.
Defined.

Lemma isrdistr_setofendabgr_op {G : abgr} :
  isrdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Lemma isdistr_setofendabgr_op {G : abgr} :
  isdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof. exact (dirprodpair isldistr_setofendabgr_op isrdistr_setofendabgr_op). Defined.

Lemma isrngops_setofendabgr_op {G : abgr} :
  isrngops (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
  exact (mk_isrngops isabgrop_rngofendabgr_op1 ismonoidop_rngofendabgr_op2 isdistr_setofendabgr_op).
Defined.

(** The set of endomorphisms of an abelian group is a ring *)

Definition rngofendabgr (G : abgr) : rng :=
  @rngpair (setwith2binopofendabgr G) (@isrngops_setofendabgr_op G).


(** ** Modules: the definition of the small type of R-modules over a ring R  *)

(** A module over R may be defined as a ring homomorphism from R to the ring of
    endomorphisms of an Abelian group (in other words, a ring action on the
    abelian group). An equivalence with the more common axiomatic definition is
    established below.

    In this development, we concern ourselves with left modules. Recall that a
    right module is equivalent to a left module over the opposite ring.
 *)

Definition module_struct (R : rng) (G : abgr) : UU := rngfun R (rngofendabgr G).

Definition module (R : rng) : UU := ∑ G, module_struct R G.

Definition pr1module {R : rng} (M : module R) : abgr := pr1 M.

Coercion pr1module : module >-> abgr.

Definition pr2module {R : rng} (M : module R) : module_struct R (pr1module M) := pr2 M.

Identity Coercion id_module_struct : module_struct >-> rngfun.

Definition modulepair {R : rng} (G : abgr) (f : module_struct R G) : module R := tpair _ G f.

(** The ring action gives rise to a notion of multiplication. *)

Definition module_mult {R : rng} (M : module R) : R -> M -> M :=
  λ r : R, λ x : M, (pr1setofendabgr (pr2module M r) x).

Notation "r * x" := (module_mult _ r x) : module_scope.

Delimit Scope module_scope with module.

Local Open Scope rig_scope.

Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f 0 = 0 := pr2 (pr1 (pr2 f)).

Local Close Scope rig_scope.

Local Open Scope module.

Lemma module_mult_0_to_0 {R : rng} {M : module R} (x : M) : rngunel1 * x = @unel M.
Proof.
   unfold module_mult. cbn.
   assert (pr2module M rngunel1 = @rngunel1 (rngofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2module M)).
   - rewrite X.
     reflexivity.
Defined.

Local Open Scope addmonoid.

Lemma module_mult_is_ldistr {R : rng} {M : module R} (r : R) (x y : M) :
  r * (x + y) = r * x + r * y.
Proof. exact (pr1 (pr2 (pr2module M r)) x y). Defined.

Lemma module_mult_is_rdistr {R : rng} {M : module R} (r s : R) (x : M) :
  (op1 r s) * x = r * x + s * x.
Proof. exact (maponpaths (λ r, pr1setofendabgr r x) (pr1 (pr1 (pr2 (pr2module M))) r s)). Defined.

Lemma module_mult_assoc {R : rng} {M : module R} (r s : R) (x : M) :
  (op2 r s) * x = r * (s * x).
Proof. exact (maponpaths (λ r, pr1setofendabgr r x) (pr1 (pr2 (pr2 (pr2module M))) r s)). Defined.

Lemma module_mult_1 {R : rng} {M : module R} (r : R) : r * unel M = unel M.
Proof. exact (pr2 (pr2 (pr2module M r))). Defined.

Lemma module_mult_unel2 {R : rng} {M : module R} (m : M) : rngunel2 * m = m.
Proof. exact (maponpaths (λ r, pr1setofendabgr r m) (pr2 (pr2 (pr2 (pr2module M))))). Defined.

Lemma module_inv_mult {R : rng} {M : module R} (r : R) (x : M) :
  @grinv _ (r * x) = r * @grinv _ x.
Proof.
  apply grinv_path_from_op_path. now rewrite <- module_mult_is_ldistr, grrinvax, module_mult_1.
Defined.

(* Definition module_mult_neg1 {R : rng} {M : module R} (x : M) : rngminus1 * x = @grinv _ x. *)

(* Definition module_inv_mult_to_inv1 {R : rng} {M : module R} (r : R) (x : M) : *)
(*   @grinv _ (r * x) = rnginv1 r * x. *)

(* Definition module_mult_inv_to_inv1 {R : rng} {M : module R} (r : R) (x : M) : *)
(*   r * @grinv _ x = rnginv1 r * x. *)

(** To construct a module from a left action satisfying four axioms *)

Definition mult_isldistr_wrt_grop {R : rng} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r : R, ∏ x y : G, m r (x + y) = (m r x) + (m r y).

Definition mult_isrdistr_wrt_rngop1 {R : rng} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (op1 r s) x = (m r x) + (m s x).

Definition mult_isrdistr_wrt_rngop2 {R : rng} {G : abgr} (m : R -> G -> G) : UU :=
  ∏ r s : R, ∏ x : G, m (op2 r s) x = m r (m s x).

Definition mult_unel {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ x : G, m rngunel2 x = x.

Local Close Scope addmonoid.

Definition mult_to_rngofendabgr {R : rng} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (r : R) : rngofendabgr G.
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

Definition mult_to_module_struct {R : rng} {G : abgr} {m : R -> G -> G}
           (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_rngop1 m)
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
      * apply funextfun. intro x. change (m rngunel1 x = unel G). apply (grlcan G (m (rngunel1) x)).
        rewrite runax. rewrite <- (ax2 rngunel1 rngunel1 x). rewrite rngrunax1. apply idpath.
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

Definition mult_to_module {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m)
           (ax2 : mult_isrdistr_wrt_rngop1 m) (ax3 : mult_isrdistr_wrt_rngop2 m)
           (ax4 : mult_unel m) : module R := modulepair G (mult_to_module_struct ax1 ax2 ax3 ax4).

(** *** R-module morphisms *)

(** **** Linearity *)

Definition islinear {R : rng} {M N : module R} (f : M -> N) :=
  ∏ r : R, ∏ x : M, f (r * x) = r * (f x).

Definition linearfun {R : rng} (M N : module R) : UU := ∑ f : M -> N, islinear f.

Definition linearfunpair {R : rng} {M N : module R} (f : M -> N) (is : islinear f) :
  linearfun M N := tpair _ f is.

Definition pr1linearfun {R : rng} {M N : module R} (f : linearfun M N) : M -> N := pr1 f.

Coercion pr1linearfun : linearfun >-> Funclass.

Definition linearfun_islinear {R} {M N : module R} (f : linearfun M N) :
  islinear f := pr2 f.

Lemma islinearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  islinear (funcomp f g).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (linearfun_islinear f).
  rewrite (linearfun_islinear g).
  apply idpath.
Defined.

Definition linearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) :
  linearfun M P := tpair _ (funcomp f g) (islinearfuncomp f g).

Lemma isapropislinear {R : rng} {M N : module R} (f : M -> N) :
  isaprop (islinear f).
Proof.
   apply (impred 1 _). intro r.
   apply (impred 1 _). intro x.
   apply (setproperty N).
Defined.

(** The type of linear functions M -> N is a set. *)
Lemma isasetlinearfun {R : rng} (M N : module R) : isaset (linearfun M N).
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

Definition ismodulefun {R : rng} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (islinear f).

Lemma isapropismodulefun {R : rng} {M N : module R} (f : M -> N) :
  isaprop (ismodulefun f).
Proof.
  exact (@isofhleveldirprod 1 (isbinopfun f) (islinear f)
                            (isapropisbinopfun f) (isapropislinear f)).
Defined.

Definition modulefun {R : rng} (M N : module R) : UU := ∑ f : M -> N, ismodulefun f.

Definition modulefunpair {R : rng} {M N : module R} (f : M -> N) (is : ismodulefun f) :
  modulefun M N := tpair _ f is.

Section accessors.
  Context {R : rng} {M N : module R} (f : modulefun M N).

  Definition pr1modulefun : M -> N := pr1 f.
  
  Definition modulefun_ismodulefun : ismodulefun pr1modulefun := pr2 f.
  
  Definition modulefun_to_isbinopfun : isbinopfun pr1modulefun :=
    pr1 modulefun_ismodulefun.

  Definition modulefun_to_binopfun : binopfun M N :=
    binopfunpair pr1modulefun modulefun_to_isbinopfun.

  Definition modulefun_to_islinear : islinear pr1modulefun := pr2 modulefun_ismodulefun.

  Definition modulefun_to_linearfun : linearfun M N :=
    linearfunpair pr1modulefun modulefun_to_islinear.
End accessors.

Coercion pr1modulefun : modulefun >-> Funclass.

Lemma ismodulefun_comp {R} {M N P : module R} (f : modulefun M N) (g : modulefun N P) :
  ismodulefun (g ∘ f)%functions.
Proof.
  exact (dirprodpair (isbinopfuncomp (modulefun_to_binopfun f)
                                     (modulefun_to_binopfun g))
                     (islinearfuncomp (modulefun_to_linearfun f)
                                      (modulefun_to_linearfun g))).
Defined.

Definition modulefun_comp
  {R} {M N P : module R} (f : modulefun M N) (g : modulefun N P) : modulefun M P :=
  (funcomp f g,, ismodulefun_comp f g).

Lemma modulefun_unel {R : rng} {M N : module R} (f : modulefun M N) : f (unel M) = unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (unel M)).
   rewrite ((modulefun_to_islinear f) rngunel1 (unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.

Definition modulefun_to_monoidfun {R : rng} {M N : module R} (f : modulefun M N) :
  monoidfun (abgrtoabmonoid (pr1module M)) (abgrtoabmonoid (pr1module N)) :=
tpair _ (pr1 f) (tpair _ (pr1 (pr2 f)) (modulefun_unel f)).

Definition modulefun_from_monoidfun {R : rng} {M N : module R} (f : monoidfun M N)
          (H : ismodulefun (pr1 f)) : modulefun M N :=
(tpair _ (pr1 f) H).

Lemma modulefun_paths {R : rng} {M N : module R} {f g : modulefun M N} (p : pr1 f ~ pr1 g) :
  f = g.
Proof.
  use total2_paths_f.
  - apply funextfun. exact p.
  - use proofirrelevance. use isapropismodulefun.
Defined.

(** The type of module morphisms M -> N is a set. *)
Lemma isasetmodulefun {R : rng} (M N : module R) : isaset (modulefun M N).
Proof.
  intros. apply (isasetsubset (@pr1modulefun R M N)).
  - change (isofhlevel 2 (M -> N)).
    apply impred. intro.
    apply (setproperty N).
  - refine (isinclpr1 _ _). intro.
    apply isapropismodulefun.
Defined.

(* categorical structure of modules *)
Lemma modulehombinop_ismodulefun {R : rng} {M N : module R} (f g : modulefun M N) :
  @ismodulefun R M N (λ x : pr1 M, (pr1 f x * pr1 g x)%multmonoid).
Proof.
  - use tpair.
    exact (pr1 (abmonoidshombinop_ismonoidfun (modulefun_to_monoidfun f)
                                              (modulefun_to_monoidfun g))).
    intros r m. rewrite (pr2 (pr2 f)). rewrite (pr2 (pr2 g)).
    rewrite <- module_mult_is_ldistr. reflexivity.
Defined.

Definition modulehombinop {R : rng} {M N : module R} : binop (modulefun M N) :=
  (λ f g, modulefunpair _ (modulehombinop_ismodulefun f g)).

Lemma unelmodulefun_ismodulefun {R : rng} (M N : module R) : ismodulefun (λ x : M, (unel N)).
Proof.
  use tpair.
  - use mk_isbinopfun. intros m m'. use pathsinv0. use lunax.
  - intros r m. rewrite module_mult_1. reflexivity.
Qed.

Definition unelmodulefun {R : rng} (M N : module R) : modulefun M N :=
  modulefunpair _ (unelmodulefun_ismodulefun M N).

Lemma modulebinop_runax {R : rng} {M N : module R} (f : modulefun M N) :
  modulehombinop f (unelmodulefun M N) = f.
Proof.
  use modulefun_paths. intros x. use (runax N).
Qed.

Lemma modulebinop_lunax {R : rng} {M N : module R} (f : modulefun M N) :
  modulehombinop (unelmodulefun M N) f = f.
Proof.
  use modulefun_paths. intros x. use (lunax N).
Qed.

Lemma modulehombinop_assoc {R : rng} {M N : module R} (f g h : modulefun M N) :
  modulehombinop (modulehombinop f g) h = modulehombinop f (modulehombinop g h).
Proof.
  use modulefun_paths. intros x. use assocax.
Qed.

Lemma modulehombinop_comm {R : rng} {M N : module R} (f g : modulefun M N) :
  modulehombinop f g = modulehombinop g f.
Proof.
  use modulefun_paths. intros x. use (commax N).
Qed.

Lemma modulehomabmodule_ismoduleop {R : rng} {M N : module R} :
  ismonoidop (λ f g : modulefun M N, modulehombinop f g).
Proof.
  use mk_ismonoidop.
  - intros f g h. exact (modulehombinop_assoc f g h).
  - use isunitalpair.
    + exact (unelmodulefun M N).
    + use isunitpair.
      * intros f. exact (modulebinop_lunax f).
      * intros f. exact (modulebinop_runax f).
Defined.

Lemma modulehombinop_inv_ismodulefun {R : rng} {M N : module R} (f : modulefun M N) :
  ismodulefun (λ m : M, grinv N (pr1 f m)).
Proof.
  use tpair.
  - use mk_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 (pr1module N))). use (grinvop N).
  - intros r m. rewrite <- module_inv_mult. apply maponpaths.
    apply (pr2 f).
Qed.

Definition modulehombinop_inv {R : rng} {M N : module R} (f : modulefun M N) : modulefun M N :=
  tpair _ _ (modulehombinop_inv_ismodulefun f).

Lemma modulehombinop_linvax {R : rng} {M N : module R} (f : modulefun M N) :
  modulehombinop (modulehombinop_inv f) f = unelmodulefun M N.
Proof.
  use modulefun_paths. intros x. use (@grlinvax N).
Qed.

Lemma modulehombinop_rinvax {R : rng} {M N : module R} (f : modulefun M N) :
  modulehombinop f (modulehombinop_inv f) = unelmodulefun M N.
Proof.
  use modulefun_paths. intros x. use (grrinvax N).
Qed.

Lemma modulehomabgr_isabgrop {R : rng} (M N : module R) :
  isabgrop (λ f g : modulefun M N, modulehombinop f g).
Proof.
  use mk_isabgrop.
  use mk_isgrop.
  - use modulehomabmodule_ismoduleop.
  - use mk_invstruct.
    + intros f. exact (modulehombinop_inv f).
    + use mk_isinv.
      * intros f. exact (modulehombinop_linvax f).
      * intros f. exact (modulehombinop_rinvax f).
  - intros f g. exact (modulehombinop_comm f g).
Defined.

Definition modulehomabgr {R : rng} (M N : module R) : abgr.
Proof.
  use abgrpair.
  use setwithbinoppair.
  use hSetpair.
  - exact (modulefun M N).
  - exact (isasetmodulefun M N).
  - exact (@modulehombinop R M N).
  - exact (modulehomabgr_isabgrop M N).
Defined.

Definition modulehombinop_scalar_ismodulefun {R : commrng} {M N : module R} (r : R)
           (f : modulefun M N) : ismodulefun (λ m : M, r * (pr1 f m)).
Proof.
  use tpair.
  - use mk_isbinopfun. intros x x'. cbn.
    rewrite (pr1 (pr2 f)). rewrite module_mult_is_ldistr. reflexivity.
  - intros r0 m. rewrite (pr2 (pr2 f)). do 2 rewrite <- module_mult_assoc.
    rewrite rngcomm2. reflexivity.
Qed.

Definition modulehombinop_smul {R : commrng} {M N : module R} (r : R) (f : modulefun M N) :
  modulefun M N :=
modulefunpair _ (modulehombinop_scalar_ismodulefun r f).

Definition modulehommodule {R : commrng} (M N : module R) : module R.
Proof.
  use modulepair.
  use (modulehomabgr M N).
  use mult_to_module_struct.
  exact modulehombinop_smul.
  - intros r f g. use modulefun_paths. intros x. apply module_mult_is_ldistr.
  - intros r r0 f. use modulefun_paths. intros x. apply module_mult_is_rdistr.
  - intros r r0 f. use modulefun_paths. intros x. apply module_mult_assoc.
  - intros f. use modulefun_paths. intros x. cbn. apply module_mult_unel2.
Defined.

(** **** Isomorphisms ([moduleiso]) *)

Definition moduleiso {R : rng} (M N : module R) : UU :=
  ∑ w : pr1module M ≃ pr1module N, ismodulefun w.

Section accessors_moduleiso.
  Context {R : rng} {M N : module R} (f : moduleiso M N).

  Definition moduleiso_to_weq : (pr1module M) ≃ (pr1module N) := pr1 f.
  Definition moduleiso_ismodulefun : ismodulefun moduleiso_to_weq := pr2 f.
  Definition moduleiso_to_modulefun : modulefun M N :=
    (tpair _ (pr1weq moduleiso_to_weq) (pr2 f)).
End accessors_moduleiso.

Coercion moduleiso_to_weq : moduleiso >-> weq.
Coercion moduleiso_to_modulefun : moduleiso >-> modulefun.

Definition mk_moduleiso {R} {M N : module R} f is : moduleiso M N := tpair _ f is.

Lemma isbinopfuninvmap {R} {M N : module R} (f : moduleiso M N) :
  isbinopfun (invmap f).
Proof.
   intros x y.
   apply (invmaponpathsweq f).
   rewrite (homotweqinvweq f (op x y)).
   symmetry.
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
   symmetry.
   apply (pr2 (moduleiso_ismodulefun f) r (invmap f x)).
Defined.

Definition invmoduleiso {R} {M N : module R} (f : moduleiso M N) : moduleiso N M.
Proof.
   use mk_moduleiso.
   - exact (invweq f).
   - apply dirprodpair.
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
   - apply dirprodpair.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
Defined.

Lemma moduleiso'_to_moduleiso_isweq {R} (M N : module R) :
  isweq (moduleiso'_to_moduleiso M N).
Proof.
  use (gradth _ (moduleiso_to_moduleiso' M N)).
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

Definition moduleiso'_to_moduleiso_weq {R} (M N : module R) : (moduleiso' M N) ≃ (moduleiso M N) :=
   weqpair (moduleiso'_to_moduleiso M N) (moduleiso'_to_moduleiso_isweq M N).
