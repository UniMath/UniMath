(** Anthony Bordg, February-March 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.Foundations.PartD.


Local Open Scope addmonoid_scope.

(** * The ring of endomorphisms of an abelian group *)

(** The underlying set of the ring of endomorphisms of an abelian group *)

 Definition setofendabgr (G : abgr) : hSet :=
  hSetpair (monoidfun G G) (isasetmonoidfun G G).

(** Two binary operations on the underlying set of the ring of endomorphisms of an abelian group *)

Definition setofendabgr_to_isbinopfun {G : abgr} (f : setofendabgr G) : isbinopfun (pr1 f) := pr1 (pr2 f).

Definition setofendabgr_to_unel {G : abgr} (f : setofendabgr G) : pr1 f 0 = 0 := pr2 (pr2 f).

Definition setofendabgr_op1 {G: abgr} : binop (setofendabgr G).
Proof.
  intros f g.
  apply (@monoidfunconstr _ _ (λ x : G, pr1 f x + pr1 g x)).
  apply tpair.
  - intros x x'.
    rewrite (setofendabgr_to_isbinopfun f).
    rewrite (setofendabgr_to_isbinopfun g).
    apply (abmonoidrer G).
  - rewrite (setofendabgr_to_unel f).
    rewrite (setofendabgr_to_unel g).
    rewrite (lunax G).
    reflexivity.
Defined.

Definition setofendabgr_op2 {G : abgr} : binop (setofendabgr G).
Proof.
  intros f g.
  apply (monoidfuncomp f g).
Defined.

Notation "f + g" := (setofendabgr_op1 f g) : abgr_scope.

(* the composition below uses the diagrammatic order *)
Notation "f ∘ g" := (setofendabgr_op2 f g) : abgr_scope.

Definition setwith2binopofendabgr (G : abgr) : setwith2binop :=
  setwith2binoppair (setofendabgr G) (dirprodpair (setofendabgr_op1) (setofendabgr_op2)).


(** setofendabgr_op1 G and setofendabgr_op2 G are ring operations *)

Local Open Scope abgr_scope.

(** setofendabgr_op1 is a monoid operation *)

 Definition isassoc_setofendabgr_op1 {G : abgr} : isassoc (@op1 (setwith2binopofendabgr G)).
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro.
     cbn.
     apply (pr2 G).
   - apply isapropismonoidfun.
 Defined.

 Definition setofendabgr_un0 {G: abgr} : setofendabgr G.
 Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).
   apply dirprodpair.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
 Defined.

 Definition islunit_setofendabgr_un0 {G : abgr} : islunit (@op1 (setwith2binopofendabgr G)) setofendabgr_un0.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (lunax G (pr1 f x)).
   - apply isapropismonoidfun.
 Defined.

Definition isrunit_setofendabgr_un0 {G : abgr} : isrunit (@op1 (setwith2binopofendabgr G)) setofendabgr_un0.
 Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn .
     apply (runax G (pr1 f x)).
   - apply isapropismonoidfun.
 Defined.

 Definition isunit_setofendabgr_un0 {G : abgr} : isunit (@op1 (setwith2binopofendabgr G)) setofendabgr_un0.
 Proof.
   exact (dirprodpair islunit_setofendabgr_un0 isrunit_setofendabgr_un0).
 Defined.

 Definition isunital_setofendabgr_op1 {G : abgr} : isunital (@op1 (setwith2binopofendabgr G)).
 Proof.
   exact (isunitalpair setofendabgr_un0 isunit_setofendabgr_un0).
 Defined.

 Definition ismonoidop_setofendabgr_op1 {G : abgr} : ismonoidop (@op1 (setwith2binopofendabgr G)) :=
   dirprodpair isassoc_setofendabgr_op1 isunital_setofendabgr_op1.

Local Close Scope abgr_scope.

(** setofendabgr_op1 is a group operation *)

(* The definition below should be moved to Monoids_and_Groups *)

Definition ismonoidfun_abgrinv {G : abgr} : ismonoidfun (grinv G).
 Proof.
   apply dirprodpair.
   - intros x y.
     transitivity (grinv G y + grinv G x).
     exact (grinvop G x y).
     apply (commax G).
   - apply (grinvunel G).
 Defined.

Definition setofendabgr_inv {G : abgr} : setofendabgr G -> setofendabgr G.
 Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1 f x))).
   apply dirprodpair.
   - intros x x'.
     rewrite (setofendabgr_to_isbinopfun f).
     apply (dirprod_pr1 ismonoidfun_abgrinv).
   - rewrite (setofendabgr_to_unel f).
     apply (grinvunel G).
 Defined.

Local Open Scope abgr_scope.

 Definition islinv_setofendabgr_inv {G : abgr} : islinv (@op1 (setwith2binopofendabgr G)) setofendabgr_un0 setofendabgr_inv.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (grlinvax G).
   - apply isapropismonoidfun.
 Defined.

Definition isrinv_setofendabgr_inv {G : abgr} : isrinv (@op1 (setwith2binopofendabgr G)) setofendabgr_un0 setofendabgr_inv.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (grrinvax G).
   - apply isapropismonoidfun.
 Defined.

Definition isinv_setofendabgr_inv {G : abgr} : isinv (@op1 (setwith2binopofendabgr G)) setofendabgr_un0 setofendabgr_inv.
 Proof.
   apply dirprodpair.
   - exact islinv_setofendabgr_inv.
   - exact isrinv_setofendabgr_inv.
 Defined.

 Definition invstruct_setofendabgr_inv {G : abgr} : invstruct (@op1 (setwith2binopofendabgr G)) ismonoidop_setofendabgr_op1 :=
   tpair (λ inv0 : (setofendabgr G) -> (setofendabgr G), isinv setofendabgr_op1 setofendabgr_un0 inv0)
         setofendabgr_inv isinv_setofendabgr_inv.

 Definition isgrop_setofendabgr_op1 {G : abgr} : isgrop (@op1 (setwith2binopofendabgr G)) :=
   tpair (λ is : ismonoidop setofendabgr_op1, invstruct setofendabgr_op1 is) ismonoidop_setofendabgr_op1 invstruct_setofendabgr_inv.

 Definition iscomm_setofendabgr_op1 {G : abgr} : iscomm (@op1 (setwith2binopofendabgr G)).
 Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (commax G).
   - apply (isapropismonoidfun).
 Defined.

Definition isabgrop_setofendabgr_op1 {G : abgr} : isabgrop (@op1 (setwith2binopofendabgr G)) :=
  dirprodpair isgrop_setofendabgr_op1 iscomm_setofendabgr_op1.

(** setofendabgr_op2 is a monoid operation *)

Definition isassoc_setofendabgr_op2 {G : abgr} : isassoc (@op2 (setwith2binopofendabgr G)).
Proof.
  intros f g h.
  use total2_paths_f.
  - apply funcomp_assoc.
  - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un1 {G: abgr} : setofendabgr G.
 Proof.
   apply (@monoidfunconstr _ _ (idfun G)).
   apply dirprodpair.
   - intros x x'.
     reflexivity.
   - reflexivity.
 Defined.

 Definition islunit_setofendabgr_un1 {G : abgr} : islunit (@op2 (setwith2binopofendabgr G)) setofendabgr_un1.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
    Defined.

Definition isrunit_setofendabgr_un1 {G : abgr} : isrunit (@op2 (setwith2binopofendabgr G)) setofendabgr_un1.
 Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
 Defined.

 Definition isunit_setofendabgr_un1 {G : abgr} : isunit (@op2 (setwith2binopofendabgr G)) setofendabgr_un1.
 Proof.
   exact (dirprodpair islunit_setofendabgr_un1 isrunit_setofendabgr_un1).
 Defined.

 Definition isunital_setofendabgr_op2 {G : abgr} : isunital (@op2 (setwith2binopofendabgr G)).
 Proof.
   exact (isunitalpair setofendabgr_un1 isunit_setofendabgr_un1).
 Defined.

 Definition ismonoidop_setofendabgr_op2 {G : abgr} : ismonoidop (@op2 (setwith2binopofendabgr G)) :=
   dirprodpair isassoc_setofendabgr_op2 isunital_setofendabgr_op2.

 (** setofendabgr_op2 is distributive over setofendabgr_op1 *)

 Definition isldistr_setofendabgr_op {G : abgr} : isldistr (@op1 (setwith2binopofendabgr G)) op2.
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
 Defined.

Definition isrdistr_setofendabgr_op {G : abgr} : isrdistr (@op1 (setwith2binopofendabgr G)) op2.
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (setofendabgr_to_isbinopfun h).
   - apply isapropismonoidfun.
 Defined.

 Definition isdistr_setofendabgr_op {G : abgr} : isdistr (@op1 (setwith2binopofendabgr G)) op2 :=
   dirprodpair isldistr_setofendabgr_op isrdistr_setofendabgr_op.

 Definition isrngops_setofendabgr_op {G : abgr} : isrngops (@op1 (setwith2binopofendabgr G)) op2 :=
   dirprodpair (dirprodpair isabgrop_setofendabgr_op1 ismonoidop_setofendabgr_op2) isdistr_setofendabgr_op.

 (** The set of endomorphisms of an abelian group is a ring *)

 Definition rngofendabgr (G : abgr) : rng :=
   rngpair (@isrngops_setofendabgr_op G).

 (** ** The definition of the small type of (left) R-modules over a ring R *)

 Definition module (R : rng) : UU := ∑ G, rngfun R (rngofendabgr G).

 Definition pr1module {R : rng} (M : module R) : abgr := pr1 M.

 Coercion pr1module : module >-> abgr.

 Definition module_struct {R : rng} (G : abgr) : UU := rngfun R (rngofendabgr G).

 (** The multiplication defined from a module *)

 Definition module_mult {R : rng} {M : @module R} : R × M -> M.
 Proof.
   apply uncurry.
   intros r x.
   exact (pr1 (pr2 M r) x).
 Defined.

 Local Open Scope rig_scope.

 Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f 0 = 0 := pr2 (pr1 (pr2 f)).

 Local Close Scope rig_scope.

 Local Open Scope rng_scope.

 Definition module_mult_0_to_0 {R : rng} {M : @module R} (x : M) : module_mult (0,,x) = @unel M.
 Proof.
   unfold module_mult, uncurry.
   cbn.
   assert ((pr2 M) rngunel1 = @rngunel1 (rngofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2 M)).
   - rewrite X.
     cbn.
     reflexivity.
 Defined.


 (** (left) R-module homomorphism *)

 Definition ismodulefun {R : rng} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x))).


 Lemma isapropismodulefun {R : rng} {M N : module R} (f : M -> N) : isaprop (@ismodulefun R M N f).
 Proof.
   refine (@isofhleveldirprod 1 (isbinopfun f) (∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x))) _ _).
   exact (isapropisbinopfun f).
   apply (impred 1 _).
   intro r.
   apply (impred 1 _).
   intro x.
   apply (setproperty N).
 Defined.


 Definition modulefun {R : rng} (M N : module R) := total2 (λ f : M -> N, @ismodulefun R M N f).

 Definition modulefunpair {R : rng} {M N : module R} (f : M -> N) (is : @ismodulefun R M N f) :=
   tpair _ f is.

 Definition islinear {R : rng} {M N : module R} (f : M -> N) :=
   ∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x)).

 Definition modulefun_to_islinear {R : rng} {M N : module R} (f : modulefun M N): islinear (pr1 f) := pr2 (pr2 f).

 Definition modulefun_unel {R : rng} {M N : module R} (f : @modulefun R M N) : pr1 f (@unel M) = @unel N.
 Proof.
   rewrite <- (module_mult_0_to_0 (@unel M)).
   rewrite ((modulefun_to_islinear f) rngunel1 (@unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
 Defined.

 Definition modulefun_to_isbinopfun {R : rng} {M N : module R} (f : modulefun M N) : isbinopfun (pr1 f) := pr1 (pr2 f).

 (** *** The precategory of (left) R-modules and R-modules homomorphisms *)

 Section modules_precategory.

 Definition precategory_ob_mor_module {R: rng} : precategory_ob_mor :=
   precategory_ob_mor_pair (@module R) (λ M N, modulefun M N).

 Local Open Scope Cat.

 Definition modulefun_id {R : rng}: ∏ M : @precategory_ob_mor_module R, M --> M.
 Proof.
   intro M.
   refine (tpair _ (idfun (pr1 M)) _).
   apply dirprodpair.
     - intros x y.
       reflexivity.
     - intros.
       reflexivity.
 Defined.

 Definition modulefun_comp {R : rng} : ∏ M N P : @precategory_ob_mor_module R, M --> N → N --> P → M --> P.
 Proof.
    intros  M N P f g.
    refine (tpair _ (funcomp (pr1 f) (pr1 g)) _).
    apply dirprodpair.
     + intros x y.
       unfold funcomp.
       rewrite <- (modulefun_to_isbinopfun g).
       rewrite <- (modulefun_to_isbinopfun f).
       reflexivity.
     + intros.
       unfold funcomp.
       rewrite (modulefun_to_islinear f).
       rewrite (modulefun_to_islinear g).
       reflexivity.
 Defined.

 Definition precategory_id_comp_module {R : rng} : precategory_id_comp (@precategory_ob_mor_module R).
 Proof.
   apply dirprodpair.
   - exact (modulefun_id).
   - exact (modulefun_comp).
 Defined.

 Definition precategory_data_module {R : rng} : precategory_data :=
   tpair _ (@precategory_ob_mor_module R) (precategory_id_comp_module).

 Definition is_precategory_precategory_data_module {R : rng} : is_precategory (@precategory_data_module R).
 Proof.
   apply dirprodpair.
   - apply dirprodpair.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun.
         intro x.
         reflexivity.
       * apply isapropismodulefun.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun.
         intro x.
         reflexivity.
       * apply isapropismodulefun.
   - intros M N P Q f g h.
     use total2_paths_f.
     + apply funextfun.
       intro x.
       unfold compose.
       cbn.
       rewrite funcomp_assoc.
       reflexivity.
     + apply isapropismodulefun.
 Defined.

 Definition precategory_module (R : rng) : precategory :=
   tpair _ (@precategory_data_module R) (is_precategory_precategory_data_module).

 End modules_precategory.


 (** **** The category of (left) R-modules and R-modules homomorphisms *)

 Section modules_category.

 Variable R : rng.
 Notation "R-mod" := (precategory_module R).

 Definition has_homsets_precategory_module : has_homsets (R-mod).
 Proof.
   intros M N.
   unfold isaset.
   intros f g.
   unfold isaprop.
   apply (isofhlevelweqb 1 (total2_paths_equiv (λ x : pr1 M -> pr1 N, ismodulefun x) f g)).
   refine (isofhleveltotal2 1 _ _ _).
   - assert (p : isofhlevel 2 (pr1 M -> pr1 N)).
     + apply impred.
       intro.
       exact (setproperty (pr1 N)).
     + exact (p (pr1 f) (pr1 g)).
   - intro p.
     assert (q : isaset (@ismodulefun R M N (pr1 g))).
     + exact (isasetaprop (isapropismodulefun (pr1 g))).
     + apply q.
 Defined.

 Definition moduleiso (M N : R-mod) := total2 (λ w : pr1 M ≃ pr1 N, ismodulefun w).

 Definition moduleiso_modulefun {M N : R-mod} : moduleiso M N -> modulefun M N.
 Proof.
   intro f.
   exact (tpair _ (pr1 (pr1 f)) (pr2 f)).
 Defined.

 Coercion moduleiso_modulefun : moduleiso >-> modulefun.

 Definition moduleisopair {M N : R-mod} (f : pr1 M ≃ pr1 N) (is : ismodulefun f) : moduleiso M N :=
   tpair _ f is.

 Definition idmoduleiso (M : R-mod) : moduleiso M M.
 Proof.
   use moduleisopair.
   - exact (idweq (pr1 M)).
   - use dirprodpair.
     + intros x y.
       use idpath.
     + intros r x.
       use idpath.
 Defined.

 Definition isbinopfuninvmap {M N : R-mod} (f : moduleiso M N) : isbinopfun (invmap (pr1 f)).
 Proof.
   intros x y.
   apply (invmaponpathsweq (pr1 f)).
   rewrite (homotweqinvweq (pr1 f) (op x y)).
   symmetry.
   transitivity (op (pr1 f (invmap (pr1 f) x)) (pr1 f (invmap (pr1 f) y))).
   apply (modulefun_to_isbinopfun f (invmap (pr1 f) x) (invmap (pr1 f) y)).
   rewrite 2 (homotweqinvweq (pr1 f)).
   reflexivity.
 Defined.

 Definition islinearinvmap {M N : R-mod} (f : moduleiso M N) : islinear (invmap (pr1 f)).
 Proof.
   intros r x.
   induction f as [f is].
   cbn.
   apply (invmaponpathsweq f).
   transitivity (module_mult (r,,x)).
   exact (homotweqinvweq f (@module_mult R N (r,, x))).
   transitivity (module_mult (r,, f(invmap f x))).
   rewrite (homotweqinvweq f x).
   reflexivity.
   symmetry.
   apply (pr2 is r (invmap f x)).
   Defined.

 Definition invmoduleiso {M N : R-mod} (f : moduleiso M N) : moduleiso N M.
 Proof.
   use moduleisopair.
   - exact (invweq (pr1 f)).
   - use dirprodpair.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
 Defined.

 Definition isaprop_islinear {M N : R-mod} {f : (pr1 M) -> (pr1 N)} : isaprop (@islinear R M N f).
 Proof.
   use impred.
   intro r.
   use impred.
   intro x.
   use setproperty.
 Defined.

 Definition moduleiso' (M N : R-mod) : UU :=
   total2 (λ w : monoidiso (pr1 M) (pr1 N), islinear w).

 Definition moduleiso_to_moduleiso' {M N : R-mod} : moduleiso M N -> moduleiso' M N.
 Proof.
   intro w.
   use tpair.
   - use tpair.
     + exact (pr1 w).
     + use tpair.
       * exact (modulefun_to_isbinopfun w).
       * use (modulefun_unel w).
   - exact (modulefun_to_islinear w).
 Defined.

 Definition moduleiso'_to_moduleiso {M N : R-mod} : moduleiso' M N -> moduleiso M N.
 Proof.
   intro w.
   use tpair.
   - exact (pr1 (pr1 w)).
   - use dirprodpair.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
 Defined.

 Lemma modulefun_unel_uniqueness {M N : R-mod} {f : pr1 M -> pr1 N} {is: ismodulefun f} (p : f (@unel (pr1 M)) = @unel (pr1 N)) :
   modulefun_unel (f,,is) = p.
 Proof.
   apply (setproperty (pr1 (pr1 (pr1 N)))).
 Defined.

 Definition moduleiso'_to_moduleiso_isweq {M N : R-mod} : isweq (@moduleiso'_to_moduleiso M N).
 Proof.
   use (gradth _ moduleiso_to_moduleiso').
   intro w.
   induction w as [w is].
   unfold moduleiso'_to_moduleiso, moduleiso_to_moduleiso'.
   cbn.
   induction w as [w is'].
   cbn.
   induction is' as [is'' p].
   cbn.
   rewrite (modulefun_unel_uniqueness p).
   reflexivity.
   intro w.
   induction w as [w is].
   unfold moduleiso_to_moduleiso', moduleiso'_to_moduleiso.
   cbn.
   reflexivity.
   Defined.

 Definition moduleiso'_to_moduleiso_weq {M N : R-mod} : (moduleiso' M N) ≃ (moduleiso M N) :=
   weqpair (@moduleiso'_to_moduleiso M N) moduleiso'_to_moduleiso_isweq.

 Lemma isaset_el_of_setwith2binop {X : setwith2binop} : isaset X.
 Proof.
   intros x y.
   use (setproperty (pr1 X)).
 Defined.

 Lemma isaprop_isrigfun {X Y : rig} (f : X -> Y) : isaprop (isrigfun f).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropismonoidfun.
  - apply isapropismonoidfun.
Defined.

 Lemma isaset_rngfun {X Y : rng} : isaset (rngfun X Y).
 Proof.
   apply (isofhleveltotal2 2).
   - use impred_isaset.
     intro x.
     cbn.
     induction Y as [Y is].
     cbn.
     apply isaset_el_of_setwith2binop.
   - intro f.
     apply (isasetaprop (isaprop_isrigfun f)).
 Defined.

 Definition modules_univalence_weq1 (M N : R-mod) : (M = N) ≃ (M ╝ N) :=
   total2_paths_equiv _ M N.

 Definition modules_univalence_weq2 (M N : R-mod) : (M ╝ N) ≃ (moduleiso' M N).
 Proof.
   use weqbandf.
   - apply abgr_univalence.
   - intro e.
     use invweq.
     induction M as [M f].
     induction N as [N g].
     cbn in e.
     induction e.
     use weqimplimpl.
     + intro i.
       cbn.
       use total2_paths2_f.
       * use funextfun.
         intro r.
         use total2_paths2_f.
           use funextfun.
           intro x.
           exact (i r x).
           apply isapropismonoidfun.
       * apply isaprop_isrigfun.
     + intro i.
       cbn.
       intros r x.
       unfold idmonoidiso.
       cbn.
       cbn in i.
       induction i.
       reflexivity.
     + use isaprop_islinear.
     + use isaset_rngfun.
 Defined.

 Definition modules_univalence_map (M N : R-mod) : (M = N) -> (moduleiso M N).
 Proof.
   intro p.
   induction p.
   exact (idmoduleiso M).
 Defined.

 Definition modules_univalence_map_isweq (M N : R-mod) : isweq (modules_univalence_map M N).
 Proof.
   use isweqhomot.
   - exact (weqcomp (weqcomp (modules_univalence_weq1 M N) (modules_univalence_weq2 M N)) moduleiso'_to_moduleiso_weq).
   - intro p.
     induction p.
     use (pathscomp0 weqcomp_to_funcomp_app).
     use idpath.
   - use weqproperty.
 Defined.

 Definition modules_univalence (M N : R-mod) : (M = N) ≃ (moduleiso M N).
 Proof.
   use weqpair.
   - exact (modules_univalence_map M N).
   - exact (modules_univalence_map_isweq M N).
 Defined.

 (** Equivalence between isomorphisms and moduleiso in R-mod *)

 Lemma iso_isweq {M N : ob R-mod} (f : iso M N) : isweq (pr1 (pr1 f)).
 Proof.
   use (gradth (pr1 (pr1 f))).
   - exact (pr1 (inv_from_iso f)).
   - intro x.
     set (T:= iso_inv_after_iso f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
   - intro y.
     set (T:= iso_after_iso_inv f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
 Defined.

 Lemma iso_moduleiso {M N : ob R-mod} : iso M N -> moduleiso M N.
 Proof.
   intro f.
   use moduleisopair.
   - use weqpair.
     + exact (pr1 (pr1 f)).
     + exact (iso_isweq f).
   - exact (pr2 (pr1 f)).
 Defined.

 Lemma moduleiso_is_iso {M N : ob R-mod} (f : moduleiso M N) : @is_iso R-mod M N (modulefunpair (pr1 (pr1 f)) (pr2 f)).
 Proof.
   apply (is_iso_qinv (C:= R-mod) _ (modulefunpair (pr1 (pr1 (invmoduleiso f))) (pr2 (invmoduleiso f)))).
   split.
   - use total2_paths_f.
     + cbn.
       apply funextfun.
       intro x.
       unfold funcomp, idfun.
       apply homotinvweqweq.
     + apply isapropismodulefun.
   - use total2_paths_f.
     + cbn.
       apply funextfun.
       intro y.
       apply homotweqinvweq.
     + apply isapropismodulefun.
   Defined.

 Lemma moduleiso_iso {M N : ob R-mod} : moduleiso M N -> iso M N.
 Proof.
   intro f.
   use isopair.
   - use tpair.
     + exact (pr1 (pr1 f)).
     + exact (pr2 f).
   - exact (moduleiso_is_iso f).
   Defined.

 Lemma moduleiso_iso_isweq {M N : ob R-mod} : isweq (@moduleiso_iso M N).
 Proof.
   apply (gradth _ iso_moduleiso).
   - intro f.
     apply subtypeEquality.
     + intro w.
       apply isapropismodulefun.
     + unfold moduleiso_iso, iso_moduleiso.
       cbn.
       use total2_paths_f.
       * cbn.
         reflexivity.
       * apply isapropisweq.
   - intro f.
     unfold iso_moduleiso, moduleiso_iso.
     cbn.
     use total2_paths_f.
     + cbn.
       reflexivity.
     + apply isaprop_is_iso.
 Defined.

 Definition moduleiso_iso_weq (M N : R-mod) : (moduleiso M N) ≃ (iso M N) :=
   weqpair moduleiso_iso moduleiso_iso_isweq.

 Definition precategory_module_idtoiso_isweq : ∏ M N : ob R-mod, isweq (fun p : M = N => idtoiso p).
 Proof.
   intros M N.
   use (isweqhomot (weqcomp (modules_univalence M N) (moduleiso_iso_weq M N)) _).
   - intro p.
     induction p.
     use (pathscomp0 weqcomp_to_funcomp_app).
     cbn.
     use total2_paths_f.
     + reflexivity.
     + apply isaprop_is_iso.
   - apply weqproperty.
 Defined.

 Definition precategory_module_is_category : is_category (R-mod).
 Proof.
   apply dirprodpair.
   - exact (precategory_module_idtoiso_isweq).
   - exact (has_homsets_precategory_module).
 Defined.

 Theorem category_module : category.
 Proof.
   use tpair.
   - exact R-mod.
   - exact precategory_module_is_category.
 Defined.


 End modules_category.

 Variable R : rng.
 Local Notation "R-Mod" := (category_module R).