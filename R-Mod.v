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

Definition setrngofend (G : abgr) : hSet :=
  hSetpair (monoidfun G G) (isasetmonoidfun G G).

(** Two binary operations on the underlying set of the ring of endomorphisms of an abelian group *)

Definition setrngofendop1 {G: abgr} : binop (setrngofend G).
Proof.
  intros f g.
  apply (@monoidfunconstr _ _ (λ x : G, pr1 f x + pr1 g x)).
  apply tpair.
  - intros x x'.
    rewrite (pr1 (pr2 f)).
    rewrite (pr1 (pr2 g)).
    apply (abmonoidrer G).
  - rewrite (pr2 (pr2 f)).
    rewrite (pr2 (pr2 g)).
    rewrite (lunax G).
    reflexivity.
Defined.

Definition setrngofendop2 {G : abgr} : binop (setrngofend G).
Proof.
  intros f g.
  apply (monoidfuncomp f g).
Defined.

Notation "f + g" := (setrngofendop1 f g) : abgr_scope.
Notation "g ∘ f" := (setrngofendop2 f g) : abgr_scope.

Definition setwith2binoprngofend (G : abgr) : setwith2binop :=
  setwith2binoppair (setrngofend G) (dirprodpair (setrngofendop1) (setrngofendop2)).


(** setrngofendop1 G and setrngofendop2 G are ring operations *)

Local Open Scope abgr_scope.

(** setrngofendop1 is a monoid operation *)

 Definition isassoc_setrngofendop1 {G : abgr} : isassoc (@op1 (setwith2binoprngofend G)).
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro.
     cbn.
     apply (pr2 G).
   - apply isapropismonoidfun.
 Defined.

 Definition setrngofendun0 {G: abgr} : setrngofend G.
 Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).
   apply dirprodpair.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
 Defined.

 Definition islunit_setrngofendun0 {G : abgr} : islunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (lunax G (pr1 f x)).
   - apply isapropismonoidfun.
 Defined.

Definition isrunit_setrngofendun0 {G : abgr} : isrunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn .
     apply (runax G (pr1 f x)).
   - apply isapropismonoidfun.
 Defined.

 Definition isunit_setrngofendun0 {G : abgr} : isunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   exact (dirprodpair islunit_setrngofendun0 isrunit_setrngofendun0).
 Defined.

 Definition isunital_setrngofendop1 {G : abgr} : isunital (@op1 (setwith2binoprngofend G)).
 Proof.
   exact (isunitalpair setrngofendun0 isunit_setrngofendun0).
 Defined.

 Definition ismonoidop_setrngofendop1 {G : abgr} : ismonoidop (@op1 (setwith2binoprngofend G)) :=
   dirprodpair isassoc_setrngofendop1 isunital_setrngofendop1.

Local Close Scope abgr_scope.

(** setrngofendop1 is a group operation *)

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

Definition setrngofendinv {G : abgr} : setrngofend G -> setrngofend G.
 Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1 f x))).
   apply dirprodpair.
   - intros x x'.
     rewrite (dirprod_pr1 (pr2 f)).
     apply (dirprod_pr1 ismonoidfun_abgrinv).
   - rewrite (dirprod_pr2 (pr2 f)).
     apply (grinvunel G).
 Defined.

Local Open Scope abgr_scope.

 Definition islinv_setrngofendinv {G : abgr} : islinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (grlinvax G).
   - apply isapropismonoidfun.
 Defined.

Definition isrinv_setrngofendinv {G : abgr} : isrinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (grrinvax G).
   - apply isapropismonoidfun.
 Defined.

Definition isinv_setrngofendinv {G : abgr} : isinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   apply dirprodpair.
   - exact islinv_setrngofendinv.
   - exact isrinv_setrngofendinv.
 Defined.

 Definition isinvstruct_setrngofendinv {G : abgr} : invstruct (@op1 (setwith2binoprngofend G)) ismonoidop_setrngofendop1 :=
   tpair (λ inv0 : (setrngofend G) -> (setrngofend G), isinv setrngofendop1 setrngofendun0 inv0)
         setrngofendinv isinv_setrngofendinv.

 Definition isgrop_setrngofendop1 {G : abgr} : isgrop (@op1 (setwith2binoprngofend G)) :=
   tpair (λ is : ismonoidop setrngofendop1, invstruct setrngofendop1 is) ismonoidop_setrngofendop1 isinvstruct_setrngofendinv.

 Definition iscomm_setrngofendop1 {G : abgr} : iscomm (@op1 (setwith2binoprngofend G)).
 Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (commax G).
   - apply (isapropismonoidfun).
 Defined.

Definition isabgrop_setrngofendop1 {G : abgr} : isabgrop (@op1 (setwith2binoprngofend G)) :=
  dirprodpair isgrop_setrngofendop1 iscomm_setrngofendop1.

(** setrngofend_op2 is a monoid operation *)

Definition isassoc_setrngofendop2 {G : abgr} : isassoc (@op2 (setwith2binoprngofend G)).
Proof.
  intros f g h.
  use total2_paths_f.
  - apply funcomp_assoc.
  - apply isapropismonoidfun.
Defined.

Definition setrngofendun1 {G: abgr} : setrngofend G.
 Proof.
   apply (@monoidfunconstr _ _ (idfun G)).
   apply dirprodpair.
   - intros x x'.
     reflexivity.
   - reflexivity.
 Defined.

 Definition islunit_setrngofendun1 {G : abgr} : islunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
    Defined.

Definition isrunit_setrngofendun1 {G : abgr} : isrunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
 Defined.

 Definition isunit_setrngofendun1 {G : abgr} : isunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   exact (dirprodpair islunit_setrngofendun1 isrunit_setrngofendun1).
 Defined.

 Definition isunital_setrngofendop2 {G : abgr} : isunital (@op2 (setwith2binoprngofend G)).
 Proof.
   exact (isunitalpair setrngofendun1 isunit_setrngofendun1).
 Defined.

 Definition ismonoidop_setrngofendop2 {G : abgr} : ismonoidop (@op2 (setwith2binoprngofend G)) :=
   dirprodpair isassoc_setrngofendop2 isunital_setrngofendop2.

 (** setrngofendop2 is distributive over setrngofendop1 *)

 Definition isldistr_setrngofendop {G : abgr} : isldistr (@op1 (setwith2binoprngofend G)) op2.
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     reflexivity.
   - apply isapropismonoidfun.
 Defined.

Definition isrdistr_setrngofendop {G : abgr} : isrdistr (@op1 (setwith2binoprngofend G)) op2.
 Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro x.
     cbn.
     apply (pr1 (pr2 h)).
   - apply isapropismonoidfun.
 Defined.

 Definition isdistr_setrngofendop {G : abgr} : isdistr (@op1 (setwith2binoprngofend G)) op2 :=
   dirprodpair isldistr_setrngofendop isrdistr_setrngofendop.

 Definition isrngops_setrngofendop {G : abgr} : isrngops (@op1 (setwith2binoprngofend G)) op2 :=
   dirprodpair (dirprodpair isabgrop_setrngofendop1 ismonoidop_setrngofendop2) isdistr_setrngofendop.

 (** The set of endomorphisms of an abelian group is a ring *)

 Definition isarng_setrngofend (G : abgr) : rng :=
   rngpair (@isrngops_setrngofendop G).

 (** ** The definition of the small type of (left) R-modules over a ring R *)

 Definition module {R : rng} : UU := ∑ G, rngfun R (isarng_setrngofend G).

 (** The definition of the small type of vector spaces over a field K *)

 Definition VectSp {K : fld} : UU := ∑ G : abgr, rngfun K (isarng_setrngofend G).

 Definition isaVectSp {K : fld} (G : abgr) : UU :=
   rngfun K (isarng_setrngofend G).


 (** from functions returning functions to functions of products *)

 Definition uncurry_for_prod {X Y Z : UU} (f : X -> Y -> Z) : X × Y -> Z.
 Proof.
   intro x.
   exact (f (pr1 x) (pr2 x)).
 Defined.

 (** The multiplication defined from a module *)

 Definition module_mult {R : rng} {M : @module R} : R × pr1 M -> pr1 M.
 Proof.
   apply uncurry_for_prod.
   intros r x.
   exact ((pr1 (pr1 (pr2 M) r)) x).
 Defined.

 Local Open Scope rng_scope.

 Definition module_mult_0_is_0 {R : rng} {M : @module R} : ∏ x : pr1 M, module_mult (0,,x) = @unel (pr1 M).
 Proof.
   intro x.
   unfold module_mult, uncurry_for_prod.
   cbn.
   assert (pr1 (pr2 M) rngunel1 = @rngunel1 (isarng_setrngofend (pr1 M))).
   - exact (pr2 (pr1 (pr2 (pr2 M)))).
   - rewrite X.
     cbn.
     reflexivity.
 Defined.


 (** (left) R-module homomorphism *)

 Definition ismodulefun {R : rng} {M N : module} (f : pr1 M -> pr1 N) : UU :=
   (isbinopfun f) × (∏ r : R, ∏ x : (pr1 M), f (module_mult (r,,x)) = module_mult (r,,(f x)) ).


 Lemma isapropismodulefun {R : rng} {M N : module} (f : pr1 M -> pr1 N) : isaprop (@ismodulefun R M N f).
 Proof.
   refine (@isofhleveldirprod 1 (isbinopfun f) (∏ r : R, ∏ x : (pr1 M), f (module_mult (r,,x)) = module_mult (r,,(f x))) _ _).
   exact (isapropisbinopfun f).
   apply (impred 1 _).
   intro r.
   apply (impred 1 _).
   intro x.
   apply (setproperty (pr1 N)).
 Defined.


 Definition modulefun {R : rng} (M N : module) := total2 (λ f : pr1 M -> pr1 N, @ismodulefun R M N f).

 Definition modulefunpair {R : rng} {M N : module} (f : pr1 M -> pr1 N) (is : @ismodulefun R M N f) :=
   tpair _ f is.

 Definition modulefun_unel {R : rng} {M N : module} (f : @modulefun R M N) : pr1 f (@unel (pr1 M)) = @unel (pr1 N).
 Proof.
   rewrite <- (module_mult_0_is_0 (@unel (pr1 M))).
   rewrite (pr2 (pr2 f) rngunel1 (@unel (pr1 M))).
   rewrite (module_mult_0_is_0 _).
   reflexivity.
 Defined.


 (** *** The precategory of (left) R-modules and R-modules homomorphisms *)

 Section modules_precategory.

 Definition precategory_ob_mor_module {R: rng} : precategory_ob_mor :=
   precategory_ob_mor_pair (@module R) (λ M N, modulefun M N).

 Local Open Scope functions.

 Definition precategory_id_comp_module {R : rng} : precategory_id_comp (@precategory_ob_mor_module R).
 Proof.
   apply dirprodpair.
   - intro M.
     refine (tpair _ (idfun (pr1 M)) _).
     apply dirprodpair.
     + intros x y.
       reflexivity.
     + intros.
       reflexivity.
   - intros  M N P f g.
     refine (tpair _ ((pr1 g) ∘ (pr1 f)) _).
     apply dirprodpair.
     + intros x y.
       unfold funcomp.
       rewrite <- (pr1 (pr2 g)).
       rewrite <- (pr1 (pr2 f)).
       reflexivity.
     + intros.
       unfold funcomp.
       rewrite (pr2 (pr2 f)).
       rewrite (pr2 (pr2 g)).
       reflexivity.
 Defined.

 Definition precategory_data_module {R : rng} : precategory_data :=
   tpair _ (@precategory_ob_mor_module R) (precategory_id_comp_module).

 Local Close Scope functions.

 Local Open Scope cat.

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

 Definition precategory_module {R : rng} : precategory :=
   tpair _ (@precategory_data_module R) (is_precategory_precategory_data_module).

 End modules_precategory.


 (** **** The category of (left) R-modules and R-modules homomorphisms *)

 Section modules_category.

 Variable R : rng.
 Notation "R-mod" := (@precategory_module R).

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
   set (is := pr1 (pr2 f)).
   intros x y.
   apply (invmaponpathsweq (pr1 f)).
   rewrite (homotweqinvweq (pr1 f) (op x y)).
   rewrite (is (invmap (pr1 f) x) (invmap (pr1 f) y)).
   rewrite (homotweqinvweq (pr1 f) x).
   rewrite (homotweqinvweq (pr1 f) y).
   reflexivity.
 Defined.

 Definition islinear {M N : R-mod} (f : pr1 M -> pr1 N) :=
   ∏ r : R, ∏ x : (pr1 M), f (module_mult (r,,x)) = module_mult (r,,(f x)).

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
   rewrite <- (pr2 is r (invmap f x)).
   reflexivity.
   Defined.

 Definition invmoduleiso {M N : R-mod} (f : moduleiso M N) : moduleiso N M.
 Proof.
   use moduleisopair.
   - exact (invweq (pr1 f)).
   - use dirprodpair.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
 Defined.

 Definition isaprop_islinear {M N : R-mod} {f : (pr1 M) -> (pr1 N)} : isaprop (@islinear M N f).
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
       * exact (pr1 (pr2 w)).
       * use (modulefun_unel w).
   - use (pr2 (pr2 w)).
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
 Notation "R-Mod" := (category_module R).