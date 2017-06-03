(** Anthony Bordg, February-March 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.CategoryTheory.Categories.
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

Definition setofendabgr_inv {G : abgr} : monoidfun G G -> monoidfun G G.
Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1setofendabgr f x))).
   apply dirprodpair.
   - intros x x'.
     rewrite (setofendabgr_to_isbinopfun f).
     apply (dirprod_pr1 ismonoidfun_abgrinv).
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

Definition module (R : rng) : UU := ∑ G, rngfun R (rngofendabgr G).

Definition pr1module {R : rng} (M : module R) : abgr := pr1 M.

Coercion pr1module : module >-> abgr.

Definition module_struct {R : rng} (G : abgr) : UU := rngfun R (rngofendabgr G).

Definition pr2module {R : rng} (M : module R) : rngfun R (rngofendabgr (pr1module M)) := pr2 M.

Coercion pr2module : module >-> rngfun.

(** The multiplication defined from a module *)

Definition module_mult {R : rng} {M : @module R} : R × M -> M.
Proof.
   apply uncurry. intros r x.
   exact (pr1setofendabgr (M r) x).
Defined.

Local Open Scope rig_scope.

Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f 0 = 0 := pr2 (pr1 (pr2 f)).

Local Close Scope rig_scope.

Local Open Scope rng_scope.

Definition module_mult_0_to_0 {R : rng} {M : @module R} (x : M) : module_mult (0,,x) = @unel M.
Proof.
   unfold module_mult, uncurry. cbn.
   assert (M rngunel1 = @rngunel1 (rngofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid M).
   - rewrite X.
     reflexivity.
Defined.


(** (left) R-module homomorphism *)

Definition ismodulefun {R : rng} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x))).


Lemma isapropismodulefun {R : rng} {M N : module R} (f : M -> N) : isaprop (@ismodulefun R M N f).
Proof.
   refine (@isofhleveldirprod 1 (isbinopfun f) (∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x))) _ _).
   exact (isapropisbinopfun f).
   apply (impred 1 _). intro r.
   apply (impred 1 _). intro x.
   apply (setproperty N).
Defined.


Definition modulefun {R : rng} (M N : module R) := total2 (λ f : M -> N, @ismodulefun R M N f).

Definition modulefunpair {R : rng} {M N : module R} (f : M -> N) (is : @ismodulefun R M N f) :=
   tpair _ f is.

Definition pr1modulefun {R : rng} {M N : module R} (f : @modulefun R M N) : M -> N := pr1 f.

Coercion pr1modulefun : modulefun >-> Funclass.

Definition islinear {R : rng} {M N : module R} (f : M -> N) :=
   ∏ r : R, ∏ x : M, f (module_mult (r,,x)) = module_mult (r,,(f x)).

Definition modulefun_to_islinear {R : rng} {M N : module R} (f : modulefun M N): islinear f := pr2 (pr2 f).

Definition modulefun_unel {R : rng} {M N : module R} (f : @modulefun R M N) : f (@unel M) = @unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (@unel M)).
   rewrite ((modulefun_to_islinear f) rngunel1 (@unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.

Definition modulefun_to_isbinopfun {R : rng} {M N : module R} (f : modulefun M N) : isbinopfun f := pr1 (pr2 f).

(** *** The precategory of (left) R-modules and R-modules homomorphisms *)

Section modules_precategory.

Definition precategory_ob_mor_module {R: rng} : precategory_ob_mor :=
   precategory_ob_mor_pair (@module R) (λ M N, modulefun M N).

Local Open Scope Cat.

Definition modulefun_id {R : rng}: ∏ M : @precategory_ob_mor_module R, M --> M.
Proof.
   intro M.
   refine (tpair _ (idfun (pr1module M)) _).
   apply dirprodpair.
     - intros x y. reflexivity.
     - intros. reflexivity.
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

Definition precategory_id_comp_module {R : rng} : precategory_id_comp (@precategory_ob_mor_module R) :=
  dirprodpair modulefun_id modulefun_comp.

Definition precategory_data_module {R : rng} : precategory_data :=
   tpair _ (@precategory_ob_mor_module R) (precategory_id_comp_module).

Definition is_precategory_precategory_data_module {R : rng} : is_precategory (@precategory_data_module R).
Proof.
   apply dirprodpair.
   - apply dirprodpair.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. reflexivity.
       * apply isapropismodulefun.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. reflexivity.
       * apply isapropismodulefun.
   - intros M N P Q f g h.
     use total2_paths_f.
     + apply funextfun. intro x.
       unfold compose. cbn.
       rewrite funcomp_assoc.
       reflexivity.
     + apply isapropismodulefun.
Defined.

Definition precategory_module (R : rng) : precategory :=
   mk_precategory (@precategory_data_module R) (is_precategory_precategory_data_module).

End modules_precategory.


(** **** The category of (left) R-modules and R-modules homomorphisms *)

Section univalent_category_module.

Variable R : rng.
Notation "R-mod" := (precategory_module R).

Definition has_homsets_precategory_module : has_homsets (R-mod).
Proof.
   intros M N. unfold isaset. intros f g. unfold isaprop.
   apply (isofhlevelweqb 1 (total2_paths_equiv (λ x :  pr1module M ->  pr1module N, ismodulefun x) f g)).
   refine (isofhleveltotal2 1 _ _ _).
   - assert (p : isofhlevel 2 (pr1module M ->  pr1module N)).
     + apply impred. intro.
       exact (setproperty (pr1module N)).
     + exact (p (pr1 f) (pr1 g)).
   - intro p.
     assert (q : isaset (@ismodulefun R M N (pr1 g))).
     + exact (isasetaprop (isapropismodulefun (pr1 g))).
     + apply q.
Defined.

Definition category_module : category := category_pair R-mod has_homsets_precategory_module.

Definition moduleiso (M N : R-mod) := total2 (λ w : pr1module M ≃ pr1module N, ismodulefun w).

Definition moduleiso_modulefun {M N : R-mod} : moduleiso M N -> modulefun M N.
Proof.
   intro f.
   exact (tpair _ (pr1weq (pr1 f)) (pr2 f)).
Defined.

Coercion moduleiso_modulefun : moduleiso >-> modulefun.

Definition pr1moduleiso {M N : R-mod} (f : moduleiso M N) : weq (pr1module M) (pr1module N) := pr1 f.

Coercion pr1moduleiso : moduleiso >-> weq.

Definition moduleisopair {M N : R-mod} (f : pr1module M ≃ pr1module N) (is : ismodulefun f) : moduleiso M N :=
   tpair _ f is.

Definition idmoduleiso (M : R-mod) : moduleiso M M.
Proof.
   use moduleisopair.
   - exact (idweq (pr1module M)).
   - use dirprodpair.
     + intros x y. apply idpath.
     + intros r x. apply idpath.
Defined.

Definition isbinopfuninvmap {M N : R-mod} (f : moduleiso M N) : isbinopfun (invmap f).
Proof.
   intros x y.
   apply (invmaponpathsweq f).
   rewrite (homotweqinvweq f (op x y)).
   symmetry.
   transitivity (op ((pr1moduleiso f) (invmap f x)) ((pr1moduleiso f) (invmap f y))).
   apply (modulefun_to_isbinopfun f (invmap f x) (invmap f y)).
   rewrite 2 (homotweqinvweq f).
   reflexivity.
Defined.

Definition islinearinvmap {M N : R-mod} (f : moduleiso M N) : islinear (invmap f).
Proof.
   intros r x.
   induction f as [f is].
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
   - exact (invweq f).
   - use dirprodpair.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
Defined.

Definition isaprop_islinear {M N : R-mod} {f : (pr1module M) -> (pr1module N)} : isaprop (@islinear R M N f).
Proof.
   use impred. intro r.
   use impred. intro x.
   use setproperty.
Defined.

Definition moduleiso' (M N : R-mod) : UU :=
   total2 (λ w : monoidiso (pr1module M) (pr1module N), islinear w).

Definition moduleiso_to_moduleiso' {M N : R-mod} : moduleiso M N -> moduleiso' M N.
Proof.
   intro w.
   use tpair.
   - use tpair.
     + exact w.
     + use tpair.
       * exact (modulefun_to_isbinopfun w).
       * use (modulefun_unel w).
   - exact (modulefun_to_islinear w).
Defined.

Definition moduleiso'_to_moduleiso {M N : R-mod} : moduleiso' M N -> moduleiso M N.
Proof.
   intro w.
   use tpair.
   - exact (pr1 w).
   - use dirprodpair.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
Defined.

Lemma modulefun_unel_uniqueness {M N : R-mod} {f : pr1module M -> pr1module N} {is: ismodulefun f}
       (p : f (@unel (pr1module M)) = @unel (pr1module N)) : modulefun_unel (f,,is) = p.
Proof.
   apply (setproperty (pr1module N)).
Defined.

Definition moduleiso'_to_moduleiso_isweq {M N : R-mod} : isweq (@moduleiso'_to_moduleiso M N).
Proof.
   use (gradth _ moduleiso_to_moduleiso'). intro w.
   induction w as [w is].
   unfold moduleiso'_to_moduleiso, moduleiso_to_moduleiso'.
   induction w as [w is'].
   induction is' as [is'' p].
   rewrite (modulefun_unel_uniqueness p).
   reflexivity.
   intro w.
   induction w as [w is].
   unfold moduleiso_to_moduleiso', moduleiso'_to_moduleiso.
   reflexivity.
Defined.

Definition moduleiso'_to_moduleiso_weq {M N : R-mod} : (moduleiso' M N) ≃ (moduleiso M N) :=
   weqpair (@moduleiso'_to_moduleiso M N) moduleiso'_to_moduleiso_isweq.

Lemma isaset_el_of_setwith2binop {X : setwith2binop} : isaset X.
Proof.
   intros x y.
   use (setproperty X).
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
   - use impred_isaset. intro x.
     induction Y as [Y is].
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
     induction M as [M f]. induction N as [N g]. cbn in e. induction e.
     use weqimplimpl.
     + intro i. cbn.
       use total2_paths2_f.
       * use funextfun. intro r.
         use total2_paths2_f.
           use funextfun. intro x.
           exact (i r x).
           apply isapropismonoidfun.
       * apply isaprop_isrigfun.
     + intro i. cbn.
       intros r x.
       unfold idmonoidiso. cbn. cbn in i.
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

Lemma moduleiso_is_iso {M N : ob R-mod} (f : moduleiso M N) : @is_iso R-mod M N (modulefunpair f (pr2 f)).
Proof.
   apply (is_iso_qinv (C:= R-mod) _ (modulefunpair (invmoduleiso f) (pr2 (invmoduleiso f)))).
   split.
   - use total2_paths_f.
     + cbn.
       apply funextfun. intro x.
       unfold funcomp, idfun.
       apply homotinvweqweq.
     + apply isapropismodulefun.
   - use total2_paths_f.
     + cbn.
       apply funextfun. intro y.
       apply homotweqinvweq.
     + apply isapropismodulefun.
Defined.

Lemma moduleiso_iso {M N : ob R-mod} : moduleiso M N -> iso M N.
Proof.
   intro f.
   use isopair.
   - use tpair.
     + exact f.
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
     + unfold moduleiso_iso, iso_moduleiso. cbn.
       use total2_paths_f.
       * cbn.
         reflexivity.
       * apply isapropisweq.
   - intro f.
     unfold iso_moduleiso, moduleiso_iso. cbn.
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
     use (pathscomp0 weqcomp_to_funcomp_app). cbn.
     use total2_paths_f.
     + reflexivity.
     + apply isaprop_is_iso.
   - apply weqproperty.
Defined.

Definition precategory_module_is_univalent : is_univalent (R-mod) :=
  mk_is_univalent precategory_module_idtoiso_isweq has_homsets_precategory_module.

Definition univalent_category_module : univalent_category := mk_category R-mod precategory_module_is_univalent.


End univalent_category_module.

Variable R : rng.
Local Notation "R-Mod" := (category_module R).