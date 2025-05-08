(**

  Quotient Ring Modules

  This file constructs quotient ring modules from submodules or appropriate equivalence relations.

  Contents
  1. Preliminaries
  1.1. Equivalence relations on a module that are closed under the module structure [module_eqrel]
  1.2. Construction of an appropriate equivalence relation from a submodule [module_eqrelsubmodule]
  2. The quotient module and its universal property
  2.1. The module [quotmod]
  2.2. The universal property [quotmoduniv]

  Originally written by Auke Booij, December 2017

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.ModuleCore.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Submodule.
Require Import UniMath.Algebra.RigsAndRings.

Local Open Scope abgr.
Local Open Scope addmonoid.
Local Open Scope module.

(** * 1. Preliminaries *)
(** ** 1.1. Equivalence relations on a module that are closed under the module structure *)
Section quotmod_rel.

  Context {R : ring}
          (M : module R).

  Definition isactionhrel (E : hrel M) : UU :=
    ∏ r a b, E a b → E (r * a) (r * b).

  Definition module_eqrel : UU :=
    ∑ E : eqrel M, isbinophrel E × isactionhrel E.
  Definition hrelmodule_eqrel (E : module_eqrel) : eqrel M := pr1 E.
  Coercion hrelmodule_eqrel : module_eqrel >-> eqrel.

  Definition binophrelmodule_eqrel (E : module_eqrel) : binopeqrel M := make_binopeqrel E (pr1 (pr2 E)).
  Coercion binophrelmodule_eqrel : module_eqrel >-> binopeqrel.

  Definition isactionhrelmodule_eqrel (E : module_eqrel) : isactionhrel E := pr2 (pr2 E).
  Coercion isactionhrelmodule_eqrel : module_eqrel >-> isactionhrel.

  Definition make_module_eqrel (E : eqrel M) : isbinophrel E -> isactionhrel E -> module_eqrel :=
    λ H0 H1, (E,,(H0,,H1)).

End quotmod_rel.

(** ** 1.2. Construction of an appropriate equivalence relation from a submodule *)
Section quotmod_submodule.

  Context {R : ring}
          (M : module R)
          (A : submodule M).

  Definition hrelsubmodule : hrel M := λ m m', A (m - m').

  Lemma iseqrelsubmodule : iseqrel hrelsubmodule.
  Proof.
    use iseqrelconstr.
    - intros x y z xy yz.
      assert (K := submoduleadd A (x - y) (y - z) xy yz).
      rewrite (assocax M) in K.
      rewrite <- (assocax M (-y) y) in K.
      rewrite grlinvax in K.
      rewrite lunax in K.
      exact K.
    - intros x.
      refine (transportb (λ y, A y) (grrinvax M x) _).
      exact (submodule0 A).
    - intros x y axy.
      assert (K := submoduleinv A (x - y) axy).
      rewrite grinvop in K.
      rewrite grinvinv in K.
      exact K.
  Qed.

  Definition eqrelsubmodule : eqrel M
    := make_eqrel hrelsubmodule iseqrelsubmodule.

  Lemma isbinophrel_eqrelsubmodule
    : isbinophrel eqrelsubmodule.
  Proof.
    split.
    - intros a b c.
      assert (H : a - b = c + a - (c + b)).
      {
        etrans; [|eapply (maponpaths (λ z, z - (c + b))); apply (commax M)];
          rewrite assocax.
        apply maponpaths.
        now rewrite grinvop, commax, assocax, grlinvax, runax.
      }
      intro H2.
      exact (transportf (λ y, A y) H H2).
    - intros a b c.
      assert (H : a - b = a + c - (b + c)).
      {
        rewrite assocax.
        apply maponpaths.
        now rewrite grinvop, <- (assocax M), grrinvax, lunax.
      }
      intro H2.
      exact (transportf (λ y, A y) H H2).
  Qed.

  Lemma isactionhrel_eqrelsubmodule
    : isactionhrel M eqrelsubmodule.
  Proof.
    intros r m m'.
    assert (H : (r * m) - (r * m') = r * (m - m')) by
        now rewrite module_inv_mult, module_mult_is_ldistr.
    generalize (submodulemult A r (m - m')).
    intros H2 H3.
    simpl in *.
    unfold hrelsubmodule.
    exact (transportb (λ x, A x) H (H2 H3)).
  Qed.

  Definition module_eqrelsubmodule : module_eqrel M
    := make_module_eqrel _
      eqrelsubmodule
      isbinophrel_eqrelsubmodule
      isactionhrel_eqrelsubmodule.

End quotmod_submodule.

(** * 2. The quotient module and its universal property *)
Section quotmod_def.

  Context {R : ring}
          (M : module R)
          (E : module_eqrel M).

(** ** 2.1. The module *)

  Definition quotmod_abgr : abgr := abgrquot E.

  Definition quotmod_ringact (r : R) : quotmod_abgr → quotmod_abgr.
  Proof.
    use setquotuniv.
    - intros m.
      exact (setquotpr E (r * m)).
    - abstract (
        intros m m' Hmm';
        apply weqpathsinsetquot;
        now apply isactionhrelmodule_eqrel
      ).
  Defined.

  Lemma isbinopfun_quotmod_ringact
    (r : R)
    : isbinopfun (quotmod_ringact r).
  Proof.
    apply make_isbinopfun.
    use (setquotuniv2prop E (λ a b, make_hProp _ _)); [use isasetsetquot|].
    intros m m'.
    unfold quotmod_ringact, setquotfun2;
      rewrite (setquotunivcomm E), (setquotunivcomm E);
      simpl; unfold setquotfun2;
        rewrite (setquotuniv2comm E), (setquotuniv2comm E), (setquotunivcomm E).
    apply weqpathsinsetquot.
    assert (H : r * (m + m') = r * m + r * m') by use module_mult_is_ldistr.
    simpl in H; rewrite H.
    use eqrelrefl.
  Qed.

  Definition quotmod_ringmap (r : R) : group_endomorphism_ring quotmod_abgr.
  Proof.
    use make_abelian_group_morphism.
    - exact (quotmod_ringact r).
    - exact (isbinopfun_quotmod_ringact r).
  Defined.

  Lemma isrigfun_quotmod_ringmap
    : isrigfun (X := R) (Y := group_endomorphism_ring quotmod_abgr) quotmod_ringmap.
  Proof.
    use make_isrigfun.
    (* To show that quotmod_ringmap is a ring action, we show it is a monoid homomorphism with
    respect to both monoids on R. *)
    all: use make_ismonoidfun;
      (* To show that a map is a monoid homomorphism, we show that it respects the binary
      operation, as well as that it preserves the unit. *)
      [ use make_isbinopfun; intros r r' | ].
    (* It suffices to prove the underlying maps of the resulting automorphism of our group are
    equal. *)
    all: apply abelian_group_morphism_eq.
    (* We show this using the universal property of the set quotient. *)
    all: use (setquotunivprop E (λ m, make_hProp _ _)); [use isasetsetquot|].
    (* Expand out some definitions. *)
    all: intros m; simpl; unfold unel, quotmod_ringact, compose; simpl.
    (* Apply the computation rule of the universal property of the set quotient. *)
    all: [> do 3 rewrite (setquotunivcomm E) | rewrite (setquotunivcomm E)
          | do 3 rewrite (setquotunivcomm E) | rewrite (setquotunivcomm E)].
    (* We can show the required equalities because the representatives of the equivalence classes
    are already equal. *)
    all: use maponpaths; simpl.
    (* The representatives are equal because of the fact that our input map was a ring action. *)
    - use module_mult_is_rdistr.
    - use module_mult_0_to_0.
    - use module_mult_assoc.
    - use module_mult_unel2.
  Qed.

  Definition quotmod_ringfun : ringfun R (group_endomorphism_ring quotmod_abgr)
    := rigfunconstr isrigfun_quotmod_ringmap.

  Definition quotmod_mod_struct : module_struct R quotmod_abgr := quotmod_ringfun.

  Definition quotmod : module R.
  Proof.
    use make_module.
    - exact quotmod_abgr.
    - exact quotmod_mod_struct.
  Defined.
  Notation "M / A" := (quotmod M (module_eqrelsubmodule M A)) : module_scope.

(** ** 2.2. The universal property *)

  Notation "R-mod( M , N )" := (modulefun M N) : module_scope.
  Definition quotmod_quotmap : R-mod(M, quotmod).
  Proof.
    use make_modulefun.
    - exact (setquotpr E).
    - now use (make_ismodulefun (make_isbinopfun _)).
  Defined.

  Definition quotmoduniv_data
    (N : module R)
    (f : R-mod(M, N))
    (is : iscomprelfun E f)
    : quotmod → N
    := setquotuniv E _ f is.

  Lemma quotmoduniv_ismodulefun
    (N : module R)
    (f : R-mod(M, N))
    (is : iscomprelfun E f)
    : ismodulefun (quotmoduniv_data N f is).
  Proof.
    unfold quotmoduniv_data.
    use make_ismodulefun.
    - use make_isbinopfun.
      use (setquotuniv2prop E (λ m n, make_hProp _ _)); [apply setproperty|].
      intros m m'.
      simpl.
      unfold op, setquotfun2.
      rewrite setquotuniv2comm.
      do 3 rewrite (setquotunivcomm E).
      apply modulefun_to_isbinopfun.
    - intros r.
      use (setquotunivprop E (λ m, make_hProp _ _)); [apply setproperty|].
      intros m.
      assert (H : r * quotmod_quotmap m = quotmod_quotmap (r * m)) by
          use (! modulefun_to_islinear _ _ _).
      simpl in H. simpl.
      refine (maponpaths _ H @ _).
      rewrite (setquotunivcomm E).
      refine (setquotunivcomm E _ _ _ _ @ _).
      apply modulefun_to_islinear.
  Qed.

  Definition quotmoduniv
    (N : module R)
    (f : R-mod(M, N))
    (is : iscomprelfun E f)
    : R-mod(quotmod, N)
    := make_modulefun (quotmoduniv_data N f is) (quotmoduniv_ismodulefun N f is).

End quotmod_def.

(** * Universal property in terms of submodules
*)
Section from_submodule.

  Context {R : ring}
          (M : module R)
          (A : submodule M).

  Notation "R-mod( M , N )" := (modulefun M N) : module_scope.

  Definition quotmoduniv_submodule
             (N : module R)
             (f : R-mod(M, N))
             (is : iscomprelfun (module_eqrelsubmodule M A) f) :
    R-mod(quotmod M (module_eqrelsubmodule M A), N) :=
    quotmoduniv M (module_eqrelsubmodule M A) N f is.

End from_submodule.
