(** * Taking a quotient of a submodule of a module over a fixed ring

Auke Booij, December 2017
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Submodule.

(** * Preliminaries: notion of an equivalence relation on a module that is closed under the module
structure
*)
Section quotmod_rel.

  Context {R : ring}
          (M : module R).


  Local Open Scope module_scope.
  Definition isactionhrel (E : hrel M) : UU :=
    ∏ r a b, E a b -> E (r * a) (r * b).

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

(** * Preliminaries: construction of an appropriate equivalence relation from a submodule
*)
Section quotmod_submodule.

  Context {R : ring}
          (M : module R)
          (A : submodule M).

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).
  Local Notation "  - y" := (grinv _ y).
  Local Notation "0" := (unel _).
  Local Open Scope module_scope.

  Definition eqrelsubmodule : eqrel M.
  Proof.
    use eqrelconstr.
    - exact (λ m m', A (m - m')).
    - intros x y z xy yz.
      assert (K := submoduleadd A (x - y) (y - z) xy yz).
      rewrite (assocax M) in K.
      rewrite <- (assocax M (grinv _ y) y) in K.
      rewrite grlinvax in K.
      rewrite lunax in K.
      exact K.
    - intros x.
      rewrite (grrinvax M x).
      exact (submodule0 A).
    - intros x y axy.
      assert (K := submoduleinv A (x - y) axy).
      rewrite grinvop in K.
      rewrite grinvinv in K.
      exact K.
  Defined.

  Definition module_eqrelsubmodule : module_eqrel M.
  Proof.
    use make_module_eqrel.
    - exact eqrelsubmodule.
    - split.
      + intros a b c.
        assert (H : a - b = c + a - (c + b)).
        {
          etrans; [|eapply (maponpaths (λ z, z - (c + b))); apply (commax M)];
            rewrite assocax.
          apply maponpaths.
          now rewrite grinvop, commax, assocax, grlinvax, runax.
        }
        simpl in *.
        now rewrite H.
      + intros a b c.
        assert (H : a - b = a + c - (b + c)).
        {
          rewrite assocax.
          apply maponpaths.
          now rewrite grinvop, <- (assocax M), grrinvax, lunax.
        }
        simpl in *.
        now rewrite H.
    - intros r m m'.
      assert (H : (r * m) - (r * m') = r * (m - m')) by
          now rewrite module_inv_mult, module_mult_is_ldistr.
      generalize (submodulemult A r (m - m')).
      simpl in *.
      now rewrite H.
  Defined.

End quotmod_submodule.

(** * Construction of quotient module, as well as its universal property
*)
Section quotmod_def.

  Context {R : ring}
          (M : module R)
          (E : module_eqrel M).

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).
  Local Open Scope module_scope.

  Definition quotmod_abgr : abgr := abgrquot E.

  Definition quotmod_ringact (r : R) : quotmod_abgr -> quotmod_abgr.
  Proof.
    use setquotuniv.
    - intros m.
      exact (setquotpr E (r * m)).
    - intros m m' Hmm'.
      apply weqpathsinsetquot.
      now apply isactionhrelmodule_eqrel.
  Defined.

  Definition quotmod_ringmap : R -> ringofendabgr quotmod_abgr.
  Proof.
    intros r. use tpair.
    + exact (quotmod_ringact r).
    + use make_ismonoidfun.
      * use make_isbinopfun.
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
      * unfold unel, quotmod_ringact; simpl; rewrite (setquotunivcomm E).
        apply maponpaths.
        apply module_mult_1.
  Defined.

  Definition quotmod_ringfun : ringfun R (ringofendabgr quotmod_abgr).
  Proof.
    unfold ringfun, rigfun.
    use rigfunconstr.
    - exact quotmod_ringmap.
    - use make_isrigfun.
      (* To show that quotmod_ringmap is a ring action, we show it is a monoid homomorphism with
      respect to both monoids on R. *)
      all: use make_ismonoidfun;
        (* To show that a map is a monoid homomorphism, we show that it respects the binary
        operation, as well as that it preserves the unit. *)
        [ use make_isbinopfun; intros r r' | ].
      (* It suffices to prove the underlying maps of the resulting automorphism of our group are
      equal. *)
      all: use monoidfun_paths; use funextfun.
      (* We show this using the universal property of the set quotient. *)
      all: use (setquotunivprop E (λ m, make_hProp _ _)); [use isasetsetquot|].
      (* Expand out some definitions. *)
      all: intros m; simpl; unfold unel, quotmod_ringact, funcomp.
      (* Apply the computation rule of the universal property of the set quotient. *)
      all: [> do 3 rewrite (setquotunivcomm E) | rewrite (setquotunivcomm E)
            | do 3 rewrite (setquotunivcomm E) | rewrite (setquotunivcomm E)].
      (* We can show the required equalities because the representatives of the equivalence classes
      are already equal. *)
      all: use maponpaths; simpl.
      (* The representatives are equal because of the fact that our input map was a ring action. *)
      + use module_mult_is_rdistr.
      + use module_mult_0_to_0.
      + use module_mult_assoc.
      + use module_mult_unel2.
  Defined.

  Definition quotmod_mod_struct : module_struct R quotmod_abgr := quotmod_ringfun.

  Definition quotmod : module R.
  Proof.
    use make_module.
    - exact quotmod_abgr.
    - exact quotmod_mod_struct.
  Defined.
  Notation "M / A" := (quotmod M (module_eqrelsubmodule M A)) : module_scope.

  Notation "R-mod( M , N )" := (modulefun M N) : module_scope.
  Definition quotmod_quotmap : R-mod(M, quotmod).
  Proof.
    use make_modulefun.
    - exact (setquotpr E).
    - now use (make_ismodulefun (make_isbinopfun _)).
  Defined.

  Definition quotmoduniv
             (N : module R)
             (f : R-mod(M, N))
             (is : iscomprelfun E f) :
    R-mod(quotmod, N).
  Proof.
    use make_modulefun.
    - now use (setquotuniv E _ f).
    - use make_ismodulefun.
      + use make_isbinopfun.
        use (setquotuniv2prop E (λ m n, make_hProp _ _)); [use isasetmodule|].
        intros m m'.
        simpl.
        unfold op, setquotfun2.
        rewrite setquotuniv2comm.
        do 3 rewrite (setquotunivcomm E).
        apply modulefun_to_isbinopfun.
      + intros r.
        use (setquotunivprop E (λ m, make_hProp _ _)); [use isasetmodule|].
        intros m.
        assert (H : r * quotmod_quotmap m = quotmod_quotmap (r * m)) by
            use (! modulefun_to_islinear _ _ _).
        simpl in H. simpl.
        rewrite H.
        do 2 rewrite (setquotunivcomm E).
        apply modulefun_to_islinear.
  Defined.

End quotmod_def.

(** * Universal property in terms of submodules
*)
Section from_submodule.

  Context {R : ring}
          (M : module R)
          (A : submodule M).

  Notation "R-mod( M , N )" := (modulefun M N) : module_scope.
  Local Open Scope module_scope.

  Definition quotmoduniv_submodule
             (N : module R)
             (f : R-mod(M, N))
             (is : iscomprelfun (module_eqrelsubmodule M A) f) :
    R-mod(quotmod M (module_eqrelsubmodule M A), N) :=
    quotmoduniv M (module_eqrelsubmodule M A) N f is.

End from_submodule.
