Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Submodule.

Section quotmod_rel.

  Context {R : rng}
          (M : module R).


  Local Open Scope module_scope.
  Definition isacthrel (E : hrel M) : UU :=
    ∏ r a b, E a b -> E (r * a) (r * b).

  Definition monoideqrel : UU :=
    total2 (λ E : eqrel M, isbinophrel E × isacthrel E).
  Definition hrelmonoideqrel (E : monoideqrel) : eqrel M := pr1 E.
  Coercion hrelmonoideqrel : monoideqrel >-> eqrel.

  Definition binophrelmonoideqrel (E : monoideqrel) : binopeqrel := binopeqrelpair E (pr1 (pr2 E)).
  Coercion binophrelmonoideqrel : monoideqrel >-> binopeqrel.

  Definition isacthrelmonoideqrel (E : monoideqrel) : isacthrel E := pr2 (pr2 E).
  Coercion isacthrelmonoideqrel : monoideqrel >-> isacthrel.

  Definition mk_monoideqrel (E : eqrel M) : isbinophrel E -> isacthrel E -> monoideqrel :=
    λ H0 H1, (E,,(H0,,H1)).

End quotmod_rel.

Section quotmod_submodule.

  Context {R : rng}
          (M : module R)
          (A : submodule M).

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).
  Local Open Scope module_scope.

  Definition eqrelsubmodule : eqrel M.
  Proof.
    use eqrelconstr.
    - exact (λ m m', A (m - m')).
    - intros x y z xy yz.
      assert (xyyz := submoduleadd A (x - y) (y - z) xy yz).
      rewrite (assocax M) in xyyz.
      rewrite <- (assocax M (grinv _ y) y) in xyyz.
      rewrite grlinvax in xyyz.
      now rewrite lunax in xyyz.
    - intros x. assert (a0 := submodule0 A).
      now rewrite <- (grrinvax M x) in a0.
    - unfold issymm. intros x y axy.
      assert (ainv := submoduleinv A (x - y) axy).
      rewrite grinvop in ainv.
      now rewrite grinvinv in ainv.
  Defined.

  Definition monoideqrelsubmodule : monoideqrel M.
  Proof.
    use mk_monoideqrel.
    - exact eqrelsubmodule.
    - split.
      + intros a b c.
        assert (H : a - b = c + a - (c + b)).
        {
          etrans; [|eapply (maponpaths (λ z, z - (c + b))); apply (commax M)];
          rewrite assocax.
          apply maponpaths.
          rewrite grinvop, commax, assocax, grlinvax;
          now rewrite runax.
        }
        simpl in *.
        now rewrite H.
      + intros a b c.
        assert (H : a - b = a + c - (b + c)).
        {
          rewrite assocax;
          use (@maponpaths _ _ (λ z, a + z));
          rewrite grinvop, <- (assocax M), grrinvax;
          now rewrite lunax.
        }
        simpl in *.
        now rewrite H.
    - intros r m m'.
      assert (H : (r * m) - (r * m') = r * (m - m')).
      {
        rewrite module_inv_mult;
        now rewrite module_mult_is_ldistr.
      }
      generalize (submodulemult A r (m - m')).
      simpl in *.
      now rewrite H.
  Defined.

End quotmod_submodule.

Section quotmod_def.

  Context {R : rng}
          (M : module R)
          (E : monoideqrel M).

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).
  Local Open Scope module_scope.

  Definition quotmod_U : hSet := hSetpair (setquot E) (isasetsetquot E).

  Definition quotmod_abgr : abgr := abgrquot E.

  Definition quotmod_rngact : R -> rngofendabgr quotmod_abgr.
  Proof.
    intros r. use tpair.
    + use setquotuniv.
      intros m.
      exact (setquotpr E (r * m)).
      intros m m' Hmm'.
      apply weqpathsinsetquot.
      now apply isacthrelmonoideqrel.
    + use mk_ismonoidfun.
      * use mk_isbinopfun.
        use (setquotuniv2prop E (λ a b, hProppair _ _)); [use isasetsetquot|].
        intros m m'.
        unfold setquotfun2.
        rewrite (setquotunivcomm E), (setquotunivcomm E).
        simpl. unfold setquotfun2.
        rewrite (setquotuniv2comm E), (setquotuniv2comm E), (setquotunivcomm E).
        apply weqpathsinsetquot.
        assert (H : r * (m + m') = r * m + r * m') by use module_mult_is_ldistr.
        simpl in H.
        rewrite H.
        use eqrelrefl.
      * unfold unel. simpl. rewrite (setquotunivcomm E).
        apply maponpaths.
        apply module_mult_1.
  Defined.


  Definition quotmod_rngfun : rngfun R (rngofendabgr quotmod_abgr).
  Proof.
    unfold rngfun. unfold rigfun.
    use rigfunconstr.
    - use quotmod_rngact.
    - use mk_isrigfun.
      + use mk_ismonoidfun.
        * use mk_isbinopfun.
          intros r r'.
          use monoidfun_paths.
          use funextfun.
          use (setquotunivprop E (λ m, hProppair _ _)); [use isasetsetquot|].
          intros m.
          simpl.
          do 3 rewrite (setquotunivcomm E).
          unfold op, setquotfun2.
          rewrite (setquotuniv2comm E).
          apply maponpaths.
          use module_mult_is_rdistr.
        * use monoidfun_paths. use funextfun.
          use (setquotunivprop E (λ m, hProppair _ _)); [use isasetsetquot|].
          intros m.
          simpl.
          unfold unel.
          rewrite (setquotunivcomm E).
          simpl. unfold unel.
          use maponpaths.
          use module_mult_0_to_0.
      + use mk_ismonoidfun.
        * use mk_isbinopfun.
          intros r r'.
          use monoidfun_paths.
          use funextfun.
          use (setquotunivprop E (λ m, hProppair _ _)); [use isasetsetquot|].
          intros m.
          simpl.
          unfold funcomp.

          do 2 rewrite (setquotunivcomm E).


          rewrite (setquotunivcomm E).
          apply maponpaths.
          use module_mult_assoc.
        * use monoidfun_paths. use funextfun.
          use (setquotunivprop E (λ m, hProppair _ _)); [use isasetsetquot|].
          intros m.
          simpl.
          unfold unel.
          rewrite (setquotunivcomm E).
          simpl. unfold unel.
          use maponpaths.
          use module_mult_unel2.
  Defined.

  Definition quotmod_mod_struct : module_struct R quotmod_abgr.
  Proof.
    unfold module_struct.
    exact quotmod_rngfun.
  Defined.

  Definition quotmod : module R.
  Proof.
    use modulepair.
    - exact quotmod_abgr.
    - exact quotmod_mod_struct.
  Defined.

  Definition quotmod_quotmap : modulefun M quotmod.
  Proof.
    use modulefunpair.
    - exact (setquotpr E).
    - split.
      + use mk_isbinopfun.
        intros m m'.
        apply idpath.
      + intros r m.
        apply idpath.
  Defined.

  Definition quotmoduniv
             (N : module R)
             (f : modulefun M N)
             (is : iscomprelfun E f) :
    modulefun quotmod N.
  Proof.
    use modulefunpair.
    - use setquotuniv.
      + exact f.
      + assumption.
    - split.
      + use mk_isbinopfun.
        use (setquotuniv2prop E (λ m n, hProppair _ _)).
        * apply (pr2 (pr1 (pr1 (pr1 N)))).
        * intros m m'.
          simpl.
          unfold op, setquotfun2.
          rewrite setquotuniv2comm.
          do 3 rewrite (setquotunivcomm E).
          apply modulefun_to_isbinopfun.
      + intros r.
        use (setquotunivprop E (λ m, hProppair _ _)).
        * apply (pr2 (pr1 (pr1 (pr1 N)))).
        * intros m.
          simpl.
          assert (H : r * quotmod_quotmap m = quotmod_quotmap (r * m)).
          {
            apply (! modulefun_to_islinear _ _ _).
          }
          simpl in H.
          rewrite H.
          do 2 rewrite (setquotunivcomm E).
          apply modulefun_to_islinear.
  Defined.

End quotmod_def.
