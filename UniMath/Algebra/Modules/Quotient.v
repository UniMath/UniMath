Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Submodule.

Section bla.

  Context {R : rng}
          (M : module R)
          (A : hsubtype M)
          {subm : issubmodule A}.

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).

  Definition quotrel : eqrel M.
  Proof.
    unfold eqrel. exists (λ x y, A (x - y)).
    unfold iseqrel.
    split.
    - unfold ispreorder. split.
      + unfold istrans. intros x y z xy yz.
        assert (xyyz := submoduleadd A subm (x - y) (y - z) xy yz).
        rewrite (assocax M) in xyyz.
        rewrite <- (assocax M (grinv _ y) y) in xyyz.
        rewrite grlinvax in xyyz.
        now rewrite lunax in xyyz.
      + unfold isrefl. intros x. assert (a0 := submodule0 A subm).
        now rewrite <- (grrinvax M x) in a0.
    - unfold issymm. intros x y axy.
      assert (ainv := submoduleinv A subm (x - y) axy).
      rewrite grinvop in ainv.
      now rewrite grinvinv in ainv.
  Defined.

  Definition quotmod_U : hSet := hSetpair (setquot quotrel) (isasetsetquot quotrel).

  Definition quotmod_op : binop quotmod_U.
  Proof.
    use setquotuniv2.
    exact (λ m n, setquotpr quotrel (m + n)).
    intros m m' n n' Hmm' Hnn'.
    apply weqpathsinsetquot.
    unfold quotrel in Hmm', Hnn'.
    generalize (submoduleadd A subm _ _ Hmm' Hnn').
    assert (H : m + n - (m' + n') = (m - m') + (n - n')).
    {
      rewrite assocax, assocax; apply maponpaths.
      rewrite grinvop.
      etrans. apply maponpaths; apply (commax M).
      rewrite <- assocax, <- assocax.
      apply (maponpaths (λ z, z - n')).
      apply (commax M).
    }
    simpl in *.
    now rewrite H.
  Defined.

  Definition quotmod_inv : quotmod_U -> quotmod_U.
  Proof.
    use setquotuniv.
    exact (λ m, setquotpr quotrel (grinv M m)).
    intros m m' Hmm'.
    apply weqpathsinsetquot.
    simpl.
    assert (H : grinv M m - grinv M m' = m' - m).
    {
      rewrite grinvinv.
      apply (commax M).
    }
    simpl in H.
    rewrite H.
    assert (H'mm' : A (grinv M (m - m'))).
    apply (submoduleinv A subm _ Hmm').
    rewrite grinvop in H'mm'.
    now rewrite grinvinv in H'mm'.
  Defined.

  Definition quotmod_un : quotmod_U := setquotpr quotrel 0%addmonoid.

  Definition quotmod_abgr : abgr.
  Proof.
    use abgrpair.
    - use setwithbinoppair.
      + use hSetpair.
        * exact quotmod_U.
        * apply isasetsetquot.
      + exact quotmod_op.
    -
      use mk_isabgrop.
      + use mk_isgrop.
        * use mk_ismonoidop.
          -- simple refine (setquotuniv3prop quotrel (λ x y z, hProppair (quotmod_op (quotmod_op x y) z = quotmod_op x (quotmod_op y z)) _) _).
             ++ use isasetsetquot.
             ++ intros x' y' z'.
                assert (H : ∏ u v, quotmod_op (setquotpr quotrel u) (setquotpr quotrel v) = setquotpr quotrel (u + v)).
                refine (setquotuniv2comm quotrel _ _ _).
                etrans.
                eapply (maponpaths (λ z, quotmod_op z (setquotpr quotrel z'))).
                apply H.
                rewrite H, H, H.
                apply maponpaths.
                apply assocax.
          -- use isunitalpair.
             ++ exact quotmod_un.
             ++ split.
                ** simple refine (setquotunivprop quotrel (λ m, hProppair (quotmod_op (setquotpr quotrel 0%addmonoid) m = m) _) _).
                   { use isasetsetquot. }
                   {
                     intros m.
                     etrans.
                     refine (setquotuniv2comm quotrel quotmod_U _ _ _ _).
                     apply maponpaths.
                     apply lunax.
                   }
                ** simple refine (setquotunivprop quotrel (λ m, hProppair (quotmod_op m (setquotpr quotrel 0%addmonoid) = m) _) _).
                   { use isasetsetquot. }
                   {
                     intros m.
                     etrans.
                     refine (setquotuniv2comm quotrel quotmod_U _ _ _ _).
                     apply maponpaths.
                     apply runax.
                   }
        * use mk_invstruct.
          -- exact quotmod_inv.
          -- split.
             ++ unfold islinv.
                simple refine (setquotunivprop quotrel (λ a, hProppair (quotmod_op (quotmod_inv a) a = quotmod_un) _) _).
                { use isasetsetquot. }
                {
                  intros m.
                  etrans.
                  refine (maponpaths (λ z, quotmod_op z _) _).
                  refine (setquotunivcomm _ _ _ _ _).
                  etrans.
                  unfold quotmod_op.
                  refine (setquotuniv2comm quotrel _ _ _ _ _).
                  apply weqpathsinsetquot.
                  rewrite (commax M).
                  rewrite (grrinvax M).
                  apply eqrelrefl.
                }
             ++ unfold islinv. simple refine (setquotunivprop quotrel (λ a, hProppair (quotmod_op a (quotmod_inv a) = quotmod_un) _) _).
                { use isasetsetquot. }
                {
                  intros m.
                  etrans.
                  refine (maponpaths (λ z, quotmod_op _ z) _).
                  refine (setquotunivcomm _ _ _ _ _).
                  etrans.
                  unfold quotmod_op.
                  refine (setquotuniv2comm quotrel _ _ _ _ _).
                  apply weqpathsinsetquot.
                  rewrite (commax M).
                  rewrite (grlinvax M).
                  apply eqrelrefl.
                }
      + unfold iscomm.
        simple refine (setquotuniv2prop quotrel (λ a b, hProppair (quotmod_op a b = quotmod_op b a) _) _).
        * use isasetsetquot.
        * intros m m'.
          unfold quotmod_op.
          etrans.
          apply setquotuniv2comm.
          rewrite setquotuniv2comm.
          apply maponpaths.
          apply (commax M).
  Defined.

  Local Open Scope module_scope.

  Definition quotmod_rngact : R -> rngofendabgr quotmod_abgr.
  Proof.
    intros r. use tpair.
    + use setquotuniv.
      intros m.
      exact (setquotpr quotrel (r * m)).
      intros m m' Hmm'.
      apply weqpathsinsetquot.
      unfold quotrel. simpl.
      rewrite module_inv_mult.
      rewrite <- (module_mult_is_ldistr r m).
      use (submodulemult A subm). assumption.
    + use mk_ismonoidfun.
      * use mk_isbinopfun.
        simple refine (setquotuniv2prop quotrel (λ a b, hProppair _ _) _); [use isasetsetquot|].
        intros m m'.
        assert (H : (quotmod_op (setquotpr quotrel m) (setquotpr quotrel m')) = setquotpr quotrel (m + m')).
        {
          unfold quotmod_op.
          refine (setquotuniv2comm _ _ _ _ m m').
        }
        simpl in H. simpl.
        rewrite H.
        rewrite (setquotunivcomm quotrel).
        rewrite (setquotunivcomm quotrel).
        rewrite (setquotunivcomm quotrel).
        unfold quotmod_op.
        rewrite (setquotuniv2comm quotrel).
        apply maponpaths.
        use module_mult_is_ldistr.
      * unfold unel. simpl. unfold quotmod_un. rewrite (setquotunivcomm quotrel).
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
          simple refine (setquotunivprop quotrel (λ m, hProppair _ _) _); [use isasetsetquot|].
          intros m.
          simpl.
          do 3 rewrite (setquotunivcomm quotrel).
          unfold quotmod_op.
          rewrite (setquotuniv2comm quotrel).
          apply maponpaths.
          use module_mult_is_rdistr.
        * use monoidfun_paths. use funextfun.
          simple refine (setquotunivprop quotrel (λ m, hProppair _ _) _); [use isasetsetquot|].
          intros m.
          simpl.
          unfold unel.
          rewrite (setquotunivcomm quotrel).
          simpl. unfold quotmod_un.
          use maponpaths.
          use module_mult_0_to_0.
      + use mk_ismonoidfun.
        * use mk_isbinopfun.
          intros r r'.
          use monoidfun_paths.
          use funextfun.
          simple refine (setquotunivprop quotrel (λ m, hProppair _ _) _); [use isasetsetquot|].
          intros m.
          simpl.
          unfold funcomp.

          do 2 rewrite (setquotunivcomm quotrel).


          rewrite (setquotunivcomm quotrel).
          apply maponpaths.
          use module_mult_assoc.
        * use monoidfun_paths. use funextfun.
          simple refine (setquotunivprop quotrel (λ m, hProppair _ _) _); [use isasetsetquot|].
          intros m.
          simpl.
          unfold unel.
          rewrite (setquotunivcomm quotrel).
          simpl. unfold quotmod_un.
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
    - exact (setquotpr quotrel).
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
             (is : iscomprelfun quotrel f) :
    modulefun quotmod N.
  Proof.
    use modulefunpair.
    - use setquotuniv.
      + exact f.
      + assumption.
    - split.
      + use mk_isbinopfun.
        simple refine (setquotuniv2prop quotrel (λ m n, hProppair _ _) _).
        * apply (pr2 (pr1 (pr1 (pr1 N)))).
        * intros m m'.
          simpl.
          unfold quotmod_op.
          rewrite setquotuniv2comm.
          do 3 rewrite (setquotunivcomm quotrel).
          apply modulefun_to_isbinopfun.
      + intros r.
        simple refine (setquotunivprop quotrel (λ m, hProppair _ _) _).
        * apply (pr2 (pr1 (pr1 (pr1 N)))).
        * intros m.
          simpl.
          assert (H : r * quotmod_quotmap m = quotmod_quotmap (r * m)).
          {
            rewrite <- modulefun_to_islinear.
            apply idpath.
          }
          simpl in H.
          rewrite H.
          do 2 rewrite (setquotunivcomm quotrel).
          apply modulefun_to_islinear.
  Defined.

End bla.
