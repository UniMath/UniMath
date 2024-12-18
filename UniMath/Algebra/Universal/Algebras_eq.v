Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Universal.Algebras.

Local Open Scope sorted.
Local Open Scope hom_scope.

Theorem make_algebra_eq {σ : signature} {A B : algebra σ}
  (h : A ↷ B) (isweq : ∏ s:(sorts σ), isweq (h s))
  : A = B.
Proof.
  use total2_paths2_f.
  - use funextsec.
    intro s.
    use weqtopaths.
    exact (h s ,, isweq s).
  - eapply pathscomp0. 
    { use transportf_sec_constant. }
    use funextsec.
    intro nm.
    eapply pathscomp0. 
    { use transportf_fun_op. }
    use funextsec.
    intro xs.
    simpl.
    eapply pathscomp0.
    { use (transportf_funextfun (λ arg, arg) _ _ _ (sort nm)). }
    change (λ x0 : UU, x0) with (idfun UU).
    simpl.
    change (λ x0 : UU, x0) with (idfun UU).
    eapply pathscomp0.
    { use (maponpaths (λ arg, arg _) (weqpath_transport _)). }
    cbn.
    eapply pathscomp0.
    { eapply (maponpaths (h (sort nm))).
      eapply (maponpaths (ops A nm)).
      use transportb_funextfun_hvec. }
    simpl.
    eapply pathscomp0.
    { use (pr2 h). }
    use maponpaths.
    unfold starfun.
    eapply pathscomp0.
    { use h1map_compose. }
    simpl.
    eapply pathscomp0.
    2 :{ use h1map_idfun. }
    use (maponpaths (λ arg, h1map arg xs)).
    use funextsec.
    intro s.
    simpl.
    use funextsec.
    intro b.
    simpl.
    use (pathsweq1' (h s,, isweq s)).
    use (maponpaths (λ arg, arg b)).
    use weqpath_transportb'.
Defined.