Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Algebras_eq.
Require Import UniMath.Algebra.Universal.SortedTypes.
Require Import UniMath.Algebra.Universal.HVectors.

Section Definitions.

Context {σ:signature}.

Definition disp_alg (A:algebra σ) :=
  ∑ fib : (∏ (s: sorts σ) (a : support A s), UU),
    ∏ (nm: names σ) (base_xs : hvec (vec_map A (arity nm))),
      hvec (h1map_vec (v:= (arity nm)) fib base_xs)
      → (fib (sort nm) (ops A nm (base_xs))).

Definition make_disp_alg {A:algebra σ}
  (fib : (∏ (s: sorts σ) (a : support A s), UU))
  (overops : ∏ (nm: names σ) (base_xs : hvec (vec_map A (arity nm))),
    hvec (h1map_vec (v:= (arity nm)) fib base_xs) → (fib (sort nm) (ops A nm (base_xs))))
  : disp_alg A
  := fib,, overops.

(*Accessors*)
  Definition fib {A:algebra σ} (D: disp_alg A)
  : (∏ (s: sorts σ) (a : support A s), UU) := pr1 D.
  Definition overops {A:algebra σ} (D: disp_alg A)
    (nm: names σ) (base_xs : hvec (vec_map A (arity nm)))
  : hvec (h1map_vec (v:= (arity nm)) (fib D) base_xs) → ((fib D) (sort nm) (ops A nm (base_xs))) := pr2 D nm base_xs.


Definition total_alg {A: algebra σ} (D: disp_alg A) : algebra σ.
Proof.
  use make_algebra.
  - intro s.
    exact (∑(a: A s), fib D s a).
  - intros nm xs.
    use tpair.
    + exact (ops A nm (h1map (λ s, pr1) xs)).
    + use overops. (*TODO: can we define this without transport and/or a new "map" variant ?*)
      use (transportb (λ arg, hvec (h1lower arg)) (h1map_compose (λ s, pr1) (fib D) xs)).
      use (h12map (λ s, pr2) xs).
Defined.

End Definitions.

  Lemma transportf_overops
    {σ : signature} {B : algebra σ}
    (D : disp_alg B)
    {nm : names σ}
    {base_xs base_xs' : hvec (vec_map B (arity nm))}
    (fiber : hvec (h1lower (h1map (pr1 D) base_xs)))
    (e : base_xs = base_xs')
:
    transportf
    (λ x : hvec (vec_map B (arity nm)), fib D (sort nm) (ops B nm x))
    e (overops D nm base_xs fiber)
    =
    overops D nm base_xs' (transportf (λ bs, hvec (h1lower (h1map (fib D) bs))) e fiber).
  Proof.
    induction e.
    apply idpath.
  Defined.

Section ForgetfulMorphism.

  Local Open Scope hom.

  Context {σ:signature} {A: algebra σ} (D: disp_alg A).

  Definition forgetful_sfun : total_alg D s→ A.
  Proof.
    intro s.
    use pr1.
  Defined.

  Lemma forgetful_ishom : ishom (forgetful_sfun).
  Proof.
    intros nm xs.
    apply idpath.
  Defined.

  Definition forgetful_hom : total_alg D ↷ A.
  Proof.
    use make_hom.
    - use forgetful_sfun.
    - use forgetful_ishom.
  Defined.

End ForgetfulMorphism.

Section SubAlgebrasAsTotalAlgebras.

  (**
    If all the fibers are propositions then the total algebra is a sub-algebra of the base one.
    The inclusion is given by the forgetful_hom.
    We show it is indeed an inclusion
  *)

  Context {σ:signature} (A: algebra σ) (D: disp_alg A)
    (fiberinprop: ∏ (s: sorts σ) (a : support A s), isaprop (fib D s a)).

  Theorem isincl_forgetful : ∏ (s: sorts σ), isincl (forgetful_hom D s).
  Proof.
    intros s.
    use isinclpr1.
    use fiberinprop.
  Qed.

End SubAlgebrasAsTotalAlgebras.

Section DisplayedAlgebrasFromMorphisms.

  Definition fibers_dispalg {σ : signature} {A B : algebra σ}
    (h : hom A B)
  : disp_alg B.
  Proof.
    use make_disp_alg.
    - exact (shfiber h).
    - intros nm bs xs.
      use tpair.
      + use (ops A nm).
        unfold star.
        exact (h2lower (h2map (λ a b, pr1) xs)).
      + simpl.
        eapply pathscomp0.
        { use (hom2axiom h). }
        apply maponpaths.
        use hvec_of_shfiber.
  Defined.

End DisplayedAlgebrasFromMorphisms.

Section weqHomDispAlg.

  Context {σ : signature} {B : algebra σ}.
  Context (setprop : has_supportsets B).

  Definition total_fibers_sfun {A : algebra σ} (h : hom A B)
    : total_alg (fibers_dispalg h) s→ A.
  Proof.
    intro s.
    intro fib.
    simpl in fib.
    exact (pr12 fib).
  Defined.

  Lemma total_fibers {A : algebra σ} (h : hom A B)
    : total_alg (fibers_dispalg h) = A.
  Proof.
    use make_algebra_eq.
    - use make_hom.
      + apply total_fibers_sfun.
      + intros nm xs.
        unfold total_fibers_sfun.
        simpl.
        use maponpaths.
        unfold starfun.
        unfold total_alg, dom, star in xs.
        simpl in xs.
        use h2map_transport_h1mapcompose.
    - intros s.
      simpl.
      unfold total_fibers_sfun.
      use isweq_iso.
      + intro a.
        use (tpair _ (h s a)).
        simpl.
        use (tpair _ a).
        apply idpath.
      + simpl.
        intros.
        destruct x as [b fib].
        destruct fib as [a e].
        simpl.
        destruct e.
        apply idpath.
      + simpl.
        apply idpath.
  Defined.

  Lemma shfiber_forgetful_hom (D : disp_alg B)
  : shfiber (forgetful_hom D) = fib D.
  Proof.
    simpl.
    use funextsec.
    intro s.
    use funextsec.
    intro b.
    use weqtopaths.
    use weq_iso.
    - intro fib.
      use (transportf _ (shfiber_path fib) _).
      use (pr2 (shfiber_fiber fib)).
    - intro d.
      unfold shfiber.
      use tpair.
      + use (tpair _ b d).
      + apply idpath.
    - simpl.
      intro fib.
      simpl.
      use subtypePath.
      { intro.
        use setprop. }
      simpl.
      use total2_paths2_f.
      + use pathsinv0.
        use (shfiber_path fib).
      + induction (shfiber_path fib).
        apply idpath.
    - simpl.
      apply idpath.
  Defined.

  Lemma transportb_hvecmap_shfiber_forgetful_hom
    (D : disp_alg B)
    (nm : names σ)
    (base_xs : hvec (vec_map B (arity nm)))
    : transportb
      (λ D0 : ∏ a : sorts σ, B a → UU, hvec (h1lower (h1map D0 base_xs)))
      (shfiber_forgetful_hom D)
    = h2map (λ (s : sorts σ) (b : B s) (d : fib D s b), (b,, d),, idpath b).
  Proof.
    use funextsec.
    intro fiber.
    eapply pathscomp0.
    { use transportb_h2vec. }
    simpl.
    use (maponpaths (λ arg, h2map arg fiber)).
    use funextsec. intro s.
    use funextsec. intro b.
    use funextsec. intro d.
    eapply pathscomp0.
    { use (transportb_funextsec_op
        (S:= sorts σ)
        (A:= B) _ _ _ s b d).
      exact (arity nm). }
    simpl.
    eapply pathscomp0.
    { use (transportb_funextfun (idfun UU) (X:= B s) _ _ _ b d). }
    simpl.
    eapply pathscomp0.
    { fold (idfun UU).
      eapply (toforallpaths _ (transportb (idfun UU) (weqtopaths _))).
      change (λ x0 : UU, x0) with (idfun UU).
      use weqpath_transportb'. }
    reflexivity.
  Defined.

  Lemma fibers_dispalg_forgetful_hom (D : disp_alg B)
  : fibers_dispalg (forgetful_hom D) = D.
  Proof.
    use total2_paths2_f.
    - use shfiber_forgetful_hom.
    - simpl.
      eapply pathscomp0.
      { use (transportf_sec_constant
          (A:= ∏ s : sorts σ, B s → UU)
          (B:= names σ)
          (C:= λ fib0 nm, ∏ (base_xs : hvec (vec_map B (arity nm))),
    hvec (h1map_vec fib0 base_xs) → fib0 (sort nm) (ops B nm base_xs))
          _ _). }
      use funextsec.
      intro nm.
      eapply pathscomp0.
      { use (transportf_sec_constant
          (A:= ∏ s : sorts σ, B s → UU)
          (B:= hvec (vec_map B (arity nm)))
          (C:= λ fib0 base_xs, hvec (h1map_vec fib0 base_xs) → fib0 (sort nm) (ops B nm base_xs))
          _ _). }
      use funextsec.
      intro base_xs.
      unfold h1map_vec.
      eapply pathscomp0.
      { use transportf_fun_op2. }
      rewrite (transportb_hvecmap_shfiber_forgetful_hom D). (*Doable without rewrite?*)
      unfold funcomp.
      use funextsec.
      intro fiber.
      eapply pathscomp0.
      { use transportf_funextsec_op.
        exact (arity nm). }
      eapply pathscomp0.
      { use (transportf_funextfun (idfun UU)). }
      simpl.
      eapply pathscomp0.
      { eapply (toforallpaths _ (transportf (λ x0 : UU, x0) (weqtopaths _))).
        change (λ x0 : UU, x0) with (idfun UU).
        use weqpath_transport. }
      simpl.
      eapply pathscomp0.
      { use (!functtransportf _ _ _ _). }
      eapply pathscomp0.
      { use (transportf_overops _ _ _). }
      use maponpaths.
      unfold hvec_of_shfiber.
      eapply pathscomp0.
      { use transport_hvec_ofpaths. }
      eapply pathscomp0.
      { apply h2map_compose. }
      apply h2map_idfun.
    Defined.

  Theorem morphism_dispalg_weq :
    (∑ (A:algebra σ), hom A B) ≃ (disp_alg B).
  Proof.
    use weq_iso.
    - intro A.
      destruct A as [A h].
      use (fibers_dispalg h).
    - intro D.
      use tpair.
      + use (total_alg D).
      + use forgetful_hom.
    - intros A.
      destruct A as [A h].
      use total2_paths2_f.
      + use total_fibers.
      + use subtypePath.
        * intro.
          use isapropishom.
          use setprop.
        * eapply pathscomp0.
          { unfold hom.
            use (pr1_transportf (P:= λ x h, ishom h)). }
          use funextsec.
          intros s.
          eapply pathscomp0.
          { use transportf_sfun. }
          use funextsec.
          intros a.
          simpl.
          unfold forgetful_sfun.
          eapply pathscomp0.
          { eapply (maponpaths pr1).
            use (functtransportb support (λ x, x s) (total_fibers h) a). }
          (*TODO: code almost repeated from [embeddingofsubuniverse_image]*)
          unfold total_fibers.
          rewrite support_make_algebra_eq.
          unfold make_algebra_support_eq.
          eapply pathscomp0.
          { eapply (maponpaths pr1).
            eapply pathscomp0.
            { use (transportb_funextfun (idfun UU)). }
            simpl.
            refine (toforallpaths _ _ _ _ a).
            use weqpath_transportb'. }
          apply idpath.
    - simpl.
      intros D.
      use fibers_dispalg_forgetful_hom.
  Defined.

End weqHomDispAlg.