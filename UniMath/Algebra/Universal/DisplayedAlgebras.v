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

(*TODO: constructor*)

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
  Qed.

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
        (*TODO: put this as a lemma?*)
        use hvec_ofpaths.
        use (h2map _ xs).
        intros s a _.
        use pr2.
  Defined.

End DisplayedAlgebrasFromMorphisms.

Section weqHomDispAlg.

  Context {σ : signature} {B : algebra σ}.


  Lemma total_fibers  {A : algebra σ} (h : hom A B)
    : total_alg (fibers_dispalg h) = A.
  Proof.
    use make_algebra_eq.
    - use make_hom.
      + (*TODO: define this as an accessor*)
        intro s.
        intro fib.
        simpl in fib.
        exact (pr12 fib).
      + intros nm xs.
        simpl.
        use maponpaths.
        unfold starfun.
        unfold total_alg, dom, star in xs.
        simpl in xs.
        use h2map_transport_h1mapcompose.
    - admit.
  Abort.

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
      admit.
    - admit.

  Defined.

End weqHomDispAlg.