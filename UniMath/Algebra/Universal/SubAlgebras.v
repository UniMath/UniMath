Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Export UniMath.Algebra.Universal.SortedTypes.
Require Export UniMath.Algebra.Universal.Signatures.
Require Export UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Algebras_eq.

Open Scope sorted.
Open Scope hom.

Section Embedding.

Definition embedding {σ : signature} (B A : algebra σ) :=
  ∑ (i : B s→ A), (∏ s, isincl (i s)) × (ishom i).

Definition make_embedding {σ : signature} {B A : algebra σ}
  (i : B s→ A)
  (ishom : ishom i)
  (isincl : ∏ s, isincl (i s))
  : embedding B A
  := (i,,(isincl,,ishom)).

Definition make_embedding' {σ : signature} {B A : algebra σ}
  (i : B ↷ A)
  (isincl : ∏ s, isincl (i s))
  : embedding B A
  := (hom2fun i,,(isincl,,hom2axiom i)).

Definition embedding_pr1 {σ : signature} {B A : algebra σ} (i:embedding B A)
  : B s→ A := pr1 i.

Definition embedding_hom {σ : signature} {B A : algebra σ} (i:embedding B A)
  : hom B A
  := (pr1 i,,pr22 i).
Coercion embedding_hom : embedding >-> hom.

Definition embedding_isincl {σ : signature} {B A : algebra σ} (i:embedding B A)
  : ∏ s, isincl (i s) := pr12 i.

Definition embedding_ishom {σ : signature} {B A : algebra σ} (i:embedding B A)
  : ishom i := pr22 i.

End Embedding.

Section SubUniverse.

Definition issubuniverse {σ : signature} (A : algebra σ) (B : shsubtype A): UU
  := ∏(nm : names σ) (xs : B⋆ (arity nm)),
    B (sort nm) (ops A nm ((λ s, pr1carrier (B s))⋆⋆ (arity nm) xs)).

Definition isapropissubuniverse {σ : signature} (A : algebra σ) (B : shsubtype A)
  : isaprop (issubuniverse A B).
Proof.
  use impred.
  intro.
  use impred.
  intro.
  use propproperty.
Qed.

(*TODO: use dispAlg to define this*)
Definition algebraofsubuniverse {σ : signature}
  {A : algebra σ} {B : shsubtype A}
  (is : issubuniverse A B)
  : algebra σ.
Proof.
  use make_algebra.
  - use B.
  - intros nm xs.
    cbn.
    use make_carrier.
    + use (ops A nm).
      use (h1map (λ s, pr1carrier (B s)) xs).
    + use is.
Defined.

Definition embeddingofsubuniverse {σ : signature}
  {A : algebra σ} {B : shsubtype A}
  (isB : issubuniverse A B)
  : embedding (algebraofsubuniverse isB) A.
Proof.
  use make_embedding.
  - intros s.
    use pr1carrier.
  - intros nm xs.
    apply idpath.
  - intros s.
    use isinclpr1.
    intro a. cbn beta.
    use propproperty.
Defined.


End SubUniverse.

Theorem issubuniverse_image {σ : signature} {A B: algebra σ} (f : B ↷ A) 
: issubuniverse A (simage_shsubtype f).
Proof.
  intros nm ys.
  use (squash_simage f (arity nm) ys (isapropishinh _)).
  intro fibers.
  use hinhpr.
  use tpair.
  - use ops.
    use (h2lower (h2map (λ s _, pr1) fibers)).
  - cbn.
    eapply pathscomp0.
    { use (hom2axiom f). }
    use maponpaths.
    use hvec_ofpaths.
    use (h2map _ fibers).
    intros s a _.
    use pr2.
Qed.

Section embedding_subuniverse_weq.

Context {σ : signature} (A : algebra σ).

Local Theorem algebraofsubuniverse_image
  (B : algebra σ) (i : embedding B A)
  : B = algebraofsubuniverse (issubuniverse_image i).
Proof.
  use make_algebra_eq.
  - use make_hom.
    + intro s.
      use prtoimage.
    + intros nm xs.
      use subtypePath.
      * intro.
        use propproperty.
      * simpl.
        eapply pathscomp0.
        { use embedding_ishom. }
        use maponpaths.
        use pathsinv0.
        use h1map_compose.
  - intro s.
    use isweqinclandsurj.
      * use isinclprtoimage.
        use embedding_isincl.
      * use issurjprtoimage.
Defined. 

Theorem aaa (extra : has_supportsets A):
  (∑ (B:algebra σ), embedding B A) ≃
  (∑ (PB : shsubtype A), issubuniverse A PB). 

Proof.
  use weq_iso.
  - intro B.
    destruct B as [B i].
    exact (simage_shsubtype i,,issubuniverse_image i).
  - intro B.
    destruct B as [PB is_su_PB].
    use (tpair _ (algebraofsubuniverse is_su_PB) (embeddingofsubuniverse is_su_PB)).
  - intros B.
    destruct B as [B i].
    use total2_paths2_f.
    + use pathsinv0.
      use algebraofsubuniverse_image.
    + admit.
      (* use subtypePath.
      { (*TODO: the [extra] hypothesis can probably be removed, but the proof of [algebraofsubuniverse_image] need to be better*)
        intro.
        use isapropdirprod.
        - use impred.
          intro.
          use isapropisincl.
        - use isapropishom.
          use extra. }
      eapply pathscomp0.
      { use (pr1_transportf (A:= algebra σ) (B:= λ B0, B0 s→ A)
          (P:= λ B0 i, (∏ s, isincl (i s)) × (ishom i))). }
      simpl.
      change (λ x : algebra σ, x s→ A) with (λ x: algebra σ, (support x) s→ A). *)
Abort.

End embedding_subuniverse_weq.