Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Local Open Scope cat.

Section RegularEpi.
  Context {C : category}
          {x y : C}
          (f : x --> y).

  Definition is_regular_epi
    : UU
    := ∃ (w : C)
         (g₁ : w --> x)
         (g₂ : w --> x)
         (p : g₁ · f = g₂ · f),
       isCoequalizer g₁ g₂ f p.

  Proposition isaprop_is_regular_epi
    : isaprop is_regular_epi.
  Proof.
    apply isapropishinh.
  Qed.
End RegularEpi.

Section RegularVersusEffective.
  Context {C : category}
          {x y : C}
          (f : x --> y)
          (PB : Pullbacks C).

  Let K : Pullback f f := PB y x x f f.

  Section CoeqKernelPair.
    Context {w : C}
            {g₁ g₂ : w --> x}
            (p : g₁ · f = g₂ · f)
            (H : isCoequalizer g₁ g₂ f p)
            (Coeq := make_Coequalizer g₁ g₂ f p H)
            {a : C}
            {h : x --> a}
            (q : PullbackPr1 K · h = PullbackPr2 K· h).

    Let φ : w --> K := PullbackArrow K _ g₁ g₂ p.
    Let pg₁ : φ · PullbackPr1 K = g₁
      := PullbackArrow_PullbackPr1 K _ g₁ g₂ p.
    Let pg₂ : φ · PullbackPr2 K = g₂
      := PullbackArrow_PullbackPr2 K _ g₁ g₂ p.

    Lemma is_regular_to_isEffective_mor_eq
      : g₁ · h = g₂ · h.
    Proof.
      rewrite <- pg₁, <- pg₂.
      rewrite !assoc'.
      rewrite q.
      apply idpath.
    Qed.

    Proposition is_regular_to_isEffective_unique
      : isaprop (∑ ζ, f · ζ = h).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (CoequalizerOutsEq Coeq).
      cbn.
      exact (pr2 ζ₁ @ !(pr2 ζ₂)).
    Qed.

    Definition is_regular_to_isEffective_mor
      : y --> a.
    Proof.
      use (CoequalizerOut Coeq _ h).
      exact is_regular_to_isEffective_mor_eq.
    Defined.

    Proposition is_regular_to_isEffective_comm
      : f · is_regular_to_isEffective_mor = h.
    Proof.
      apply (CoequalizerCommutes Coeq).
    Qed.
  End CoeqKernelPair.

  Definition is_regular_to_isEffective
             (HC : is_univalent C)
             (H : is_regular_epi f)
    : isEffective f.
  Proof.
    revert H.
    use factor_through_squash.
    {
      apply isaprop_isEffective.
      exact HC.
    }
    intros H.
    induction H as ( w & g₁ & g₂ & p & H ).
    pose (Coeq := make_Coequalizer _ _ _ _ H).
    simple refine (_ ,, _).
    - exact (PB _ _ _ f f).
    - intros a h q.
      use iscontraprop1.
      + exact (is_regular_to_isEffective_unique p H).
      + simple refine (_ ,, _).
        * exact (is_regular_to_isEffective_mor p H q).
        * apply is_regular_to_isEffective_comm.
  Qed.

  Definition isEffective_to_is_regular
             (H : isEffective f)
    : is_regular_epi f.
  Proof.
    use hinhpr.
    pose (P := pr1 H : Pullback f f).
    refine (_ ,, _ ,, _ ,, PullbackSqrCommutes P ,, _).
    exact (pr2 H).
  Qed.

  Definition isEffective_weq_is_regular
             (HC : is_univalent C)
    : isEffective f ≃ is_regular_epi f.
  Proof.
    use weqimplimpl.
    - exact isEffective_to_is_regular.
    - exact (is_regular_to_isEffective HC).
    - apply isaprop_isEffective.
      exact HC.
    - apply isaprop_is_regular_epi.
  Defined.
End RegularVersusEffective.

Proposition is_epi_regular_epi
            {C : category}
            {x y : C}
            (f : x --> y)
  : is_regular_epi f → isEpi f.
Proof.
  use factor_through_squash.
  {
    apply isapropisEpi.
    apply homset_property.
  }
  intros ( w & g₁ & g₂ & p & H ).
  pose (Coeq := make_Coequalizer _ _ _ _ H).
  intros z h₁ h₂ q.
  assert (g₁ · (f · h₁) = g₂ · (f · h₁)) as r.
  {
    rewrite !assoc.
    rewrite p.
    apply idpath.
  }
  assert (h₁ = CoequalizerOut Coeq z (f · h₁) r) as s₁.
  {
    use (CoequalizerOutsEq Coeq).
    rewrite CoequalizerCommutes.
    apply idpath.
  }
  refine (s₁ @ _).
  use (CoequalizerOutsEq Coeq).
  rewrite CoequalizerCommutes.
  exact q.
Qed.

Proposition z_iso_is_regular_epi
            {C : category}
            {x y : C}
            (f : z_iso x y)
  : is_regular_epi f.
Proof.
  use hinhpr.
  refine (y ,, inv_from_z_iso f ,, inv_from_z_iso f ,, idpath _ ,, _).
  intros z h q.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use (cancel_z_iso' f).
    exact (pr2 φ₁ @ !(pr2 φ₂)).
  - simple refine (_ ,, _).
    + exact (inv_from_z_iso f · h).
    + cbn.
      rewrite !assoc.
      rewrite z_iso_inv_after_z_iso.
      apply id_left.
Qed.

Proposition is_z_isomorphism_is_regular_epi
            {C : category}
            {x y : C}
            (f : x --> y)
            (Hf : is_z_isomorphism f)
  : is_regular_epi f.
Proof.
  exact (z_iso_is_regular_epi (f ,, Hf)).
Qed.

Proposition is_regular_epi_arrow_z_iso_f
            {C : category}
            {x₁ x₂ y₁ y₂ : C}
            (f₁ : x₁ --> y₁)
            (f₂ : x₂ --> y₂)
            (i₁ : z_iso x₁ x₂)
            (i₂ : z_iso y₁ y₂)
            (p : f₁ · i₂ = i₁ · f₂)
  : is_regular_epi f₁ → is_regular_epi f₂.
Proof.
  assert (inv_from_z_iso i₁ · f₁ = f₂ · inv_from_z_iso i₂) as p'.
  {
    use z_iso_inv_on_left.
    rewrite !assoc'.
    refine (!_).
    use z_iso_inv_on_right.
    exact p.
  }
  use factor_through_squash.
  {
    apply isaprop_is_regular_epi.
  }
  intros ( w & g₁ & g₂ & q & H ).
  pose (Coeq := make_Coequalizer _ _ _ _ H).
  use hinhpr.
  simple refine (w ,, g₁ · i₁ ,, g₂ · i₁ ,, _ ,, _).
  - abstract
      (rewrite !assoc' ;
       rewrite <- !p ;
       rewrite !assoc ;
       rewrite q ;
       apply idpath).
  - intros z h r.
    use iscontraprop1.
    + use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (cancel_z_iso' i₂).
      use (CoequalizerOutsEq Coeq).
      cbn.
      rewrite !assoc.
      rewrite !p.
      rewrite !assoc'.
      apply maponpaths.
      exact (pr2 φ₁ @ !(pr2 φ₂)).
    + simple refine (_ ,, _).
      * simple refine (inv_from_z_iso i₂ · CoequalizerOut Coeq _ _ _).
        ** exact (i₁ · h).
        ** abstract
            (rewrite !assoc ;
             exact r).
      * cbn.
        refine (assoc _ _ _ @ _).
        rewrite <- p'.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (CoequalizerCommutes Coeq).
        }
        rewrite !assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
Qed.





Definition preserves_regular_epi
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y),
     is_regular_epi f
     → is_regular_epi (#F f).

Proposition isaprop_preserves_regular_epi
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
  : isaprop (preserves_regular_epi F).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_regular_epi.
Qed.

Definition regular_epi_pb_stable
           (C : category)
  : UU
  := ∏ (pb x y z : C)
       (f : x --> z)
       (g : y --> z)
       (π₁ : pb --> x)
       (π₂ : pb --> y)
       (p : π₁ · f = π₂ · g)
       (H : isPullback p),
     is_regular_epi f
     → is_regular_epi π₂.

Proposition isaprop_regular_epi_pb_stable
            (C : category)
  : isaprop (regular_epi_pb_stable C).
Proof.
  do 11 (use impred ; intro).
  apply isaprop_is_regular_epi.
Qed.



Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.

Definition to_regular_epi_in_slice
           {C : category}
           {x : C}
           {yg₁ zg₂ : C/x}
           {hp : yg₁ --> zg₂}
           (H : is_regular_epi (pr1 hp))
  : is_regular_epi hp.
Proof.
  revert H.
  use factor_through_squash.
  {
    apply isaprop_is_regular_epi.
  }
  intros H.
  induction H as ( w & g₁ & g₂ & p & H ).
  use hinhpr.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (make_cod_fib_ob (g₁ · cod_mor yg₁)).
  - use make_cod_fib_mor.
    + exact g₁.
    + abstract
        (cbn ;
         apply idpath).
  - use make_cod_fib_mor.
    + exact g₂.
    + abstract
        (cbn ;
         rewrite <- (mor_eq hp) ; cbn ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (!p)).
  - abstract
      (use eq_mor_cod_fib ;
       rewrite !comp_in_cod_fib ; cbn ;
       exact p).
  - use is_coequalizer_cod_fib.
    + exact p.
    + exact H.
Qed.

Definition from_regular_epi_in_slice
           {C : category}
           {x : C}
           {yg₁ zg₂ : C/x}
           {hp : yg₁ --> zg₂}
           (H : is_regular_epi hp)
  : is_regular_epi (pr1 hp).
Proof.
(*
  Idea:
  - characterize regular epis as strong epis
    (strong epis being left orthogonal to monos)
  - we need the epi-mono factorization
 *)
Admitted.


Section PullbackStable.
  Context {C : category}
          (PB : Pullbacks C).

  Section PreservesFromStable.
    Context (H : regular_epi_pb_stable C)
            {x y : C}
            (f : x --> y)
            {zg₁ zg₂ : C/y}
            (hp : zg₁ --> zg₂).

    Let z₁ : C := cod_dom zg₁.
    Let z₂ : C := cod_dom zg₂.
    Let g₁ : z₁ --> y := cod_mor zg₁.
    Let g₂ : z₂ --> y := cod_mor zg₂.
    Let h : z₁ --> z₂ := dom_mor hp.

    Let P₁ : Pullback g₁ f := PB _ _ _ g₁ f.
    Let π₁ : P₁ --> z₁ := PullbackPr1 P₁.
    Let π₂ : P₁ --> x := PullbackPr2 P₁.

    Let P₂ : Pullback g₂ f := PB _ _ _ g₂ f.
    Let ρ₁ : P₂ --> z₂ := PullbackPr1 P₂.
    Let ρ₂ : P₂ --> x := PullbackPr2 P₂.

    Context (r : π₁ · h · g₂ = π₂ · f).

    Let k : P₁ --> P₂
      := PullbackArrow P₂ P₁ (π₁ · h) π₂ r.

    Lemma regular_epi_pb_stable_to_pb_preserves_pb_sqr_eq
      : π₁ · h = k · ρ₁.
    Proof.
      refine (!_).
      apply PullbackArrow_PullbackPr1.
    Qed.

    Lemma regular_epi_pb_stable_to_pb_preserves_pb_sqr
      : isPullback regular_epi_pb_stable_to_pb_preserves_pb_sqr_eq.
    Proof.
      intros w l l' q.
      use iscontraprop1.
      - use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback P₁)).
        + exact (pr12 ζ₁ @ !(pr12 ζ₂)).
        + pose (maponpaths (λ z, z · PullbackPr2 P₂) (pr22 ζ₁ @ !(pr22 ζ₂))) as qr.
          cbn in qr.
          rewrite !assoc' in qr.
          unfold k in qr.
          rewrite !PullbackArrow_PullbackPr2 in qr.
          exact qr.
      - simple refine (_ ,, _ ,, _).
        + use PullbackArrow.
          * exact l.
          * exact (l' · ρ₂).
          * refine (maponpaths (λ z, _ · z) (!(mor_eq hp)) @ _).
            rewrite !assoc.
            refine (maponpaths (λ z, z · _) q @ _).
            rewrite !assoc'.
            apply maponpaths.
            apply PullbackSqrCommutes.
        + apply PullbackArrow_PullbackPr1.
        + use (MorphismsIntoPullbackEqual (isPullback_Pullback P₂)).
          * unfold k.
            refine (assoc' _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            refine (assoc _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            exact q.
          * unfold k.
            refine (assoc' _ _ _ @ _).
            rewrite !PullbackArrow_PullbackPr2.
            apply idpath.
    Qed.

    Let HP' := regular_epi_pb_stable_to_pb_preserves_pb_sqr.
    Let P' := make_Pullback _ HP'.

    Lemma regular_epi_pb_stable_to_pb_preserves_lem
          (Hp : is_regular_epi hp)
      : is_regular_epi k.
    Proof.
      use (H _ _ _ _ _ _ _ _ _ HP').
      apply from_regular_epi_in_slice.
      exact Hp.
    Qed.
  End PreservesFromStable.

  Definition regular_epi_pb_stable_to_pb_preserves
             (H : regular_epi_pb_stable C)
             {x y : C}
             (f : x --> y)
    : preserves_regular_epi (cod_pb PB f).
  Proof.
    intros g h p Hp.
    use to_regular_epi_in_slice.
    rewrite cod_fiber_functor_on_mor.
    exact (regular_epi_pb_stable_to_pb_preserves_lem H f p _ Hp).
  Qed.

  Definition pb_preserves_to_regular_epi_pb_stable
             (H : ∏ (x y : C)
                    (f : x --> y),
                  preserves_regular_epi (cod_pb PB f))
    : regular_epi_pb_stable C.
  Proof.
    intros pb x y z f g π₁ π₂ p Hp Hf.
    specialize (H _ _ g _ _ (mor_to_cod_fib_id (make_cod_fib_ob f))).
    assert (is_regular_epi (mor_to_cod_fib_id (make_cod_fib_ob f))).
    {
      use to_regular_epi_in_slice.
      exact Hf.
    }
    specialize (H X).
    clear X.
    apply from_regular_epi_in_slice in H.
    rewrite cod_fiber_functor_on_mor in H.
    simpl in H.
     *)
    (*
      we also need some properties of regular epimorphisms
      i.e., closed under isomorphism in the arrow category
     *)
  Admitted.

  Definition regular_epi_pb_stable_weq_pb_preserves
    : regular_epi_pb_stable C
      ≃
      ∏ (x y : C) (f : x --> y), preserves_regular_epi (cod_pb PB f).
  Proof.
    use weqimplimpl.
    - exact (λ H x y f, regular_epi_pb_stable_to_pb_preserves H f).
    - admit.
    - apply isaprop_regular_epi_pb_stable.
    - do 3 (use impred ; intro).
      apply isaprop_preserves_regular_epi.
