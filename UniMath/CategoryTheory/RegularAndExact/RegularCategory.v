(********************************************************************************************

 Regular categories

 In this file, we define regular categories. Regular categories are categories with
 - finite limits
 - coequalizers for kernel pairs
 such that regular epimorphisms are stable under pullback.

 If we have a morphism `f : X --> Y`, then the kernel pair of `f` is the pullback of `f` and
 `f`. In Set, this would represent the collection of all `(x , y) : X × Y` such that `f x = f y`.
 In a regular category, we can take the coequalizer of the projections in this pullback.
 Concretely, this means that we take `Y` where we identify all `f x` and `f y` where `x` and
 `y` are in the aforementioned pullback. This construction allows us to factor every morphism
 into a regular epimorphism followed by a monomorphism. In fact, this gives rise to an
 orthogonal factorization system, because regular epimorphisms have the left lifting property
 with respect to all monomorphisms.

 References
 - Chapter 2 in "Handbook of Categorical Algebra, Categories and Structures" by Borceux

 Contents
 1. Coequalizers of kernel pairs
 2. Regular categories
 3. Morphisms between kernel pairs (Lemma 2.1.2 in Borceux)
 4. Factorization in regular categories

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.

Local Open Scope cat.

(** * 1. Coequalizers of kernel pairs *)
Definition coeqs_of_kernel_pair
           (C : category)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (K : kernel_pair f),
     Coequalizer (PullbackPr1 K) (PullbackPr2 K).

Proposition isaprop_coeqs_of_kernel_pair
            (C : univalent_category)
  : isaprop (coeqs_of_kernel_pair C).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_Coequalizer.
  apply univalent_category_is_univalent.
Qed.

(** * 2. Regular categories *)
Definition is_regular_category
           (C : category)
  : UU
  := Terminal C
     ×
     Pullbacks C
     ×
     coeqs_of_kernel_pair C
     ×
     regular_epi_pb_stable C.

Definition is_regular_category_terminal
           {C : category}
           (HC : is_regular_category C)
  : Terminal C
  := pr1 HC.

Definition is_regular_category_pullbacks
           {C : category}
           (HC : is_regular_category C)
  : Pullbacks C
  := pr12 HC.

Definition is_regular_category_coeqs_of_kernel_pair
           {C : category}
           (HC : is_regular_category C)
  : coeqs_of_kernel_pair C
  := pr122 HC.

Definition is_regular_category_regular_epi_pb_stable
           {C : category}
           (HC : is_regular_category C)
  : regular_epi_pb_stable C
  := pr222 HC.

Proposition isaprop_is_regular_category
            (C : univalent_category)
  : isaprop (is_regular_category C).
Proof.
  repeat (use isapropdirprod).
  - apply isaprop_Terminal.
    apply univalent_category_is_univalent.
  - apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  - apply isaprop_coeqs_of_kernel_pair.
  - apply isaprop_regular_epi_pb_stable.
Qed.

(** * 3. Morphisms between kernel pairs (Lemma 2.1.2 in Borceux) *)
Section KernelPairMap.
  Context {C : category}
          (PB : Pullbacks C)
          (H : regular_epi_pb_stable C)
          {x y z : C}
          (f : x --> y)
          (g : y --> z)
          (h : x --> z)
          (p : f · g = h).

  Let Kgg : Pullback g g := PB _ _ _ g g.
  Let Khh : Pullback h h := PB _ _ _ h h.

  Definition kernel_pair_map
    : Khh --> Kgg.
  Proof.
    use PullbackArrow.
    - exact (PullbackPr1 Khh · f).
    - exact (PullbackPr2 Khh · f).
    - abstract
        (rewrite !assoc' ;
         rewrite !p ;
         apply PullbackSqrCommutes).
  Defined.

  Let Kl : Pullback f (PullbackPr1 Kgg) := PB _ _ _ f (PullbackPr1 Kgg).
  Let Kr : Pullback f (PullbackPr2 Kgg) := PB _ _ _ f (PullbackPr2 Kgg).

  Context (Hf : is_regular_epi f).

  Local Lemma is_regular_epi_left
    : is_regular_epi (PullbackPr2 Kl).
  Proof.
    exact (H _ _ _ _ _ _ _ _ _ (isPullback_Pullback Kl) Hf).
  Qed.

  Local Lemma is_regular_epi_right
    : is_regular_epi (PullbackPr2 Kr).
  Proof.
    exact (H _ _ _ _ _ _ _ _ _ (isPullback_Pullback Kr) Hf).
  Qed.

  Local Definition map_to_pullback_left
    : Khh --> Kl.
  Proof.
    use PullbackArrow.
    - apply PullbackPr1.
    - exact kernel_pair_map.
    - abstract
        (unfold kernel_pair_map ;
         rewrite PullbackArrow_PullbackPr1 ;
         apply idpath).
  Defined.

  Local Definition map_to_pullback_right
    : Khh --> Kr.
  Proof.
    use PullbackArrow.
    - apply PullbackPr2.
    - exact kernel_pair_map.
    - abstract
        (unfold kernel_pair_map ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Local Lemma map_to_pullback_sqr
    : map_to_pullback_left · PullbackPr2 Kl
      =
      map_to_pullback_right · PullbackPr2 Kr.
  Proof.
    unfold map_to_pullback_left, map_to_pullback_right.
    rewrite !PullbackArrow_PullbackPr2.
    apply idpath.
  Qed.

  Section IsPullback.
    Context {w : C}
            (k₁ : w --> Kl)
            (k₂ : w --> Kr)
            (r : k₁ · PullbackPr2 Kl = k₂ · PullbackPr2 Kr).

    Local Lemma is_pullback_sqr_mor_eq
      : k₁ · PullbackPr1 Kl · h = k₂ · PullbackPr1 Kr · h.
    Proof.
      rewrite <- !p.
      rewrite !assoc.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite (PullbackSqrCommutes Kl).
      rewrite (PullbackSqrCommutes Kr).
      rewrite !assoc.
      rewrite r.
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply PullbackSqrCommutes.
    Qed.

    Local Definition is_pullback_sqr_mor
      : w --> Khh.
    Proof.
      use PullbackArrow.
      - exact (k₁ · PullbackPr1 Kl).
      - exact (k₂ · PullbackPr1 Kr).
      - exact is_pullback_sqr_mor_eq.
    Defined.

    Local Proposition is_pullback_sqr_mor_pr1
      : is_pullback_sqr_mor · map_to_pullback_left = k₁.
    Proof.
      unfold is_pullback_sqr_mor, map_to_pullback_left.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback Kl)).
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        unfold kernel_pair_map.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback Kgg)).
        + rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr1.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc'.
          apply maponpaths.
          exact (PullbackSqrCommutes Kl).
        + rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr2.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr2.
          rewrite r.
          rewrite !assoc'.
          apply maponpaths.
          exact (PullbackSqrCommutes Kr).
    Qed.

    Local Proposition is_pullback_sqr_mor_pr2
      : is_pullback_sqr_mor · map_to_pullback_right = k₂.
    Proof.
      unfold is_pullback_sqr_mor, map_to_pullback_right.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback Kr)).
      - rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        unfold kernel_pair_map.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback Kgg)).
        + rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr1.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc'.
          rewrite (PullbackSqrCommutes Kl).
          rewrite !assoc.
          rewrite <- r.
          apply idpath.
        + rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr2.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr2.
          rewrite !assoc'.
          apply maponpaths.
          exact (PullbackSqrCommutes Kr).
    Qed.

    Local Proposition is_pullback_sqr_unique
      : isaprop
          (∑ hk,
           (hk · map_to_pullback_left = k₁)
           ×
           (hk · map_to_pullback_right = k₂)).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback Khh)).
      - pose (maponpaths (λ z, z · PullbackPr1 _) (pr12 φ₁ @ !(pr12 φ₂))) as s.
        cbn in s.
        unfold map_to_pullback_left in s.
        rewrite !assoc' in s.
        rewrite PullbackArrow_PullbackPr1 in s.
        exact s.
      - pose (maponpaths (λ z, z · PullbackPr1 _) (pr22 φ₁ @ !(pr22 φ₂))) as s.
        cbn in s.
        unfold map_to_pullback_right in s.
        rewrite !assoc' in s.
        rewrite PullbackArrow_PullbackPr1 in s.
        exact s.
    Qed.
  End IsPullback.

  Local Definition is_pullback_sqr
    : isPullback map_to_pullback_sqr.
  Proof.
    intros w k₁ k₂ r.
    use iscontraprop1.
    - apply is_pullback_sqr_unique.
    - simple refine (_ ,, _ ,, _).
      + exact (is_pullback_sqr_mor k₁ k₂ r).
      + apply is_pullback_sqr_mor_pr1.
      + apply is_pullback_sqr_mor_pr2.
  Qed.

  Definition isEpi_kernel_pair_map
    : isEpi kernel_pair_map.
  Proof.
    assert (kernel_pair_map = map_to_pullback_right · PullbackPr2 Kr) as q.
    {
      refine (!_).
      apply PullbackArrow_PullbackPr2.
    }
    rewrite q.
    use isEpi_comp.
    - use is_epi_regular_epi.
      exact (H _ _ _ _ _ _ _ _ _ is_pullback_sqr is_regular_epi_left).
    - use is_epi_regular_epi.
      exact is_regular_epi_right.
  Qed.
End KernelPairMap.

(** * 4. Factorization in regular categories *)
Section Factorization.
  Context {C : category}
          (PB : Pullbacks C)
          (QC : coeqs_of_kernel_pair C)
          (H : regular_epi_pb_stable C)
          {x y : C}
          (f : x --> y).

  Let K : kernel_pair f := PB _ _ _ f f.

  Definition regular_epi_mono_factorization_image
    : Coequalizer (PullbackPr1 K) (PullbackPr2 K)
    := QC x y f K.

  Let im := regular_epi_mono_factorization_image.

  Definition regular_epi_mono_factorization_epi
    : x --> im
    := CoequalizerArrow
         regular_epi_mono_factorization_image.

  Let e := regular_epi_mono_factorization_epi.

  Definition regular_epi_mono_factorization_mono
    : im --> y.
  Proof.
    use CoequalizerOut.
    - exact f.
    - abstract
        (apply PullbackSqrCommutes).
  Defined.

  Let m := regular_epi_mono_factorization_mono.

  Proposition regular_epi_mono_factorization_is_regular_epi
    : is_regular_epi e.
  Proof.
    use hinhpr.
    simple refine (_ ,, PullbackPr1 K ,, PullbackPr2 K ,, _ ,, _).
    - exact (CoequalizerEqAr im).
    - exact (isCoequalizer_Coequalizer im).
  Qed.

  Let K' : kernel_pair m := PB _ _ _ m m.

  Proposition regular_epi_mono_factorization_is_regular_is_monic_eq
    : PullbackPr1 K · CoequalizerArrow im · m = PullbackPr2 K · CoequalizerArrow im · m.
  Proof.
    rewrite !assoc'.
    unfold m, regular_epi_mono_factorization_mono.
    rewrite !CoequalizerCommutes.
    exact (PullbackSqrCommutes K).
  Qed.

  Proposition regular_epi_mono_factorization_comm
    : f = e · m.
  Proof.
    unfold e, m.
    unfold regular_epi_mono_factorization_epi, regular_epi_mono_factorization_mono.
    rewrite CoequalizerCommutes.
    apply idpath.
  Qed.

  Local Definition regular_epi_mono_factorization_is_regular_is_monic_mor
    : PullbackObject K --> PullbackObject K'.
  Proof.
    use kernel_pair_map.
    - exact e.
    - exact (!regular_epi_mono_factorization_comm).
  Defined.

  Let φ : PullbackObject K --> PullbackObject K'
    := regular_epi_mono_factorization_is_regular_is_monic_mor.

  Local Proposition is_epi_monic_mor
    : isEpi φ.
  Proof.
    apply isEpi_kernel_pair_map.
    - exact H.
    - exact regular_epi_mono_factorization_is_regular_epi.
  Qed.

  Local Lemma monic_mor_pr1
    : φ · PullbackPr1 K' = PullbackPr1 K · CoequalizerArrow im.
  Proof.
    apply PullbackArrow_PullbackPr1.
  Qed.

  Local Lemma monic_mor_pr2
    : φ · PullbackPr2 K' = PullbackPr2 K · CoequalizerArrow im.
  Proof.
    apply PullbackArrow_PullbackPr2.
  Qed.

  Local Lemma monic_mor_eq
    : PullbackPr1 K' = PullbackPr2 K'.
  Proof.
    use is_epi_monic_mor.
    rewrite monic_mor_pr1, monic_mor_pr2.
    exact (CoequalizerEqAr im).
  Qed.

  Proposition regular_epi_mono_factorization_is_regular_is_monic
    : isMonic m.
  Proof.
    intros w g h p.
    pose (ζ := PullbackArrow K' _ g h p).
    refine (!(PullbackArrow_PullbackPr1 K' _ g h p) @ _).
    refine (_ @ PullbackArrow_PullbackPr2 K' _ g h p).
    apply maponpaths.
    apply monic_mor_eq.
  Qed.

  Definition regular_epi_mono_factorization
    : ∑ (im : C)
        (e : x --> im)
        (m : im --> y),
      is_regular_epi e
      ×
      isMonic m
      ×
      f = e · m.
  Proof.
    simple refine (_ ,, e ,, m ,, _ ,, _ ,, _).
    - exact regular_epi_mono_factorization_is_regular_epi.
    - exact regular_epi_mono_factorization_is_regular_is_monic.
    - exact regular_epi_mono_factorization_comm.
  Defined.
End Factorization.

Definition regular_category_epi_mono_factorization
           {C : category}
           (HC : is_regular_category C)
           {x y : C}
           (f : x --> y)
  : ∑ (im : C)
      (e : x --> im)
      (m : im --> y),
     is_regular_epi e
     ×
     isMonic m
     ×
     f = e · m.
Proof.
  use regular_epi_mono_factorization.
  - exact (is_regular_category_pullbacks HC).
  - exact (is_regular_category_coeqs_of_kernel_pair HC).
  - exact (is_regular_category_regular_epi_pb_stable HC).
Defined.
