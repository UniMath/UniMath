(** * Translation functors *)
(**
- Translation functors for C(A)
 - T ∘ T^{-1} = Id
 - Translation functors form equivalence
- Translation functors for K(A)
 - T ∘ T^{-1} = Id
 - Translation functors form equivalence
*)
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.
Require Import UniMath.HomologicalAlgebra.KA.

Unset Kernel Term Sharing.

Open Scope hz_scope.
Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommrngops ZeroArrow.

(** * Translation funtor for C(A) and for K(A) *)
(** ** Introduction
We define the translation functor T : C(A) -> C(A) for complexes, and a translation functor
T' : K(A) -> K(A). The functor T' is constructed so that we have the following commutative
diagram
                            C(A) ---T---> C(A)
                             |             |
                            K(A) ---T'--> K(A)
Here the vertical functors are given by [ComplexHomotFunctor]. The functor T sends a complex
      # ... -> X^{i-1} --(d^{i-1})--> X^i --(d^i)--> X^{i+1} -> ... #
      $ ... -> X^{i-1} --(d^{i-1})--> X^i --(d^i)--> X^{i+1} -> ... $
to the complex
      # ... -> X^i --(-d^i)--> X^{i+1} --(-d^{i+1})--> X^{i+2} -> ... #
      $ ... -> X^i --(-d^i)--> X^{i+1} --(-d^{i+1})--> X^{i+2} -> ... $
More precicely, on objects # X^i ↦ X^{i+1} # $ X^i ↦ X^{i+1} $ and differentials
# d^i_X ↦ -d^{i+1}_X # $ d^i_X ↦ -d^{i+1}_X $. A morphism f : X -> Y is mapped by
# f^i ↦ f^{i+1} # $ f^i ↦ f^{i+1} $. We also construct the inverse translation T^{-1} which is the
unique functor such that T ∘ T^{-1} = id and T^{-1} ∘ T = id. All the functors T, T^{-1}, and T'
are additive.

The functor T : C(A) -> C(A) is constructed in [TranslationFunctor]. It is shown to be additive in
[TranslationFunctor_Additive]. In [TranslationFunctorPreservesHomotopies] we show that T preserves
homotopies, that is if f is homotopic to g, then T(f) is homotopic to T(g). In
[InvTranslationFunctor] we construct T^{-1}.
*)
Section translation_functor.

  Variable A : Additive.


  (** ** Translation functor for C(A) *)

  Local Lemma TranslationFunctor_comp (C : Complex A) (i : hz) :
    (to_inv (Diff C (i + 1))) · (to_inv (Diff C (i + 1 + 1))) =
    ZeroArrow (Additive.to_Zero A) (C (i + 1)) (C (i + 1 + 1 + 1)).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq. apply (DSq A C (i + 1)).
  Qed.

  Definition TranslationComplex (C : Complex A) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (C (i + 1)).
    - intros i. exact (to_inv (Diff C (i + 1))).
    - intros i. exact (TranslationFunctor_comp C i).
  Defined.
  Global Transparent TranslationComplex.

  Definition DiffTranslationComplex (C : Complex A) (i : hz) :
    A⟦ TranslationComplex C i, TranslationComplex C (i + 1) ⟧ := to_inv (Diff C (i + 1)).
  Global Transparent DiffTranslationComplex.

  Lemma DiffTranslationComplex_comp (C : Complex A) (i : hz) :
    (DiffTranslationComplex C i) · (DiffTranslationComplex C (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    exact (TranslationFunctor_comp C i).
  Qed.

  Definition TranslationMorphism_mor {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A⟦TranslationComplex C1 i, TranslationComplex C2 i⟧ := f (i + 1).

  Local Lemma TranslationFunctor_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (TranslationMorphism_mor f i) · (DiffTranslationComplex C2 i) =
    (DiffTranslationComplex C1 i) · (TranslationMorphism_mor f (i + 1)).
  Proof.
    unfold DiffTranslationComplex.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    apply maponpaths. apply (MComm f (i + 1)).
  Qed.

  Definition TranslationMorphism (C1 C2 : Complex A) (f : Morphism C1 C2) :
    Morphism (TranslationComplex C1) (TranslationComplex C2) :=
    mk_Morphism
      A (TranslationComplex C1) (TranslationComplex C2)
      (λ i : hz, TranslationMorphism_mor f i) (λ i : hz, TranslationFunctor_comm f i).

  Definition TranslationFunctor_data :
    functor_data (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (TranslationComplex C).
    - intros C1 C2 f. exact (TranslationMorphism C1 C2 f).
  Defined.

  Lemma TranslationFunctor_isfunctor : is_functor TranslationFunctor_data.
  Proof.
    split.
    - intros C. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - intros C1 C2 C3 f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
  Qed.

  Definition TranslationFunctor :
    functor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor.
    - exact TranslationFunctor_data.
    - exact TranslationFunctor_isfunctor.
  Defined.

  Definition TranslationFunctor_isAdditive : isAdditiveFunctor TranslationFunctor.
  Proof.
    use mk_isAdditiveFunctor.
    intros C1 C2.
    split.
    - intros f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - cbn. use MorphismEq. intros i. apply idpath.
  Qed.

  Definition TranslationFunctor_Additive :
    AdditiveFunctor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact TranslationFunctor.
    - exact TranslationFunctor_isAdditive.
  Defined.

  (** *** Translation functor preserves homotopies *)
  Definition TranslationHomot {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomot A (TranslationComplex C1) (TranslationComplex C2).
  Proof.
    intros i.
    exact (transportf (precategory_morphisms (C1 (i + 1)))
                      (maponpaths C2 (hzrplusminus i 1 @ ! hzrminusplus i 1))
                      (to_inv (H (i + 1)))).
  Defined.

  Lemma TranslationFunctorHomotopies {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomotMorphism A (TranslationHomot H) =
    TranslationMorphism C1 C2 (ComplexHomotMorphism A H).
  Proof.
    unfold TranslationHomot. cbn. use MorphismEq. intros i. cbn.
    induction (hzrminusplus i 1). cbn. rewrite pathscomp0rid. cbn. unfold idfun.
    rewrite <- PreAdditive_invrcomp. rewrite <- transport_target_to_inv.
    rewrite PreAdditive_invlcomp. rewrite inv_inv_eq.
    rewrite <- transport_target_to_inv.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq.
    assert (e : (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus (i - 1 + 1) 1)) =
                (maponpaths C2 (maponpaths (λ (i0 : hz), i0 + 1) (hzrplusminus (i - 1 + 1) 1)))).
    {
      induction (hzrplusminus (i - 1 + 1) 1). apply idpath.
    }
    cbn in e. rewrite e. clear e.
    (* The first elements of to_binop are the same *)
    assert (e1 : (transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                             (maponpaths C2 (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                        (hzrplusminus (i - 1 + 1) 1)))
                             ((Diff C1 (i - 1 + 1 + 1))
                                · (transportf
                                      (precategory_morphisms (C1 (i - 1 + 1 + 1 + 1)))
                                      (maponpaths C2
                                                  (hzrplusminus (i - 1 + 1 + 1) 1 @
                                                                ! hzrminusplus (i - 1 + 1 + 1) 1))
                                      (H (i - 1 + 1 + 1 + 1)))) =
                  (transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                              (maponpaths C2 (hzrplusminus (i - 1 + 1 + 1) 1))
                              (Diff C1 (i - 1 + 1 + 1) · H (i - 1 + 1 + 1 + 1))))).
    {
      rewrite transport_target_postcompose. rewrite transport_f_f. rewrite <- maponpathscomp0.
      set (tmp := ((hzrplusminus (i - 1 + 1 + 1) 1
                                 @ ! hzrminusplus (i - 1 + 1 + 1) 1)
                     @ maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrplusminus (i - 1 + 1) 1))).
      assert (ee : tmp = (hzrplusminus (i - 1 + 1 + 1) 1)) by apply isasethz.
      unfold tmp in ee. cbn in ee. unfold tmp. cbn. rewrite ee. clear ee. clear tmp.
      induction (hzrplusminus (i - 1 + 1 + 1) 1). cbn. unfold idfun. apply idpath.
    }
    cbn in e1. rewrite e1. clear e1. use to_lrw.
    (* Show that the first elements of to_binop are the same *)
    set (tmp := @transport_hz_source_target A C2 1 (Diff C2) _ _ (hzrplusminus (i - 1 + 1) 1)).
    rewrite tmp. clear tmp. rewrite transport_compose.
    rewrite transport_target_postcompose. apply cancel_precomposition.
    rewrite transport_f_f. rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
    rewrite pathsinv0r. rewrite <- functtransportf. rewrite idpath_transportf.
    apply transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Lemma TranslationFunctorPreservesHomotopies {C1 C2 : Complex A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : subgrhrel (ComplexHomotSubgrp A C1 C2) f g) :
    subgrhrel (ComplexHomotSubgrp A _ _) (TranslationMorphism C1 C2 f)
              (TranslationMorphism C1 C2 g).
  Proof.
    use (squash_to_prop H). apply propproperty. intros H'. clear H.
    induction H' as [H1 H2]. induction H1 as [H11 H12]. cbn in H11.
    use (squash_to_prop H12). apply propproperty. intros H. cbn in H2.
    induction H as [HH1 HH2].
    intros P X. apply X. clear X P.
    use tpair.
    - use tpair. cbn. exact (TranslationMorphism _ _ H11).
      intros P X. apply X. clear X P.
      use tpair.
      + exact (TranslationHomot HH1).
      + cbn. rewrite TranslationFunctorHomotopies. rewrite HH2. apply idpath.
    - cbn. rewrite H2.
      set (tmp := @AdditiveFunctorLinear (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                         TranslationFunctor_Additive C1 C2 f (to_inv g)).
      cbn in tmp.
      rewrite tmp. clear tmp. apply maponpaths.
      set (tmp := @AdditiveFunctorInv (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                      TranslationFunctor_Additive C1 C2 g). cbn in tmp.
      exact tmp.
  Qed.

  (** *** Inverse of the translation functor functor *)

  Local Lemma InvTranslationFunctor_comp (C : Complex A) (i : hz) :
    (transportf (precategory_morphisms (C (i - 1)))
                (maponpaths C (hzrminusplus i 1 @ ! hzrplusminus i 1))
                (to_inv (Diff C (i - 1))))
      · (transportf (precategory_morphisms (C (i + 1 - 1)))
                     (maponpaths C (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                     (to_inv (Diff C (i + 1 - 1)))) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    induction (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1).
    induction (hzrminusplus i 1 @ ! hzrplusminus i 1). cbn. unfold idfun.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq. apply DSq.
  Qed.

  Definition InvTranslationComplex (C : Complex A) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (C (i - 1)).
    - intros i. exact (transportf
                         (precategory_morphisms (C (i - 1)))
                         (maponpaths C ((hzrminusplus i 1) @ (! hzrplusminus i 1)))
                         (to_inv (Diff C (i - 1)))).
    - intros i. exact (InvTranslationFunctor_comp C i).
  Defined.
  Global Transparent InvTranslationComplex.

  Definition DiffInvTranslationComplex (C : Complex A) (i : hz) :
    A⟦ InvTranslationComplex C i, InvTranslationComplex C (i + 1) ⟧ :=
    transportf
      (precategory_morphisms (C (i - 1)))
      (maponpaths C ((hzrminusplus i 1) @ (! hzrplusminus i 1)))
      (to_inv (Diff C (i - 1))).

  Lemma DiffInvTranslationComplex_comp (C : Complex A) (i : hz) :
    (DiffInvTranslationComplex C i) · (DiffInvTranslationComplex C (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    exact (InvTranslationFunctor_comp C i).
  Qed.

  Definition InvTranslationMorphism_mor {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A⟦InvTranslationComplex C1 i, InvTranslationComplex C2 i⟧ := f (i - 1).

  Local Lemma InvTranslationFunctor_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (InvTranslationMorphism_mor f i) · (DiffInvTranslationComplex C2 i) =
    (DiffInvTranslationComplex C1 i) · (InvTranslationMorphism_mor f (i + 1)).
  Proof.
    unfold DiffInvTranslationComplex. rewrite <- transport_target_postcompose.
    unfold InvTranslationMorphism_mor. cbn. rewrite <- PreAdditive_invrcomp.
    rewrite (MComm f (i - 1)). rewrite PreAdditive_invlcomp.
    rewrite transport_target_postcompose.
    use transport_target_path.
    - exact (C2 i).
    - exact (maponpaths C2 (hzrplusminus i 1)).
    - rewrite transport_target_postcompose. rewrite transport_f_f. rewrite <- maponpathscomp0.
      rewrite <- path_assoc. rewrite pathsinv0l. rewrite pathscomp0rid.
      induction (hzrminusplus i 1). cbn. unfold idfun.
      rewrite transport_target_postcompose.
      set (tmp := transport_hz_double_section A C1 C2 (MMor f) _ _ (hzrplusminus (i - 1 + 1) 1)).
      cbn. cbn in tmp. rewrite tmp. clear tmp.
      rewrite <- (transport_compose' _ _ (maponpaths C1 (! hzrplusminus (i - 1 + 1) 1))).
      apply cancel_precomposition. apply idpath.
  Qed.

  Definition InvTranslationMorphism (C1 C2 : Complex A) (f : Morphism C1 C2) :
    Morphism (InvTranslationComplex C1) (InvTranslationComplex C2) :=
    mk_Morphism
      A (InvTranslationComplex C1) (InvTranslationComplex C2)
      (λ i : hz, InvTranslationMorphism_mor f i) (λ i : hz, InvTranslationFunctor_comm f i).

  Definition InvTranslationFunctor_data :
    functor_data (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (InvTranslationComplex C).
    - intros C1 C2 f. exact (InvTranslationMorphism C1 C2 f).
  Defined.

  Lemma InvTranslationFunctor_isfunctor : is_functor InvTranslationFunctor_data.
  Proof.
    split.
    - intros C. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - intros C1 C2 C3 f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
  Qed.

  Definition InvTranslationFunctor :
    functor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor.
    - exact InvTranslationFunctor_data.
    - exact InvTranslationFunctor_isfunctor.
  Defined.

  Definition InvTranslationFunctor_isAdditive : isAdditiveFunctor InvTranslationFunctor.
  Proof.
    use mk_isAdditiveFunctor.
    intros C1 C2.
    split.
    - intros f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - cbn. use MorphismEq. intros i. apply idpath.
  Qed.

  Definition InvTranslationFunctor_Additive :
    AdditiveFunctor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact InvTranslationFunctor.
    - exact InvTranslationFunctor_isAdditive.
  Defined.


  (** *** InvTranslation functor preserves homotopies *)

  Definition InvTranslationHomot {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomot A (InvTranslationComplex C1) (InvTranslationComplex C2).
  Proof.
    intros i. exact (to_inv (H (i - 1))).
  Defined.

  Lemma InvTranslationFunctorHomotopies {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomotMorphism A (InvTranslationHomot H) =
    InvTranslationMorphism C1 C2 (ComplexHomotMorphism A H).
  Proof.
    unfold InvTranslationHomot. cbn. use MorphismEq. intros i. cbn.
    induction (hzrplusminus i 1). cbn. unfold idfun. rewrite pathscomp0rid.
    rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite inv_inv_eq.
    rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invrcomp. rewrite inv_inv_eq.
    assert (e1 : transportf (precategory_morphisms (C1 (i + 1 - 1 - 1)))
                            (maponpaths C1 (hzrminusplus (i + 1 - 1) 1))
                            (Diff C1 (i + 1 - 1 - 1)) · H (i + 1 - 1) =
                 transportf (precategory_morphisms (C1 (i + 1 - 1 - 1)))
                            (maponpaths C2 (hzrplusminus (i + 1 - 1 - 1) 1))
                            (Diff C1 (i + 1 - 1 - 1) · H (i + 1 - 1 - 1 + 1))).
    {
      rewrite transport_target_postcompose. rewrite transport_compose. apply cancel_precomposition.
      rewrite <- maponpathsinv0.
      rewrite <- (transport_hz_double_section A _ _ H _ _ (hzrminusplus (i + 1 - 1) 1)).
      use transportf_paths.
      assert (e2 : maponpaths (λ i0 : hz, C2 (i0 - 1)) (hzrminusplus (i + 1 - 1) 1) =
                   maponpaths C2 (maponpaths (λ i0 : hz, i0 - 1) (hzrminusplus (i + 1 - 1) 1))).
      {
        induction (hzrminusplus (i + 1 - 1) 1). apply idpath.
      }
      rewrite e2. clear e2. apply maponpaths. apply isasethz.
    }
    cbn in e1. rewrite e1. clear e1. use to_lrw.
    rewrite <- transport_target_postcompose. rewrite transport_f_f.
    assert (e2 : maponpaths (λ i0 : pr1 hz, C2 (i0 - 1)) (hzrminusplus (i + 1 - 1) 1) =
                 maponpaths C2 (maponpaths (λ i0 : hz, i0 - 1) (hzrminusplus (i + 1 - 1) 1))).
    {
      induction (hzrminusplus (i + 1 - 1) 1). apply idpath.
    }
    rewrite e2. clear e2. rewrite <- maponpathscomp0.
    use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Lemma InvTranslationFunctorPreservesHomotopies {C1 C2 : Complex A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : subgrhrel (ComplexHomotSubgrp A C1 C2) f g) :
    subgrhrel (ComplexHomotSubgrp A _ _) (InvTranslationMorphism C1 C2 f)
              (InvTranslationMorphism C1 C2 g).
  Proof.
    use (squash_to_prop H). apply propproperty. intros H'. clear H.
    induction H' as [H1 H2]. induction H1 as [H11 H12]. cbn in H11.
    use (squash_to_prop H12). apply propproperty. intros H. cbn in H2.
    induction H as [HH1 HH2].
    intros P X. apply X. clear X P.
    use tpair.
    - use tpair. cbn. exact (InvTranslationMorphism _ _ H11).
      intros P X. apply X. clear X P.
      use tpair.
      + exact (InvTranslationHomot HH1).
      + cbn. rewrite InvTranslationFunctorHomotopies. rewrite HH2. apply idpath.
    - cbn. rewrite H2.
      set (tmp := @AdditiveFunctorLinear (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                         InvTranslationFunctor_Additive C1 C2 f (to_inv g)).
      cbn in tmp.
      rewrite tmp. clear tmp. apply maponpaths.
      set (tmp := @AdditiveFunctorInv (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                      InvTranslationFunctor_Additive C1 C2 g). cbn in tmp.
      exact tmp.
  Qed.

  (** ** Translation functor is an isomorphism, with inverse the inverse translation. *)

  Lemma transportf_total2_base {AA : UU} {B : AA -> UU} {BB : AA -> UU} (s s' : ∑ x : AA, B x)
        (p : pr1 s = pr1 s') (q : transportf B p (pr2 s) = pr2 s') (x : BB (pr1 s)) :
    transportf (λ x' : ∑ x : AA, B x, BB (pr1 x')) (total2_paths_f p q) x =
    transportf (λ x : AA, BB x) p x.
  Proof.
    induction s as [s1 s2]. induction s' as [s1' s2']. cbn in *.
    induction p. induction q. apply idpath.
  Qed.

  Lemma ComplexEq_transport_target {C1 C2 C2' : Complex A} (H : ∏ (i : hz), C2 i = C2' i)
        (H1 : ∏ (i : hz),
              transportf (λ x : A, C2' i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C2 (i + 1)) (H i) (Diff C2 i)) =
              Diff C2' i) (f : Morphism C1 C2) (i : hz) :
    (transportf (λ x : Complex A, Morphism C1 x) (ComplexEq A C2 C2' H H1) f) i =
    transportf (λ x : A, C1 i --> x) (H i) (f i).
  Proof.
    assert (e : (transportf (λ x : Complex A, Morphism C1 x) (ComplexEq A C2 C2' H H1) f) i =
                (transportf (λ x : Complex A, C1 i --> x i) (ComplexEq A C2 C2' H H1) (f i))).
    {
      induction (ComplexEq A C2 C2' H H1). apply idpath.
    }
    use (pathscomp0 e). clear e.
    rewrite <- (@transport_target_funextfun hz _ C2 C2' H i (C1 i) (f i)).
    unfold ComplexEq. unfold Complex_Funclass.
    set (e := (funextfun (pr1 (pr1 C2)) (pr1 (pr1 C2')) (λ x0 : pr1 hz, H x0))).
    cbn. cbn in e. fold e.
    set (tmp := @transportf_total2_base _ _ (λ x0 : _ , A ⟦ pr1 (pr1 C1) i, (pr1 x0) i ⟧) C2 C2'
                                        (total2_paths_f e (ComplexEq' A C2 C2' H H1))
                                        (ComplexEq'' A C2 C2' H H1) (f i)).
    cbn beta in tmp.
    use (pathscomp0 tmp). clear tmp.
    use transportf_total2_base.
  Qed.

  Lemma ComplexEq_transport_source {C1 C1' C2 : Complex A} (H : ∏ (i : hz), C1' i = C1 i)
        (H1 : ∏ (i : hz),
              transportf (λ x : A, C1 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1' (i + 1)) (H i) (Diff C1' i)) =
              Diff C1 i) (f : Morphism C1' C2) (i : hz) :
    (transportf (λ x : Complex A, Morphism x C2) (ComplexEq A C1' C1 H H1) f) i =
    transportf (λ x : A, x --> C2 i) (H i) (f i).
  Proof.
    assert (e : (transportf (λ x : Complex A, Morphism x C2) (ComplexEq A C1' C1 H H1) f) i =
                (transportf (λ x : Complex A, x i --> C2 i) (ComplexEq A C1' C1 H H1) (f i))).
    {
      induction (ComplexEq A C1' C1 H H1). apply idpath.
    }
    use (pathscomp0 e). clear e.
    rewrite <- (@transport_source_funextfun hz _ C1' C1 H i (C2 i) (f i)).
    unfold ComplexEq. unfold Complex_Funclass.
    set (e := (funextfun (pr1 (pr1 C1')) (pr1 (pr1 C1)) (λ i0 : hz, H i0))).
    cbn. cbn in e. fold e.
    set (tmp := @transportf_total2_base
                  (hz -> ob A) _ (λ x0 : pr1 hz → A, A ⟦ x0 i, pr1 (pr1 C2) i ⟧)
                  (pr1 C1') (pr1 C1) e (ComplexEq' A C1' C1 H H1) (f i)).
    use (pathscomp0 _ tmp). clear tmp. cbn beta.
    use transportf_total2_base.
  Qed.

  Local Lemma TranslationInvTranslation_eq1 (C : Complex A) (i : hz) :
    transportf (λ x : A, A ⟦ C i, x ⟧) (maponpaths C (hzrminusplus (i + 1) 1))
               (transportf (λ x : A, A ⟦ x, C (i + 1 - 1 + 1) ⟧)
                           (maponpaths C (hzrminusplus i 1))
                           (transportf (precategory_morphisms (C (i - 1 + 1)))
                                       (maponpaths (λ i0 : pr1 hz, C (i0 + 1))
                                                   (hzrminusplus i 1 @ ! hzrplusminus i 1))
                                       (to_inv (to_inv (Diff C (i - 1 + 1)))))) = Diff C i.
  Proof.
    rewrite inv_inv_eq.
    induction (hzrminusplus i 1). cbn. unfold idfun.
    rewrite transport_f_f.
    assert (e : maponpaths (λ i0 : pr1 hz, (C : Complex _) (i0 + 1))
                           (! hzrplusminus (i - 1 + 1) 1) =
                maponpaths (C : Complex _)
                           (maponpaths (λ i0 : hz, i0 + 1) (! hzrplusminus (i - 1 + 1) 1))).
    {
      induction (hzrplusminus (i - 1 + 1) 1). apply idpath.
    }
    cbn in e. rewrite e. clear e.
    rewrite <- maponpathscomp0.
    assert (e : (maponpaths (λ i0 : pr1 hz, i0 + 1) (! hzrplusminus (i - 1 + 1) 1) @
                            hzrminusplus (i - 1 + 1 + 1) 1) = idpath _).
    {
      apply isasethz.
    }
    cbn in e. cbn. rewrite e. clear e. apply idpath.
  Qed.

  Local Lemma TranslationInvTranslation_eq2 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    transportf (λ x : Complex A, Morphism C1 x)
               (ComplexEq A (InvTranslationComplex (TranslationComplex C2)) C2
                          (λ i : pr1 hz, maponpaths C2 (hzrminusplus i 1))
                          (λ i : pr1 hz, TranslationInvTranslation_eq1 C2 i))
               (transportf (λ x : Complex A,
                                  Morphism x (InvTranslationComplex (TranslationComplex C2)))
                           (ComplexEq A (InvTranslationComplex (TranslationComplex C1)) C1
                                      (λ i : pr1 hz, maponpaths C1 (hzrminusplus i 1))
                                      (λ i : pr1 hz, TranslationInvTranslation_eq1 C1 i))
                           (InvTranslationMorphism (TranslationComplex C1) (TranslationComplex C2)
                                                   (TranslationMorphism C1 C2 f))) = f.
  Proof.
    use MorphismEq. intros i. Local Opaque ComplexEq. cbn.
    rewrite ComplexEq_transport_target. rewrite ComplexEq_transport_source. cbn.
    induction (hzrminusplus i 1). cbn. unfold idfun. apply idpath.
  Qed.

  Lemma TranslationInvTranslation :
    functor_composite TranslationFunctor InvTranslationFunctor = functor_identity _.
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. use ComplexEq.
        * intros i. cbn. apply maponpaths. apply (hzrminusplus i 1).
        * intros i. cbn. exact (TranslationInvTranslation_eq1 C i).
      + intros C1 C2 f. Local Opaque ComplexEq. cbn.
        exact (TranslationInvTranslation_eq2 f).
  Qed.

  Local Lemma InvTranslationTranslation_eq1 (C : Complex A) (i : hz) :
    transportf (λ x : A, A ⟦ C i, x ⟧) (maponpaths C (hzrplusminus (i + 1) 1))
               (transportf (λ x : A, A ⟦ x, C (i + 1 + 1 - 1) ⟧) (maponpaths C (hzrplusminus i 1))
                           (to_inv
                              (transportf
                                 (precategory_morphisms (C (i + 1 - 1)))
                                 (maponpaths C (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                                 (to_inv (Diff C (i + 1 - 1)))))) = Diff C i.
  Proof.
    rewrite transport_target_to_inv. rewrite inv_inv_eq.
    rewrite <- transport_source_target_comm.
    rewrite transport_f_f. rewrite <- maponpathscomp0.
    rewrite <- path_assoc. rewrite pathsinv0l. rewrite pathscomp0rid.
    rewrite (transport_hz_source_target A C 1 (Diff C) _ _ (hzrplusminus i 1)).
    apply maponpaths. use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Local Lemma InvTranslationTranslation_eq2 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    transportf (λ x : Complex A, Morphism C1 x)
               (ComplexEq A (TranslationComplex (InvTranslationComplex C2)) C2
                          (λ i : pr1 hz, maponpaths C2 (hzrplusminus i 1))
                          (λ i : pr1 hz, InvTranslationTranslation_eq1 C2 i))
               (transportf (λ x : Complex A,
                                  Morphism x (TranslationComplex (InvTranslationComplex C2)))
                           (ComplexEq A (TranslationComplex (InvTranslationComplex C1)) C1
                                      (λ i : pr1 hz, maponpaths C1 (hzrplusminus i 1))
                                      (λ i : pr1 hz, InvTranslationTranslation_eq1 C1 i))
                           (TranslationMorphism (InvTranslationComplex C1)
                                                (InvTranslationComplex C2)
                                                (InvTranslationMorphism C1 C2 f))) = f.
  Proof.
    Local Opaque ComplexEq. use MorphismEq. intros i. cbn.
    rewrite ComplexEq_transport_target. rewrite ComplexEq_transport_source. cbn.
    induction (hzrplusminus i 1). cbn. unfold idfun. apply idpath.
  Qed.

  Lemma InvTranslationTranslation :
    functor_composite InvTranslationFunctor TranslationFunctor = functor_identity _.
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. use ComplexEq.
        * intros i. cbn. apply maponpaths. apply (hzrplusminus i 1).
        * intros i. cbn. apply (InvTranslationTranslation_eq1 C i).
      + intros C1 C2 f. Local Opaque ComplexEq. cbn.
        exact (InvTranslationTranslation_eq2 f).
  Qed.

  (** *** Natural transformation for equivalence consisting of the translations *)

  Local Lemma TranslationTranslationInvNatTrans_Eq1 (x : Complex A):
    ∏ i : hz,
          transportf (precategory_morphisms (x i))
                     (maponpaths x (! hzrminusplus i 1)) (identity (x i)) ·
                     Diff (InvTranslationComplex (TranslationComplex x)) i =
          (Diff x i)
            · (transportf (precategory_morphisms (x (i + 1)))
                           (maponpaths x (! hzrminusplus (i + 1) 1)) (identity (x (i + 1)))).
  Proof.
    intros i. cbn. rewrite inv_inv_eq.
    rewrite <- transport_target_postcompose.
    rewrite <- transport_target_postcompose.
    rewrite id_right.
    rewrite transport_target_postcompose.
    induction (hzrminusplus i 1). cbn. unfold idfun. rewrite id_left.
    use transportf_paths.
    assert (e : maponpaths (λ i0 : pr1 hz, (x : Complex A) (i0 + 1))
                           (! hzrplusminus (i - 1 + 1) 1) =
                maponpaths (x : Complex A) (maponpaths (λ i0 : hz, i0 + 1)
                                                       (! hzrplusminus (i - 1 + 1) 1))).
    {
      induction (hzrplusminus (i - 1 + 1) 1). apply idpath.
    }
    use (pathscomp0 e). apply maponpaths. apply isasethz.
  Qed.

  Definition TranslationTranslationInvNatTrans_Mor (x : Complex A) :
    Morphism x (InvTranslationComplex (TranslationComplex x)).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      exact (transportf (precategory_morphisms ((x : Complex A) i))
                        (maponpaths (x : Complex A) (! hzrminusplus i 1))
                        (identity ((x : Complex A) i))).
    - exact (TranslationTranslationInvNatTrans_Eq1 x).
  Defined.

  Local Lemma TranslationTranslationInvNatTrans_isnattrans :
    is_nat_trans (functor_identity (ComplexPreCat_Additive A))
                 (functor_composite TranslationFunctor_Additive InvTranslationFunctor_Additive)
                 (λ x : ComplexPreCat_Additive A, TranslationTranslationInvNatTrans_Mor x).
  Proof.
    intros x y f. cbn. use MorphismEq. intros i. cbn.
    induction (hzrminusplus i 1). cbn. rewrite id_right. rewrite id_left.
    apply idpath.
  Qed.

  Definition TranslationTranslationInvNatTrans :
    nat_trans (functor_identity (ComplexPreCat_Additive A))
              (functor_composite TranslationFunctor_Additive InvTranslationFunctor_Additive).
  Proof.
    use mk_nat_trans.
    - intros x. exact (TranslationTranslationInvNatTrans_Mor x).
    - exact (TranslationTranslationInvNatTrans_isnattrans).
  Defined.

  Local Lemma InvTranslationTranslationNatTrans_Eq1 (x : Complex A) :
    ∏ i : hz,
          (transportf (precategory_morphisms (x (i + 1 - 1))) (maponpaths x (hzrplusminus i 1))
                      (identity (x (i + 1 - 1)))) · Diff x i =
          (Diff (TranslationComplex (InvTranslationComplex x)) i)
            · (transportf (precategory_morphisms (x (i + 1 + 1 - 1)))
                           (maponpaths x (hzrplusminus (i + 1) 1))
                           (identity (x (i + 1 + 1 - 1)))).
  Proof.
    intros i. cbn. rewrite transport_target_to_inv. rewrite inv_inv_eq.
    rewrite <- transport_target_postcompose.
    rewrite id_right. rewrite transport_f_f. rewrite <- maponpathscomp0.
    rewrite <- path_assoc. rewrite pathsinv0l. rewrite pathscomp0rid.
    rewrite transport_compose. rewrite id_left.
    apply pathsinv0. rewrite <- maponpathsinv0.
    use (pathscomp0 _ (transport_hz_section A x 1 (Diff x) _ _ (hzrplusminus i 1))).
    use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Definition InvTranslationTranslationNatTrans_Mor (x : Complex A) :
    Morphism (TranslationComplex (InvTranslationComplex x)) x.
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      exact (transportf (precategory_morphisms ((x : Complex A) (i + 1 - 1)))
                        (maponpaths (x : Complex A) (hzrplusminus i 1))
                        (identity ((x : Complex A) (i + 1 - 1)))).
    - exact (InvTranslationTranslationNatTrans_Eq1 x).
  Defined.

  Local Lemma InvTranslationTranslationNatTrans_isnattrans :
    is_nat_trans (functor_composite InvTranslationFunctor_Additive TranslationFunctor_Additive)
                 (functor_identity (ComplexPreCat_Additive A))
                 (λ x : ComplexPreCat_Additive A, InvTranslationTranslationNatTrans_Mor x).
  Proof.
    intros x y f. use MorphismEq. intros i. cbn. induction (hzrplusminus i 1).
    cbn. rewrite id_right. rewrite id_left. apply idpath.
  Qed.

  Definition InvTranslationTranslationNatTrans :
    nat_trans (functor_composite InvTranslationFunctor_Additive TranslationFunctor_Additive)
              (functor_identity (ComplexPreCat_Additive A)).
  Proof.
    use mk_nat_trans.
    - intros x. exact (InvTranslationTranslationNatTrans_Mor x).
    - exact InvTranslationTranslationNatTrans_isnattrans.
  Defined.

  Lemma TranslationInvTranslation_adjunction_eq1 (x : ob (ComplexPreCat_Additive A)) :
    (# TranslationFunctor_Additive (TranslationTranslationInvNatTrans x))
      · (InvTranslationTranslationNatTrans (TranslationFunctor_Additive x)) =
    identity (TranslationFunctor_Additive x).
  Proof.
    use MorphismEq. intros i. cbn.
    rewrite <- transport_target_postcompose. rewrite id_right.
    rewrite transport_f_f.
    assert (e : maponpaths (λ i0 : pr1 hz, (x : Complex A) (i0 + 1)) (hzrplusminus i 1) =
                maponpaths (x : Complex A) (maponpaths (λ i0 : hz, (i0 + 1)) (hzrplusminus i 1))).
    {
      induction (hzrplusminus i 1). apply idpath.
    }
    rewrite e. clear e. rewrite <- maponpathscomp0.
    assert (e : ! hzrminusplus (i + 1) 1 @ maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1) =
                idpath _) by apply isasethz.
    cbn in e. cbn. rewrite e. clear e. apply idpath.
  Qed.

  Lemma TranslationInvTranslation_adjunction_eq2 (x : ob (ComplexPreCat_Additive A)) :
    (TranslationTranslationInvNatTrans (InvTranslationFunctor_Additive x))
      · (# InvTranslationFunctor_Additive (InvTranslationTranslationNatTrans x)) =
    identity (InvTranslationFunctor_Additive x).
  Proof.
    use MorphismEq. intros i. cbn.
    rewrite <- transport_target_postcompose. rewrite id_right.
    rewrite transport_f_f.
    assert (e : maponpaths (λ i0 : pr1 hz, (x : Complex A) (i0 - 1)) (! hzrminusplus i 1)
                           @ maponpaths (x : Complex A) (hzrplusminus (i - 1) 1) = idpath _).
    {
      assert (e1 : maponpaths (λ i0 : pr1 hz, (x : Complex A) (i0 - 1)) (! hzrminusplus i 1) =
                   maponpaths (x : Complex A)
                              (maponpaths (λ i0 : hz, (i0 - 1)) (! hzrminusplus i 1))).
      {
        induction (hzrminusplus i 1). apply idpath.
      }
      rewrite e1. rewrite <- maponpathscomp0. clear e1.
      assert (e2 : maponpaths (λ i0 : hz, i0 - 1) (! hzrminusplus i 1) @ hzrplusminus (i - 1) 1 =
                   idpath _) by apply isasethz.
      rewrite e2. apply idpath.
    }
    cbn. cbn in e. rewrite e. clear e. apply idpath.
  Qed.

  Definition TranslationInvTranslation_adjunction :
    form_adjunction TranslationFunctor_Additive InvTranslationFunctor_Additive
                    TranslationTranslationInvNatTrans InvTranslationTranslationNatTrans.
  Proof.
    use mk_form_adjunction.
    - intros x. exact (TranslationInvTranslation_adjunction_eq1 x).
    - intros x. exact (TranslationInvTranslation_adjunction_eq2 x).
  Qed.

  Local Lemma TranslationEquivUnitInvComm (a : Complex A) (i : hz) :
    transportf (precategory_morphisms (a (i - 1 + 1))) (maponpaths a (hzrminusplus i 1))
               (identity (a (i - 1 + 1))) · Diff a i =
    transportf (precategory_morphisms (a (i - 1 + 1)))
               (maponpaths (λ i0 : pr1 hz, a (i0 + 1)) (hzrminusplus i 1 @ ! hzrplusminus i 1))
               (to_inv (to_inv (Diff a (i - 1 + 1))))
               · transportf (precategory_morphisms (a (i + 1 - 1 + 1)))
               (maponpaths a (hzrminusplus (i + 1) 1))
               (identity (a (i + 1 - 1 + 1))).
  Proof.
    rewrite <- transport_target_postcompose. rewrite id_right.
    rewrite inv_inv_eq.
    assert (e : maponpaths (λ i0 : pr1 hz, a (i0 + 1)) (hzrminusplus i 1 @ ! hzrplusminus i 1) =
                maponpaths a (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                         (hzrminusplus i 1 @ ! hzrplusminus i 1))).
    {
      induction (hzrminusplus i 1 @ ! hzrplusminus i 1). apply idpath.
    }
    rewrite e. rewrite transport_f_f.
    rewrite <- maponpathscomp0. rewrite transport_compose. rewrite id_left.
    apply pathsinv0. rewrite <- maponpathsinv0.
    set (tmp := transport_hz_section A (a : Complex A) 1 (Diff a) _ _ (hzrminusplus i 1)).
    cbn in tmp. use (pathscomp0 _ tmp). clear tmp. use transportf_paths.
    apply maponpaths. apply isasethz.
  Qed.

  Definition TranslationEquivUnitInv (a : ComplexPreCat_Additive A) :
    Morphism (InvTranslationFunctor (TranslationFunctor a)) a.
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      exact (transportf (precategory_morphisms ((a : Complex A) (i - 1 + 1)))
                        (maponpaths (a : Complex A) (hzrminusplus i 1)) (identity _)).
    - intros i. cbn. exact (TranslationEquivUnitInvComm a i).
  Defined.

  Lemma TranslationEquiv_is_iso1_eq1 (a : ComplexPreCat_Additive A) :
    ((unit_from_left_adjoint
          (mk_are_adjoints _ _ TranslationTranslationInvNatTrans InvTranslationTranslationNatTrans
                           TranslationInvTranslation_adjunction)) a)
      · (TranslationEquivUnitInv a) = identity _.
  Proof.
    use MorphismEq. intros i. cbn. rewrite <- transport_target_postcompose.
    rewrite id_right. rewrite transport_f_f. rewrite <- maponpathscomp0.
    rewrite pathsinv0l. apply idpath.
  Qed.

  Lemma TranslationEquiv_is_iso1_eq2 (a : ComplexPreCat_Additive A) :
    ((TranslationEquivUnitInv a) : (ComplexPreCat_Additive A)⟦_, _⟧)
      · ((unit_from_left_adjoint
            (mk_are_adjoints _ _ TranslationTranslationInvNatTrans
                             InvTranslationTranslationNatTrans
                             TranslationInvTranslation_adjunction)) a) =
    identity _.
  Proof.
    use MorphismEq. intros i. cbn. rewrite <- transport_target_postcompose.
    rewrite id_right. rewrite transport_f_f. rewrite <- maponpathscomp0.
    rewrite pathsinv0r. apply idpath.
  Qed.

  Definition TranslationEquiv_is_iso1 (a : ComplexPreCat_Additive A) :
    is_z_isomorphism
      ((unit_from_left_adjoint
          (mk_are_adjoints _ _ TranslationTranslationInvNatTrans InvTranslationTranslationNatTrans
                           TranslationInvTranslation_adjunction)) a).
  Proof.
    use mk_is_z_isomorphism.
    - exact (TranslationEquivUnitInv a).
    - use mk_is_inverse_in_precat.
      + exact (TranslationEquiv_is_iso1_eq1 a).
      + exact (TranslationEquiv_is_iso1_eq2 a).
  Defined.

  Local Lemma TranslationEquivCounitInvComm (a : ComplexPreCat_Additive A) (i : hz) :
    transportf (precategory_morphisms ((a : Complex A) i))
               (maponpaths (a : Complex A) (! hzrplusminus i 1)) (identity ((a : Complex A) i)) ·
               to_inv
               (transportf (precategory_morphisms ((a : Complex A) (i + 1 - 1)))
                           (maponpaths (a : Complex A)
                                       (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                           (to_inv (Diff (a : Complex A) (i + 1 - 1)))) =
    Diff a i · transportf (precategory_morphisms ((a : Complex A) (i + 1)))
         (maponpaths (a : Complex A) (! hzrplusminus (i + 1) 1))
         (identity ((a : Complex A) (i + 1))).
  Proof.
    rewrite <- transport_target_to_inv. rewrite inv_inv_eq.
    set (tmp' := transport_hz_source_target A (a : Complex A) 1 (Diff a) _ _ (hzrplusminus i 1)).
    cbn in tmp'. rewrite tmp'. clear tmp'. rewrite transport_source_target_comm.
    rewrite <- transport_target_postcompose.
    rewrite <- transport_target_postcompose. rewrite id_right.
    rewrite transport_f_f. rewrite transport_compose. rewrite id_left.
    rewrite <- maponpathsinv0. rewrite pathsinv0inv0. use transportf_paths.
    rewrite <- maponpathscomp0. apply maponpaths. apply isasethz.
  Qed.

  Definition TranslationEquivCounitInv (a : ComplexPreCat_Additive A) :
    Morphism a (TranslationFunctor (InvTranslationFunctor a)).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      exact (transportf (precategory_morphisms ((a : Complex A) i))
                        (maponpaths (a : Complex A) (! hzrplusminus i 1)) (identity _)).
    - intros i. cbn. exact (TranslationEquivCounitInvComm a i).
  Defined.

  Lemma TranslationEquiv_is_iso2_eq1 (a : ComplexPreCat_Additive A) :
    ((counit_from_left_adjoint
        (mk_are_adjoints _ _ TranslationTranslationInvNatTrans InvTranslationTranslationNatTrans
                         TranslationInvTranslation_adjunction)) a)
      · TranslationEquivCounitInv a = identity _.
  Proof.
    use MorphismEq. intros i. cbn. induction (hzrplusminus i 1). apply id_left.
  Qed.

  Lemma TranslationEquiv_is_iso2_eq2 (a : ComplexPreCat_Additive A) :
    ((TranslationEquivCounitInv a) : (ComplexPreCat_Additive A)⟦_, _⟧)
      · ((counit_from_left_adjoint
            (mk_are_adjoints _ _ TranslationTranslationInvNatTrans
                             InvTranslationTranslationNatTrans
                             TranslationInvTranslation_adjunction)) a) =
    identity _.
  Proof.
    use MorphismEq. intros i. cbn. induction (hzrplusminus i 1). apply id_left.
  Qed.

  Lemma TranslationEquiv_is_iso2 (b : ComplexPreCat_Additive A) :
    is_z_isomorphism
      ((counit_from_left_adjoint
          (mk_are_adjoints _ _ TranslationTranslationInvNatTrans InvTranslationTranslationNatTrans
                           TranslationInvTranslation_adjunction)) b).
  Proof.
    use mk_is_z_isomorphism.
    - exact (TranslationEquivCounitInv b).
    - use mk_is_inverse_in_precat.
      + exact (TranslationEquiv_is_iso2_eq1 b).
      + exact (TranslationEquiv_is_iso2_eq2 b).
  Defined.

  Definition TranslationEquiv : AddEquiv (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_AddEquiv.
    - exact TranslationFunctor_Additive.
    - exact InvTranslationFunctor_Additive.
    - use mk_are_adjoints.
      + exact TranslationTranslationInvNatTrans.
      + exact InvTranslationTranslationNatTrans.
      + exact TranslationInvTranslation_adjunction.
    - exact TranslationEquiv_is_iso1.
    - exact TranslationEquiv_is_iso2.
  Defined.

  (** ** Translation functor for K(A) *)

  (** *** Image for the translation functor *)

  Definition TranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : UU :=
    ∑ (h : (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧),
    ∏ (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f),
    h = # (ComplexHomotFunctor A) (# TranslationFunctor f').


  Definition TranslationFunctorHImMor {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : TranslationFunctorHIm f) :
    (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧ := pr1 h.

  Definition TranslationFunctorHImEq {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : TranslationFunctorHIm f)
             (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f) :
    TranslationFunctorHImMor h = # (ComplexHomotFunctor A) (# TranslationFunctor f') := pr2 h f' H.

  Definition mk_TranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧}
             (h : (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧)
             (HH : ∏ (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧)
                     (H : # (ComplexHomotFunctor A) f' = f),
                   h = # (ComplexHomotFunctor A) (# TranslationFunctor f')) :
    TranslationFunctorHIm f := tpair _ h HH.

  Lemma TranslationFunctorHImEquality {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h h' : TranslationFunctorHIm f)
             (e : TranslationFunctorHImMor h = TranslationFunctorHImMor h') : h = h'.
  Proof.
    use total2_paths_f.
    - exact e.
    - apply proofirrelevance. apply impred_isaprop. intros t0.
      apply impred_isaprop. intros H0. use to_has_homsets.
  Qed.


  (** *** Construction of the functor *)

  Lemma TranslationFunctor_eq {C1 C2 : ComplexHomot_Additive A}
        (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f)
        (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H' : # (ComplexHomotFunctor A) f' = f) :
    # (ComplexHomotFunctor A) (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f H)) =
    # (ComplexHomotFunctor A) (# TranslationFunctor f').
  Proof.
    use ComplexHomotFunctor_rel_mor.
    use TranslationFunctorPreservesHomotopies.
    use ComplexHomotFunctor_mor_rel.
    rewrite H'. apply hfiberpr2.
  Qed.

  Definition TranslationFunctorH_Mor_data {C1 C2 : ob (ComplexHomot_Additive A)}
             (f : ComplexHomot_Additive A ⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f) :
    TranslationFunctorHIm f.
  Proof.
    use mk_TranslationFunctorHIm.
    - exact (# (ComplexHomotFunctor A) (# (TranslationFunctor) (hfiberpr1 _ _ H))).
    - intros f' H'. exact (TranslationFunctor_eq f H f' H').
  Defined.

  Definition TranslationFunctorH_Mor {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : iscontr (TranslationFunctorHIm f).
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    apply isapropiscontr. intros H.
    use iscontrpair.
    - exact (TranslationFunctorH_Mor_data f H).
    - intros t. use TranslationFunctorHImEquality.
      use TranslationFunctorHImEq.
      exact (hfiberpr2 _ _ H).
  Qed.

  Lemma TranslationFunctorH_Mor_unique {C1 C2 : ob (ComplexHomot_Additive A)}
        (f : ComplexHomot_Additive A ⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f) :
    iscontrpr1 (TranslationFunctorH_Mor f) = (TranslationFunctorH_Mor_data f H).
  Proof.
    use TranslationFunctorHImEquality.
    use TranslationFunctorHImEq.
    exact (hfiberpr2 _ _ H).
  Qed.

  Definition TranslationFunctorH_data :
    functor_data (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (TranslationComplex C).
    - intros C1 C2 f. exact (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor f))).
  Defined.

  Lemma TranslationFunctorH_Mor_Id : functor_idax TranslationFunctorH_data.
  Proof.
    intros C.
    use (pathscomp0 (TranslationFunctorHImEq
                       (iscontrpr1 (TranslationFunctorH_Mor (identity C)))
                       (identity _)
                       (functor_id (ComplexHomotFunctor A) _))).
    rewrite functor_id. rewrite functor_id. apply idpath.
  Qed.

  Lemma TranslationFunctorH_Mor_Comp {C1 C2 C3 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (g : (ComplexHomot_Additive A)⟦C2, C3⟧) :
    (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor (f · g)))) =
    (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor f)))
      · (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor g))) .
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    use to_has_homsets. intros f'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g)).
    use to_has_homsets. intros g'.
    rewrite (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor f)) _ (hfiberpr2 _ _ f')).
    rewrite (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor g)) _ (hfiberpr2 _ _ g')).
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f'))
                             (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) g g'))).
    use (pathscomp0 _ tmp). clear tmp.
    set (tmp := functor_comp TranslationFunctor (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 _ tmp). clear tmp.
    use (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor (f · g)))).
    rewrite functor_comp. rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition TranslationFunctorH_is_functor : is_functor TranslationFunctorH_data.
  Proof.
    split.
    - exact TranslationFunctorH_Mor_Id.
    - intros C1 C2 C3 f g. exact (TranslationFunctorH_Mor_Comp f g).
  Qed.

  Definition TranslationFunctorH :
    functor (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor.
    - exact TranslationFunctorH_data.
    - exact TranslationFunctorH_is_functor.
  Defined.

  Lemma TranslationFunctorH_comm :
    functor_composite (ComplexHomotFunctor A) TranslationFunctorH =
    functor_composite TranslationFunctor (ComplexHomotFunctor A).
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. cbn. apply idpath.
      + intros C1 C2 f.
        cbn beta.
        rewrite idpath_transportf. rewrite idpath_transportf.
        assert (e1 : pr2 (pr1 (functor_composite (ComplexHomotFunctor A) TranslationFunctorH))
                         C1 C2 f =
                    # TranslationFunctorH (# (ComplexHomotFunctor A) f)) by apply idpath.
        rewrite e1. clear e1.
        assert (e2 : pr2 (pr1 (functor_composite TranslationFunctor (ComplexHomotFunctor A)))
                         C1 C2 f =
                    # (ComplexHomotFunctor A) (# TranslationFunctor f)) by apply idpath.
        rewrite e2. clear e2.
        use (squash_to_prop
               (ComplexHomotFunctor_issurj
                  A (# (ComplexHomotFunctor A) f))).
        apply to_has_homsets. intros f'.
        set (im := TranslationFunctorH_Mor_data (# (ComplexHomotFunctor A) f) f').
        rewrite <- (@TranslationFunctorHImEq C1 C2 _ im f (idpath _)).
        use TranslationFunctorHImEq.
        exact (hfiberpr2 _ _ f').
  Qed.

  Lemma TranslationFunctorH_Mor_Im {C1 C2 : ob (ComplexHomot_Additive A)}
        (f : ComplexHomot_Additive A ⟦C1, C2⟧) (f' : hfiber # (ComplexHomotFunctor A) f) :
    # TranslationFunctorH f = # (ComplexHomotFunctor A) (# TranslationFunctor (hfiberpr1 _ _ f')).
  Proof.
    use TranslationFunctorHImEq. exact (hfiberpr2 _ _ f').
  Qed.

  Lemma TranslationFunctorH_isAdditiveFunctor : isAdditiveFunctor TranslationFunctorH.
  Proof.
    use mk_isAdditiveFunctor'.
    - intros C1 C2.
      use (pathscomp0 _ (@AdditiveFunctorZeroArrow
                           (ComplexPreCat_Additive A) (ComplexHomot_Additive A)
                           (ComplexHomotFunctor A)
                           (TranslationFunctorH C1) (TranslationFunctorH C2))).
      set (tmp := (@AdditiveFunctorZeroArrow
                     (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                     TranslationFunctor_Additive C1 C2)).
      apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
      use (pathscomp0 _ tmp). clear tmp.
      use TranslationFunctorHImEq.
      use AdditiveFunctorZeroArrow.
    - intros C1 C2 f g.
      use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
      apply to_has_homsets. intros f'.
      use (squash_to_prop (ComplexHomotFunctor_issurj A g)).
      apply to_has_homsets. intros g'.
      rewrite (TranslationFunctorH_Mor_Im f f').
      rewrite (TranslationFunctorH_Mor_Im g g').
      use (pathscomp0 _ (AdditiveFunctorLinear
                           (ComplexHomotFunctor A) (# TranslationFunctor (hfiberpr1 _ _ f'))
                           (# TranslationFunctor (hfiberpr1 _ _ g')))).
      set (tmp := AdditiveFunctorLinear
                    TranslationFunctor_Additive (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
      apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
      use (pathscomp0 _ tmp). clear tmp.
      use TranslationFunctorHImEq.
      rewrite AdditiveFunctorLinear.
      rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition TranslationFunctorH_AdditiveFunctor :
    AdditiveFunctor (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact TranslationFunctorH.
    - exact TranslationFunctorH_isAdditiveFunctor.
  Defined.


  (** ** Inverse translation in K(A) *)

  Definition InvTranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : UU :=
    ∑ (h : (ComplexHomot_Additive A)⟦InvTranslationComplex C1, InvTranslationComplex C2⟧),
    ∏ (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f),
    h = # (ComplexHomotFunctor A) (# InvTranslationFunctor f').

  Definition InvTranslationFunctorHImMor {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : InvTranslationFunctorHIm f) :
    (ComplexHomot_Additive A)⟦InvTranslationComplex C1, InvTranslationComplex C2⟧ := pr1 h.

  Definition InvTranslationFunctorHImEq {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : InvTranslationFunctorHIm f)
             (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f) :
    InvTranslationFunctorHImMor h = # (ComplexHomotFunctor A) (# InvTranslationFunctor f') :=
    pr2 h f' H.

  Definition mk_InvTranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧}
             (h : (ComplexHomot_Additive A)⟦InvTranslationComplex C1, InvTranslationComplex C2⟧)
             (HH : ∏ (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧)
                     (H : # (ComplexHomotFunctor A) f' = f),
                   h = # (ComplexHomotFunctor A) (# InvTranslationFunctor f')) :
    InvTranslationFunctorHIm f := tpair _ h HH.

  Lemma InvTranslationFunctorHImEquality {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h h' : InvTranslationFunctorHIm f)
             (e : InvTranslationFunctorHImMor h = InvTranslationFunctorHImMor h') : h = h'.
  Proof.
    use total2_paths_f.
    - exact e.
    - apply proofirrelevance. apply impred_isaprop. intros t0.
      apply impred_isaprop. intros H0. use to_has_homsets.
  Qed.


  (** *** Construction of the functor *)

  Lemma InvTranslationFunctor_eq {C1 C2 : ComplexHomot_Additive A}
        (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f)
        (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H' : # (ComplexHomotFunctor A) f' = f) :
    # (ComplexHomotFunctor A) (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f H)) =
    # (ComplexHomotFunctor A) (# InvTranslationFunctor f').
  Proof.
    use ComplexHomotFunctor_rel_mor.
    use InvTranslationFunctorPreservesHomotopies.
    use ComplexHomotFunctor_mor_rel.
    rewrite H'. apply hfiberpr2.
  Qed.

  Definition InvTranslationFunctorH_Mor_data {C1 C2 : ob (ComplexHomot_Additive A)}
             (f : ComplexHomot_Additive A ⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f) :
    InvTranslationFunctorHIm f.
  Proof.
    use mk_InvTranslationFunctorHIm.
    - exact (# (ComplexHomotFunctor A) (# (InvTranslationFunctor) (hfiberpr1 _ _ H))).
    - intros f' H'. exact (InvTranslationFunctor_eq f H f' H').
  Defined.

  Definition InvTranslationFunctorH_Mor {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : iscontr (InvTranslationFunctorHIm f).
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    apply isapropiscontr. intros H.
    use iscontrpair.
    - exact (InvTranslationFunctorH_Mor_data f H).
    - intros t. use InvTranslationFunctorHImEquality.
      use InvTranslationFunctorHImEq.
      exact (hfiberpr2 _ _ H).
  Qed.

  Lemma InvTranslationFunctorH_Mor_unique {C1 C2 : ob (ComplexHomot_Additive A)}
        (f : ComplexHomot_Additive A ⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f) :
    iscontrpr1 (InvTranslationFunctorH_Mor f) = (InvTranslationFunctorH_Mor_data f H).
  Proof.
    use InvTranslationFunctorHImEquality.
    use InvTranslationFunctorHImEq.
    exact (hfiberpr2 _ _ H).
  Qed.

  Definition InvTranslationFunctorH_data :
    functor_data (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (InvTranslationComplex C).
    - intros C1 C2 f.
      exact (InvTranslationFunctorHImMor (iscontrpr1 (InvTranslationFunctorH_Mor f))).
  Defined.

  Lemma InvTranslationFunctorH_Mor_Id : functor_idax InvTranslationFunctorH_data.
  Proof.
    intros C.
    use (pathscomp0 (InvTranslationFunctorHImEq
                       (iscontrpr1 (InvTranslationFunctorH_Mor (identity C)))
                       (identity _)
                       (functor_id (ComplexHomotFunctor A) _))).
    rewrite functor_id. rewrite functor_id. apply idpath.
  Qed.

  Lemma InvTranslationFunctorH_Mor_Comp {C1 C2 C3 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (g : (ComplexHomot_Additive A)⟦C2, C3⟧) :
    (InvTranslationFunctorHImMor (iscontrpr1 (InvTranslationFunctorH_Mor (f · g)))) =
    (InvTranslationFunctorHImMor (iscontrpr1 (InvTranslationFunctorH_Mor f)))
      · (InvTranslationFunctorHImMor (iscontrpr1 (InvTranslationFunctorH_Mor g))) .
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    use to_has_homsets. intros f'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g)).
    use to_has_homsets. intros g'.
    rewrite (InvTranslationFunctorHImEq
               (iscontrpr1 (InvTranslationFunctorH_Mor f)) _ (hfiberpr2 _ _ f')).
    rewrite (InvTranslationFunctorHImEq
               (iscontrpr1 (InvTranslationFunctorH_Mor g)) _ (hfiberpr2 _ _ g')).
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f'))
                             (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) g g'))).
    use (pathscomp0 _ tmp). clear tmp.
    set (tmp := functor_comp InvTranslationFunctor (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 _ tmp). clear tmp.
    use (InvTranslationFunctorHImEq (iscontrpr1 (InvTranslationFunctorH_Mor (f · g)))).
    rewrite functor_comp. rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition InvTranslationFunctorH_is_functor : is_functor InvTranslationFunctorH_data.
  Proof.
    split.
    - exact InvTranslationFunctorH_Mor_Id.
    - intros C1 C2 C3 f g. exact (InvTranslationFunctorH_Mor_Comp f g).
  Qed.

  Definition InvTranslationFunctorH :
    functor (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor.
    - exact InvTranslationFunctorH_data.
    - exact InvTranslationFunctorH_is_functor.
  Defined.

  Lemma InvTranslationFunctorH_comm :
    functor_composite (ComplexHomotFunctor A) InvTranslationFunctorH =
    functor_composite InvTranslationFunctor (ComplexHomotFunctor A).
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. cbn. apply idpath.
      + intros C1 C2 f.
        cbn beta.
        rewrite idpath_transportf. rewrite idpath_transportf.
        assert (e1 : pr2 (pr1 (functor_composite (ComplexHomotFunctor A) InvTranslationFunctorH))
                         C1 C2 f =
                    # InvTranslationFunctorH (# (ComplexHomotFunctor A) f)) by apply idpath.
        rewrite e1. clear e1.
        assert (e2 : pr2 (pr1 (functor_composite InvTranslationFunctor (ComplexHomotFunctor A)))
                         C1 C2 f =
                    # (ComplexHomotFunctor A) (# InvTranslationFunctor f)) by apply idpath.
        rewrite e2. clear e2.
        use (squash_to_prop (ComplexHomotFunctor_issurj A (# (ComplexHomotFunctor A) f))).
        apply to_has_homsets. intros f'.
        set (im := InvTranslationFunctorH_Mor_data (# (ComplexHomotFunctor A) f) f').
        rewrite <- (@InvTranslationFunctorHImEq C1 C2 _ im f (idpath _)).
        use InvTranslationFunctorHImEq.
        exact (hfiberpr2 _ _ f').
  Qed.

  Lemma InvTranslationFunctorH_Mor_Im {C1 C2 : ob (ComplexHomot_Additive A)}
        (f : ComplexHomot_Additive A ⟦C1, C2⟧) (f' : hfiber # (ComplexHomotFunctor A) f) :
    # InvTranslationFunctorH f =
    # (ComplexHomotFunctor A) (# InvTranslationFunctor (hfiberpr1 _ _ f')).
  Proof.
    use InvTranslationFunctorHImEq. exact (hfiberpr2 _ _ f').
  Qed.

  Lemma InvTranslationFunctorH_isAdditiveFunctor : isAdditiveFunctor InvTranslationFunctorH.
  Proof.
    use mk_isAdditiveFunctor'.
    - intros C1 C2.
      use (pathscomp0 _ (@AdditiveFunctorZeroArrow
                           (ComplexPreCat_Additive A) (ComplexHomot_Additive A)
                           (ComplexHomotFunctor A)
                           (InvTranslationFunctorH C1) (InvTranslationFunctorH C2))).
      set (tmp := (@AdditiveFunctorZeroArrow
                     (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                     InvTranslationFunctor_Additive C1 C2)).
      apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
      use (pathscomp0 _ tmp). clear tmp.
      use InvTranslationFunctorHImEq.
      use AdditiveFunctorZeroArrow.
    - intros C1 C2 f g.
      use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
      apply to_has_homsets. intros f'.
      use (squash_to_prop (ComplexHomotFunctor_issurj A g)).
      apply to_has_homsets. intros g'.
      rewrite (InvTranslationFunctorH_Mor_Im f f').
      rewrite (InvTranslationFunctorH_Mor_Im g g').
      use (pathscomp0 _ (AdditiveFunctorLinear
                           (ComplexHomotFunctor A) (# InvTranslationFunctor (hfiberpr1 _ _ f'))
                           (# InvTranslationFunctor (hfiberpr1 _ _ g')))).
      set (tmp := AdditiveFunctorLinear
                    InvTranslationFunctor_Additive (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
      apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
      use (pathscomp0 _ tmp). clear tmp.
      use InvTranslationFunctorHImEq.
      rewrite AdditiveFunctorLinear.
      rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition InvTranslationFunctorH_AdditiveFunctor :
    AdditiveFunctor (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact InvTranslationFunctorH.
    - exact InvTranslationFunctorH_isAdditiveFunctor.
  Defined.


  (** Translation functors in K(A) are isomorphisms and inverse to each other. *)

  Lemma transport_target_ComplexHomotFunctor {C1 C2 C2' : Complex A} (e : C2 = C2')
        (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) (transportf (λ x : Complex A, Morphism C1 x) e f) =
    transportf (λ x : Complex A, (ComplexHomot_Additive A)⟦C1, x⟧) e (# (ComplexHomotFunctor A) f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_source_ComplexHomotFunctor {C1' C1 C2 : Complex A} (e : C1' = C1)
        (f : Morphism C1' C2) :
    # (ComplexHomotFunctor A) (transportf (λ x : Complex A, Morphism x C2) e f) =
    transportf (λ x : Complex A, (ComplexHomot_Additive A)⟦x, C2⟧) e
               (# (ComplexHomotFunctor A) f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma TranslationHInvTranslationH :
    functor_composite TranslationFunctorH InvTranslationFunctorH = functor_identity _.
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. cbn. use ComplexEq.
        * intros i. cbn. apply maponpaths. apply (hzrminusplus i 1).
        * intros i. cbn. exact (TranslationInvTranslation_eq1 C i).
      + intros C1 C2 f. cbn beta.
        use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
        use to_has_homsets. intros f'. cbn.
        rewrite (TranslationFunctorH_Mor_unique _ f').
        use (squash_to_prop (ComplexHomotFunctor_issurj
                               A (TranslationFunctorHImMor (TranslationFunctorH_Mor_data f f')))).
        use (@to_has_homsets (ComplexHomot_Additive A)). intros f''.
        rewrite (InvTranslationFunctorH_Mor_unique _ f'').
        rewrite <- (hfiberpr2 _ _ f').
        rewrite <- (TranslationInvTranslation_eq2 (hfiberpr1 # (ComplexHomotFunctor A) f f')).
        rewrite transport_target_ComplexHomotFunctor. rewrite transport_source_ComplexHomotFunctor.
        apply maponpaths. apply maponpaths.
        assert (e1 : # (ComplexHomotFunctor A)
                       (InvTranslationMorphism
                          (TranslationComplex C1) (TranslationComplex C2)
                          (TranslationMorphism
                             C1 C2 (hfiberpr1 # (ComplexHomotFunctor A) f f'))) =
                     # InvTranslationFunctorH
                       (# (ComplexHomotFunctor A)
                          (TranslationMorphism
                             C1 C2 (hfiberpr1 # (ComplexHomotFunctor A) f f')))).
        {
          apply pathsinv0. use InvTranslationFunctorHImEq. apply idpath.
        }
        use (pathscomp0 _ (! e1)). clear e1.
        apply pathsinv0. use InvTranslationFunctorHImEq.
        set (tmp := hfiberpr2 _ _ f''). rewrite tmp. clear tmp. use TranslationFunctorHImEq.
        apply (hfiberpr2 _ _ f').
  Qed.

  Lemma InvTranslationHTranslationH :
    functor_composite InvTranslationFunctorH TranslationFunctorH = functor_identity _.
  Proof.
    use functor_eq.
    - apply to_has_homsets.
    - use functor_data_eq.
      + intros C. cbn. use ComplexEq.
        * intros i. cbn. apply maponpaths. apply (hzrplusminus i 1).
        * intros i. cbn. exact (InvTranslationTranslation_eq1 C i).
      + intros C1 C2 f. cbn beta.
        use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
        use to_has_homsets.  intros f'. cbn.
        rewrite (InvTranslationFunctorH_Mor_unique _ f').
        use (squash_to_prop
               (ComplexHomotFunctor_issurj
                  A (InvTranslationFunctorHImMor (InvTranslationFunctorH_Mor_data f f')))).
        use (@to_has_homsets (ComplexHomot_Additive A)). intros f''.
        rewrite (TranslationFunctorH_Mor_unique _ f'').
        rewrite <- (hfiberpr2 _ _ f').
        rewrite <- (InvTranslationTranslation_eq2 (hfiberpr1 # (ComplexHomotFunctor A) f f')).
        rewrite transport_target_ComplexHomotFunctor. rewrite transport_source_ComplexHomotFunctor.
        apply maponpaths. apply maponpaths.
        assert (e1 : # (ComplexHomotFunctor A)
                       (TranslationMorphism
                          (InvTranslationComplex C1) (InvTranslationComplex C2)
                          (InvTranslationMorphism
                             C1 C2 (hfiberpr1 # (ComplexHomotFunctor A) f f'))) =
                     # TranslationFunctorH
                       (# (ComplexHomotFunctor A)
                          (InvTranslationMorphism
                             C1 C2 (hfiberpr1 # (ComplexHomotFunctor A) f f')))).
        {
          apply pathsinv0. use TranslationFunctorHImEq. apply idpath.
        }
        use (pathscomp0 _ (! e1)). clear e1.
        apply pathsinv0. use TranslationFunctorHImEq.
        set (tmp := hfiberpr2 _ _ f''). rewrite tmp. clear tmp. use InvTranslationFunctorHImEq.
        apply (hfiberpr2 _ _ f').
  Qed.

  (** ** Translation equivalence for K(A) *)
  Local Lemma TranslationHInvTranslationHNatTrans_isnattrans :
    is_nat_trans (functor_identity (ComplexHomot_Additive A))
                 (functor_composite TranslationFunctorH_AdditiveFunctor
                                    InvTranslationFunctorH_AdditiveFunctor)
                 (λ x : ComplexHomot_Additive A, # (ComplexHomotFunctor A)
                                                   (TranslationTranslationInvNatTrans_Mor x)).
  Proof.
    intros x y f.
    Local Opaque precategory_morphisms InvTranslationFunctorHIm TranslationFunctorHIm
          ComplexHomotFunctor compose InvTranslationFunctorH TranslationFunctorH
          TranslationFunctor InvTranslationFunctor.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    use to_has_homsets. intros f'.
    cbn. set (tmp := TranslationFunctorH_Mor_Im f f'). cbn in tmp. rewrite tmp. clear tmp.
    set (f'' := @hfiberpair
                  _ _ (# (ComplexHomotFunctor A))
                  (# (ComplexHomotFunctor A)
                     (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f')))
                  (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f'))
                  (idpath _)).
    set (tmp := InvTranslationFunctorH_Mor_Im _ f'').
    apply (maponpaths (compose (# (ComplexHomotFunctor A)
                                  (TranslationTranslationInvNatTrans_Mor x)))) in tmp.
    use (pathscomp0 _ (! tmp)). clear tmp. cbn.
    set (tmp := functor_comp
                  (ComplexHomotFunctor A)
                  (TranslationTranslationInvNatTrans_Mor x)
                  (# InvTranslationFunctor
                     (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f')))).
    use (pathscomp0 _ tmp). clear tmp.
    set (tmp := hfiberpr2 _ _ f'). clear f''.
    apply (maponpaths
             (postcompose (# (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor y))))
      in tmp.
    use (pathscomp0 (! tmp)). clear tmp. unfold postcompose. rewrite <- functor_comp.
    apply maponpaths.
    set (tmp := TranslationTranslationInvNatTrans_isnattrans x y (hfiberpr1 _ _ f')).
    cbn in tmp. exact tmp.
  Qed.

  Definition TranslationHTranslationInvHNatTrans :
    nat_trans (functor_identity (ComplexHomot_Additive A))
              (functor_composite TranslationFunctorH_AdditiveFunctor
                                 InvTranslationFunctorH_AdditiveFunctor).
  Proof.
    use mk_nat_trans.
    - intros x.
      exact (# (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor x)).
    - exact TranslationHInvTranslationHNatTrans_isnattrans.
  Defined.

  Local Lemma InvTranslationHTranslationHNatTrans_isnattrans :
    is_nat_trans (functor_composite InvTranslationFunctorH_AdditiveFunctor
                                    TranslationFunctorH_AdditiveFunctor)
                 (functor_identity (ComplexHomot_Additive A))
                 (λ x : ComplexHomot_Additive A, # (ComplexHomotFunctor A)
                                                   (InvTranslationTranslationNatTrans_Mor x)).
  Proof.
    intros x y f.
    Local Opaque precategory_morphisms InvTranslationFunctorHIm TranslationFunctorHIm
          ComplexHomotFunctor compose InvTranslationFunctorH TranslationFunctorH
          TranslationFunctor InvTranslationFunctor.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    use to_has_homsets. intros f'.
    cbn. set (tmp := InvTranslationFunctorH_Mor_Im f f'). cbn in tmp. rewrite tmp. clear tmp.
    set (f'' := @hfiberpair
                  _ _ (# (ComplexHomotFunctor A))
                  (# (ComplexHomotFunctor A)
                     (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f')))
                  (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f'))
                  (idpath _)).
    set (tmp := TranslationFunctorH_Mor_Im _ f'').
    apply (maponpaths (postcompose (# (ComplexHomotFunctor A)
                                      (InvTranslationTranslationNatTrans_Mor y)))) in tmp.
    use (pathscomp0 tmp). clear tmp. cbn. unfold postcompose.
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             (# TranslationFunctor
                                (# InvTranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f')))
                             (InvTranslationTranslationNatTrans_Mor y)).
    use (pathscomp0 (! tmp)). clear tmp.
    set (tmp := hfiberpr2 _ _ f'). clear f''.
    apply (maponpaths
             (compose (# (ComplexHomotFunctor A) (InvTranslationTranslationNatTrans_Mor x))))
      in tmp.
    use (pathscomp0 _ tmp). clear tmp. rewrite <- functor_comp.
    apply maponpaths.
    set (tmp := InvTranslationTranslationNatTrans_isnattrans x y (hfiberpr1 _ _ f')).
    cbn in tmp. exact tmp.
  Qed.

  Definition InvTranslationHTranslationHNatTrans :
    nat_trans (functor_composite InvTranslationFunctorH_AdditiveFunctor
                                 TranslationFunctorH_AdditiveFunctor)
              (functor_identity (ComplexHomot_Additive A)).
  Proof.
    use mk_nat_trans.
    - intros x.
      exact (# (ComplexHomotFunctor A) (InvTranslationTranslationNatTrans_Mor x)).
    - exact InvTranslationHTranslationHNatTrans_isnattrans.
  Defined.

  Local Opaque precategory_morphisms InvTranslationFunctorHIm TranslationFunctorHIm
        ComplexHomotFunctor compose InvTranslationFunctorH TranslationFunctorH
        TranslationFunctor InvTranslationFunctor identity.


  Lemma TranslationHInvTranslationH_adjunction_eq1 (x : ComplexHomot_Additive A) :
    # TranslationFunctorH (# (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor x)) ·
      # (ComplexHomotFunctor A) (InvTranslationTranslationNatTrans_Mor (TranslationFunctorH x)) =
    identity (TranslationFunctorH x).
  Proof.
    use (pathscomp0 _ (functor_id TranslationFunctorH_AdditiveFunctor x)).
    set (tmp := functor_id (ComplexHomotFunctor A) x).
    apply (maponpaths (# TranslationFunctorH_AdditiveFunctor)) in tmp.
    use (pathscomp0 _ tmp). clear tmp.
    cbn.
    set (f' := @hfiberpair
                 _ _ (# (ComplexHomotFunctor A))
                 (# (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor x))
                 (TranslationTranslationInvNatTrans_Mor x)
                 (idpath _)).
    set (tmp := TranslationFunctorH_Mor_Im _ f').
    apply (maponpaths (postcompose
                         (# (ComplexHomotFunctor A) (InvTranslationTranslationNatTrans_Mor
                                                       (TranslationFunctorH x))))) in tmp.
    use (pathscomp0 tmp). clear tmp. unfold postcompose.
    set (id' := @hfiberpair
                  _ _ (# (ComplexHomotFunctor A))
                  (# (ComplexHomotFunctor A) (identity _))
                  (identity (x : ob (ComplexPreCat_Additive A)))
                  (idpath _)).
    set (tmp := TranslationFunctorH_Mor_Im _ id').
    use (pathscomp0 _ (! tmp)). clear tmp. cbn. clear id'.
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             (# TranslationFunctor (TranslationTranslationInvNatTrans_Mor x))
                             (InvTranslationTranslationNatTrans_Mor (TranslationFunctorH x))).
    use (pathscomp0 (! tmp)). clear tmp. apply maponpaths.
    Local Transparent TranslationFunctorH. cbn.
    set (tmp := TranslationInvTranslation_adjunction_eq1 x). cbn in tmp.
    use (pathscomp0 tmp). clear tmp. apply pathsinv0. use (functor_id TranslationFunctor).
  Qed.

  Lemma TranslationHInvTranslationH_adjunction_eq2 (x : ComplexHomot_Additive A) :
    # (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor (InvTranslationFunctorH x)) ·
      # InvTranslationFunctorH (# (ComplexHomotFunctor A)
                                  (InvTranslationTranslationNatTrans_Mor x)) =
    identity (InvTranslationFunctorH x).
  Proof.
    use (pathscomp0 _ (functor_id InvTranslationFunctorH_AdditiveFunctor x)).
    set (tmp := functor_id (ComplexHomotFunctor A) x).
    apply (maponpaths (# InvTranslationFunctorH_AdditiveFunctor)) in tmp.
    use (pathscomp0 _ tmp). clear tmp.
    set (f' := @hfiberpair
                 _ _ (# (ComplexHomotFunctor A))
                 (# (ComplexHomotFunctor A) (InvTranslationTranslationNatTrans_Mor x))
                 (InvTranslationTranslationNatTrans_Mor x)
                 (idpath _)).
    set (tmp := InvTranslationFunctorH_Mor_Im _ f').
    apply (maponpaths (compose
                         (# (ComplexHomotFunctor A) (TranslationTranslationInvNatTrans_Mor
                                                       (InvTranslationFunctorH x))))) in tmp.
    use (pathscomp0 tmp). clear tmp.
    set (id' := @hfiberpair
                  _ _ (# (ComplexHomotFunctor A))
                  (# (ComplexHomotFunctor A) (identity _))
                  (identity (x : ob (ComplexPreCat_Additive A)))
                  (idpath _)).
    set (tmp := InvTranslationFunctorH_Mor_Im _ id').
    use (pathscomp0 _ (! tmp)). clear tmp. cbn. clear id'.
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             (TranslationTranslationInvNatTrans_Mor (InvTranslationFunctorH x))
                             (# InvTranslationFunctor
                                (InvTranslationTranslationNatTrans_Mor x))).
    use (pathscomp0 (! tmp)). clear tmp. apply maponpaths.
    Local Transparent InvTranslationFunctorH. cbn.
    set (tmp := TranslationInvTranslation_adjunction_eq2 x). cbn in tmp.
    use (pathscomp0 tmp). clear tmp. apply pathsinv0. use (functor_id InvTranslationFunctor).
  Qed.

  Definition TranslationHInvTranslationH_adjunction :
    form_adjunction TranslationFunctorH_AdditiveFunctor
                    InvTranslationFunctorH_AdditiveFunctor
                    TranslationHTranslationInvHNatTrans InvTranslationHTranslationHNatTrans.
  Proof.
    use mk_form_adjunction.
    - intros x. exact (TranslationHInvTranslationH_adjunction_eq1 x).
    - intros x. exact (TranslationHInvTranslationH_adjunction_eq2 x).
  Qed.

  Local Lemma TranslationHEquiv_is_iso1_eq1' (x : ComplexHomot_Additive A) :
    (unit_from_left_adjoint
       (mk_are_adjoints _ _ TranslationHTranslationInvHNatTrans InvTranslationHTranslationHNatTrans
                        TranslationHInvTranslationH_adjunction))
      x · # (ComplexHomotFunctor A) (TranslationEquivUnitInv x) =
    identity ((functor_identity (ComplexHomot_Additive A)) x).
  Proof.
    cbn.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A)
                                     (TranslationTranslationInvNatTrans_Mor x)
                                     (TranslationEquivUnitInv x)))).
    use (pathscomp0 _ (functor_id (ComplexHomotFunctor A) x)).
    apply maponpaths.
    exact (TranslationEquiv_is_iso1_eq1 x).
  Qed.

  Local Lemma TranslationHEquiv_is_iso1_eq2' (x : ComplexHomot_Additive A) :
    (# (ComplexHomotFunctor A) (TranslationEquivUnitInv x))
      · (unit_from_left_adjoint
            (mk_are_adjoints
               _ _ TranslationHTranslationInvHNatTrans
               InvTranslationHTranslationHNatTrans
               TranslationHInvTranslationH_adjunction)) x =
    identity _.
  Proof.
    cbn.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A)
                                     (TranslationEquivUnitInv x)
                                     (TranslationTranslationInvNatTrans_Mor x)))).
    use (pathscomp0 _ (functor_id (ComplexHomotFunctor A) _)).
    apply maponpaths.
    exact (TranslationEquiv_is_iso1_eq2 x).
  Qed.

  Definition TranslationHEquiv_is_iso1 (x : ComplexHomot_Additive A) :
    is_z_isomorphism
      ((unit_from_left_adjoint
          (mk_are_adjoints _ _ TranslationHTranslationInvHNatTrans
                           InvTranslationHTranslationHNatTrans
                           TranslationHInvTranslationH_adjunction)) x).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) (TranslationEquivUnitInv x)).
    - use mk_is_inverse_in_precat.
      + exact (TranslationHEquiv_is_iso1_eq1' x).
      + exact (TranslationHEquiv_is_iso1_eq2' x).
  Defined.

  Local Lemma TranslationHEquiv_is_iso2_eq1' (x : ComplexHomot_Additive A) :
    (counit_from_left_adjoint
       (mk_are_adjoints _ _ TranslationHTranslationInvHNatTrans InvTranslationHTranslationHNatTrans
                        TranslationHInvTranslationH_adjunction))
      x · # (ComplexHomotFunctor A) (TranslationEquivCounitInv x) =
    identity _.
  Proof.
    cbn.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A)
                                     (InvTranslationTranslationNatTrans_Mor x)
                                     (TranslationEquivCounitInv x)))).
    use (pathscomp0 _ (functor_id (ComplexHomotFunctor A) _)).
    apply maponpaths.
    exact (TranslationEquiv_is_iso2_eq1 x).
  Qed.

  Local Lemma TranslationHEquiv_is_iso2_eq2' (x : ComplexHomot_Additive A) :
    (# (ComplexHomotFunctor A) (TranslationEquivCounitInv x))
      · (counit_from_left_adjoint
            (mk_are_adjoints
               _ _ TranslationHTranslationInvHNatTrans
               InvTranslationHTranslationHNatTrans
               TranslationHInvTranslationH_adjunction)) x = identity _.
  Proof.
    cbn.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A)
                                     (TranslationEquivCounitInv x)
                                     (InvTranslationTranslationNatTrans_Mor x)))).
    use (pathscomp0 _ (functor_id (ComplexHomotFunctor A) _)).
    apply maponpaths.
    exact (TranslationEquiv_is_iso2_eq2 x).
  Qed.

  Definition TranslationHEquiv_is_iso2 (x : ComplexHomot_Additive A) :
    is_z_isomorphism
      ((counit_from_left_adjoint
          (mk_are_adjoints _ _ TranslationHTranslationInvHNatTrans
                           InvTranslationHTranslationHNatTrans
                           TranslationHInvTranslationH_adjunction)) x).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) (TranslationEquivCounitInv x)).
    - use mk_is_inverse_in_precat.
      + exact (TranslationHEquiv_is_iso2_eq1' x).
      + exact (TranslationHEquiv_is_iso2_eq2' x).
  Defined.

  Definition TranslationHEquiv : AddEquiv (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_AddEquiv.
    - exact TranslationFunctorH_AdditiveFunctor.
    - exact InvTranslationFunctorH_AdditiveFunctor.
    - use mk_are_adjoints.
      + exact TranslationHTranslationInvHNatTrans.
      + exact InvTranslationHTranslationHNatTrans.
      + exact TranslationHInvTranslationH_adjunction.
    - intros x. exact (TranslationHEquiv_is_iso1 x).
    - intros x. exact (TranslationHEquiv_is_iso2 x).
  Defined.

End translation_functor.
