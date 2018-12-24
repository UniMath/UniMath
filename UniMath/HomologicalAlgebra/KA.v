(** * K(A), the naive homotopy category of C(A) *)
(** ** Contents
- Definition of K(A)
*)
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
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
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.

Local Open Scope cat.

Unset Kernel Term Sharing.
Global Opaque hz.

Local Open Scope hz_scope.
Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommringops ZeroArrow ishinh.

(** * Homotopies of complexes and K(A), the naive homotopy category of A. *)
(** ** Introduction
   We define homotopy of complexes and the naive homotopy category K(A). A homotopy χ from complex
   X to a complex Y is a family of morphisms χ^i : X^i --> Y^{i-1}. Note that a homotopy χ induces
   a morphism of complexes h : X --> Y by setting
                      # h^i = χ^i · d^{i-1}_Y + d^i_X · χ^{i+1}. #
                      $ h^i = χ^i · d^{i-1}_Y + d^i_X · χ^{i+1}. $
   The subset of morphisms in Mor(X, Y) which are of the form h form an abelian subgroup of
   Mor(X, Y). Also, if f : Z_1 --> X and g : Y --> Z_2 are morphisms of complexes, then f · h and
   h · g have paths to morphisms induced by homotopies. These are given (f^i · χ^i) and
   (χ^i · g^{i-1}), respectively.

   These are the properties that are enough to form the quotient category of C(A) using
   [Quotcategory_Additive]. We call the resulting category the naive homotopy category of A, and
   denote it by K(A). The objects of K(A) are objects of C(A) and Mor_{K(A)}(X, Y) =
   Mor_{C(A)}(X, Y) / (the subgroup of null-homotopic morphisms, [ComplexHomotSubgrp]).

   Homotopies are defined in [ComplexHomot]. The induced morphisms of a homotopy is constructed in
   [ComplexHomotMorphism]. The subgroup of morphisms coming from homotopies is defined in
   [ComplexHomotSubgrp]. Pre- and postcomposition of morphisms coming from homotopies are morphisms
   coming from homotopies are proven in [ComplexHomotSubgrop_comp_right] and
   [ComplexHomotSubgrop_comp_left]. The naive homotopy category K(A) is constructed in
   [ComplexHomot_Additive].
*)
Section complexes_homotopies.

  Variable A : CategoryWithAdditiveStructure.

  Definition ComplexHomot (C1 C2 : Complex A) : UU := ∏ (i : hz), A⟦C1 i, C2 (i - 1)⟧.

  (** This lemma shows that the squares of the morphism map, defined by the homotopy H, commute. *)
  Local Lemma ComplexHomotMorphism_comm {C1 C2 : Complex A} (H : ComplexHomot C1 C2) (i : hz) :
    to_binop (C1 i) (C2 i)
             (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                         (H i · Diff C2 (i - 1)))
             (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                         (Diff C1 i · H (i + 1))) ·
             Diff C2 i =
    Diff C1 i · to_binop (C1 (i + 1)) (C2 (i + 1))
         (transportf (precategory_morphisms (C1 (i + 1))) (maponpaths C2 (hzrminusplus (i + 1) 1))
                     (H (i + 1) · Diff C2 (i + 1 - 1)))
         (transportf (precategory_morphisms (C1 (i + 1))) (maponpaths C2 (hzrplusminus (i + 1) 1))
                     (Diff C1 (i + 1) · H (i + 1 + 1))).
  Proof.
    (* First we get rid of the ZeroArrows *)
    rewrite to_postmor_linear'. rewrite to_premor_linear'.
    assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                             (H i · Diff C2 (i - 1)) ·
                             Diff C2 i) = ZeroArrow (Additive.to_Zero A) _ _).
    {
      induction (hzrminusplus i 1). cbn. unfold idfun. rewrite <- assoc.
      rewrite (@DSq A C2 (i - 1)). apply ZeroArrow_comp_right.
    }
    rewrite e0. clear e0.
    assert (e1 : (Diff C1 i · transportf (precategory_morphisms (C1 (i + 1)))
                       (maponpaths
                          C2 (hzrplusminus (i + 1) 1)) (Diff C1 (i + 1) · H (i + 1 + 1))) =
                 ZeroArrow (Additive.to_Zero A) _ _).
    {
      rewrite <- transport_target_postcompose. rewrite assoc. rewrite (@DSq A C1 i).
      rewrite ZeroArrow_comp_left. apply transport_target_ZeroArrow.
    }
    rewrite e1. clear e1.
    rewrite <- PreAdditive_unel_zero. rewrite to_lunax'. rewrite to_runax'.
    (* Here the idea is to apply cancel_precomposition *)
    rewrite transport_target_postcompose. rewrite <- assoc. apply cancel_precomposition.
    (* Other application of cancel_precomposition *)
    rewrite transport_compose. rewrite transport_target_postcompose. apply cancel_precomposition.
    (* Follows frm transport of differentials *)
    apply pathsinv0. rewrite <- maponpathsinv0.
    use (pathscomp0 _ (transport_hz_section A C2 1 (Diff C2) _ _ (hzrplusminus i 1))).
    use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  (** Every homotopy H of complexes induces a morphism of complexes. The morphism is defined by
      taking the map C1 i --> C2 i to be the sum
                         (H i) · (Diff C2 (i - 1)) + (Diff C1 i) · (H (i + 1)).
      Note that we need to use transportf because the targets are not definitionally equal. The
      target of the first is C2 (i - 1 + 1) and the second target is C2 (i + 1 - 1). We transport
      these to C2 i. *)
  Definition ComplexHomotMorphism {C1 C2 : Complex A} (H : ComplexHomot C1 C2) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i.
      use (@to_binop A (C1 i) (C2 i)).
      + exact (transportf _ (maponpaths C2 (hzrminusplus i 1)) ((H i) · (Diff C2 (i - 1)))).
      + exact (transportf _ (maponpaths C2 (hzrplusminus i 1)) ((Diff C1 i) · (H (i + 1)))).
    - intros i. exact (ComplexHomotMorphism_comm H i).
  Defined.

  (** For all complexes C1 and C2, we define a subset of C1 --> C2 to consist of all the morphisms
      which have a path to a morphism induced by a homotopy H by [ComplexHomotMorphism]. Our goal is
      to show that this subset is an abelian subgroup, and thus we can form the quotient group. *)
  Definition ComplexHomotSubset (C1 C2 : Complex A) :
    @hsubtype ((ComplexPreCat_Additive A)⟦C1, C2⟧) :=
    (fun (f : ((ComplexPreCat_Additive A)⟦C1, C2⟧)) =>
       ∃ (H : ComplexHomot C1 C2), ComplexHomotMorphism H = f).

  (** This lemma shows that the subset [ComplexHomotSubset] satisfies the axioms of a subgroup. *)
  Lemma ComplexHomotisSubgrop (C1 C2 : Complex A) :
    @issubgr (@to_abgr (ComplexPreCat_Additive A) C1 C2) (ComplexHomotSubset C1 C2).
  Proof.
    use tpair.
    - use tpair.
      + intros f g. induction f as [f1 f2]. induction g as [g1 g2].
        use (squash_to_prop f2). apply propproperty. intros f3.
        use (squash_to_prop g2). apply propproperty. intros g3.
        induction f3 as [f3 f4]. induction g3 as [g3 g4].
        use hinhpr. cbn.
        use tpair.
        * intros i.
          use to_binop.
          -- exact (f3 i).
          -- exact (g3 i).
        * cbn.
          rewrite <- f4. rewrite <- g4.
          use MorphismEq.
          intros i. cbn.
          rewrite to_postmor_linear'.
          rewrite to_premor_linear'.
          assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                                   (to_binop (C1 i) (C2 (i + 1 - 1)) (Diff C1 i · f3 (i + 1))
                                             (Diff C1 i · g3 (i + 1)))) =
                       to_binop (C1 i) (C2 i)
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrplusminus i 1))
                                            (Diff C1 i · f3 (i + 1)))
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrplusminus i 1))
                                            (Diff C1 i · g3 (i + 1)))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          cbn in e0. rewrite e0. clear e0.
          assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                                   (to_binop (C1 i) (C2 (i - 1 + 1)) (f3 i · Diff C2 (i - 1))
                                             (g3 i · Diff C2 (i - 1)))) =
                       to_binop (C1 i) (C2 i)
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (f3 i · Diff C2 (i - 1)))
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (g3 i · Diff C2 (i - 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          cbn in e1. rewrite e1. clear e1.
          set (tmp := @assocax (@to_abgr A (C1 i) (C2 i))). cbn in tmp.
          rewrite tmp. rewrite tmp. apply maponpaths.
          rewrite <- tmp. rewrite <- tmp.
          set (tmp' := @commax (@to_abgr A (C1 i) (C2 i))). cbn in tmp'.
          rewrite tmp'.
          rewrite (tmp' _ (transportf (precategory_morphisms (C1 i))
                                      (maponpaths C2 (hzrplusminus i 1))
                                      (Diff C1 i · g3 (i + 1)))).
          apply maponpaths.
          apply tmp'.
      (* ZeroMorphisms *)
      + use hinhpr.
        use tpair.
        * intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
        * cbn. use MorphismEq. intros i. cbn. rewrite ZeroArrow_comp_left.
          rewrite transport_target_ZeroArrow.
          rewrite ZeroArrow_comp_right. rewrite transport_target_ZeroArrow.
          rewrite <- PreAdditive_unel_zero. rewrite to_lunax'. apply idpath.
    - intros f H. use (squash_to_prop H). apply propproperty. intros H'. clear H.
      induction H' as [homot eq]. use hinhpr.
      use tpair.
      + intros i. exact (grinv (to_abgr (C1 i) (C2 (i - 1))) (homot i)).
      + cbn. rewrite <- eq. use MorphismEq. intros i. cbn.
        set (tmp := @PreAdditive_invrcomp A _ _ _ (Diff C1 i) (homot (i + 1))).
        unfold to_inv in tmp. cbn in tmp. cbn. rewrite <- tmp. clear tmp.
        assert (e0 : (transportf (precategory_morphisms (C1 i))
                                 (maponpaths C2 (hzrplusminus i 1))
                                 (grinv (to_abgr (C1 i) (C2 (i + 1 - 1)))
                                        (Diff C1 i · homot (i + 1)))) =
                     to_inv (transportf (precategory_morphisms (C1 i))
                                        (maponpaths C2 (hzrplusminus i 1))
                                        (Diff C1 i · homot (i + 1)))).
        {
          unfold to_inv. cbn. induction (hzrplusminus i 1). apply idpath.
        }
        cbn in e0. rewrite e0. clear e0.
        assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                                 (grinv (to_abgr (C1 i) (C2 (i - 1)))
                                        (homot i) · Diff C2 (i - 1))) =
                     to_inv (transportf (precategory_morphisms (C1 i))
                                        (maponpaths C2 (hzrminusplus i 1))
                                        (homot i · Diff C2 (i - 1)))).
        {
          unfold to_inv. cbn. induction (hzrminusplus i 1). cbn. unfold idfun.
          set (tmp := @PreAdditive_invlcomp A (C1 i) (C2 (i - 1)) (C2 (i - 1 + 1))
                                            (homot i) (Diff C2 (i - 1))).
          apply pathsinv0. unfold to_inv in tmp.
          apply tmp.
        }
        cbn in e1. rewrite e1. clear e1.
        set (tmp' := @commax (@to_abgr A (C1 i) (C2 i))). cbn in tmp'. rewrite tmp'. clear tmp'.
        set (tmp := @grinvop (@to_abgr A (C1 i) (C2 i))). cbn in tmp. unfold to_inv.
        apply pathsinv0.
        apply tmp.
  Qed.

  Definition ComplexHomotSubgrp (C1 C2 : Complex A) :
    @subabgr (@to_abgr (ComplexPreCat_Additive A) C1 C2).
  Proof.
    use subgrconstr.
    - exact (ComplexHomotSubset C1 C2).
    - exact (ComplexHomotisSubgrop C1 C2).
  Defined.

  (** Pre- and postcomposition with morphisms in ComplexHomotSubset is in ComplexHomotSubset. *)
  Lemma ComplexHomotSubgrop_comp_left (C1 : Complex A) {C2 C3 : Complex A}
        (f : ((ComplexPreCat_Additive A)⟦C2, C3⟧)) (H : ComplexHomotSubset C2 C3 f) :
    ∏ (g : ((ComplexPreCat_Additive A)⟦C1, C2⟧)), ComplexHomotSubset C1 C3 (g · f).
  Proof.
    intros g.
    use (squash_to_prop H). apply propproperty. intros HH.
    use hinhpr.
    induction HH as [homot eq].
    use tpair.
    - intros i. exact ((MMor g i) · (homot i)).
    - cbn. rewrite <- eq. use MorphismEq. intros i. cbn. rewrite assoc.
      rewrite <- (MComm g i). rewrite transport_target_postcompose.
      rewrite transport_target_postcompose.
      rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
      rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
      apply idpath.
  Qed.

  Lemma ComplexHomotSubgrop_comp_right {C1 C2 : Complex A} (C3 : Complex A)
        (f : ((ComplexPreCat_Additive A)⟦C1, C2⟧)) (H : ComplexHomotSubset C1 C2 f) :
    ∏ (g : ((ComplexPreCat_Additive A)⟦C2, C3⟧)), ComplexHomotSubset C1 C3 (f · g).
  Proof.
    intros g.
    use (squash_to_prop H). apply propproperty. intros HH.
    use hinhpr.
    induction HH as [homot eq].
    use tpair.
    - intros i. exact ((homot i) · (MMor g (i - 1))).
    - cbn. rewrite <- eq. use MorphismEq. intros i. cbn. rewrite <- assoc.
      rewrite (MComm g (i - 1)). rewrite assoc. rewrite assoc.
      assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C3 (hzrminusplus i 1))
                               (homot i · Diff C2 (i - 1) · MMor g (i - 1 + 1))) =
                   (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                               (homot i · Diff C2 (i - 1))) · (MMor g i)).
      {
        induction (hzrminusplus i 1). apply idpath.
      }
      cbn in e0. rewrite e0. clear e0.
      assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C3 (hzrplusminus i 1))
                               (Diff C1 i · homot (i + 1) · MMor g (i + 1 - 1))) =
                   (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                               (Diff C1 i · homot (i + 1))) · (MMor g i)).
      {
        induction (hzrplusminus i 1). apply idpath.
      }
      cbn in e1. rewrite e1. clear e1.
      rewrite <- to_postmor_linear'. apply idpath.
  Qed.


  (** ** Naive homotopy category
     We know that the homotopies from C1 to C2 form an abelian subgroup of the abelian group of all
     morphisms from C1 to C2, by [ComplexHomotSubgrp]. We also know that composition of a morphism
     with a morphism coming from a homotopy, is a morphism which comes from a homotopy, by
     [ComplexHomotSubgrop_comp_left] and [ComplexHomotSubgrop_comp_right]. This is enough to
     invoke our abstract construction Quotcategory_Additive, to construct the naive homotopy
     category. *)
  Local Lemma ComplexHomot_Additive_Comp :
    PreAdditiveComps (ComplexPreCat_Additive A)
                     (λ C1 C2 : ComplexPreCat_Additive A, ComplexHomotSubgrp C1 C2).
  Proof.
    intros C1 C2. split.
    - intros C3 f H g.
      apply ComplexHomotSubgrop_comp_right. apply H.
    - intros C3 f g H.
      apply ComplexHomotSubgrop_comp_left. apply H.
  Qed.

  (** Here we construct K(A). *)
  Definition ComplexHomot_Additive : CategoryWithAdditiveStructure :=
    Quotcategory_Additive
      (ComplexPreCat_Additive A) ComplexHomotSubgrp ComplexHomot_Additive_Comp.

  Definition ComplexHomotFunctor :
    AdditiveFunctor (ComplexPreCat_Additive A) ComplexHomot_Additive :=
    QuotcategoryAdditiveFunctor
      (ComplexPreCat_Additive A) ComplexHomotSubgrp ComplexHomot_Additive_Comp.
  Arguments ComplexHomotFunctor : simpl never.

  Lemma ComplexHomotFunctor_issurj {C1 C2 : ComplexPreCat_Additive A}
        (f : ComplexHomot_Additive⟦C1, C2⟧) : ∥ hfiber (# ComplexHomotFunctor) f ∥.
  Proof.
    apply issurjsetquotpr.
  Qed.

  Lemma ComplexHomotFunctor_rel_mor {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : subgrhrel (ComplexHomotSubgrp C1 C2) f g) :
    # ComplexHomotFunctor f = # ComplexHomotFunctor g.
  Proof.
    apply abgrquotpr_rel_image. apply H.
  Qed.

  Lemma ComplexHomotFunctor_rel_mor' {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : ComplexHomot C1 C2)
        (H' : to_binop _ _ f (to_inv g) = ComplexHomotMorphism H) :
    # ComplexHomotFunctor f = # ComplexHomotFunctor g.
  Proof.
    apply ComplexHomotFunctor_rel_mor.
    use hinhpr.
    use tpair.
    - cbn. use tpair.
      + exact (ComplexHomotMorphism H).
      + use hinhpr.
        use tpair.
        * exact H.
        * apply idpath.
    - exact (! H').
  Qed.

  Lemma ComplexHomotFunctor_mor_rel {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : # ComplexHomotFunctor f = # ComplexHomotFunctor g) :
    subgrhrel (ComplexHomotSubgrp C1 C2) f g.
  Proof.
    use (@abgrquotpr_rel_paths _ (binopeqrel_subgr_eqrel (ComplexHomotSubgrp C1 C2))).
    apply H.
  Qed.

  Lemma ComplexHomotFunctor_im_to_homot {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : # ComplexHomotFunctor f = # ComplexHomotFunctor g) :
    ∥ ∑ h : ComplexHomot C1 C2, ComplexHomotMorphism h = to_binop _ _ f (to_inv g) ∥.
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_mor_rel f g H) (propproperty _)). intros h.
    induction h as [b hh]. cbn in b. unfold ComplexHomotSubset in b.
    use (squash_to_prop (pr2 b) (propproperty _)). intros hhh.
    induction hhh as [H1 H2]. cbn in hh. cbn in H2.
    use hinhpr.
    use tpair.
    - exact H1.
    - exact (H2 @ hh).
  Qed.

  Lemma ComplexHomotPreCompHomot {C1 C2 C3 : ComplexPreCat_Additive A}
        (f1 : (ComplexPreCat_Additive A)⟦C1, C2⟧) (f2 f3 : (ComplexPreCat_Additive A)⟦C2, C3⟧)
        (H : # ComplexHomotFunctor f2 = # ComplexHomotFunctor f3) :
    ∥ ∑ (h : ComplexHomot C1 C3),
    ComplexHomotMorphism h = to_binop _ _ (f1 · f2) (to_inv (f1 · f3)) ∥.
  Proof.
    assert (e : # ComplexHomotFunctor (f1 · f2) = # ComplexHomotFunctor (f1 · f3)).
    {
      rewrite functor_comp. rewrite H. rewrite functor_comp. apply idpath.
    }
    exact (ComplexHomotFunctor_im_to_homot (f1 · f2) (f1 · f3) e).
  Qed.

  Lemma ComplexHomotPostCompHomot {C1 C2 C3 : ComplexPreCat_Additive A}
        (f1 f2 : (ComplexPreCat_Additive A)⟦C1, C2⟧) (f3 : (ComplexPreCat_Additive A)⟦C2, C3⟧)
        (H : # ComplexHomotFunctor f1 = # ComplexHomotFunctor f2) :
    ∥ ∑ (h : ComplexHomot C1 C3),
    ComplexHomotMorphism h = to_binop _ _ (f1 · f3) (to_inv (f2 · f3)) ∥.
  Proof.
    assert (e : # ComplexHomotFunctor (f1 · f3) = # ComplexHomotFunctor (f2 · f3)).
    {
      rewrite functor_comp. rewrite H. rewrite functor_comp. apply idpath.
    }
    exact (ComplexHomotFunctor_im_to_homot (f1 · f3) (f2 · f3) e).
  Qed.

  (** Commutativity of squares *)

  Lemma ComplexHomotComm2 {C1 C2 C3 C4 : ob ComplexHomot_Additive}
        {f1 : C1 --> C2} {f2 : C2 --> C4} {g1 : C1 --> C3} {g2 : C3 --> C4}
        (f1' : hfiber (# ComplexHomotFunctor) f1) (f2' : hfiber (# ComplexHomotFunctor) f2)
        (g1' : hfiber (# ComplexHomotFunctor) g1) (g2' : hfiber (# ComplexHomotFunctor) g2)
        (H : f1 · f2 = g1 · g2) :
    # ComplexHomotFunctor ((hfiberpr1 _ _ f1') · (hfiberpr1 _ _ f2')) =
    # ComplexHomotFunctor ((hfiberpr1 _ _ g1') · (hfiberpr1 _ _ g2')).
  Proof.
    rewrite functor_comp. rewrite functor_comp.
    rewrite (hfiberpr2 _ _ f1'). rewrite (hfiberpr2 _ _ f2').
    rewrite (hfiberpr2 _ _ g1'). rewrite (hfiberpr2 _ _ g2').
    exact H.
  Qed.

  Lemma ComplexHomotComm3 {C1 C2 C3 C4 C5 C6 : ob ComplexHomot_Additive}
        {f1 : C1 --> C2} {f2 : C2 --> C3} {f3 : C3 --> C6}
        {g1 : C1 --> C4} {g2 : C4 --> C5} {g3 : C5 --> C6}
        (f1' : hfiber (# ComplexHomotFunctor) f1) (f2' : hfiber (# ComplexHomotFunctor) f2)
        (f3' : hfiber (# ComplexHomotFunctor) f3)
        (g1' : hfiber (# ComplexHomotFunctor) g1) (g2' : hfiber (# ComplexHomotFunctor) g2)
        (g3' : hfiber (# ComplexHomotFunctor) g3)
        (H : f1 · f2 · f3 = g1 · g2 · g3 ) :
    # ComplexHomotFunctor ((hfiberpr1 _ _ f1') · (hfiberpr1 _ _ f2') · (hfiberpr1 _ _ f3')) =
    # ComplexHomotFunctor ((hfiberpr1 _ _ g1') · (hfiberpr1 _ _ g2') · (hfiberpr1 _ _ g3')).
  Proof.
    rewrite functor_comp. rewrite functor_comp. rewrite functor_comp. rewrite functor_comp.
    rewrite (hfiberpr2 _ _ f1'). rewrite (hfiberpr2 _ _ f2'). rewrite (hfiberpr2 _ _ f3').
    rewrite (hfiberpr2 _ _ g1'). rewrite (hfiberpr2 _ _ g2'). rewrite (hfiberpr2 _ _ g3').
    exact H.
  Qed.

  Lemma ComplexHomotComm4 {C1 C2 C3 C4 C5 C6 C7 C8 : ob ComplexHomot_Additive}
        {f1 : C1 --> C2} {f2 : C2 --> C3} {f3 : C3 --> C4} {f4 : C4 --> C8}
        {g1 : C1 --> C5} {g2 : C5 --> C6} {g3 : C6 --> C7} {g4 : C7 --> C8}
        (f1' : hfiber (# ComplexHomotFunctor) f1) (f2' : hfiber (# ComplexHomotFunctor) f2)
        (f3' : hfiber (# ComplexHomotFunctor) f3) (f4' : hfiber (# ComplexHomotFunctor) f4)
        (g1' : hfiber (# ComplexHomotFunctor) g1) (g2' : hfiber (# ComplexHomotFunctor) g2)
        (g3' : hfiber (# ComplexHomotFunctor) g3) (g4' : hfiber (# ComplexHomotFunctor) g4)
        (H : f1 · f2 · f3 · f4 = g1 · g2 · g3 · g4) :
    # ComplexHomotFunctor ((hfiberpr1 _ _ f1') · (hfiberpr1 _ _ f2') · (hfiberpr1 _ _ f3')
                                               · (hfiberpr1 _ _ f4')) =
    # ComplexHomotFunctor ((hfiberpr1 _ _ g1') · (hfiberpr1 _ _ g2') · (hfiberpr1 _ _ g3')
                                               · (hfiberpr1 _ _ g4')).
  Proof.
    rewrite functor_comp. rewrite functor_comp. rewrite functor_comp. rewrite functor_comp.
    rewrite functor_comp. rewrite functor_comp.
    rewrite (hfiberpr2 _ _ f1'). rewrite (hfiberpr2 _ _ f2'). rewrite (hfiberpr2 _ _ f3').
    rewrite (hfiberpr2 _ _ f4').
    rewrite (hfiberpr2 _ _ g1'). rewrite (hfiberpr2 _ _ g2'). rewrite (hfiberpr2 _ _ g3').
    rewrite (hfiberpr2 _ _ g4').
    exact H.
  Qed.

End complexes_homotopies.