(** instantiates the scheme from [GenMendlerIteration_alt] for use in the analysis of recursion schemes involving
    actegories (hence, with actions of monoidal categories on categories)

author: Ralph Matthes, 2023
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration_alt.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.

Local Open Scope cat.

Import BifunctorNotations.
Import ActegoryNotations.

Section FixAnActegory.

  Context {V : category} (Mon_V : monoidal V) {C : category}
    (IC : Initial C) (CC : Colims_of_shape nat_graph C)
    (Act : actegory Mon_V C)
    (v : V).

Section FixAFunctor.

  Context (F : functor C C) (HF : is_omega_cocont F).

  Let AF : category := FunctorAlg F.
  Let chnF : chain C := initChain IC F.
  Let μF_Initial : Initial AF := colimAlgInitial IC HF (CC chnF).
  Let μF : C := alg_carrier _ (InitialObject μF_Initial).
  Let α : F μF --> μF := alg_map F (pr1 μF_Initial).

  Context (y : C) (G : functor C C) (ρ' : G y --> y).

  Let L : functor C C := leftwhiskering_functor Act v.

  Context (IL : isInitial C (v ⊗_{Act} (InitialObject IC))) (HL : is_omega_cocont L).

  Definition SpecialGenMendlerIterationWithActegory (θ' : F ∙ L ⟹ L ∙ G) :
    ∃! h : v ⊗_{Act} μF --> y, v ⊗^{Act}_{l} α · h = θ' μF · #G h · ρ'
    := SpecialGenMendlerIteration IC CC F HF y L IL HL G ρ' θ'.

End FixAFunctor.

Section Const_H_AsFunctor.

  Context (CP : BinCoproducts C).

  Context (H : functor C C) (HH : is_omega_cocont H) (c0 : C).

  Let Const_plus_H (c : C) : functor C C := GeneralizedSubstitutionSystems.Const_plus_H H CP c.

  Let AF : category := FunctorAlg (Const_plus_H c0).
  Let chnF : chain C := initChain IC (Const_plus_H c0).

  Local Lemma HF : is_omega_cocont (Const_plus_H c0).
  Proof.
    apply is_omega_cocont_BinCoproduct_of_functors.
    - apply is_omega_cocont_constant_functor.
    - exact HH.
  Qed.

  Let μF_Initial : Initial AF := colimAlgInitial IC HF (CC chnF).
  Let μF : C := alg_carrier _ (InitialObject μF_Initial).
  Let α : Const_plus_H c0 μF --> μF := alg_map (Const_plus_H c0) (pr1 μF_Initial).

  Let η : constant_functor C C c0 μF --> μF := BinCoproductIn1 (CP _ _) · α.
  Let τ : H μF --> μF := BinCoproductIn2 (CP _ _) · α.

  Context (y : C) (θ : lineator_lax Mon_V Act Act H) (ρ : H y --> y) (f : v ⊗_{Act} c0 --> y).

  Context (IL : isInitial C (v ⊗_{Act} (InitialObject IC))).

  Let L : functor C C := leftwhiskering_functor Act v.

  Context (HL : is_omega_cocont L).


  Definition charprop_SpecialGenMendlerIterationWithActegoryAndStrength (h : C ⟦v ⊗_{Act} μF, y⟧) : UU :=
    v ⊗^{Act}_{l} η · h = f × v ⊗^{Act}_{l} τ · h = θ v μF · #H h · ρ.

  Lemma isaprop_charprop_SpecialGenMendlerIterationWithActegoryAndStrength (h : C ⟦v ⊗_{Act} μF, y⟧) :
    isaprop (charprop_SpecialGenMendlerIterationWithActegoryAndStrength h).
  Proof.
    apply isapropdirprod; apply C.
  Qed.

  Definition singleeq_SpecialGenMendlerIterationWithActegoryAndStrength (h : C ⟦v ⊗_{Act} μF, y⟧) : UU :=
    actegory_bincoprod_antidistributor Mon_V CP Act _ _ _ · v ⊗^{Act}_{l} α · h =
                                     BinCoproductArrow (CP _ _) f (θ v μF · #H h · ρ).

  Context (δ : actegory_bincoprod_distributor Mon_V CP Act).

  Definition instance_SpecialGenMendlerIterationWithActegory (h : C ⟦v ⊗_{Act} μF, y⟧) : UU :=
    v ⊗^{Act}_{l} α · h = δ v c0 (H μF) · BinCoproductOfArrows _ (CP _ _) (CP _ _) f (θ v μF) ·
                            #(Const_plus_H y) h · BinCoproductArrow (CP _ _) (identity y) ρ.

  Local Lemma charpropequivsingleeq (h : v ⊗_{Act} μF --> y) :
    charprop_SpecialGenMendlerIterationWithActegoryAndStrength h <-> singleeq_SpecialGenMendlerIterationWithActegoryAndStrength h.
  Proof.
    split.
    - intros [Hchar1 Hchar2].
      red.
      use BinCoproductArrowsEq.
      + etrans.
        { repeat rewrite assoc.
          do 2 apply cancel_postcomposition.
          apply BinCoproductIn1Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        { exact Hchar1. }
        apply pathsinv0, BinCoproductIn1Commutes.
      + etrans.
        { repeat rewrite assoc.
          do 2 apply cancel_postcomposition.
          apply BinCoproductIn2Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        { exact Hchar2. }
        apply pathsinv0, BinCoproductIn2Commutes.
    - intro Hsingle.
      red in Hsingle.
      split.
      + apply (maponpaths (fun m => BinCoproductIn1 (CP _ _) · m)) in Hsingle.
        unfold actegory_bincoprod_antidistributor, bifunctor_bincoprod_antidistributor, bincoprod_antidistributor in Hsingle.
        repeat rewrite assoc in Hsingle.
        rewrite BinCoproductIn1Commutes in Hsingle.
        assert (aux := functor_comp (leftwhiskering_functor Act v)
                         (BinCoproductIn1 (CP (constant_functor C C c0 μF) (H μF)))
                         α).
        cbn in aux.
        apply (maponpaths (fun m => m · h)) in aux.
        assert (Hsingle' := aux @ Hsingle).
        clear Hsingle aux.
        rewrite BinCoproductIn1Commutes in Hsingle'.
        exact Hsingle'.
      + apply (maponpaths (fun m => BinCoproductIn2 (CP _ _) · m)) in Hsingle.
        unfold actegory_bincoprod_antidistributor, bifunctor_bincoprod_antidistributor, bincoprod_antidistributor in Hsingle.
        repeat rewrite assoc in Hsingle.
        rewrite BinCoproductIn2Commutes in Hsingle.
        assert (aux := functor_comp (leftwhiskering_functor Act v)
                         (BinCoproductIn2 (CP (constant_functor C C c0 μF) (H μF)))
                         α).
        cbn in aux.
        apply (maponpaths (fun m => m · h)) in aux.
        assert (Hsingle' := aux @ Hsingle).
        clear Hsingle aux.
        rewrite BinCoproductIn2Commutes in Hsingle'.
        exact Hsingle'.
  Qed.

  Local Lemma instanceequivsingle (h : v ⊗_{Act} μF --> y) :
    instance_SpecialGenMendlerIterationWithActegory h <-> singleeq_SpecialGenMendlerIterationWithActegoryAndStrength h.
  Proof.
    split.
    - intro Hinst.
      red in Hinst.
      red.
      rewrite assoc'.
      apply (z_iso_inv_on_right _ _ _ (_,,bincoprod_functor_lineator_strongly Mon_V CP Act δ v (_,,_))).
      etrans.
      { exact Hinst. }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply maponpaths.
        apply precompWithBinCoproductArrow. }
      etrans.
      { apply precompWithBinCoproductArrow. }
      apply maponpaths_2.
      cbn.
      rewrite id_left.
      apply id_right.
    - intro Hsingle.
      red in Hsingle.
      red.
      rewrite assoc' in Hsingle.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly Mon_V CP Act δ v (_,,_))) in Hsingle.
      etrans.
      { exact Hsingle. }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      2: { apply maponpaths.
           apply pathsinv0, precompWithBinCoproductArrow. }
      etrans.
      2: { apply pathsinv0, precompWithBinCoproductArrow. }
      apply maponpaths_2.
      cbn.
      rewrite id_left.
      apply pathsinv0, id_right.
  Qed.


  Local Definition θ'_data := fun (c : C) => δ v c0 (H c) · BinCoproductOfArrows _ (CP _ _) (CP _ _) f (θ v c).

  Let δll : lineator Mon_V (ProductActegory.actegory_binprod Mon_V Act Act) Act
    (bincoproduct_functor CP) := bincoprod_functor_lineator Mon_V CP Act δ.

  Local Lemma θ'_data_is_nat_trans : is_nat_trans ((Const_plus_H c0) ∙ L) (L ∙ (Const_plus_H y)) θ'_data.
  Proof.
    intros c c' g.
    unfold θ'_data. cbn.
    etrans.
    { rewrite assoc.
      apply cancel_postcomposition.
      apply (lineator_linnatleft _ _ _ _ δll v (_,,_) (_,,_) (_,,_)). }
    repeat rewrite assoc'.
    apply maponpaths.
    cbn.
    etrans.
    { apply BinCoproductOfArrows_comp. }
    etrans.
    2: { apply pathsinv0, BinCoproductOfArrows_comp. }
    cbn.
    rewrite (lineator_linnatleft _ _ _ _ θ v).
    apply maponpaths_2.
    etrans.
    { apply cancel_postcomposition.
      apply (functor_id (leftwhiskering_functor Act v)). }
    rewrite id_right.
    apply id_left.
  Qed.

  Local Definition θ' : (Const_plus_H c0) ∙ L ⟹ L ∙ (Const_plus_H y) := _,, θ'_data_is_nat_trans.

  Definition SpecialGenMendlerIterationWithActegoryAndStrength :
    ∃! h : v ⊗_{Act} μF --> y, charprop_SpecialGenMendlerIterationWithActegoryAndStrength h.
  Proof.
    simple refine (iscontrretract _ _ _ (SpecialGenMendlerIterationWithActegory
                                           (Const_plus_H c0) HF y (Const_plus_H y)
                                           (BinCoproductArrow (CP _ _) (identity y) ρ) IL HL θ')).
    - intros [h Hyp].
      exists h.
      apply charpropequivsingleeq.
      apply instanceequivsingle.
      exact Hyp.
    - intros [h Hyp].
      exists h.
      apply charpropequivsingleeq in Hyp.
      apply instanceequivsingle in Hyp.
      exact Hyp.
    - intros [h Hyp].
      use total2_paths_f.
      + apply idpath.
      + apply isaprop_charprop_SpecialGenMendlerIterationWithActegoryAndStrength.
  Defined.

End Const_H_AsFunctor.


End FixAnActegory.
