(****************************************************************

 In this file, we combine the facts from `precomp_ess_surj.v`
 and `precomp_fully_faithful.v`. We show that if we have a fully
 faithful and essential surjective functor `F : C₁ ⟶ C₂` and a
 univalent category `D`, then we have an adjoint equivalence
 between `[ C₂ , D ]` and `[ C₁ , D ]` (the functor is given
 by precomposition). We also give some functions to use this
 adjoint equivalence.

 ****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.precomp_ess_surj.
Require Import UniMath.CategoryTheory.precomp_fully_faithful.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Section PrecompEquivalence.
  Context {C₁ C₂ : category}
          (D : univalent_category)
          (F : C₁ ⟶ C₂)
          (HF₁ : essentially_surjective F)
          (HF₂ : fully_faithful F).

  Definition precomp_adjoint_equivalence
    : adj_equivalence_of_cats (pre_composition_functor C₁ C₂ (pr1 D) F).
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      exact (pr2 D).
    - exact (pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful
               C₁ C₂ D
               F
               HF₁ HF₂).
    - exact (pre_composition_essentially_surjective
               C₁ C₂ D (pr2 D)
               F
               HF₁ HF₂).
  Defined.

  Let L : [ C₂ , D ] ⟶ [ C₁ , D ]
    := pre_composition_functor C₁ C₂ (pr1 D) F.
  Let R : [ C₁ , D ] ⟶ [ C₂ , D ]
    := right_adjoint precomp_adjoint_equivalence.
  Let ε : nat_z_iso (R ∙ L) (functor_identity _)
    := counit_nat_z_iso_from_adj_equivalence_of_cats
         precomp_adjoint_equivalence.
  Let η : nat_z_iso (functor_identity _) (L ∙ R)
    := unit_nat_z_iso_from_adj_equivalence_of_cats
         precomp_adjoint_equivalence.

  Definition lift_functor_along
             (G : C₁ ⟶ D)
    : C₂ ⟶ D
    := R G.

  Definition lift_functor_along_comm
             (G : C₁ ⟶ D)
    : nat_z_iso (F ∙ lift_functor_along G) G
    := nat_z_iso_from_z_iso _ (nat_z_iso_pointwise_z_iso ε G).

  Definition lift_nat_trans_along
             {G₁ G₂ : C₂ ⟶ D}
             (α : F ∙ G₁ ⟹ F ∙ G₂)
    : G₁ ⟹ G₂.
  Proof.
    exact (invmap
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   precomp_adjoint_equivalence
                   G₁ G₂))
          α).
  Defined.

  Definition lift_nat_trans_along_comm
             {G₁ G₂ : C₂ ⟶ D}
             (α : F ∙ G₁ ⟹ F ∙ G₂)
    : pre_whisker F (lift_nat_trans_along α) = α.
  Proof.
    exact (homotweqinvweq
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   precomp_adjoint_equivalence
                   G₁ G₂))
             α).
  Qed.

  Definition lift_nat_trans_eq_along
             {G₁ G₂ : C₂ ⟶ D}
             {β₁ β₂ : G₁ ⟹ G₂}
             (p : pre_whisker F β₁ = pre_whisker F β₂)
    : β₁ = β₂.
  Proof.
    exact (maponpaths
             pr1
             (proofirrelevance
                _
                (pr2 (fully_faithful_implies_full_and_faithful
                        _ _ _
                        (fully_faithful_from_equivalence
                           _ _ _
                           precomp_adjoint_equivalence))
                   G₁ G₂
                   (pre_whisker F β₂))
                (β₁ ,, p)
                (β₂ ,, idpath _))).
  Qed.

  Definition lift_nat_z_iso_along
             {G₁ G₂ : C₂ ⟶ D}
             (α : nat_z_iso (F ∙ G₁) (F ∙ G₂))
    : nat_z_iso G₁ G₂.
  Proof.
    exists (lift_nat_trans_along α).

    use is_functor_z_iso_pointwise_if_z_iso.
    { apply homset_property. }

    set (β := (z_iso_from_nat_z_iso (homset_property _) α)).
    set (ff_precomp := (fully_faithful_from_equivalence
                          [C₂, pr1 D] [C₁, pr1 D]
                          (pre_composition_functor C₁ C₂ (pr1 D) F)
                          precomp_adjoint_equivalence)).

    exact (fully_faithful_reflects_iso_proof
             [C₂, pr1 D] [C₁, pr1 D]
             (pre_composition_functor _ _ D F)
             ff_precomp _ _ β
          ).
  Defined.

End PrecompEquivalence.

Section WeakEquivalenceProperties.

  Lemma iscontr_prod (A B : UU)
    : iscontr A -> iscontr B -> iscontr (A × B).
  Proof.
    intros p q.
    exists (pr1 p ,, pr1 q).
    intro t.
    use total2_paths_f.
    { apply (pr2 p). }
    rewrite transportf_const.
    apply (pr2 q).
  Qed.

  Context {C1 C2 D1 D2 : category}
          (F : functor C1 C2) (G : functor D1 D2).

  Definition pair_functor_ff
             (F_ff : fully_faithful F)
             (G_ff : fully_faithful G)
    : fully_faithful (pair_functor F G).
  Proof.

    intros cd cd' cd2.

    assert (hfiberprod : hfiber # (pair_functor F G) cd2 ≃ (hfiber # F (pr1 cd2) × hfiber # G (pr2 cd2))).
    {
      use weq_iso.
      - intro x.
        use tpair.
        + exists (pr11 x).
          exact (maponpaths pr1 (pr2 x)).
        + exists (pr21 x).
          etrans.
          2: {
            apply maponpaths.
            apply x.
          }
          apply idpath.
      - intro xy.
        exists (catbinprodmor (pr11 xy) (pr12 xy)).
        use total2_paths_f.
        + exact (pr21 xy).
        + etrans. {
            exact (toforallpaths _ _ _ (transportf_const (pr21 xy) ( D2 ⟦ pr2 (pair_functor F G cd), pr2 (pair_functor F G cd') ⟧)) (pr2 (# (pair_functor F G) (catbinprodmor (pr11 xy) (pr12 xy))))).
          }
          exact (pr22 xy).
      - intro.
        use total2_paths_f.
        + apply idpath.
        + apply homset_property.
      - intro.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath.
          * apply homset_property.
        + use total2_paths_f.
          * cbn.
            etrans. {
              apply maponpaths.
              rewrite transportf_const.
              apply idpath.
            }
            apply idpath.
          * apply homset_property.
    }

    use iscontrweqb'.
    3: { apply hfiberprod. }
    apply iscontr_prod.
    - apply (F_ff (pr1 cd) (pr1 cd') (pr1 cd2)).
    - apply (G_ff (pr2 cd) (pr2 cd') (pr2 cd2)).
  Qed.

  Definition pair_functor_eso
             (F_eso : essentially_surjective F)
             (G_eso : essentially_surjective G)
    : essentially_surjective (pair_functor F G).
  Proof.
    intro cd2.
    use (factor_through_squash _ _ (F_eso (pr1 cd2))).
    { apply ishinh. }
    intro d1.
    use (factor_through_squash _ _ (G_eso (pr2 cd2))).
    { apply ishinh. }
    intro d2.
    apply hinhpr.
    exists (pr1 d1 ,, pr1 d2).
    use precatbinprod_z_iso.
    - exact (pr2 d1).
    - exact (pr2 d2).
  Qed.

End WeakEquivalenceProperties.

Section LiftedFunctorsIdentity.

  Definition lift_functor_along_id
             {C : category}
             (D : univalent_category)
             {F : functor C D}
             (F_eso : essentially_surjective F)
             (F_ff : fully_faithful F)
    :   nat_z_iso
          (lift_functor_along D F F_eso F_ff (functor_identity C ∙ F))
          (functor_identity D).
  Proof.
    use (lift_nat_z_iso_along D F F_eso F_ff).
    use nat_z_iso_comp.
    2: apply lift_functor_along_comm.
    use make_nat_z_iso.
    - use make_nat_trans.
      { exact (λ _, identity _). }
      abstract (intro ; intros ; exact (id_right _ @ ! id_left _)).
    - intro.
      exists (identity _).
      abstract (split ; apply id_right).
  Defined.

End LiftedFunctorsIdentity.


Section LiftedFunctorsComposition.

  Context {C1 C2 C3 D1 : category}
          (D2 D3 : univalent_category)
          {F1 : functor C1 D1}
          {F2 : functor C2 D2}
          (F3 : functor C3 D3)
          (F1_eso : essentially_surjective F1)
          (F1_ff : fully_faithful F1)
          (F2_eso : essentially_surjective F2)
          (F2_ff : fully_faithful F2).

  Definition lift_functor_along_comp
             (G1 : functor C1 C2) (G2 : functor C2 C3)
    : nat_z_iso
        (lift_functor_along D3 F1 F1_eso F1_ff ((G1 ∙ G2) ∙ F3))
        (lift_functor_along D2 F1 F1_eso F1_ff (G1 ∙ F2)
                           ∙ lift_functor_along D3 F2 F2_eso F2_ff (G2 ∙ F3)).
  Proof.
    use (lift_nat_z_iso_along D3 F1 F1_eso F1_ff).

    set (l := lift_functor_along_comm D3 F2 F2_eso F2_ff (G2 ∙ F3)).
    set (l2_i := pre_whisker_on_nat_z_iso G1 (pr1 l) (pr2 l)).
    set (u := lift_functor_along_comm D2 F1 F1_eso F1_ff (G1 ∙ F2)).
    set (u2_i := post_whisker_z_iso_is_z_iso
                   (pr1 u)
                   (lift_functor_along D3 F2 F2_eso F2_ff ((G2 ∙ F3)))
                   (pr2 u)
        ).


    transparent assert ( l2 : (nat_z_iso
                                (functor_composite G1 (F2 ∙ lift_functor_along D3 F2 F2_eso F2_ff (G2 ∙ F3)))
                                (functor_composite G1 (G2 ∙ F3)))).
    {
      use make_nat_z_iso.
      2: exact l2_i.
    }

    transparent assert (u2 : (nat_z_iso
                                (functor_composite
                                    (F1 ∙ lift_functor_along D2 F1 F1_eso F1_ff (G1 ∙ F2))
                                    (lift_functor_along D3 F2 F2_eso F2_ff (G2 ∙ F3)))
                                (functor_composite (G1 ∙ F2) (lift_functor_along D3 F2 F2_eso F2_ff (G2 ∙ F3))))).
    {
      use make_nat_z_iso.
      2: exact u2_i.
    }

    use nat_z_iso_comp.
    2: { apply lift_functor_along_comm. }
    use nat_z_iso_comp.
    2: { exact (nat_z_iso_inv l2). }
    exact (nat_z_iso_inv u2).
  Defined.

End LiftedFunctorsComposition.

Section LiftedFunctorsPairFunctor.

  Local Lemma nat_z_iso_pair {C1 C2 D1 D2 E1 E2 : category}
        (F1 : functor C1 D1) (F2 : functor D1 E1)
        (G1 : functor C2 D2) (G2 : functor D2 E2)
    : nat_z_iso (pair_functor (F1 ∙ F2) (G1 ∙ G2))
                (pair_functor F1 G1 ∙ pair_functor F2 G2).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; apply catbinprodmor ; apply identity.
      + abstract (intro ; intros ; use total2_paths_f ;
          [ exact (id_right _ @ ! id_left _) | rewrite transportf_const ; exact (id_right _ @ ! id_left _) ]).
    - intro.
      use make_is_z_isomorphism.
      + apply catbinprodmor ; apply identity.
      + abstract (split ; (use total2_paths_f ; [ apply id_right | rewrite transportf_const ; apply id_right ])).
  Defined.

  Local Lemma nat_z_iso_between_pair {C1 C2 D1 D2 : category}
        {F1 F1' : functor C1 D1}
        {G1 G1' : functor C2 D2}
        (α : nat_z_iso F1 F1') (β : nat_z_iso G1 G1')
    : nat_z_iso (pair_functor F1 G1)
                (pair_functor F1' G1').
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; apply catbinprodmor ; [apply α | apply β].
      + abstract (intro ; intros ; use total2_paths_f ; [apply (pr1 α) | rewrite transportf_const ; apply (pr1 β)]).
    - intro.
      use tpair.
      + apply catbinprodmor ; [apply (pr2 α) | apply (pr2 β)].
      + abstract (split ; (use total2_paths_f ; [apply (pr2 α) | rewrite transportf_const ; apply (pr2 β)])).
  Defined.

  Context {C1 C2 C1' C2' D1 D2 : category}
          (D1' D2' : univalent_category)
          {F1 : functor C1 D1}
          {F2 : functor C2 D2}
          (F1' : functor C1' D1')
          (F2' : functor C2' D2')
          (F1_eso : essentially_surjective F1)
          (F2_eso : essentially_surjective F2)
          (F1_ff : fully_faithful F1)
          (F2_ff : fully_faithful F2).

  Let FF := pair_functor F1 F2.
  Let FF' := pair_functor F1' F2'.

  Let FF_eso := pair_functor_eso _ _ F1_eso F2_eso.
  Let FF_ff := pair_functor_ff _ _ F1_ff F2_ff.

  Let DD' := (_ ,, is_unvialent_category_binproduct (pr2 D1') (pr2 D2')) : univalent_category.

  Definition lift_functor_along_pair
             (H1 : functor C1 C1') (H2 : functor C2 C2')
    : nat_z_iso (lift_functor_along DD' FF FF_eso FF_ff (pair_functor H1 H2 ∙ pair_functor F1' F2'))
                (pair_functor (lift_functor_along D1' F1 F1_eso F1_ff (H1 ∙ F1'))
                              (lift_functor_along D2' F2 F2_eso F2_ff (H2 ∙ F2'))).
  Proof.
    use (lift_nat_z_iso_along DD' FF FF_eso FF_ff).
    set (l := lift_functor_along_comm DD' FF FF_eso FF_ff  (pair_functor H1 H2 ∙ pair_functor F1' F2')).
    use nat_z_iso_comp.
    2: { exact l. }
    use nat_z_iso_comp.
    3: { apply nat_z_iso_pair. }
    use nat_z_iso_comp.
    2: { apply (nat_z_iso_inv (nat_z_iso_pair _ _ _ _)). }
    use nat_z_iso_between_pair ; apply (nat_z_iso_inv (lift_functor_along_comm _ _ _ _ _)).
  Defined.

End LiftedFunctorsPairFunctor.

Section LiftedFunctorsProperties.

  Local Lemma post_whisker_nat_z_iso {C D E : category}
        {F1 F2 : functor C D} (α : nat_z_iso F1 F2) (G : functor D E)
    : nat_z_iso (F1 ∙ G) (F2 ∙ G).
  Proof.
    use make_nat_z_iso.
    2: { exact (post_whisker_z_iso_is_z_iso α G (pr2 α)). }
  Defined.

  Context {C : category} (D : univalent_category)
            (F1 : functor C D)
            (F1_eso : essentially_surjective F1)
            (F1_ff : fully_faithful F1).

  Let FF := pair_functor F1 F1.
  Let FF_ff := pair_functor_ff _ _ F1_ff F1_ff.
  Let FF_eso := pair_functor_eso _ _ F1_eso F1_eso.

  Let FFF := pair_functor FF F1.
  Let FFF_ff := pair_functor_ff _ _ FF_ff F1_ff.
  Let FFF_eso := pair_functor_eso _ _ FF_eso F1_eso.

  Let FFF' := pair_functor F1 FF.
  Let FFF'_ff := pair_functor_ff _ _ F1_ff FF_ff.
  Let FFF'_eso := pair_functor_eso _ _ F1_eso FF_eso.

  Let DD := (_ ,, is_unvialent_category_binproduct (pr2 D) (pr2 D)) : univalent_category.
  Let DDD := (_ ,, is_unvialent_category_binproduct (pr2 DD) (pr2 D)) : univalent_category.
  Let DDD' := (_ ,, is_unvialent_category_binproduct (pr2 D) (pr2 DD)) : univalent_category.

  Lemma lift_functor_along_comm_prod
        (H : functor (category_binproduct C C) C)
    : nat_z_iso
        (lift_functor_along D FFF FFF_eso FFF_ff
                            ((pair_functor H (functor_identity C) ∙ H) ∙ F1))
        (pair_functor (lift_functor_along
                         D
                         FF
                         FF_eso
                         FF_ff
                         (functor_composite H F1)
                      )
                      (functor_identity D)
                      ∙ (lift_functor_along
                           D
                           FF
                           FF_eso
                           FF_ff
                           (functor_composite H F1))
        )
  .
  Proof.

    use nat_z_iso_comp.
    2: {
      exact (lift_functor_along_comp DD D F1 FFF_eso FFF_ff FF_eso FF_ff
                                     (pair_functor H (functor_identity C)) H).
    }

    apply post_whisker_nat_z_iso.
    use nat_z_iso_comp.
    2 : { apply lift_functor_along_pair. }
    use nat_z_iso_between_pair.
    - use make_nat_z_iso.
      2: apply is_nat_z_iso_nat_trans_id.
    - apply lift_functor_along_id.
  Defined.

  Lemma lift_functor_along_comm_prod'
        (H : functor (category_binproduct C C) C)
    : nat_z_iso
        (lift_functor_along D FFF' FFF'_eso FFF'_ff
                            ((pair_functor (functor_identity C) H ∙ H) ∙ F1))
        (pair_functor
           (functor_identity D)
           (lift_functor_along
                         D
                         FF
                         FF_eso
                         FF_ff
                         (functor_composite H F1)
                      )

                      ∙ (lift_functor_along
                           D
                           FF
                           FF_eso
                           FF_ff
                           (functor_composite H F1))
        )
  .
  Proof.

    use nat_z_iso_comp.
    2: {
      exact (lift_functor_along_comp DD D F1 FFF'_eso FFF'_ff FF_eso FF_ff
                                     (pair_functor (functor_identity C) H) H).
    }

    apply post_whisker_nat_z_iso.
    use nat_z_iso_comp.
    2 : { apply lift_functor_along_pair. }
    use nat_z_iso_between_pair.
    - apply lift_functor_along_id.
    - use make_nat_z_iso.
      2: apply is_nat_z_iso_nat_trans_id.
  Defined.

End LiftedFunctorsProperties.
