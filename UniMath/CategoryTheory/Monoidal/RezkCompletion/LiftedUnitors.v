(* In LiftedTensor.v and LiftedTensor.v, we have shown that given a category C equipped with a binary operation T and an object I (called the tensor and unit resp.),
then, this structures 'transport' to a weakly equivalent univalent category D, by a weak equivalence H:C->D, making this univalent category D with a tensor and unit,
the free univalent category equipped with a tensor and a unit.
In this file, we show that if we equip (C,T,I) with a left and/or right unitor, then
1: the unitor(s) also transports to D.
2: H preserves the unitor(s) as a monoidal functor preserves the unitor(s).
3: H makes D the free univalent category equipped with tensor, unit and the unitors.
More details about the universality and the Rezk-completion can be found in LiftedMonoidal.v
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalCategoriesTensored.
Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.TotalCategoryFacts.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.

Local Open Scope cat.

Section RezkLeftUnitor.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I).

  Let TD := TransportedTensor Duniv H_eso H_ff TC.

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Lemma LiftPreservesPretensor
    : nat_z_iso (H ∙ I_pretensor TD (H I)) (I_pretensor TC I ∙ H).
  Proof.
    use nat_z_iso_comp.
    2: {
      apply pre_whisker_nat_z_iso.
      apply tensor_after_pair_with_object_left.
    }
    use nat_z_iso_comp.
    3: {
      apply nat_z_iso_inv.
      use post_whisker_nat_z_iso.
      2: apply tensor_after_pair_with_object_left.
    }

    use nat_z_iso_comp.
    3: { apply nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: {
      apply pre_whisker_nat_z_iso.
      exact (TransportedTensorComm Duniv H_eso H_ff TC).
    }

    use nat_z_iso_comp.
    2: { apply nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: { apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)). }

    apply post_whisker_nat_z_iso.
    apply PairingWithObjectCommutesLeft.
  Defined.

  Definition TransportedLeftUnitor
    : left_unitor TD (H I).
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) H H_eso H_ff).
    use nat_z_iso_comp.
    2: exact LiftPreservesPretensor.
    exact (post_whisker_nat_z_iso lu H).
  Defined.

  Let luD := TransportedLeftUnitor.

  (* The following definition relates the transported left unitor
     with the left unitor on C. In particular, this shows that
     H preserves the left unitor *)
  Definition TransportedLeftUnitorEq
    : pre_whisker H TransportedLeftUnitor
      = nat_z_iso_comp
          LiftPreservesPretensor
          (post_whisker_nat_z_iso lu H).
  Proof.
    set (t := lift_nat_trans_along_comm
             (_,,Duniv) _ H_eso H_ff
             (nat_z_iso_comp
                LiftPreservesPretensor
                (nat_z_iso_comp
                   (post_whisker_nat_z_iso lu H)
                   (nat_z_iso_inv (functor_commutes_with_id H))
                )
             )
        ).

    refine (_ @ t @ _).
    - apply maponpaths.
      apply (maponpaths ( lift_nat_trans_along (D,, Duniv) H H_eso H_ff)).
      do 2 apply maponpaths.
      use total2_paths_f.
      2: apply isaprop_is_nat_z_iso.

      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply (! id_right _).
    - do 2 apply maponpaths.
      use total2_paths_f.
      2: { apply isaprop_is_nat_z_iso. }
      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply id_right.
  Qed.

  Definition H_plu
    : (functor_lu_disp_cat lu luD)
        (H ,, (pr1 (TransportedTensorComm Duniv H_eso H_ff TC) ,, identity _)).
  Proof.
    intro c.
    set (t := toforallpaths _ _ _ (base_paths _ _ TransportedLeftUnitorEq) c).
    refine (t @ _).
    clear t.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact (! functor_id TD (H I , H c)).
    }
    rewrite id_left.

    simpl.
    rewrite ! id_left.
    rewrite functor_id.
    rewrite ! id_right.
    rewrite (functor_id (lift_functor_along (D,, Duniv) HH HH_eso HH_ff (TC ∙ H))).
    rewrite id_left.
    apply idpath.
  Qed.

  Lemma TransportedLeftUnitorOnOb
        (c : C)
    : TransportedLeftUnitor (H c) = (LiftPreservesPretensor c) · #H (lu c).
  Proof.
    exact (toforallpaths _ _ _ (base_paths _ _ TransportedLeftUnitorEq) c).
  Qed.

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE).

  Definition precompLU
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_lu_disp_cat luD luE)
                   (functor_lu_disp_cat lu luE).
  Proof.
    use tpair.
    - use tpair.
      2: intro ; intros ; exact tt.
      exact (λ G GG, functor_lu_composition H_plu GG).
    - split ; intro ; intros ; apply isapropunit.
  Qed.

  Lemma precompLU_ff
    : disp_functor_ff precompLU.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - do 3 intro.
      assert (p : isaset ( hfiber (λ ff : unit, (# precompLU)%mor_disp ff) y0)).
      {
        use isaset_hfiber ; use isasetaprop ; apply isapropunit.
      }
      use tpair.
      + use total2_paths_f.
        { apply isapropunit. }
        use proofirrelevance.
        use hlevelntosn.
        apply isapropunit.
      + intro ; apply p.
    - intro ; intros.
      apply hinhpr.
      exists tt.
      apply isapropunit.
  Qed.

  Lemma precompLU_eso
    : disp_functor_disp_ess_split_surj precompLU.
  Proof.
    intros G GG.
    use tpair.
    - intro d.
      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d). }
      { apply homset_property. }
      2: exact (H_eso d).
      intro cd.
      induction (isotoid _ Duniv (pr2 cd)).
      refine  (GG (pr1 cd) @ _).
      simpl.
      rewrite (functor_id (pr1 G)).
      rewrite id_right.
      do 3 rewrite assoc'.
      do 2 apply maponpaths.
      rewrite <- (functor_comp (pr1 G)).
      apply maponpaths.
      simpl.
      refine (_ @ ! TransportedLeftUnitorOnOb (pr1 cd)).
      apply maponpaths_2.
      unfold LiftPreservesPretensor.
      simpl.
      rewrite ! id_left.
      rewrite ! id_right.
      rewrite (functor_id H).
      rewrite id_right.
      etrans.
      2: {
        apply maponpaths_2.
        apply (! functor_id _ _).
      }
      apply (! id_left _).
    - exists tt.
      exists tt.
      split ; apply isapropunit.
  Qed.

  Definition precomp_lunitor_is_ff
    : fully_faithful (total_functor precompLU).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompLU_ff.
  Qed.

  Definition precomp_lunitor_is_eso
    : essentially_surjective (total_functor precompLU).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompLU_eso.
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_total_category.
      + apply is_univalent_functor_category.
        exact Euniv.
      + apply functor_tensorunit_disp_cat_is_univalent.
  Qed.

  Definition precomp_lunitor_adj_equiv
    : adj_equivalence_of_cats (total_functor precompLU).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply functor_lu_disp_cat_is_univalent.
    - exact precomp_lunitor_is_ff.
    - exact precomp_lunitor_is_eso.
  Defined.

  Definition precomp_lunitor_catiso
    : catiso (total_category (functor_lu_disp_cat TransportedLeftUnitor luE))
             (total_category (functor_lu_disp_cat lu luE)).
  Proof.
    use (adj_equivalence_of_cats_to_cat_iso precomp_lunitor_adj_equiv _ _).
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_lu_disp_cat_is_univalent.
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_lu_disp_cat_is_univalent.
  Defined.

End RezkLeftUnitor.

Section RezkRightUnitor.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (ru : right_unitor TC I).

  Let TD := TransportedTensor Duniv H_eso H_ff TC.

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Lemma LiftPreservesPostTensor
    : nat_z_iso (H ∙ I_posttensor TD (H I)) (I_posttensor TC I ∙ H).
  Proof.
    use nat_z_iso_comp.
    2: {
      apply pre_whisker_nat_z_iso.
      apply tensor_after_pair_with_object_right.
    }
    use nat_z_iso_comp.
    3: {
      apply nat_z_iso_inv.
      use post_whisker_nat_z_iso.
      2: apply tensor_after_pair_with_object_right.
    }

    use nat_z_iso_comp.
    3: { apply nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: {
      apply pre_whisker_nat_z_iso.
      exact (TransportedTensorComm Duniv H_eso H_ff TC).
    }

    use nat_z_iso_comp.
    2: { apply nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: { apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)). }

    apply post_whisker_nat_z_iso.
    apply PairingWithObjectCommutesRight.
  Defined.

  Definition TransportedRightUnitor
    : right_unitor TD (H I).
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) H H_eso H_ff).
    use nat_z_iso_comp.
    2: exact LiftPreservesPostTensor.
    exact (post_whisker_nat_z_iso ru H).
  Defined.

  Let ruD := TransportedRightUnitor.

  Definition TransportedRightUnitorEq
    : pre_whisker H TransportedRightUnitor
      = nat_trans_comp _ _ _
          LiftPreservesPostTensor
          (post_whisker_nat_z_iso ru H).
  Proof.
    unfold TransportedRightUnitor.
    etrans.
    2: { apply (lift_nat_trans_along_comm (_,,Duniv) _ H_eso H_ff). }
    apply maponpaths.
    apply (maponpaths ( lift_nat_trans_along (D,, Duniv) H H_eso H_ff)).


    use nat_trans_eq.
    { apply homset_property. }
    intro ; apply idpath.
  Qed.

  Definition H_pru
    : (functor_ru_disp_cat ru ruD)
        (H ,, (pr1 (TransportedTensorComm Duniv H_eso H_ff TC) ,, identity _)).
  Proof.
    intro c.
    set (t := toforallpaths _ _ _ (base_paths _ _ TransportedRightUnitorEq) c).
    refine (t @ _).
    clear t.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact (! functor_id TD (H c , H I)).
    }
    rewrite id_left.

    simpl.
    rewrite ! id_left.
    rewrite functor_id.
    rewrite ! id_right.
    rewrite (functor_id (lift_functor_along (D,, Duniv) HH HH_eso HH_ff (TC ∙ H))).
    rewrite id_left.
    apply idpath.
  Qed.

  Lemma TransportedRightUnitorOnOb
        (c : C)
    : TransportedRightUnitor (H c) = (LiftPreservesPostTensor c) · #H (ru c).
  Proof.
    exact (toforallpaths _ _ _ (base_paths _ _ TransportedRightUnitorEq) c).
  Qed.

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (ruE : right_unitor TE IE).

  Definition precompRU
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_ru_disp_cat ruD ruE)
                   (functor_ru_disp_cat ru ruE).
  Proof.
    use tpair.
    - use tpair.
      2: intro ; intros ; exact tt.
      exact (λ G GG, functor_ru_composition H_pru GG).
    - split ; intro ; intros ; apply isapropunit.
  Qed.

  Lemma precompRU_ff
    : disp_functor_ff precompRU.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - do 3 intro.
      assert (p : isaset ( hfiber (λ ff : unit, (# precompRU)%mor_disp ff) y0)).
      {
        use isaset_hfiber ; use isasetaprop ; apply isapropunit.
      }
      use tpair.
      + use total2_paths_f.
        { apply isapropunit. }
        use proofirrelevance.
        use hlevelntosn.
        apply isapropunit.
      + intro ; apply p.
    - intro ; intros.
      apply hinhpr.
      exists tt.
      apply isapropunit.
  Qed.

  Lemma precompRU_eso
    : disp_functor_disp_ess_split_surj precompRU.
  Proof.
    intros G GG.
    use tpair.
    - intro d.
      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d). }
      { apply homset_property. }
      2: exact (H_eso d).
      intro cd.
      induction (isotoid _ Duniv (pr2 cd)).
      refine  (GG (pr1 cd) @ _).
      simpl.
      rewrite (functor_id (pr1 G)).
      rewrite id_right.
      do 3 rewrite assoc'.
      do 2 apply maponpaths.
      rewrite <- (functor_comp (pr1 G)).
      apply maponpaths.
      simpl.
      refine (_ @ ! TransportedRightUnitorOnOb (pr1 cd)).
      apply maponpaths_2.
      unfold LiftPreservesPostTensor.
      simpl.
      rewrite ! id_left.
      rewrite ! id_right.
      rewrite (functor_id H).
      rewrite id_right.
      etrans.
      2: {
        apply maponpaths_2.
        apply (! functor_id _ _).
      }
      apply (! id_left _).
    - exists tt.
      exists tt.
      split ; apply isapropunit.
  Qed.

  Definition precomp_runitor_is_ff
    : fully_faithful (total_functor precompRU).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompRU_ff.
  Qed.

  Definition precomp_runitor_is_eso
    : essentially_surjective (total_functor precompRU).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompRU_eso.
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_total_category.
      + apply is_univalent_functor_category.
        exact Euniv.
      + apply functor_tensorunit_disp_cat_is_univalent.
  Qed.

  Definition precomp_runitor_adj_equiv
    : adj_equivalence_of_cats (total_functor precompRU).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply functor_ru_disp_cat_is_univalent.
    - exact precomp_runitor_is_ff.
    - exact precomp_runitor_is_eso.
  Defined.

  Definition precomp_runitor_catiso
    : catiso (total_category (functor_ru_disp_cat TransportedRightUnitor ruE))
             (total_category (functor_ru_disp_cat ru ruE)).
  Proof.
    use (adj_equivalence_of_cats_to_cat_iso precomp_runitor_adj_equiv _ _).
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ru_disp_cat_is_univalent.
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ru_disp_cat_is_univalent.
  Defined.

End RezkRightUnitor.
