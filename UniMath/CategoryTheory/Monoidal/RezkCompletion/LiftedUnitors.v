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

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.CategoriesLemmas.
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
          (*(ru : right_unitor TC I).*)

  Let TD := TransportedTensor Duniv H_eso H_ff TC.

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Lemma LiftPreservesPretensor
    : nat_z_iso (H ∙ I_pretensor TD (H I)) (I_pretensor TC I ∙ H).
  Proof.
    use nat_z_iso_comp.
    2: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply CategoriesLemmas.tensor_after_pair_with_object_left.
    }
    use nat_z_iso_comp.
    3: {
      apply nat_z_iso_inv.
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: apply CategoriesLemmas.tensor_after_pair_with_object_left.
    }

    use nat_z_iso_comp.
    3: { apply CategoriesLemmas.nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      exact (TransportedTensorComm Duniv H_eso H_ff TC).
    }

    use nat_z_iso_comp.
    2: { apply CategoriesLemmas.nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: { apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)). }

    apply CategoriesLemmas.post_whisker_nat_z_iso.
    apply CategoriesLemmas.PairingWithObjectCommutesLeft.
  Defined.

  Definition TransportedLeftUnitor
    : left_unitor TD (H I).
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) H H_eso H_ff).
    use nat_z_iso_comp.
    2: exact LiftPreservesPretensor.
    exact (CategoriesLemmas.post_whisker_nat_z_iso lu H).
  Defined.

  Let luD := TransportedLeftUnitor.

  (* The following definition relates the transported left unitor
     with the left unitor on C. In particular, this shows that
     H preserves the left unitor *)
  Definition TransportedLeftUnitorEq
    : pre_whisker H TransportedLeftUnitor
      = nat_z_iso_comp
          LiftPreservesPretensor
          (CategoriesLemmas.post_whisker_nat_z_iso lu H).
  Proof.
    set (t := lift_nat_trans_along_comm
             (_,,Duniv) _ H_eso H_ff
             (nat_z_iso_comp
                LiftPreservesPretensor
                (nat_z_iso_comp
                   (CategoriesLemmas.post_whisker_nat_z_iso lu H)
                   (nat_z_iso_inv (CategoriesLemmas.functor_commutes_with_id H))
                )
             )
        ).

    refine (_ @ t @ _).
    - apply maponpaths.
      (** The issue here is currently with the definition of
          lift_nat_z_iso_along, one would expect that
          pr1 lift_nat_z_iso_along = lift_nat_trans_along (by definition),
          however, I currently have a different definition.
          If that is solved, then this will be straightforward normally
          by applying nat_trans_eq and then probably "apply (! id_right _)".
          *)
      admit.
    - do 2 apply maponpaths.
      use total2_paths_f.
      2: { apply isaprop_is_nat_z_iso. }
      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply id_right.
  Admitted.

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
      intros G GG x.
      refine (GG (H x) @ _).
      simpl.
      rewrite (functor_id (pr1 G)).
      rewrite id_right.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- functor_comp.
      apply maponpaths.
      refine (TransportedLeftUnitorOnOb x @ _).
      apply maponpaths_2.
      unfold LiftPreservesPretensor.
      simpl.
      rewrite ! id_left.
      rewrite functor_id.
      rewrite ! id_right.
      etrans. {
        apply maponpaths_2.
        apply functor_id.
      }
      apply id_left.
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
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply CategoriesLemmas.tensor_after_pair_with_object_right.
    }
    use nat_z_iso_comp.
    3: {
      apply nat_z_iso_inv.
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: apply CategoriesLemmas.tensor_after_pair_with_object_right.
    }

    use nat_z_iso_comp.
    3: { apply CategoriesLemmas.nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      exact (TransportedTensorComm Duniv H_eso H_ff TC).
    }

    use nat_z_iso_comp.
    2: { apply CategoriesLemmas.nat_z_iso_functor_comp_assoc. }

    use nat_z_iso_comp.
    3: { apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)). }

    apply CategoriesLemmas.post_whisker_nat_z_iso.
    apply CategoriesLemmas.PairingWithObjectCommutesRight.
  Defined.

  Definition TransportedRightUnitor
    : right_unitor TD (H I).
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) H H_eso H_ff).
    use nat_z_iso_comp.
    2: exact LiftPreservesPostTensor.
    exact (CategoriesLemmas.post_whisker_nat_z_iso ru H).
  Defined.

  Let ruD := TransportedRightUnitor.

  Definition TransportedRightUnitorEq
    : pre_whisker H TransportedRightUnitor
      = nat_trans_comp _ _ _
          LiftPreservesPostTensor
          (CategoriesLemmas.post_whisker_nat_z_iso ru H).
  Proof.
    unfold TransportedRightUnitor.
    etrans.
    2: { apply (lift_nat_trans_along_comm (_,,Duniv) _ H_eso H_ff). }
    apply maponpaths.
    use nat_trans_eq.
    { apply homset_property. }
    intro.

    (* Again same issue as with TransportedLeftUnitorEq,
       we should have that lift_nat_z_iso_along should be defined
       w.r.t. lift_nat_trans_along *)
  Admitted.

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
      intros G GG x.
      refine (GG (H x) @ _).
      simpl.
      rewrite (functor_id (pr1 G)).
      rewrite id_right.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- functor_comp.
      apply maponpaths.
      refine (TransportedRightUnitorOnOb x @ _).
      apply maponpaths_2.
      unfold LiftPreservesPretensor.
      simpl.
      rewrite ! id_left.
      rewrite functor_id.
      rewrite ! id_right.
      etrans. {
        apply maponpaths_2.
        apply functor_id.
      }
      apply id_left.
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

End RezkRightUnitor.
