Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.

(* Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.CategoriesLemmas. *)
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.DisplayedCategoriesLemmas.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.

Local Open Scope cat.

Section LiftedUnit.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H)
          (I : C) (IE : E).

  Definition ID : D := H I.

  Definition precompU_data
    : disp_functor_data (pre_composition_functor _ _ E H)
                   (functor_unit_disp_cat ID IE)
                   (functor_unit_disp_cat I IE).
  Proof.
    exists (λ G GG, GG · #(pr1 G) (identity _)).
    intros G1 G2 GG1 GG2 β ββ.
    simpl.
    unfold nat_trans_unit.
    simpl.
    rewrite (functor_id G1).
    rewrite id_right.
    rewrite (functor_id G2).
    refine (ββ @ _).
    apply (! id_right _).
  Defined.



  Definition HU
    : disp_functor (pre_composition_functor _ _ E H)
                   (functor_unit_disp_cat ID IE)
                   (functor_unit_disp_cat I IE).
  Proof.
    exists precompU_data.
    abstract (split ; intro ; intros ; apply homset_property).
  Defined.



  Definition HU_eso : disp_functor_disp_ess_split_surj HU.
  Proof.
    intros G HGG.
    exists HGG.
    use Isos.make_z_iso_disp.
    - simpl.
      unfold nat_trans_unit.
      rewrite id_right.
      rewrite (functor_id G).
      apply id_right.
    - use tpair.
      + simpl.
        unfold nat_trans_unit.
        rewrite id_right.
        rewrite (functor_id G).
        apply (! id_right _).
      + split ; apply homset_property.
  Qed.



  Definition HU_is_faithful
             {G1 G2 : [D, E]}
             (GG1 : functor_unit_disp_cat ID IE G1)
             (GG2 : functor_unit_disp_cat ID IE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    : isincl (λ ff : GG1 -->[ β] GG2, (# HU)%mor_disp ff).
  Proof.
    do 3 intro.
    assert (p : isaset ( hfiber (λ ff : GG1 -->[ β] GG2, (# HU)%mor_disp ff) y)).
    {
      use isaset_hfiber ; use isasetaprop ; apply homset_property.
    }

    use tpair.
    + use total2_paths_f.
      { apply homset_property. }
      use proofirrelevance.
      use hlevelntosn.
      apply homset_property.
    + intro ; apply p.
  Qed.



  Definition HU_is_full
             {G1 G2 : [D, E]}
             (GG1 : functor_unit_disp_cat ID IE G1)
             (GG2 : functor_unit_disp_cat ID IE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    :   issurjective (λ ff : GG1 -->[ β] GG2, (# HU)%mor_disp ff).
  Proof.
    intro βHH.
    apply hinhpr.
    use tpair.
    2: apply homset_property.
    simpl in βHH.
    unfold nat_trans_unit in βHH.
    simpl in βHH.
    rewrite (functor_id G1) in βHH.
    rewrite (functor_id G2) in βHH.
    do 2 rewrite id_right in βHH.
    exact βHH.
  Qed.



  Definition HU_ff : disp_functor_ff HU.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - apply HU_is_faithful.
    - apply HU_is_full.
  Qed.

End LiftedUnit.

Section LiftedTensorUnit.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I)
          (ru : right_unitor TC I)
          (α : associator TC)
          (tri : triangle_eq TC I lu ru α)
          (pent : pentagon_eq TC α).

  Context (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE)
          (ruE : right_unitor TE IE)
          (αE : associator TE)
          (triE : triangle_eq TE IE luE ruE αE)
          (pentE : pentagon_eq TE αE).

  Let TD := TransportedTensor Duniv H_eso H_ff TC.
  Let ID := H I.

  Definition precomp_tensorunit_disp_functor
    :  disp_functor
         (pre_composition_functor C D E H)
         (MonoidalFunctorCategory.functor_tensorunit_disp_cat TD TE ID IE)
         (MonoidalFunctorCategory.functor_tensorunit_disp_cat TC TE I IE)
    := disp_prod_functor_over_fixed_base
         (HT Duniv H_eso H_ff TC TE) (HU I IE).

  Definition precomp_tensorunit_functor
    : functor (MonoidalFunctorCategory.functor_tensorunit_cat TD TE ID IE)
              (MonoidalFunctorCategory.functor_tensorunit_cat TC TE I IE).
  Proof.
    use total_functor.
    { exact (pre_composition_functor _ _ E H). }
    exact precomp_tensorunit_disp_functor.
  Defined.

  Lemma is_disp_univalent_functor_tensorunit_disp_cat
    : Univalence.is_univalent_disp (MonoidalFunctorCategory.functor_tensorunit_disp_cat TD TE ID IE).
  Proof.
  Admitted.

  Definition precomp_tensor_cat_is_weak_equivalence
    : adj_equivalence_of_cats precomp_tensorunit_functor.
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      { apply is_univalent_functor_category, Euniv. }
      exact is_disp_univalent_functor_tensorunit_disp_cat.
    - (* Need lemmas : fully_faithful (total_functor (_ × _)). *)
      admit.
    - (* Need lemma : essentially_surjective (total_functor (_ × _)). *)
      admit.
  Admitted.

End LiftedTensorUnit.
