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
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.CategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.DisplayedCategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.

Local Open Scope cat.

Section RezkAssociator.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C)
          (α : associator TC).


  Let TD := TransportedTensor Duniv H_eso H_ff TC.

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Local Notation HHH := (pair_functor HH H).
  Let HHH_eso := pair_functor_eso HH H HH_eso H_eso.
  Let HHH_ff := pair_functor_ff HH H HH_ff H_ff.

  Local Notation HHH' := (pair_functor H HH).
  Let HHH'_eso := pair_functor_eso _ _ H_eso HH_eso.
  Let HHH'_ff := pair_functor_ff _ _ H_ff HH_ff.

  Lemma TransportedAssocLeft
    :  nat_z_iso (HHH ∙ assoc_left TD) (assoc_left TC ∙ H).
  Proof.
    use nat_z_iso_comp.
    2: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      exact (nat_z_iso_inv (lift_functor_along_comm_prod (_,,Duniv) H H_eso H_ff TC)).
    }
    apply (lift_functor_along_comm (_,,Duniv) _ HHH_eso HHH_ff).
  Defined.

  Lemma unassoc_commutes
    : nat_z_iso (HHH ∙ (precategory_binproduct_unassoc D D D))
                ((precategory_binproduct_unassoc C C C) ∙ (pair_functor H HH)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; use catbinprodmor ; apply identity.
      + intro ; intros.
        use total2_paths_f.
        * exact (id_right _ @ ! id_left _).
        * abstract (rewrite transportf_const ; exact (id_right _ @ ! id_left _)).
    - intro.
      use tpair.
      * use catbinprodmor ; apply identity.
      * abstract (split ; (use total2_paths_f ; [ apply id_right | rewrite transportf_const ; apply id_right ])).
  Defined.

  Lemma TransportedAssocRight
    : nat_z_iso (HHH ∙ assoc_right TD) (assoc_right TC ∙ H).
  Proof.
    (* This commuting diagram can be split in 3 commuting diagrams stacked together *)
    (* Step 1: The top commuting diagram is unassoc_commutes *)
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: exact unassoc_commutes.
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.pre_whisker_nat_z_iso.

    (* Step 2: The lowest commuting diagram is the tensor preserving commuting one *)
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply TransportedTensorComm.
    }

    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.post_whisker_nat_z_iso.

    (* Step 3: The middle commuting square is the tensor preserving commuting one
               but tensored with the identity functor on the left *)

    use CategoriesLemmas.product_of_commuting_squares.
    { apply (make_nat_z_iso _ _ _ (is_nat_z_iso_nat_trans_id H)). }
    apply TransportedTensorComm.
  Defined.

  Definition TransportedAssociator
    : associator TD.
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) HHH HHH_eso HHH_ff).
    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (TransportedAssocRight)).
    use nat_z_iso_comp.
    2: exact TransportedAssocLeft.
    exact (CategoriesLemmas.post_whisker_nat_z_iso α H).
  Defined.

  Let αD := TransportedAssociator.

  Context (I : C).

  Definition H_pα
    : (functor_ass_disp_cat (IC := I) α αD)
        (H ,, (pr1 (TransportedTensorComm Duniv H_eso H_ff TC) ,, identity _)).
  Proof.
    intros x y z.


  Admitted.

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E)
          (αE : associator TE).

  Context (IE : E).

  Definition precompA
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_ass_disp_cat αD αE)
                   (functor_ass_disp_cat α αE).
  Proof.
    use tpair.
    - use tpair.
      2: intro ; intros ; exact tt.
      intros G GG x y z.

      set (t := GG (H x) (H y) (H z)).
    (*refine (_ @ t @ _).*)
      admit.

    - split ; intro ; intros ; apply isapropunit.
  (*Qed.*) Admitted.

  Lemma precompA_ff
    : disp_functor_ff precompA.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - do 3 intro.
      assert (p : isaset ( hfiber (λ ff : unit, (# precompA)%mor_disp ff) y0)).
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

  Lemma precompA_eso
    : disp_functor_disp_ess_split_surj precompA.
  Proof.
    intros G GG.
    use tpair.
    - intros d1 d2 d3.
      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d1). }
      { apply homset_property. }
      2: exact (H_eso d1).
      intro cd1.
      induction (isotoid _ Duniv (pr2 cd1)).

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d2). }
      { apply homset_property. }
      2: exact (H_eso d2).
      intro cd2.
      induction (isotoid _ Duniv (pr2 cd2)).

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d3). }
      { apply homset_property. }
      2: exact (H_eso d3).
      intro cd3.
      induction (isotoid _ Duniv (pr2 cd3)).

      set (t := GG (pr1 cd1) (pr1 cd2) (pr1 cd3)).
      (* refine (_ @ t @ _). *)

      admit.
    - exists tt.
      exists tt.
      split ; apply isapropunit.
  Admitted.

  Definition precomp_associator_is_ff
    : fully_faithful (total_functor precompA).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompA_ff.
  Qed.

  Definition precomp_associator_is_eso
    : essentially_surjective (total_functor precompA).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompA_eso.
  Qed.

  Definition precomp_associator_adj_equiv
    : adj_equivalence_of_cats (total_functor precompA).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply functor_ass_disp_cat_is_univalent.
    - exact precomp_associator_is_ff.
    - exact precomp_associator_is_eso.
  Defined.

End RezkAssociator.
