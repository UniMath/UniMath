(* In LiftedTensor.v and LiftedTensor.v, we have shown that given a category C equipped with a binary operation T and an object I (called the tensor and unit resp.),
then, this structures 'transport' to a weakly equivalent univalent category D, by a weak equivalence H:C->D, making this univalent category D with a tensor and unit,
the free univalent category equipped with a tensor and a unit.
In this file, we show that if we equip (C,T) with an associator, then
1: the associator also transports to D.
2: H preserves the associator as a monoidal functor preserves the associator.
3: H makes D the free univalent category equipped with tensor, unit and the associator.
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

  Definition DDDuniv : is_univalent ((D ⊠ D) ⊠ D).
  Proof.
    Search (is_univalent (_ ⊠ _)).
    apply is_unvialent_category_binproduct.
    2: exact Duniv.
    apply is_unvialent_category_binproduct.
    exact Duniv.
    exact Duniv.
  Qed.

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
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply ((TransportedTensorComm Duniv H_eso H_ff _)).
    }
    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use (CategoriesLemmas.post_whisker_nat_z_iso _ TD).

    use nat_z_iso_comp.
    3: apply PrecompEquivalence.nat_z_iso_pair.
    use nat_z_iso_comp.
    2: apply pair_functor_composite.

    use pair_nat_z_iso.
    - apply TransportedTensorComm.
    - apply CategoriesLemmas.functor_commutes_with_id.



    (* use nat_z_iso_comp.
    3: apply (lift_functor_along_comm (_,,Duniv) _ HHH_eso HHH_ff).
    use CategoriesLemmas.pre_whisker_nat_z_iso.
    exact (nat_z_iso_inv (lift_functor_along_comm_prod (_,,Duniv) H H_eso H_ff TC)). *)
  Defined.

  Lemma TransportedAssocLeftOnOb (x y z : C)
    : TransportedAssocLeft ((x,y),z)
      = # TD (TransportedTensorComm Duniv H_eso H_ff TC (x,y) #, identity (H z))
          · (TransportedTensorComm Duniv H_eso H_ff TC (TC (x,y) , z)).
  Proof.
    cbn.
    rewrite ! id_left.
    rewrite ! id_right.
    apply idpath.
  Qed.


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

  Lemma TransportedAssocRightOnOb (x y z : C)
    : TransportedAssocRight ((x,y),z)
      =  # TD (# H (id x) #, TransportedTensorComm Duniv H_eso H_ff TC (y, z))
           · TransportedTensorComm Duniv H_eso H_ff TC (x, TC (y,z)).
  Proof.
    cbn.
    rewrite ! id_left.
    rewrite ! id_right.
    rewrite ! functor_id.
    rewrite ! assoc.
    apply maponpaths_2.
    fold (TransportedTensor Duniv H_eso H_ff).
    etrans. {
      apply (! functor_comp TD _ _).
    }
    apply maponpaths.
    rewrite <- binprod_comp.
    rewrite id_right.
    apply maponpaths.
    etrans. {
      apply maponpaths_2.
      apply (functor_id TD).
    }
    apply id_left.
  Qed.

  Lemma TransportedAssocRightInvOnOb (x y z : C)
    : nat_z_iso_inv TransportedAssocRight ((x,y),z)
      = nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)
          (x, TC (y,z))
          · # TD (# H (id x) #, (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC) (y, z))).
  Proof.
  Admitted.


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

  Definition TransportedAssociatorEq
    : pre_whisker HHH TransportedAssociator
      = nat_z_iso_comp
          (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
          (nat_z_iso_inv (TransportedAssocRight)).
  Proof.
    set (t := lift_nat_trans_along_comm (_,,Duniv) _ HHH_eso HHH_ff
          (nat_z_iso_comp TransportedAssocLeft
                          (nat_z_iso_comp
                             (CategoriesLemmas.post_whisker_nat_z_iso α H)
                             (nat_z_iso_inv TransportedAssocRight)
                          )
        )).
    refine (_ @ t @ _).
    clear t.
    - apply maponpaths.
      apply (maponpaths (lift_nat_trans_along (D,, Duniv) HHH HHH_eso HHH_ff)).
      apply nat_trans_comp_assoc'.
      apply homset_property.
    - exact (nat_trans_comp_assoc (homset_property _)
                                     _ _ _ _
              (pr1 TransportedAssocLeft)
              (CategoriesLemmas.post_whisker_nat_z_iso α H)
              (nat_z_iso_inv TransportedAssocRight)).
  Qed.

  Definition TransportedAssociatorOnOb
    : ∏ x : (C ⊠ C) ⊠ C,
        αD (HHH x) = TransportedAssocLeft x · #H (α x) · nat_z_iso_inv TransportedAssocRight x.
  Proof.
    exact (λ x, toforallpaths _ _ _ (base_paths _ _ TransportedAssociatorEq) x).
  Qed.

  Context (I : C).

  Definition H_pα
    : (functor_ass_disp_cat (IC := I) α αD)
        (H ,, (pr1 (TransportedTensorComm Duniv H_eso H_ff TC) ,, identity _)).
  Proof.
    intros x y z.

    unfold αD.
    unfold TransportedAssociator.

    etrans. {
      apply maponpaths_2.
      exact (! TransportedAssocLeftOnOb x y z).
    }

    assert (p1' : (# TD (id pr1 H x #, (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (y, z))
                     · (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (x, TC (y, z))) = TransportedAssocRight ((x,y),z)).
    {
      rewrite <- (functor_id H).
      exact (! TransportedAssocRightOnOb x y z).
    }

    assert (p1 : (nat_z_iso_inv TransportedAssocRight) ((x,y),z)
                 · (# TD (id pr1 H x #, (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (y, z))
             · (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (x, TC (y, z))) = identity _).
    {
      use (z_iso_inv_on_right _ _ _ (_,,pr2 TransportedAssocRight ((x,y),z))).
      rewrite id_right.
      exact p1'.
    }

    set (cc := lift_nat_z_iso_along (D,, Duniv) HHH HHH_eso HHH_ff
               (nat_z_iso_comp
       (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight))).

    set (cc1 := (CategoriesLemmas.post_whisker_nat_z_iso α H)).
    set (cc0 := TransportedAssocLeft).
    set (cc2 := (nat_z_iso_inv TransportedAssocRight)).
    set (dd := nat_z_iso_comp cc0 (nat_z_iso_comp cc1 cc2)).
    assert (p2' : dd = CategoriesLemmas.pre_whisker_nat_z_iso HHH cc).
    {
      use total2_paths_f.
      2: { apply isaprop_is_nat_z_iso. }

      etrans. {
        apply (! lift_nat_trans_along_comm (_,,Duniv) _ HHH_eso HHH_ff _).
      }

      apply (maponpaths (pre_whisker HHH)).
      apply (maponpaths (lift_nat_trans_along (D,, Duniv) HHH HHH_eso HHH_ff)).
      apply nat_trans_comp_assoc.
      apply homset_property.
    }

    set (cc' := lift_nat_z_iso_along (D,, Duniv) HHH HHH_eso HHH_ff
    (nat_z_iso_comp
       (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight)) (HHH ((x,y),z))).

    set (cc1' := (CategoriesLemmas.post_whisker_nat_z_iso α H) ((x,y),z)).
    set (cc0' := TransportedAssocLeft ((x,y),z)).
    set (cc2' := (nat_z_iso_inv TransportedAssocRight) ((x,y),z)).
    assert (p2 : cc0' · cc1' · cc2' = cc').
    {
      set (q := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ p2')) ((x,y),z)).
      refine (_ @ q).
      apply assoc'.
    }

    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact p2.
    }
    clear p2.
    unfold cc0', cc1', cc2'.
    clear cc0' cc1' cc2'.
    rewrite ! assoc'.
    apply maponpaths.
    etrans.
    2: {
      apply maponpaths.
      exact (! p1).
    }
    apply (! id_right _).
  Qed.

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
      exact (λ G GG, functor_ass_composition H_pα GG).
    - split ; intro ; intros ; apply isapropunit.
  Qed.

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
      intros [c1 i1].
      induction (isotoid _ Duniv i1).
      clear i1.

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d2). }
      { apply homset_property. }
      2: exact (H_eso d2).
      intros [c2 i2].
      induction (isotoid _ Duniv i2).
      clear i2.

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d3). }
      { apply homset_property. }
      2: exact (H_eso d3).
      intros [c3 i3].
      induction (isotoid _ Duniv i3).
      clear i3.

      etrans. {
        do 2 apply maponpaths.
        exact (TransportedAssociatorOnOb ((c1,c2), c3)).
      }

      set (t := GG c1 c2 c3).

      transparent assert (m : (E⟦ pr11 G (H (TC (c1, TC (c2,, c3))))
                                  ,  (pr11 G) (TD (H c1, TD (H c2,, H c3)))⟧)).
      {
        apply #(pr11 G).
        refine (_ · _).
        - apply (TransportedTensorComm Duniv H_eso H_ff).
        - apply (#TD).
          use catbinprodmor.
          + apply identity.
          + apply (TransportedTensorComm Duniv H_eso H_ff).
      }



      set (ptG := pr112 G).
      set (ptH := pr1 (TransportedTensorComm Duniv H_eso H_ff TC)).

      set (pt_GH := (pr112 (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE G))).

      set (tt := cancel_postcomposition _ _ m t :
       # TE (pt_GH (c1, c2) #, id  pr11 G (H c3))
         · pt_GH (TC (c1, c2), c3)
         · # (functor_composite H (pr1 G)) (α ((c1, c2), c3)) · m
       = αE ((pr11 G (H ( c1)), (pr11 G (H (c2)))), (pr11 G (H (c3))))
            · # TE (id pr11 G (H (c1)) #, pt_GH (c2, c3)) · pt_GH (c1, TC (c2,c3)) · m).

      refine (_ @ tt @ _) ; unfold m.
      + rewrite ! assoc'.
        rewrite TransportedAssocLeftOnOb.
        rewrite TransportedAssocRightInvOnOb.

        rewrite (! id_right (id (pr11 G) (H c3))).
        etrans.
        2: {
          apply maponpaths_2.
          assert (pp : pt_GH (c1, c2)
                       = ptG (H c1, H c2) · #(pr11 G) (ptH (c1,c2))).
          {
            apply idpath.
          }
          rewrite pp, binprod_comp.
          apply (! functor_comp TE _ _).
        }
        etrans.
        2: {


          set (q := pr212 G (TD (H c1, H c2), H c3)).
          simpl in q.

        etrans


        apply maponpaths.


        rewrite (functor_comp (pr1 G)).
        rewrite assoc.
        etrans. {
          apply maponpaths_2.

          simpl.
          Check pr212 G _ _ (TransportedTensorComm Duniv H_eso H_ff TC (c1, c2) #, id H c3).







        admit.
      + rewrite ! assoc'.
        apply maponpaths.
        rewrite assoc.

        admit.*)
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
