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
Require Import UniMath.CategoryTheory.DisplayedCats.TotalCategoryFacts.

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
    apply is_univalent_category_binproduct.
    2: exact Duniv.
    apply is_univalent_category_binproduct.
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
    3: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply pre_whisker_nat_z_iso.
      apply ((TransportedTensorComm Duniv H_eso H_ff _)).
    }
    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use (post_whisker_nat_z_iso _ TD).

    use nat_z_iso_comp.
    3: apply PrecompEquivalence.nat_z_iso_pair.
    use nat_z_iso_comp.
    2: apply pair_functor_composite.

    use pair_nat_z_iso.
    - apply TransportedTensorComm.
    - apply functor_commutes_with_id.
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
    2: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: exact unassoc_commutes.
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    3: apply nat_z_iso_functor_comp_assoc.
    apply pre_whisker_nat_z_iso.

    (* Step 2: The lowest commuting diagram is the tensor preserving commuting one *)
    use nat_z_iso_comp.
    3: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply pre_whisker_nat_z_iso.
      apply TransportedTensorComm.
    }

    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: apply nat_z_iso_functor_comp_assoc.
    apply post_whisker_nat_z_iso.

    (* Step 3: The middle commuting square is the tensor preserving commuting one
               but tensored with the identity functor on the left *)

    use product_of_commuting_squares.
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
    use (z_iso_inv_to_left _ _ _
                           (_,,pr2 (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) (x, TC (y,z)))).
    use (z_iso_inv_to_right _ _ _ _
                            (_,, pr2 (nat_z_iso_inv TransportedAssocRight) ((x, y), z))).
    set (t := TransportedAssocRightOnOb x y z).
    etrans.
    2: {
      apply maponpaths.
      apply (! t).
    }
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      apply (functor_comp TD).
    }
    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      apply binprod_comp.
    }
    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      rewrite (functor_id H).
      rewrite id_right.
      apply maponpaths.
      apply (! pr22 ((pr2 (TransportedTensorComm Duniv H_eso H_ff TC)) (y, z))).
    }
    etrans.
    2: {
      apply maponpaths_2.
      rewrite binprod_id.
      apply (! functor_id TD _).
    }
    apply (! id_left _).
  Qed.

  Definition TransportedAssociator
    : associator TD.
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) HHH HHH_eso HHH_ff).
    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (TransportedAssocRight)).
    use nat_z_iso_comp.
    2: exact TransportedAssocLeft.
    exact (post_whisker_nat_z_iso α H).
  Defined.

  Let αD := TransportedAssociator.

  Definition TransportedAssociatorEq
    : pre_whisker HHH TransportedAssociator
      = nat_z_iso_comp
          (nat_z_iso_comp TransportedAssocLeft (post_whisker_nat_z_iso α H))
          (nat_z_iso_inv (TransportedAssocRight)).
  Proof.
    set (t := lift_nat_trans_along_comm (_,,Duniv) _ HHH_eso HHH_ff
          (nat_z_iso_comp TransportedAssocLeft
                          (nat_z_iso_comp
                             (post_whisker_nat_z_iso α H)
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
              (post_whisker_nat_z_iso α H)
              (nat_z_iso_inv TransportedAssocRight)).
  Qed.

  Definition TransportedAssociatorOnOb
    : ∏ x : (C ⊠ C) ⊠ C,
        αD (HHH x) = TransportedAssocLeft x · #H (α x) · nat_z_iso_inv TransportedAssocRight x.
  Proof.
    exact (λ x, toforallpaths _ _ _ (base_paths _ _ TransportedAssociatorEq) x).
  Qed.

  Definition assoc_left_tensor_l
    : ∏ x1 x2 x3 x4 : C,
        D⟦assoc_left TD ((TD (H x1, H x2), H x3), H x4)
           , H (assoc_left TC ((TC (x1, x2), x3), x4))⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    3: apply TransportedAssocLeft.
    use (# TD).
    use catbinprodmor.
    2: apply identity.
    use (# TD).
    use catbinprodmor.
    1: exact ((TransportedTensorComm Duniv H_eso H_ff TC) (x1,x2)).
    apply identity.
  Defined.

  Definition assoc_left_tensor_m
    : ∏ x1 x2 x3 x4 : C,
        D ⟦assoc_left TD ((H x1, TD (H x2, H x3)), H x4)
            , H (assoc_left TC ((x1, TC (x2, x3)), x4))⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    3: apply TransportedAssocLeft.
    use (# TD).
    use catbinprodmor.
    2: apply identity.
    apply (#TD).
    use catbinprodmor.
    1: apply identity.
    apply ((TransportedTensorComm Duniv H_eso H_ff TC) (x2,x3)).
  Defined.

  Definition assoc_left_tensor_r
    : ∏ x1 x2 x3 x4 : C,
        D ⟦assoc_left TD ((H x1, H x2), TD (H x3, H x4))
            , H (assoc_left TC ((x1, x2), TC (x3, x4))) ⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    3: apply TransportedAssocLeft.
    use (# TD).
    use catbinprodmor.
    - apply identity.
    - exact ((TransportedTensorComm Duniv H_eso H_ff TC) (x3,x4)).
  Defined.

  Definition assoc_right_tensor_l
    : ∏ x1 x2 x3 x4 : C,
        D⟦ H (assoc_right TC ((TC (x1, x2), x3), x4))
           , assoc_right TD ((TD (H x1, H x2), H x3), H x4)⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    2: apply TransportedAssocRight.
    use (# TD).
    use catbinprodmor.
    2: apply identity.
    exact (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC) (x1,x2)).
  Defined.

  Definition assoc_right_tensor_m
    : ∏ x1 x2 x3 x4 : C,
        D⟦H (assoc_right TC ((x1, TC (x2, x3)), x4))
           , assoc_right TD ((H x1, TD (H x2, H x3)), H x4)⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    3: {
      use (# (assoc_right TD)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: {
          use catbinprodmor.
          3: apply identity.
          2: apply (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC) (x2,x3)).
        }
      }
    }
    exact (nat_z_iso_inv TransportedAssocRight ((x1,TC (x2,x3)),x4)).
  Defined.

  Definition assoc_right_tensor_r
    : ∏ x1 x2 x3 x4 : C,
        D⟦H (assoc_right TC ((x1, x2), TC (x3, x4)))
           , assoc_right TD ((H x1, H x2), TD (H x3, H x4)) ⟧.
  Proof.
    do 4 intro.
    use (_ · _).
    2: apply (nat_z_iso_inv TransportedAssocRight).
    use (# TD).
    use catbinprodmor.
    - apply identity.
    - use (# TD).
      use catbinprodmor.
      + apply identity.
      + apply TransportedTensorComm.
  Defined.

  Lemma TransportedAssociator_tensor_l_on_ob
    : ∏ x1 x2 x3 x4 : C,
        αD ((TD (H x1, H x2), H x3), H x4)
        = assoc_left_tensor_l x1 x2 x3 x4 · #H (α ((TC (x1,x2) , x3),x4)) · assoc_right_tensor_l x1 x2 x3 x4.
  Proof.
    do 4 intro.
    unfold assoc_left_tensor_l.
    unfold assoc_right_tensor_l.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (TransportedAssociatorOnOb ((TC (x1,x2),x3),x4)).
    }

    etrans.
    2: {
      apply maponpaths_2.
      exact (! pr21 αD _ _   ((TransportedTensorComm Duniv H_eso H_ff TC (x1, x2)
                                                     #, id H (pr21 ((TC (x1, x2), x3), x4))) #, id functor_identity D (pr2 (HHH ((TC (x1, x2), x3), x4))))).
    }


    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      etrans. 2: apply (functor_comp TD).
      apply maponpaths.
      etrans. 2: apply binprod_comp.
      etrans.
      2: {
        apply maponpaths.
        etrans.
        2: apply maponpaths_2, maponpaths, (! binprod_id _ _).
        rewrite functor_id.
        apply (! id_left _).
      }

      apply maponpaths_2.
      exact (! pr12 (pr2 (TransportedTensorComm Duniv H_eso H_ff TC) (x1,x2))).
    }
    etrans.
    2: {
      apply maponpaths.
      rewrite binprod_id.
      apply (! functor_id TD _).
    }
    apply (! id_right _).
  Qed.


  Lemma TransportedAssociator_tensor_m_on_ob
    : ∏ x1 x2 x3 x4 : C,
        αD ((H x1, TD (H x2, H x3)), H x4)
        = assoc_left_tensor_m x1 x2 x3 x4 · #H (α ((x1, TC (x2,x3)),x4)) · assoc_right_tensor_m x1 x2 x3 x4.
  Proof.
    do 4 intro.
    unfold assoc_left_tensor_m.
    unfold assoc_right_tensor_m.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (TransportedAssociatorOnOb ((x1, TC (x2,x3)),x4)).
    }

    etrans.
    2: {
      apply maponpaths_2.

      exact (! pr21 αD _ _  ((id H (pr11 ((x1, TC (x2, x3)), x4)) #, TransportedTensorComm Duniv H_eso H_ff TC (x2, x3))
    #, id functor_identity D (pr2 (HHH ((x1, TC (x2, x3)), x4))))).
    }


    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      etrans. 2: apply (functor_comp TD).
      etrans. 2: apply maponpaths, binprod_comp.

      (* simpl. *)
      rewrite id_left.
      do 2 apply maponpaths.
      etrans. 2: apply (functor_comp TD).
      apply maponpaths.
      etrans. 2: apply binprod_comp.
      apply maponpaths_2.
      exact (! pr12 (pr2 (TransportedTensorComm Duniv H_eso H_ff TC) (x2,x3))).
    }
    etrans.
    2: {
      apply maponpaths.
      rewrite id_right.
      rewrite (functor_id TD).
      simpl.
      rewrite binprod_id.
      apply (! functor_id TD _).
    }
    apply (! id_right _).
  Qed.

  Lemma TransportedAssociator_tensor_r_on_ob
    : ∏ x1 x2 x3 x4 : C,
        αD ((H x1, H x2), TD (H x3, H x4))
        = assoc_left_tensor_r x1 x2 x3 x4 · #H (α ((x1,x2) , TC (x3,x4))) · assoc_right_tensor_r x1 x2 x3 x4.
  Proof.
    do 4 intro.
    unfold assoc_left_tensor_r.
    unfold assoc_right_tensor_r.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (TransportedAssociatorOnOb (((x1,x2), TC (x3,x4)))).
    }

    etrans.
    2: {
      apply maponpaths_2.
      rewrite <- (functor_id TD).
      exact (! pr21 αD _ _  (id  (pr1 (HHH ((x1, x2), TC (x3, x4)))) #, TransportedTensorComm Duniv H_eso H_ff TC (x3, x4))).
    }


    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      etrans. 2: apply (functor_comp TD).
      etrans. 2: apply maponpaths, binprod_comp.

      (* simpl. *)
      rewrite id_left.
      do 2 apply maponpaths.
      etrans. 2: apply (functor_comp TD).
      apply maponpaths.
      etrans. 2: apply binprod_comp.
      apply maponpaths.
      exact (! pr12 (pr2 (TransportedTensorComm Duniv H_eso H_ff TC) (x3,x4))).
    }
    etrans.
    2: {
      apply maponpaths.
      rewrite id_right.
      rewrite (functor_id TD).
      simpl.
      rewrite binprod_id.
      apply (! functor_id TD _).
    }
    apply (! id_right _).
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
       (nat_z_iso_comp TransportedAssocLeft (post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight))).

    set (cc1 := (post_whisker_nat_z_iso α H)).
    set (cc0 := TransportedAssocLeft).
    set (cc2 := (nat_z_iso_inv TransportedAssocRight)).
    set (dd := nat_z_iso_comp cc0 (nat_z_iso_comp cc1 cc2)).
    assert (p2' : dd = pre_whisker_nat_z_iso HHH cc).
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
       (nat_z_iso_comp TransportedAssocLeft (post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight)) (HHH ((x,y),z))).

    set (cc1' := (post_whisker_nat_z_iso α H) ((x,y),z)).
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

  Lemma lift_preserves_associator
        {G : functor_tensorunit_cat (TransportedTensor Duniv H_eso H_ff TC) TE (H I) IE}
        ( GG : functor_ass_disp_cat α αE (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE G))
    : functor_ass_disp_cat αD αE G.
  Proof.
    intros d1 d2 d3.
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

    rewrite TransportedAssocLeftOnOb.
    rewrite TransportedAssocRightInvOnOb.


    set (t := GG c1 c2 c3).
    set (ptG := pr112 G).
    set (ptH := pr1 (TransportedTensorComm Duniv H_eso H_ff TC)).
    set (pt_GH := (pr112 (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE G))).
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
    set (tt := cancel_postcomposition _ _ m t :
           # TE (pt_GH (c1, c2) #, id  pr11 G (H c3))
         · pt_GH (TC (c1, c2), c3)
         · # (functor_composite H (pr1 G)) (α ((c1, c2), c3)) · m
           = αE ((pr11 G (H ( c1)), (pr11 G (H (c2)))), (pr11 G (H (c3))))
                · # TE (id pr11 G (H (c1)) #, pt_GH (c2, c3)) · pt_GH (c1, TC (c2,c3)) · m).

      set (ptF := (TransportedTensorComm Duniv H_eso H_ff TC)).
      assert (pp : pt_GH (c1, c2)
                   = ptG (H c1, H c2) · #(pr11 G) (ptH (c1,c2))).
      {
        apply idpath.
      }

      refine (_ @ tt @ _) ; unfold m ; clear tt.
    + rewrite pp.
      rewrite ! (functor_comp (pr1 G)).
      assert (qq :  pt_GH (TC (c1, c2), c3)
                    = ptG (H (TC (c1,c2)), H c3) · #(pr11 G) (ptH (TC (c1,c2),c3))).
      {
        apply idpath.
      }
      rewrite qq.
      fold ptF.
      rewrite <- (id_right (id (pr11 G) (H c3))).
      rewrite binprod_comp.
      rewrite (functor_comp TE _ _).

      rewrite ! assoc'.
      apply maponpaths.
      rewrite ! assoc.
      rewrite (functor_id H).
      do 4 apply maponpaths_2.
      rewrite <- (functor_id (pr1 G)).
      exact (! pr212 G _ _ (ptF (c1, c2) #, id H c3)).
    + rewrite ! assoc'.
      apply maponpaths.
      assert (qq' :  (pt_GH (c1, TC (c2, c3))
                      = ptG (H c1, H (TC (c2,c3))) · #(pr11 G) (ptH (c1, TC (c2,c3))))).
      {
        apply idpath.
      }
      rewrite qq'.
      fold ptF.
      assert (qq'' :  pt_GH (c2, c3)
                      = ptG (H c2, H c3) · #(pr11 G) (ptH (c2,c3))).
      { apply idpath. }
      rewrite qq''.
      rewrite (! id_right (id (pr11 G) (H c1))).
      rewrite binprod_comp.
      rewrite (functor_comp TE _ _).
      rewrite ! assoc'.
      apply maponpaths.

      etrans. {
        do 2 apply maponpaths.
        rewrite (functor_comp (pr1 G)).
        rewrite assoc.
        apply maponpaths_2.
        rewrite <- (functor_comp (pr1 G)  (ptH (c1, TC (c2, c3)))).
        etrans. {
          apply maponpaths.
          apply (pr12 (pr2 ptF (c1, TC (c2,c3)))).
        }
        apply (functor_id (pr1 G)).
        }
        rewrite id_left.
      etrans. {
        apply maponpaths.
        apply (! pr212 G _ _ ((id H c1 #, pr1 (pr2 ptF (c2,, c3))))).
      }
      unfold functor_tensor_map_dom.
      unfold functor_composite.
      simpl.
      rewrite <- (functor_id (pr1 G)).
      rewrite assoc.
      rewrite <- (functor_comp TE).
      rewrite <- binprod_comp.
      rewrite (functor_id (pr1 G)).
      rewrite id_right.
      rewrite <- (functor_id (pr1 G)).
      rewrite <- (functor_comp (pr1 G)).

      etrans. {
        apply maponpaths_2.
        do 3 apply maponpaths.
        apply (pr12 (pr2 ptF (c2,c3))).
      }
      etrans. {
        apply maponpaths_2.
        do 2 rewrite (functor_id (pr1 G)).
        apply (functor_id TE).
      }
      apply id_left.
  Qed.

  Lemma precompA_eso
    : disp_functor_disp_ess_split_surj precompA.
  Proof.
    intros G GG.
    exists (lift_preserves_associator GG).
    refine (tt,,tt,,_).
    split ; apply isapropunit.
  Qed.

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
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_total_category.
      + apply is_univalent_functor_category.
        exact Euniv.
      + apply functor_tensorunit_disp_cat_is_univalent.
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
