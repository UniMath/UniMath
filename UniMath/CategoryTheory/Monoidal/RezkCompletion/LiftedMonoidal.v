(*
In this file we conclude that any monoidal category has a "Monoidal Rezk-completion".  More precisely:
Let (C,T,I,lu,ru,α) be a monoidal category.
Then, there is a univalent monoidal category (D,TD,ID,luD,ruD,αD) which is the free univalent monoidal category/replacement of (C,T,I,lu,ru,α), i.e.
There is a strong monoidal functor H: (C,T,I,lu,ru,α) → (D,TD,ID,luD,ruD,αD)
such that for any univalent monoidal category (E,TE,IE,luE,ruE,αD), there is an (adjoint) equivalence of categories between (lax-)monoidal functor categories:
H · (-) : LaxMon(D,E) → LaxMon(C,E).

In order to show this, we assume that the underlying category, i.e. C, has a Rezk-completion.
However, the specific constructions of the Rezk-completion of (ordinary) categories has some issues:
1. The copresheaf construction increases the universe level
2. The inductive definition, as the name suggests, uses inductive types, which is not directly allowed in UniMath.
In order to solve this issue, we are given a univalent category D and a weak equivalence H:C->D

Remark:
That H might be choosen to be a weak equivalence is motivated by the copresheaf construction.
We explicitely use that H is a weak equivalence (as seen in LiftedTensor.v) because
in order to show the adjoint equivalence of the corresponding monoidal functor categories,
we use that the functor categories are univalent and hence it suffices to show
that precomposition with H is a weak equivalence which reduces to H being an equivalence.

Notice that by the universal property of the Rezk-completion,
both D and H are unique (at first sight up to isomorphism, but even up to equality since the bicategory of univalent categories is univalent.

Then, using the universal property of D as the Rezk-completion of C (i.e. the free univalent category of C),
that D can be equipped with a monoidal structure such that H becomes a strong monoidal functor.
By the universal property of (D,H) we have an (adjoint) equivalence of categories H · (-) : [D,E] → [C,E] (for any univalent category E).
We show that this equivalence of categories lifts to (lax-)monoidal functors.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalCategoryFacts.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.

Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalCategoriesTensored.
Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalFunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedUnitors.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedAssociator.

Local Open Scope cat.

Section RezkMonoidal.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I)
          (ru : right_unitor TC I)
          (α : associator TC)
          (tri : triangle_eq TC I lu ru α)
          (pent : pentagon_eq TC α).

  Let TD := TransportedTensor Duniv H_eso H_ff TC.
  Let ID := (H I).
  Let luD := TransportedLeftUnitor Duniv H_eso H_ff _ _ lu.
  Let ruD := TransportedRightUnitor Duniv H_eso H_ff _ _ ru.
  Let αD := TransportedAssociator Duniv H_eso H_ff _ α.

  Lemma TransportedTriangleEq
    :  triangle_eq TD (H I) luD ruD αD.
  Proof.
    intros y1 y2.
    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y1). }
    { apply homset_property. }
    2: exact (H_eso y1).
    intros [x1 xx1].
    induction (isotoid _ Duniv xx1).
    clear xx1.

    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y2). }
    { apply homset_property. }
    2: exact (H_eso y2).
    intros [x2 xx2].
    induction (isotoid _ Duniv xx2).
    clear xx2.

    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      exact (TransportedRightUnitorOnOb Duniv H_eso H_ff TC I ru x1).
    }

    etrans.
    2: {
      do 3 apply maponpaths.
      exact (! TransportedLeftUnitorOnOb Duniv H_eso H_ff TC I lu x2).
    }

    etrans.
    2: {
      apply maponpaths_2.
      exact (! TransportedAssociatorOnOb Duniv H_eso H_ff TC α ((x1,I),x2)).
    }

    rewrite (! id_right (id H x2)).
    rewrite (! id_right (id H x1)).

    do 2 rewrite binprod_comp.
    rewrite (functor_comp TD).
    rewrite <- functor_id.

    assert (p0 : #TD (#H (ru x1) #, #H (id x2))
                 =
                   (pr11 (TransportedTensorComm Duniv H_eso H_ff TC))
                     (I_posttensor TC I x1, x2)
                     · # (TC ∙ H) (ru x1 #, id x2)
                     · (pr1 (pr2 (TransportedTensorComm Duniv H_eso H_ff TC) (x1, x2)))).
    {
      apply pathsinv0.
      use (z_iso_inv_to_right _ _ _ _ (_,,(pr2 (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) (x1, x2)))).
      exact (! pr21 (TransportedTensorComm Duniv H_eso H_ff TC) _ _ (ru x1 #, id x2)).
    }

    etrans. {
      apply maponpaths.
      exact p0.
    }
    clear p0.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      exact (maponpaths #H (tri x1 x2)).
    }
    rewrite (functor_comp H).

    assert (p0 : # TD (LiftPreservesPostTensor Duniv H_eso H_ff TC I x1 #, # H (id x2))
               · ((pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (I_posttensor TC I x1, x2))
             =  TransportedAssocLeft Duniv H_eso H_ff TC ((x1, I), x2)).
    {
      symmetry.
      refine (TransportedAssocLeftOnOb Duniv H_eso H_ff TC x1 I x2 @ _).
      apply maponpaths_2.
      unfold LiftPreservesPostTensor.
      rewrite functor_id.
      apply maponpaths.
      apply maponpaths_2.
      unfold TransportedTensorComm.
      simpl.
      rewrite ! id_left.
      rewrite ! id_right.
      rewrite (functor_id (lift_functor_along (D,, Duniv) (pair_functor H H) (pair_functor_eso H H H_eso H_eso) (pair_functor_ff H H H_ff H_ff) (TC ∙ H))).
      rewrite functor_id.
      rewrite id_right.
      apply (! id_left _).
    }

    rewrite ! assoc.
    etrans. {
      do 3 apply maponpaths_2.
      exact p0.
    }
    clear p0.
    rewrite ! assoc'.
    do 2 apply maponpaths.

    rewrite functor_comp.

    etrans. {
      apply (pr21 (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC))).
    }
    rewrite assoc.
    rewrite <- functor_id.
    apply maponpaths_2.

    assert (p0 : LiftPreservesPretensor Duniv H_eso H_ff TC I x2 = (TransportedTensorComm Duniv H_eso H_ff TC) (I,x2)). {
      simpl.
      rewrite ! functor_id.
      rewrite ! id_left.
      rewrite ! id_right.
      etrans. {
        apply maponpaths_2.
        apply functor_id.
      }
      apply id_left.
    }
    rewrite p0.
    clear p0.

    set (i := pr2 (nat_z_iso_inv ((TransportedAssocRight Duniv H_eso H_ff TC))) ((x1, I), x2)).
    use (z_iso_inv_to_left _ _ _ (_,,i)).
    set (j := pr2 (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) (x1, I_pretensor TC I x2)).
    use (z_iso_inv_to_right _ _ _ _ (_,,j)).

    exact (TransportedAssocRightOnOb Duniv H_eso H_ff TC x1 I x2).
  Qed.

  Lemma TransportedPentagonEq
    : pentagon_eq TD αD.
  Proof.
    intros y1 y2 y3 y4.

    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y1). }
    { apply homset_property. }
    2: exact (H_eso y1).
    intros [x1 xx1].
    induction (isotoid _ Duniv xx1).
    clear xx1.

    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y2). }
    { apply homset_property. }
    2: exact (H_eso y2).
    intros [x2 xx2].
    induction (isotoid _ Duniv xx2).
    clear xx2.

    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y3). }
    { apply homset_property. }
    2: exact (H_eso y3).
    intros [x3 xx3].
    induction (isotoid _ Duniv xx3).
    clear xx3.

    use factor_through_squash.
    { exact (∑ a : C, z_iso (H a) y4). }
    { apply homset_property. }
    2: exact (H_eso y4).
    intros [x4 xx4].
    induction (isotoid _ Duniv xx4).
    clear xx4.

    set (pentH := maponpaths #H (pent x1 x2 x3 x4)).
    rewrite ! functor_comp in pentH.

    set (tαD := TransportedAssociatorOnOb Duniv H_eso H_ff TC α).

    etrans. {
      apply maponpaths.
      apply TransportedAssociator_tensor_r_on_ob.
    }

    etrans. {
      apply maponpaths_2.
      apply TransportedAssociator_tensor_l_on_ob.
    }

    assert (p0 :
             assoc_right_tensor_l Duniv H_eso H_ff TC x1 x2 x3 x4
                                  · assoc_left_tensor_r Duniv H_eso H_ff TC x1 x2 x3 x4
           = identity _).
    {
      unfold assoc_right_tensor_l, assoc_left_tensor_r.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply (! functor_comp TD _ _).
      }
      etrans. {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
      }
      etrans. {
        apply maponpaths_2.
        do 2 apply maponpaths.
        rewrite id_right.
        rewrite id_left.
        apply idpath.
      }

      etrans. {
        do 2 apply maponpaths_2.
        exact (TransportedAssocRightInvOnOb Duniv H_eso H_ff TC (TC (x1,x2)) x3 x4).
      }

      etrans. {
        apply maponpaths.
        exact (TransportedAssocLeftOnOb Duniv H_eso H_ff TC x1 x2 (TC (x3,x4))).
      }

      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        etrans. apply (! functor_comp TD _ _).
        apply maponpaths.

        etrans. apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
        rewrite functor_id.
        rewrite id_left.
        apply maponpaths.
        apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
      }

      etrans. {
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        etrans. apply (! functor_comp TD _ _).
        apply maponpaths.
        etrans. apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
        rewrite id_right.
        apply maponpaths_2.
        apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
      }
      rewrite binprod_id.
      rewrite functor_id.
      rewrite id_right.
      apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      do 2 rewrite assoc.
      do 2 apply maponpaths_2.
      exact p0.
    }

    clear p0.
    rewrite id_left.
    etrans. {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      exact pentH.
    }

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      exact (! tαD ((x1,x2),x3)).
    }

    etrans.
    2: {
      do 3 apply maponpaths.
      exact (! tαD ((x2,x3),x4)).
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      exact (! TransportedAssociator_tensor_m_on_ob _ _ _ _ _ x1 x2 x3 x4).
    }

    etrans.
    2: {
      apply maponpaths_2.
      rewrite <- (id_right (id H x4)).
      rewrite binprod_comp.
      rewrite (functor_comp TD).
      rewrite <- (id_right (id H x4)).
      rewrite binprod_comp.
      rewrite (functor_comp TD).
      rewrite id_right.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.

      assert (p :   # TD (nat_z_iso_inv (TransportedAssocRight Duniv H_eso H_ff TC) ((x1, x2), x3) #, id H x4) · assoc_left_tensor_m Duniv H_eso H_ff TC x1 x2 x3 x4 = TransportedTensorComm Duniv H_eso H_ff TC (TC (x1,(TC (x2,x3))),x4)).
      {
        rewrite TransportedAssocRightInvOnOb.
        unfold assoc_left_tensor_m.
        rewrite assoc.
        etrans. apply maponpaths_2, (! functor_comp TD _ _).
        unfold TransportedAssocLeft.

        simpl.
        do 2 rewrite id_right.
        rewrite ! assoc.
        etrans.
        2: apply id_left.
        apply maponpaths_2.
        rewrite id_right.
        fold TD.
        set (ptH :=  (TransportedTensorComm Duniv H_eso H_ff TC)).
        etrans. apply (! functor_comp TD _ _).
        rewrite <- (functor_id TD).
        apply maponpaths.

        rewrite (id_left (C := D ⊠ D)).
        rewrite (id_right (C := D ⊠ D)).

        etrans. {
          rewrite assoc'.
          apply maponpaths.
          apply binprod_comp.
        }

        etrans. {
          apply maponpaths_2.
          rewrite <- (id_left (id H x4)).
          apply binprod_comp.
        }

        rewrite assoc.
        etrans. {
          apply maponpaths_2.
          rewrite assoc'.
          apply maponpaths.
          rewrite <- binprod_comp.
          rewrite id_left.
          simpl.
          apply maponpaths_2.
          rewrite <- (functor_comp TD).
          apply maponpaths.
          rewrite <- binprod_comp.
          rewrite id_right.
          rewrite functor_id.
          apply maponpaths.
          apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
        }
        rewrite binprod_id.
        rewrite (functor_id TD).
        rewrite binprod_id.
        rewrite id_right.
        simpl.
        etrans. apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
        rewrite id_right.
        etrans. {
          apply maponpaths_2.
          apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
        }
        apply binprod_id.
      }

      exact (! p).
    }

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      rewrite <- (id_left (id H x1)).
      etrans.
      2: {
        apply maponpaths.
        rewrite binprod_comp.
        apply (! functor_comp TD _ _).
      }
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- (id_left (id H x1)).
      rewrite binprod_comp.
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.

      assert (p :  assoc_right_tensor_m Duniv H_eso H_ff TC x1 x2 x3 x4
                                        · # TD (id H x1 #, TransportedAssocLeft Duniv H_eso H_ff TC ((x2, x3), x4))
                   = nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC) (x1 , TC (TC (x2,x3), x4))).
      {
        rewrite TransportedAssocLeftOnOb.
        unfold assoc_right_tensor_m.
        rewrite TransportedAssocRightInvOnOb.
        rewrite ! assoc'.
        etrans.
        2: apply id_right.
        apply maponpaths.


        simpl.

        etrans. {
          apply maponpaths.
          rewrite <- (functor_comp TD).
          apply maponpaths.
          rewrite <- binprod_comp.
          apply maponpaths.
          rewrite assoc.
          apply maponpaths_2.
          rewrite <- (functor_comp TD).
          apply maponpaths.
          etrans. apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
          apply maponpaths_2.
          apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
        }
        rewrite ! id_left.
        rewrite binprod_id.
        rewrite (functor_id TD).
        rewrite <- (id_left (id H x1)).
        rewrite binprod_comp.
        rewrite (functor_comp TD).
        rewrite binprod_id.
        rewrite (functor_id TD).
        rewrite id_left.
        rewrite <- (functor_comp TD).
        rewrite <- (functor_id TD).
        apply maponpaths.
        rewrite <- binprod_comp.
        rewrite id_right.
        rewrite functor_id.
        etrans. apply maponpaths, (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
        apply binprod_id.
      }
      exact (! p).
    }

    unfold assoc_left_tensor_l.
    rewrite TransportedAssocLeftOnOb.
    rewrite ! assoc'.

    etrans.
    2: {
      apply maponpaths_2.
      rewrite <- (id_right (id H x4)).
      rewrite binprod_comp.
      apply (! functor_comp TD _ _).
    }
    rewrite assoc'.
    apply maponpaths.
    etrans. {
      apply maponpaths_2.
      exact (TransportedAssocLeftOnOb Duniv H_eso H_ff TC (TC (x1,x2)) x3 x4).
    }
    rewrite assoc'.
    apply maponpaths.
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      exact (! pr21 (TransportedTensorComm Duniv H_eso H_ff TC) _ _ (α ((x1,x2),x3) #, id x4)).
    }

    rewrite ! assoc'.
    rewrite <- functor_id.
    do 3 apply maponpaths.
    unfold assoc_right_tensor_r.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- (functor_id H).
      exact (pr21 (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) _ _ (id x1 #, α ((x2,x3),x4))).
    }

    rewrite ! assoc'.
    apply maponpaths.
    etrans. {
      apply maponpaths_2.
      apply (TransportedAssocRightInvOnOb Duniv H_eso H_ff TC).
    }

    rewrite ! assoc'.
    apply maponpaths.
    etrans. apply (! functor_comp TD _ _).
    apply maponpaths.
    rewrite functor_id.
    etrans. apply (! binprod_comp _ _ _ _ _ _ _ _ _ _).
    rewrite id_left.
    apply maponpaths.

    refine (_ @ ! TransportedAssocRightInvOnOb Duniv H_eso H_ff TC _ _ _).
    do 2 apply maponpaths.
    apply maponpaths_2.
    apply (! functor_id _ _).
  Qed.

  Definition TransportedMonoidal
    : monoidal_cat
    := D ,, TD ,, H I ,, luD ,, ruD ,, αD ,, TransportedTriangleEq ,, TransportedPentagonEq.

  Definition H_monoidal
    : functor_monoidal_cat lu luD ru ruD α αD.
  Proof.
    exists  (H,, pr1 (TransportedTensorComm Duniv H_eso H_ff TC),, id H I).
    split.
    - split.
      + exact (H_plu Duniv H_eso H_ff TC I lu).
      + exact (H_pru Duniv H_eso H_ff TC I ru).
    - exact (H_pα Duniv H_eso H_ff TC α I).
  Defined.

  Definition H_strong_monoidal
    : strong_functor_monoidal_cat lu luD ru ruD α αD.
  Proof.
    exists H_monoidal.
    split.
    - apply (TransportedTensorComm Duniv H_eso H_ff TC).
    - apply identity_is_z_iso.
  Defined.

  Context {E : category}
          (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE)
          (ruE : right_unitor TE IE)
          (αE : associator TE).

  Definition precompMonoidal
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_monoidal_disp_cat luD luE ruD ruE αD αE)
                   (functor_monoidal_disp_cat lu luE ru ruE α αE).
  Proof.
    apply disp_prod_functor_over_fixed_base.
    - apply disp_prod_functor_over_fixed_base.
      + apply precompLU.
      + apply precompRU.
    - apply precompA.
  Defined.

  Definition precompStrongMonoidal
    : disp_functor (total_functor precompMonoidal)
                   (functor_strong_monoidal_disp_cat luD luE ruD ruE αD αE)
                   (functor_strong_monoidal_disp_cat lu luE ru ruE α αE).
  Proof.
    use tpair.
    - exists (λ F pFi, strong_functor_composition (pr2 H_strong_monoidal) pFi).
      intro ; intros ; exact tt.
    - abstract (split ; intro ; intros ; apply isapropunit).
  Defined.

  Definition precompMonoidal_ff
    : disp_functor_ff precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_ff.
    - apply disp_prod_functor_over_fixed_base_ff.
      + apply precompLU_ff.
      + apply precompRU_ff.
    - apply precompA_ff.
  Qed.

  Definition precompStrongMonoidal_ff
    : disp_functor_ff precompStrongMonoidal.
  Proof.
    intro ; intros.
    apply isweqcontrtounit.
    apply iscontrunit.
  Qed.

  Definition precompMonoidal_eso
    :  disp_functor_disp_ess_split_surj precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_eso.
    - apply disp_prod_functor_over_fixed_base_eso.
      + apply precompLU_eso.
      + apply precompRU_eso.
    - apply precompA_eso.
      (* exact Euniv. *)
  Qed.

  Definition precompStrongMonoidal_eso
    :  disp_functor_disp_ess_split_surj precompStrongMonoidal.
  Proof.
    intro ; intros.
    use tpair.
    - use tpair.
      + transparent assert (i : (nat_z_iso (functor_tensor_map_dom TE (pr11 x))
                              (functor_tensor_map_codom (TransportedTensor Duniv H_eso H_ff TC) (pr11 x)))).
        {

          use (lift_nat_z_iso_along (_,,Euniv) _ (pair_functor_eso _ _ H_eso H_eso)
                                    (pair_functor_ff _ _ H_ff H_ff)).

          use (nat_z_iso_comp (make_nat_z_iso _ _ _ (pr1 xx)) _).
          exact (post_whisker_nat_z_iso (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) (pr11 x)).
        }

        assert (p : pr1 i = pr121 x).
        {
          use (lift_nat_trans_eq_along (_,,Euniv) _
                                       (pair_functor_eso _ _ H_eso H_eso)
                                       (pair_functor_ff _ _ H_ff H_ff)).
          etrans. { apply lift_nat_trans_along_comm. }
          refine (idpath (nat_trans_comp _ _ _
                                  (pr121 (total_functor precompMonoidal x))
                                  (post_whisker (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC)) (pr11 x))) @ _).

          use nat_trans_eq.
          { apply homset_property. }
          intro cc.
          simpl.
          rewrite assoc'.
          rewrite <- (functor_comp (pr11 x)).
          etrans. {
            do 2 apply maponpaths.
            apply (pr2 (TransportedTensorComm Duniv H_eso H_ff TC)).
          }
          rewrite (functor_id (pr11 x)).
          apply id_right.
        }
        rewrite <- p.
        exact (pr2 i).
      + set (a := pr2 xx).
        simpl in a.
        rewrite (functor_id (pr11 x)) in a.
        rewrite id_right in a.
        exact a.
    - refine (tt ,, tt ,, _).
      split ; apply isapropunit.
  Qed.

  Definition precomp_monoidal_is_ff
    : fully_faithful (total_functor precompMonoidal).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompMonoidal_ff.
  Qed.

  Definition precomp_strongmonoidal_is_ff
    : fully_faithful (total_functor precompStrongMonoidal).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply precomp_monoidal_is_ff.
    - exact precompStrongMonoidal_ff.
  Qed.

  Lemma is_univalent_LaxMonoidalFunctorCategory
    : is_univalent (total_category (functor_monoidal_disp_cat luD luE ruD ruE αD αE)).
  Proof.
    apply is_univalent_total_category.
    - apply is_univalent_total_category.
      + apply (is_univalent_functor_category _ _ Euniv).
      + apply is_disp_univalent_functor_tensorunit_disp_cat.
    - apply dirprod_disp_cat_is_univalent.
      {
        apply dirprod_disp_cat_is_univalent.
        apply functor_lu_disp_cat_is_univalent.
        apply functor_ru_disp_cat_is_univalent.
      }
      apply functor_ass_disp_cat_is_univalent.
  Qed.

  Lemma is_univalent_LaxMonoidalFunctorCategory'
    : is_univalent (total_category (functor_monoidal_disp_cat lu luE ru ruE α αE)).
  Proof.
    apply is_univalent_total_category.
    - apply is_univalent_total_category.
      + apply (is_univalent_functor_category _ _ Euniv).
      + apply functor_tensorunit_disp_cat_is_univalent.
    - apply dirprod_disp_cat_is_univalent.
      {
        apply dirprod_disp_cat_is_univalent.
        apply functor_lu_disp_cat_is_univalent.
        apply functor_ru_disp_cat_is_univalent.
      }
      apply functor_ass_disp_cat_is_univalent.
  Qed.

  Lemma is_univalent_StrongMonoidalFunctorCategory
    : is_univalent (total_category (functor_strong_monoidal_disp_cat luD luE ruD ruE αD αE)).
  Proof.
    apply is_univalent_total_category.
    - apply is_univalent_LaxMonoidalFunctorCategory.
    - apply disp_full_sub_univalent.
      intro ; apply isapropdirprod.
      apply isaprop_is_nat_z_iso.
      apply isaprop_is_z_isomorphism.
  Qed.

  Definition precomp_monoidal_is_eso
    : essentially_surjective (total_functor precompMonoidal).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompMonoidal_eso.
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_total_category.
      + apply is_univalent_functor_category.
        exact Euniv.
      + apply functor_tensorunit_disp_cat_is_univalent.
  Qed.

  Definition precomp_strongmonoidal_is_eso
    : essentially_surjective (total_functor precompStrongMonoidal).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply precomp_monoidal_is_eso.
    - exact precompStrongMonoidal_eso.
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_LaxMonoidalFunctorCategory'.
  Qed.

  Definition precomp_monoidal_adj_equiv
    : adj_equivalence_of_cats (total_functor precompMonoidal).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_LaxMonoidalFunctorCategory.
    - exact precomp_monoidal_is_ff.
    - exact precomp_monoidal_is_eso.
  Defined.

  Definition precomp_monoidal_catiso
    : catiso (total_category (functor_monoidal_disp_cat
                                (TransportedLeftUnitor Duniv H_eso H_ff TC I lu) luE
                                (TransportedRightUnitor Duniv H_eso H_ff TC I ru) ruE
                                (TransportedAssociator Duniv H_eso H_ff TC α) αE
             ))
             (total_category (functor_monoidal_disp_cat
                                lu luE ru ruE α αE
             )).
  Proof.
    use (adj_equivalence_of_cats_to_cat_iso precomp_monoidal_adj_equiv _ _).
    - apply is_univalent_LaxMonoidalFunctorCategory.
    - apply is_univalent_LaxMonoidalFunctorCategory'.
  Defined.

  Definition precomp_strongmonoidal_adj_equiv
    : adj_equivalence_of_cats (total_functor precompStrongMonoidal).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_StrongMonoidalFunctorCategory.
    - exact precomp_strongmonoidal_is_ff.
    - exact precomp_strongmonoidal_is_eso.
  Defined.

  Definition precomp_strongmonoidal_catiso
    : catiso (total_category (functor_strong_monoidal_disp_cat
                                (TransportedLeftUnitor Duniv H_eso H_ff TC I lu) luE
                                (TransportedRightUnitor Duniv H_eso H_ff TC I ru) ruE
                                (TransportedAssociator Duniv H_eso H_ff TC α) αE
             ))
             (total_category (functor_strong_monoidal_disp_cat
                                lu luE ru ruE α αE
             )).
  Proof.
    use (adj_equivalence_of_cats_to_cat_iso precomp_strongmonoidal_adj_equiv _ _).
    - apply is_univalent_StrongMonoidalFunctorCategory.
    - apply is_univalent_total_category.
      + apply is_univalent_LaxMonoidalFunctorCategory'.
      + apply disp_full_sub_univalent.
        intro ; apply isapropdirprod.
        * apply NaturalTransformations.isaprop_is_nat_z_iso.
        * apply Isos.isaprop_is_z_isomorphism.
  Defined.

End RezkMonoidal.
