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
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.DisplayedCategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedUnitors.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedAssociator.

Local Open Scope cat.

Section RezkMonoidal.

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

    exact (TransportedAssocRightOnOb Duniv H_eso H_ff TC α x1 I x2).
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

    transparent assert (f_t
                         : (D ⟦ H (assoc_right TC ((x1, x2), TC (x3, x4))),
                                assoc_right (TransportedTensor Duniv H_eso H_ff TC) ((H x1, H x2), TD (H x3, H x4)) ⟧)).
    {
      use (_ · _).
      2: {
        set (t := nat_z_iso_inv (TransportedAssocRight Duniv H_eso H_ff TC)).
        apply t.
      }
      use (# TD).
      use catbinprodmor.
      - apply identity.
      - use (# TD).
        use catbinprodmor.
        + apply identity.
        + apply TransportedTensorComm.
    }

    transparent assert ( f_s : (D ⟦ assoc_left (TransportedTensor Duniv H_eso H_ff TC) ((H x1, H x2), TD (H x3, H x4)),
                                    H (assoc_left TC ((x1, x2), TC (x3, x4))) ⟧) ).
    {
      use (_ · _).
      3: { apply (TransportedAssocLeft Duniv H_eso H_ff TC). }
      simpl.
      use (# TD).
      use catbinprodmor.
      - apply identity.
      - exact ((TransportedTensorComm Duniv H_eso H_ff TC) (x3,x4)).
    }

    assert (p0 : αD ((H x1, H x2), TD (H x3, H x4))
            = f_s · #H (α ((x1,x2) , TC (x3,x4))) · f_t).
    {
      admit.
    }

    etrans. {
      apply maponpaths.
      exact p0.
    }
    clear p0.

    transparent assert (g_t : (D ⟦ H (assoc_right TC ((TC (x1, x2), x3), x4)),
                                   assoc_right (TransportedTensor Duniv H_eso H_ff TC) ((TD (H x1, H x2), H x3), H x4)⟧)).
    {
      use (_ · _).
      2: { apply (TransportedAssocRight Duniv H_eso H_ff TC). }
      use (# TD).
      use catbinprodmor.
      2: apply identity.
      exact (nat_z_iso_inv (TransportedTensorComm Duniv H_eso H_ff TC) (x1,x2)).
    }

    transparent assert (g_s : (D ⟦ assoc_left (TransportedTensor Duniv H_eso H_ff TC) ((TD (H x1, H x2), H x3), H x4),
                                   H (assoc_left TC ((TC (x1, x2), x3), x4)) ⟧)).
    {
      use (_ · _).
      3: apply (TransportedAssocLeft Duniv H_eso H_ff TC).
      use (# TD).
      use catbinprodmor.
      2: apply identity.
      use (# TD).
      use catbinprodmor.
      1: exact ((TransportedTensorComm Duniv H_eso H_ff TC) (x1,x2)).
      apply identity.
    }

    assert (p0 : αD ((TD (H x1, H x2), H x3), H x4)
                 = g_s · #H (α ((TC (x1,x2),x3),x4)) · g_t).
    {
      admit.
    }

    etrans. { apply maponpaths_2 ; exact p0. }
    clear p0.

    assert (p0 : g_t · f_s = identity _).
    {
      admit.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      do 2 rewrite assoc.
      do 2 apply maponpaths_2.
      exact p0.
    }
    clear p0.
    clear g_t f_s.
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

    unfold f_t.
    unfold g_s.

    set (l1 :=  # TD
    (# TD (TransportedTensorComm Duniv H_eso H_ff TC (x1, x2) #, id H (pr21 ((TC (x1, x2), x3), x4)))
       #, id functor_identity D (pr2 (pair_functor (pair_functor H H) H ((TC (x1, x2), x3), x4))))).
    set (l2 :=  (pr11 (TransportedAssocLeft Duniv H_eso H_ff TC)) ((TC (x1, x2), x3), x4)).
    set (l3 :=  (# H (# TC (pr1 α ((x1, x2), x3) #, id x4)) · # H (pr1 α ((x1, TC (x2, x3)), x4))
                   · # H (# TC (id x1 #, pr1 α ((x2, x3), x4))))).

    set (l4 := (pr11 (nat_z_iso_inv (TransportedAssocRight Duniv H_eso H_ff TC))) ((x1, x2), TC (x3, x4))).
    set (l5 :=  # TD
         (id functor_identity D
               (pr1 (precategory_binproduct_unassoc D D D ((H x1, H x2), TD (H x3, H x4))))
         #, # TD
              (id pr21 ((H x1, H x2), TD (H x3, H x4))
                  #, pr1 (pr2 (TransportedTensorComm Duniv H_eso H_ff TC) (x3, x4))))).

    refine (idpath (l1 · l2 · l3 · (l4 · l5)) @ _).

    set (r1 :=   # TD
    (TransportedAssocLeft Duniv H_eso H_ff TC ((x1, x2), x3) · # H (α ((x1, x2), x3))
     · nat_z_iso_inv (TransportedAssocRight Duniv H_eso H_ff TC) ((x1, x2), x3) #, id
     H x4)).
    set (r2 := pr1 αD ((H x1, TD (H x2, H x3)), H x4)).
    set (r3 :=  # TD (id H x1 #, pr1 αD ((H x2, H x3), H x4))).
    refine (_ @ idpath (r1 · r2 · r3)).






    transparent assert ( h_t : (D ⟦ H (assoc_right TC ((x1, TC (x2, x3)), x4)),
                                    assoc_right (TransportedTensor Duniv H_eso H_ff TC) ((H x1, TD (H x2, H x3)), H x4) ⟧)).
    {
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
      exact (nat_z_iso_inv (TransportedAssocRight Duniv H_eso H_ff TC) ((x1,TC (x2,x3)),x4)).
    }

    transparent assert (h_s : (D⟦ assoc_left (TransportedTensor Duniv H_eso H_ff TC) ((H x1, TD (H x2, H x3)), H x4), H (assoc_left TC ((x1, TC (x2, x3)), x4)) ⟧)).
    {
      use (_ · _).
      3: apply (TransportedAssocLeft Duniv H_eso H_ff TC).
      use (# TD).
      use catbinprodmor.
      2: apply identity.
      simpl.
      apply (#TD).
      use catbinprodmor.
      1: apply identity.
      apply ((TransportedTensorComm Duniv H_eso H_ff TC) (x2,x3)).
    }

    assert (p0 :  αD ((H x1, TD (H x2, H x3)), H x4)
                  = h_s · #H (α ((x1, TC (x2,x3)),x4)) · h_t).
    {
      admit.
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      exact (! p0).
    }
    clear p0.
    etrans.
    2: {
      do 3 apply maponpaths.
      exact (! tαD ((x2,x3),x4)).
    }

    unfold h_s.
    unfold g_s.
    unfold h_t.

  Admitted.

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

  Context (TE : functor (E ⊠ E) E) (IE : E)
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

  Definition precompMonoidal_ff
    : disp_functor_ff precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_ff.
    - apply disp_prod_functor_over_fixed_base_ff.
      + apply precompLU_ff.
      + apply precompRU_ff.
    - apply precompA_ff.
  Qed.

  Definition precompMonoidal_eso
    :  disp_functor_disp_ess_split_surj precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_eso.
    - apply disp_prod_functor_over_fixed_base_eso.
      + apply precompLU_eso.
      + apply precompRU_eso.
    - apply precompA_eso.
      exact Euniv.
  Qed.

  Definition precomp_monoidal_is_ff
    : fully_faithful (total_functor precompMonoidal).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompMonoidal_ff.
  Qed.

  Definition precomp_monoidal_is_eso
    : essentially_surjective (total_functor precompMonoidal).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompMonoidal_eso.
  Qed.

  Definition precomp_monoidal_adj_equiv
    : adj_equivalence_of_cats (total_functor precompMonoidal).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply Constructions.dirprod_disp_cat_is_univalent.
        {
          apply Constructions.dirprod_disp_cat_is_univalent.
          apply functor_lu_disp_cat_is_univalent.
          apply functor_ru_disp_cat_is_univalent.
        }
        apply functor_ass_disp_cat_is_univalent.
    - exact precomp_monoidal_is_ff.
    - exact precomp_monoidal_is_eso.
  Defined.

End RezkMonoidal.
