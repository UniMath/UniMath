(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

Contents :

- identifies monoidal dialgebras as inserters in the bicategory of whiskered monoidal categories

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Limits.Inserters.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.


Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalFunctorLifting.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Require Import UniMath.Bicategories.MonoidalCategories.BicatOfWhiskeredMonCats.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfCatsLimits.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.
Import MonoidalNotations.

Local Lemma equality_2cells_monbicat
      {Mon_V Mon_W : monbicat} {Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧}
      (αm βm : (hom Mon_V Mon_W)⟦Fm, Gm⟧)
  : (∏ x : pr11 Mon_V,  (pr11 αm) x = (pr11 βm) x) -> αm = βm.
Proof.
  intro p.
  use total2_paths_f.
  2: apply isaprop_is_mon_nat_trans.
  use total2_paths_f.
  - apply funextsec ; intro ; apply p.
  - apply isaprop_is_nat_trans.
    apply homset_property.
Qed.

Section FixTwoMonoidalFunctors.

Context {Mon_V Mon_W : monbicat} (Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧).

  Definition monbicat_inserter_cone :
    inserter_cone Fm Gm.
  Proof.
    cbn in Fm, Gm.
    use make_inserter_cone.
    - exact (dialgebra (pr1 Fm) (pr1 Gm) ,, dialgebra_monoidal (pr2 Fm) (pr2 Gm)).
    - exists (dialgebra_pr1 (pr1 Fm) (pr1 Gm)).
      apply dialgebra_monoidal_pr1.
    - exists (dialgebra_nat_trans (pr1 Fm) (pr1 Gm)).
      apply dialgebra_nat_trans_is_mon_nat_trans.
  Defined.

  Local Definition underlying_inserter_cone (q : inserter_cone Fm Gm) : inserter_cone (pr1 Fm) (pr1 Gm).
  Proof.
    use make_inserter_cone.
    - exact (pr11 q).
    - exact (pr1 (inserter_cone_pr1 q)).
    - exact (pr1 (inserter_cone_cell q)).
  Defined.

  Local Definition underlying_inserter_1cell (q : inserter_cone Fm Gm) :
    inserter_1cell (underlying_inserter_cone q) (dialgebra_inserter_cone (pr1 Fm) (pr1 Gm))
    := dialgebra_inserter_ump_1 (pr1 Fm) (pr1 Gm) (underlying_inserter_cone q).

  (* Local Definition fmonoidal_underlying_inserter_1cell'_fmonoidal_data
        (q : inserter_cone Fm Gm)
    : fmonoidal_data (pr21 q) (pr2 Mon_V) (inserter_cone_pr1 (underlying_inserter_cone q)).
  Proof.
    induction q as [Mon_U [Hm α]].
    split.
    - intros x y.
      apply (fmonoidal_preservestensordata (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm))).
    - apply (fmonoidal_preservesunit (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm))).
  Defined.

  Local Definition fmonoidal_underlying_inserter_1cell'_fmonoidal_laxlaws
        (q : inserter_cone Fm Gm)
    : fmonoidal_laxlaws (fmonoidal_underlying_inserter_1cell'_fmonoidal_data q).
  Proof.
    repeat split ; red ; cbn ; intros.
    - apply fmonoidal_preservestensornatleft.
    - apply fmonoidal_preservestensornatright.
    - apply fmonoidal_preservesassociativity.
    - apply fmonoidal_preservesleftunitality.
    - apply fmonoidal_preservesrightunitality.
  Qed.

  Local Definition fmonoidal_underlying_inserter_1cell'_laxmonoidal (q : inserter_cone Fm Gm)
    : fmonoidal_lax (pr21 q) (pr2 Mon_V) (inserter_cone_pr1 (underlying_inserter_cone q)).
  Proof.
    exists (fmonoidal_underlying_inserter_1cell'_fmonoidal_data q).
    exact (fmonoidal_underlying_inserter_1cell'_fmonoidal_laxlaws q).
  Defined.

  Local Definition fmonoidal_underlying_inserter_1cell'_fmonoidal_stronglaws (q : inserter_cone Fm Gm)
    :  fmonoidal_stronglaws
         (fmonoidal_preservestensordata (fmonoidal_underlying_inserter_1cell'_laxmonoidal q))
         (fmonoidal_preservesunit (fmonoidal_underlying_inserter_1cell'_laxmonoidal q)).
  Proof.
    induction q as [Mon_U [Hm α]].
    split.
    - do 2 intro ; apply (pr2 Hm).
    - apply (pr2 Hm).
  Defined. *)

  (** The following definition replaces fmonoidal_underlying_inserter_1cell **)
  Local Definition fmonoidal_underlying_inserter_1cell' (q : inserter_cone Fm Gm) :
    fmonoidal (pr21 q)
              (dialgebra_monoidal (pr2 Fm) ((pr12 Gm): fmonoidal_lax (pr2 Mon_V) (pr2 Mon_W) _))
              (pr1 (underlying_inserter_1cell q)).
  Proof.
    use functorlifting_fmonoidal.
    3: {
      use monoidal_nat_trans_to_dialgebra_lifting_strong.
      + use tpair.
        * apply (pr12 q).
        * apply (pr212 q).
      + apply (pr22 q).
    }
  Defined.

  (* Local Definition fmonoidal_underlying_inserter_1cell (q : inserter_cone Fm Gm) :
    fmonoidal (pr21 q)
              (dialgebra_monoidal (pr2 Fm) ((pr12 Gm): fmonoidal_lax (pr2 Mon_V) (pr2 Mon_W) _))
              (pr1 (underlying_inserter_1cell q)).
  Proof.
    induction q as [Mon_U [Hm α]].
    use tpair.
    - use tpair.
      + split.
        * intros x y.
          use tpair.
          -- cbn.
             apply (fmonoidal_preservestensordata (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm))).
          -- cbn. unfold dialgebra_disp_tensor_op, fmonoidal_preservestensordata.
             repeat rewrite assoc'.
             apply (z_iso_inv_on_right _ _ _
                      (_,,fmonoidal_preservestensorstrongly (pr2 Fm) (pr1 (pr1 Hm) x) (pr1 (pr1 Hm) y))).
             cbn.
             unfold fmonoidal_preservestensordata.
             assert (aux := pr12 α x y). cbn in aux.
             etrans.
             2: { apply assoc'. }
             apply pathsinv0, aux.
        * use tpair.
          -- cbn.
             apply (fmonoidal_preservesunit (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm))).
          -- cbn. unfold dialgebra_disp_unit, fmonoidal_preservesunit.
             rewrite assoc'.
             apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservesunitstrongly (pr2 Fm))).
             cbn.
             unfold fmonoidal_preservesunit.
             assert (aux := pr22 α). cbn in aux.
             etrans.
             2: { apply assoc'. }
             apply pathsinv0, aux.
      + repeat split; (red; cbn; intros; use total2_paths_f; [cbn | apply (pr1 Mon_W)]). (* the lax functor laws *)
        * apply fmonoidal_preservestensornatleft.
        * apply fmonoidal_preservestensornatright.
        * apply fmonoidal_preservesassociativity.
        * apply fmonoidal_preservesleftunitality.
        * apply fmonoidal_preservesrightunitality.
    - cbn; split.
      + intros x y.
        use tpair.
        * use tpair.
          -- cbn.
             apply (pr1 (fmonoidal_preservestensorstrongly (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm)) x y)).
          -- cbn. unfold dialgebra_disp_tensor_op, fmonoidal_preservestensordata.
             repeat rewrite assoc'.
             match goal with | [ |- _ = ?HR1 · _]  => set (R1 := HR1) end.
             transparent assert (auxiso : (z_iso (pr11 Fm (pr11 Hm (x ⊗_{ pr12 Mon_U} y)))
                                             (pr11 Fm (pr11 Hm x ⊗_{ pr12 Mon_V} pr11 Hm y)))).
             { exists R1.
               exists ((# (pr11 Fm))%Cat (fmonoidal_preservestensordata (pr12 Hm) x y)).
               split.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr22 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)). }
                 apply functor_id.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr12 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)). }
                 apply functor_id.
             }
             apply (z_iso_inv_to_left _ _ _ auxiso).
             cbn.
             apply pathsinv0, (z_iso_inv_on_right _ _ _
                                 (_,,fmonoidal_preservestensorstrongly (pr2 Fm) (pr11 Hm x) (pr11 Hm y))).
             cbn.
             repeat rewrite assoc.
             match goal with | [ |- _ = _ · ?HR4 ]  => set (R4 := HR4) end.
             transparent assert (auxiso' : (z_iso (pr11 Gm (pr11 Hm (x ⊗_{ pr12 Mon_U} y)))
                                             (pr11 Gm (pr11 Hm x ⊗_{ pr12 Mon_V} pr11 Hm y)))).
             { exists R4.
               exists ((# (pr11 Gm))%Cat (fmonoidal_preservestensordata (pr12 Hm) x y)).
               split.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr22 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)). }
                 apply functor_id.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr12 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)). }
                 apply functor_id.
             }
             apply pathsinv0, (z_iso_inv_to_right _ _ _ _ auxiso').
             cbn.
             assert (aux := pr12 α x y). cbn in aux.
             etrans.
             2: { apply assoc. }
             exact aux.
        * cbn. split.
          -- use total2_paths_f; [cbn | apply (pr1 Mon_W)].
             apply (pr12 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)).
          -- use total2_paths_f; [cbn | apply (pr1 Mon_W)].
             apply (pr22 (fmonoidal_preservestensorstrongly (pr2 Hm) x y)).
      + use tpair.
        * use tpair.
          -- cbn.
             apply (pr1 (fmonoidal_preservesunitstrongly (pr2 Hm : fmonoidal (pr2 Mon_U) (pr2 Mon_V) (pr1 Hm)))).
          -- cbn. unfold dialgebra_disp_tensor_op, dialgebra_disp_unit, fmonoidal_preservesunit.
             match goal with | [ |- _ = ?HR1 · _]  => set (R1 := HR1) end.
             transparent assert (auxiso : (z_iso (pr11 Fm (pr11 Hm I_{ pr12 Mon_U }))
                                             (pr11 Fm I_{ pr12 Mon_V}))).
             { exists R1.
               exists ((# (pr11 Fm))%Cat (fmonoidal_preservesunit (pr12 Hm))).
               split.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr22 (fmonoidal_preservesunitstrongly (pr2 Hm))). }
                 apply functor_id.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr12 (fmonoidal_preservesunitstrongly (pr2 Hm))). }
                 apply functor_id.
             }
             apply (z_iso_inv_to_left _ _ _ auxiso).
             cbn.
             apply pathsinv0, (z_iso_inv_on_right _ _ _
                                 (_,,fmonoidal_preservesunitstrongly (pr2 Fm))).
             cbn.
             repeat rewrite assoc.
             match goal with | [ |- _ = _ · ?HR4 ]  => set (R4 := HR4) end.
             transparent assert (auxiso' : (z_iso (pr11 Gm (pr11 Hm I_{ pr12 Mon_U}))
                                             (pr11 Gm I_{ pr12 Mon_V}))).
             { exists R4.
               exists ((# (pr11 Gm))%Cat (fmonoidal_preservesunit (pr12 Hm))).
               split.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr22 (fmonoidal_preservesunitstrongly (pr2 Hm))). }
                 apply functor_id.
               - etrans.
                 { apply pathsinv0, functor_comp. }
                 etrans.
                 { apply maponpaths.
                   exact (pr12 (fmonoidal_preservesunitstrongly (pr2 Hm))). }
                 apply functor_id.
             }
             apply pathsinv0, (z_iso_inv_to_right _ _ _ _ auxiso').
             cbn.
             assert (aux := pr22 α). cbn in aux.
             exact aux.
        * cbn. split.
          -- use total2_paths_f; [cbn | apply (pr1 Mon_W)].
             apply (pr12 (fmonoidal_preservesunitstrongly (pr2 Hm))).
          -- use total2_paths_f; [cbn | apply (pr1 Mon_W)].
             apply (pr22 (fmonoidal_preservesunitstrongly (pr2 Hm))).
             Time Defined.
*)


  (* If we replace fmonoidal_underlying_inserter_1cell by fmonoidal_underlying_inserter_1cell',
     everything still works perfectly *)
  Lemma is_mon_nat_trans_underlying_inserter_1cell_pr1 (q : inserter_cone Fm Gm) :
    is_mon_nat_trans
      (comp_fmonoidal (fmonoidal_underlying_inserter_1cell' q) (dialgebra_monoidal_pr1 (pr2 Fm) (pr12 Gm)))
      (pr12 (inserter_cone_pr1 q))
      (pr1 (inserter_1cell_pr1 (underlying_inserter_1cell q))).
  Proof.
    split.
    - intros x y.
      cbn.
      unfold projection_preserves_tensordata, fmonoidal_preservestensordata.
      rewrite id_left.
      rewrite id_right.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in Mon_V.
             apply (bifunctor_leftid (pr2 Mon_V)).
           - cbn in Mon_V.
             apply (bifunctor_rightid (pr2 Mon_V)).
      }
      apply pathsinv0, id_left.
    - red. cbn.
      unfold projection_preserves_unit, fmonoidal_preservesunit.
      rewrite id_left.
      apply id_right.
  Qed.

  Definition monbicat_inserter_ump_1_inv_2cell
             (q : inserter_cone Fm Gm)
    : invertible_2cell
    ((_,, fmonoidal_underlying_inserter_1cell' q : monbicat ⟦ q, monbicat_inserter_cone ⟧)
       · inserter_cone_pr1 monbicat_inserter_cone) (inserter_cone_pr1 q).
  Proof.
    use tpair.
    - exists (pr112 (underlying_inserter_1cell q)).
      apply (is_mon_nat_trans_underlying_inserter_1cell_pr1 q).
    - use tpair.
      + use tpair.
        * exact (pr12 (inserter_1cell_pr1 (underlying_inserter_1cell q))).
        * apply is_mon_nat_trans_pointwise_inverse.
          apply (is_mon_nat_trans_underlying_inserter_1cell_pr1 q).
      + abstract (split ; use equality_2cells_monbicat ; intro ; apply id_left).
  Defined.

  Definition monbicat_inserter_ump_1 :
    has_inserter_ump_1 monbicat_inserter_cone.
  Proof.
    intro q.
    use make_inserter_1cell.
    - exists (underlying_inserter_1cell q).
      exact (fmonoidal_underlying_inserter_1cell' q).
    - exact (monbicat_inserter_ump_1_inv_2cell q).
    - abstract (
          use equality_2cells_monbicat ;
          intro ;
          cbn ;
          rewrite id_right, id_left ;
          etrans ;
          [ apply maponpaths ;
            apply functor_id | rewrite id_right] ;
          refine (! id_left _ @ _) ;
          apply maponpaths_2, pathsinv0, functor_id).
  Defined.

  Section UMP2Prep.

  Context {Mon_U : monbicat}
  {Hm H'm : monbicat ⟦ Mon_U, monbicat_inserter_cone ⟧}
  (α : prebicat_cells monbicat (Hm · inserter_cone_pr1 monbicat_inserter_cone) (H'm · inserter_cone_pr1 monbicat_inserter_cone))
  (Hyp : vcomp2
          (vcomp2 (vcomp2 (rassociator Hm (inserter_cone_pr1 monbicat_inserter_cone) Fm) (lwhisker Hm (inserter_cone_cell monbicat_inserter_cone)))
             (lassociator Hm (inserter_cone_pr1 monbicat_inserter_cone) Gm)) (rwhisker Gm α) =
        vcomp2 (vcomp2 (vcomp2 (rwhisker Fm α) (rassociator H'm (inserter_cone_pr1 monbicat_inserter_cone) Fm)) (lwhisker H'm (inserter_cone_cell monbicat_inserter_cone)))
          (lassociator H'm (inserter_cone_pr1 monbicat_inserter_cone) Gm)).

  Local Definition underlying_inserter_ump_2
    : ∑ ζ : prebicat_cells bicat_of_cats (pr1 Hm) (pr1 H'm),
        rwhisker (inserter_cone_pr1 (dialgebra_inserter_cone (pr1 Fm) (pr1 Gm))) ζ = pr1 α
    := dialgebra_inserter_ump_2 (pr1 Fm) (pr1 Gm) (pr1 Mon_U) (pr1 Hm) (pr1 H'm)
         (pr1 α) (maponpaths pr1 Hyp).

  Local Definition underlying_inserter_ump_cell : prebicat_cells bicat_of_cats (pr1 Hm) (pr1 H'm)
    := pr1 underlying_inserter_ump_2.

  Local Lemma is_mon_nat_trans_underlying_inserter_ump_cell :
    is_mon_nat_trans (pr2 Hm : fmonoidal (pr2 Mon_U) _ _)
                     (pr2 H'm : fmonoidal (pr2 Mon_U) _ _)
                     underlying_inserter_ump_cell.
  Proof.
    split.
    - intros x y.
      use total2_paths_f; [cbn | apply (pr1 Mon_W)].
      assert (aux := pr12 α x y). cbn in aux.
      unfold projection_preserves_tensordata in aux.
      do 2 rewrite id_left in aux.
      exact aux.
    - use total2_paths_f; [cbn | apply (pr1 Mon_W)].
      assert (aux := pr22 α). red in aux; cbn in aux.
      unfold projection_preserves_unit in aux.
      do 2 rewrite id_left in aux.
      exact aux.
  Qed.

  End UMP2Prep.

  Definition monbicat_inserter_ump_2 :
    has_inserter_ump_2 monbicat_inserter_cone.
  Proof.
    intros Mon_U Hm H'm α Hyp.
    exists (underlying_inserter_ump_cell α Hyp,,
                                    is_mon_nat_trans_underlying_inserter_ump_cell α Hyp).
    abstract (use equality_2cells_monbicat ; intro ; apply idpath).
  Defined.

  Definition monbicat_inserter_ump_eq :
    has_inserter_ump_eq monbicat_inserter_cone.
  Proof.
    intros Mon_U Hm H'm α Hyp ϕ1 ϕ2 eqϕ1 eqϕ2.
    use total2_paths_f; [cbn | apply isaprop_is_mon_nat_trans].
    use (dialgebra_inserter_ump_eq (pr1 Fm) (pr1 Gm) (pr1 Mon_U) (pr1 Hm) (pr1 H'm)
         (pr1 α) (maponpaths pr1 Hyp)).
    - exact (maponpaths pr1 eqϕ1).
    - exact (maponpaths pr1 eqϕ2).
  Qed.

End FixTwoMonoidalFunctors.

  Definition has_inserters_monbicat : has_inserters monbicat.
  Proof.
    intros Mon_V Mon_W Fm Gm.
    cbn in Fm, Gm.
    exists (dialgebra (pr1 Fm) (pr1 Gm) ,, dialgebra_monoidal (pr2 Fm) (pr2 Gm)).
    simple refine (_ ,, _ ,, _).
    - cbn. exists (dialgebra_pr1 (pr1 Fm) (pr1 Gm)).
      apply dialgebra_monoidal_pr1.
    - cbn. exists (dialgebra_nat_trans (pr1 Fm) (pr1 Gm)).
      apply dialgebra_nat_trans_is_mon_nat_trans.
    - simple refine (_ ,, _ ,, _).
      + exact (monbicat_inserter_ump_1 Fm Gm).
      + exact (monbicat_inserter_ump_2 Fm Gm).
      + exact (monbicat_inserter_ump_eq Fm Gm).
  Defined.
