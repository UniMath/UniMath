(** the coslice category I/V for a monoidal category is again monoidal

The coslice objects have a morphism from the monoidal unit I to an object of V. Since I is often not a terminal object 1 of V,
one cannot speak of pointed objects here; I suggest to call them monoidal-pointed objects.

author: Ralph Matthes 2022

in 2022 Kobe Wullaert added the part in preparation of showing that taking the category of monoidal-pointed objects is an idempotent operation (strong monoidal functors are constructed between one and two applications of that operation to some argument) - the continuation is found in the package [Bicategories]

 *)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.coslicecat.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section A.

Context {V : category} (Mon_V : monoidal V).

Let cosliced : disp_cat V := coslice_cat_disp V I_{Mon_V}.

Lemma monoidal_pointed_objects_disp_tensor_data_aux1 (v w w' : V) (g : V ⟦ w, w' ⟧)
  (pv : cosliced v) (pw : cosliced w) (pw' : cosliced w') (Hypg : pw · g = pw') :
  luinv^{ Mon_V }_{ I_{ Mon_V}} · pv ⊗^{ Mon_V} pw · v ⊗^{ Mon_V}_{l} g =
  luinv^{ Mon_V }_{ I_{ Mon_V}} · pv ⊗^{ Mon_V} pw'.
Proof.
  rewrite assoc'.
  apply maponpaths.
  rewrite <- Hypg.
  unfold functoronmorphisms1.
  rewrite assoc'.
  apply maponpaths.
  apply pathsinv0, (bifunctor_leftcomp Mon_V).
Qed.

Lemma monoidal_pointed_objects_disp_tensor_data_aux2 (v v' w : V) (f : V ⟦ v, v' ⟧)
  (pv : cosliced v) (pv' : cosliced v') (pw : cosliced w) (Hypf : pv · f = pv') :
  luinv^{ Mon_V }_{ I_{ Mon_V}} · pv ⊗^{ Mon_V} pw · f ⊗^{ Mon_V}_{r} w =
  luinv^{ Mon_V }_{ I_{ Mon_V}} · pv' ⊗^{ Mon_V} pw.
Proof.
  rewrite assoc'.
  apply maponpaths.
  rewrite <- Hypf.
  do 2 rewrite (bifunctor_equalwhiskers Mon_V).
  unfold functoronmorphisms2.
  rewrite assoc'.
  apply maponpaths.
  apply pathsinv0, (bifunctor_rightcomp Mon_V).
Qed.

Definition monoidal_pointed_objects_disp_tensor_data
  : disp_bifunctor_data Mon_V cosliced cosliced cosliced.
Proof.
  use make_disp_bifunctor_data.
  - intros v w pv pw. exact (luinv^{Mon_V}_{I_{Mon_V}} · pv ⊗^{Mon_V} pw).
  - exact monoidal_pointed_objects_disp_tensor_data_aux1.
  - exact monoidal_pointed_objects_disp_tensor_data_aux2.
Defined.

Definition monoidal_pointed_objects_disp_tensor : disp_tensor cosliced Mon_V.
Proof.
  use make_disp_bifunctor_locally_prop.
  - apply coslice_cat_disp_locally_prop.
  - exact monoidal_pointed_objects_disp_tensor_data.
Defined.

Lemma cosliced_groupoidal : groupoidal_disp_cat cosliced.
Proof.
  intros x y f Hf xx yy ff.
  use tpair.
  - cbn in *.
    rewrite <- ff.
    rewrite assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    apply (z_iso_inv_after_z_iso (make_z_iso' f Hf)).
  - split; apply coslice_cat_disp_locally_prop.
Qed.

Lemma monoidal_pointed_objects_disp_data_verif :
  disp_leftunitor_data monoidal_pointed_objects_disp_tensor (identity I_{Mon_V})
    × disp_rightunitor_data monoidal_pointed_objects_disp_tensor (identity I_{Mon_V})
    × disp_associator_data monoidal_pointed_objects_disp_tensor.
Proof.
  split3.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite (bifunctor_rightid Mon_V).
    rewrite id_left.
    rewrite assoc'.
    rewrite monoidal_leftunitornat.
    rewrite assoc.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite (bifunctor_leftid Mon_V).
    rewrite id_right.
    rewrite assoc'.
    rewrite monoidal_rightunitornat.
    rewrite assoc.
    rewrite <- unitors_coincide_on_unit.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v w u pv pw pu. cbn.
    rewrite assoc'.
    apply maponpaths.
    unfold functoronmorphisms1.
    rewrite !(bifunctor_rightcomp Mon_V).
    rewrite !(bifunctor_leftcomp Mon_V).
    rewrite !assoc'.
    rewrite <- monoidal_associatornatleft.
    rewrite !assoc.
    apply cancel_postcomposition.
    rewrite !assoc'.
    rewrite <- (monoidal_associatornatleftright Mon_V).
    rewrite !assoc.
    apply cancel_postcomposition.
    apply (z_iso_inv_to_right _ _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, monoidal_triangle_identity_inv. }
    rewrite <- !(bifunctor_rightcomp Mon_V).
    apply maponpaths.
    rewrite unitorsinv_coincide_on_unit.
    apply monoidal_rightunitorinvnat.
Qed.

Definition monoidal_pointed_objects_disp_data : disp_monoidal_data cosliced Mon_V.
Proof.
  use make_disp_monoidal_data_groupoidal.
  - exact cosliced_groupoidal.
  - exact monoidal_pointed_objects_disp_tensor.
  - apply identity.
  - apply monoidal_pointed_objects_disp_data_verif.
  - apply monoidal_pointed_objects_disp_data_verif.
  - apply monoidal_pointed_objects_disp_data_verif.
Defined.

Definition monoidal_pointed_objects_disp : disp_monoidal cosliced Mon_V.
Proof.
  apply make_disp_monoidal_locally_prop.
  - apply coslice_cat_disp_locally_prop.
  - exact monoidal_pointed_objects_disp_data.
Defined.

Definition monoidal_pointed_objects : monoidal (coslice_cat_total V I_{Mon_V})
  := total_monoidal monoidal_pointed_objects_disp.
Definition forget_monoidal_pointed_objects_data
  : fmonoidal_data monoidal_pointed_objects Mon_V (pr1_category cosliced).
Proof.
  split; try intro; intros; apply identity.
Defined.

Definition forget_monoidal_pointed_objects_monoidal_generic
  : fmonoidal monoidal_pointed_objects Mon_V (pr1_category cosliced)
  := projection_fmonoidal monoidal_pointed_objects_disp.

(** we develop a hand-crafted version since that one came first historically and is still used subsequently *)
Lemma forget_monoidal_pointed_objects_laxlaws
  : fmonoidal_laxlaws forget_monoidal_pointed_objects_data.
Proof.
  split5; intro; intros.
  - rewrite id_left; apply id_right.
  - rewrite id_left; apply id_right.
  - do 2 rewrite id_right. cbn.
    rewrite (bifunctor_leftid Mon_V).
    rewrite (bifunctor_rightid Mon_V).
    rewrite id_right; apply id_left.
  - cbn. rewrite (bifunctor_rightid Mon_V). rewrite id_left. apply id_left.
  - cbn. rewrite (bifunctor_leftid Mon_V). rewrite id_left. apply id_left.
Qed.

Definition forget_monoidal_pointed_objects_lax_monoidal
  : fmonoidal_lax monoidal_pointed_objects Mon_V (pr1_category cosliced)
  := forget_monoidal_pointed_objects_data,,forget_monoidal_pointed_objects_laxlaws.

Definition forget_monoidal_pointed_objects_monoidal_stronglaws
  : fmonoidal_stronglaws
      (fmonoidal_preservestensordata forget_monoidal_pointed_objects_lax_monoidal)
      (fmonoidal_preservesunit forget_monoidal_pointed_objects_lax_monoidal).
Proof.
  split; try intro; intros; apply identity_is_z_iso.
Defined.

Definition forget_monoidal_pointed_objects_monoidal
  : fmonoidal monoidal_pointed_objects Mon_V (pr1_category cosliced)
  := forget_monoidal_pointed_objects_lax_monoidal
     ,,
     forget_monoidal_pointed_objects_monoidal_stronglaws.

End A.

Section PointedObjectFixpoint.

  (* Let V be a monoidal category.
     In this section we construct functors (in both directions)
     between the monoidal category of monoidal-pointed objects of V,
     (i.e. the coslice category under the unit object of V)
     and the category of monoidal-pointed objects of the category of monoidal-pointed objects of V.
     The constructions in this section are used to show that
     taking the category of monoidal-pointed objects is idempotent.
   *)

  Local Definition ptd_ob {V : category} (Mon_V : monoidal V) : category
    := coslice_cat_total V I_{ Mon_V}.

  Local Definition ptd_ob_mon {V : category} (Mon_V : monoidal V) : monoidal (ptd_ob Mon_V)
    := monoidal_pointed_objects Mon_V.

  Context {V : category} (Mon_V : monoidal V).

  Definition ptdob_to_ptdptdob_data
    : functor_data (ptd_ob Mon_V) (ptd_ob (ptd_ob_mon Mon_V)).
  Proof.
    use make_functor_data.
    - intro f.
      exists f.
      exists (pr2 f).
      apply id_left.
    - intros f g α.
      exists α.
      use total2_paths_f.
      2: { apply homset_property. }
      exact (pr2 α).
  Defined.

  Definition ptdob_to_ptdptdob_is_functor
    : is_functor ptdob_to_ptdptdob_data.
  Proof.
    split.
    - intro.
      use total2_paths_f.
      2: { apply homset_property. }
      apply idpath.
    - intro ; intros.
      use total2_paths_f.
      2: { apply homset_property. }
      apply idpath.
  Qed.

  Definition ptdob_to_ptdptdob
    : functor (ptd_ob Mon_V) (ptd_ob (ptd_ob_mon Mon_V))
    := ptdob_to_ptdptdob_data ,, ptdob_to_ptdptdob_is_functor.

  Definition ptdptdob_to_ptdob_data
    : functor_data (ptd_ob (ptd_ob_mon Mon_V)) (ptd_ob Mon_V).
  Proof.
    use make_functor_data.
    - exact (λ f, pr1 f).
    - exact (λ _ _ α, pr1 α).
  Defined.

  Definition ptdptdob_to_ptdob_is_functor
    : is_functor ptdptdob_to_ptdob_data.
  Proof.
    repeat split.
  Qed.

  Definition ptdptdob_to_ptdob
    : functor (ptd_ob (ptd_ob_mon Mon_V)) (ptd_ob Mon_V)
    := ptdptdob_to_ptdob_data ,, ptdptdob_to_ptdob_is_functor.

  Definition unit_ptdob_data
    : nat_trans_data
        (functor_identity (ptd_ob Mon_V))
        (functor_composite ptdob_to_ptdptdob ptdptdob_to_ptdob).
  Proof.
    intro v.
    exists (identity _).
    abstract (apply id_right).
  Defined.

  Definition unit_ptdob_is_nat_trans
    : is_nat_trans _ _ unit_ptdob_data.
  Proof.
    intro ; intros.
    use total2_paths_f.
    2: { apply homset_property. }
    simpl.
    rewrite id_left.
    apply id_right.
  Qed.

  Definition unit_ptdob
    : nat_trans
        (functor_identity (ptd_ob Mon_V))
        (functor_composite ptdob_to_ptdptdob ptdptdob_to_ptdob)
    := unit_ptdob_data ,, unit_ptdob_is_nat_trans.

  Definition counit_ptdob_data
    : nat_trans_data
        (functor_composite ptdptdob_to_ptdob ptdob_to_ptdptdob)
        (functor_identity (ptd_ob (ptd_ob_mon Mon_V))).
  Proof.
    intro v.
    exists (identity _).
    abstract (use total2_paths_f ;
    [ simpl ;
      rewrite (! pr22 v) ;
      rewrite id_right ;
      apply id_left
    | apply homset_property ]).
  Defined.

  Definition counit_ptdob_is_nat_trans
    : is_nat_trans _ _ counit_ptdob_data.
  Proof.
    intro ; intros.
    use total2_paths_f.
    2: { apply homset_property. }
    use total2_paths_f.
    2: { apply homset_property. }
    cbn.
    rewrite id_left.
    apply id_right.
  Qed.

  Definition counit_ptdob
    : nat_trans
        (functor_composite ptdptdob_to_ptdob ptdob_to_ptdptdob)
        (functor_identity (ptd_ob (ptd_ob_mon Mon_V)))
    := counit_ptdob_data ,, counit_ptdob_is_nat_trans.

End PointedObjectFixpoint.

Section PointedObjectFixpointMonoidal.

  (* In this section, we show that the data defined in the previous section "PointedObjectFixpoint" is monoidal *)

  Context {V : category} (Mon_V : monoidal V).

  Definition ptdptdob_to_ptdob_fmonoidal_data
    : fmonoidal_data
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptd_ob_mon Mon_V)
        (ptdptdob_to_ptdob Mon_V).
  Proof.
    split.
    - intros f g.
      exists (identity _).
      abstract (apply id_right).
    - exists (identity _).
      abstract (apply id_right).
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal_data
    : fmonoidal_data
        (ptd_ob_mon Mon_V)
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptdob_to_ptdptdob Mon_V).
  Proof.
    split.
    - intros f g.
      exists (identity _).
      abstract (
          use total2_paths_f ;
          [ apply id_right | apply homset_property ]
        ).
    - exists (identity _).
      abstract (
          use total2_paths_f ;
          [ apply id_right | apply homset_property ]
        ).
  Defined.

  Lemma ptdptdob_to_ptdob_fmonoidal_laxlaws
    : fmonoidal_laxlaws ptdptdob_to_ptdob_fmonoidal_data.
  Proof.
    repeat split ; (intro ; intros ; use total2_paths_f ; [ cbn | apply homset_property ]).
    - rewrite id_left ; apply id_right.
    - rewrite id_left ; apply id_right.
    - rewrite (bifunctor_rightid Mon_V).
      rewrite (bifunctor_leftid Mon_V).
      rewrite ! id_left.
      rewrite ! id_right.
      apply idpath.
    - rewrite id_right.
      rewrite (bifunctor_rightid Mon_V).
      apply id_left.
    - rewrite id_right.
      rewrite (bifunctor_leftid Mon_V).
      apply id_left.
  Qed.

  Lemma ptdob_to_ptdptdob_fmonoidal_laxlaws
    : fmonoidal_laxlaws ptdob_to_ptdptdob_fmonoidal_data.
  Proof.
    repeat split ; (intro ; intros ; use total2_paths_f ; [ use total2_paths_f ; cbn | apply homset_property ]).
    - rewrite id_left ; apply id_right.
    - apply homset_property.
    - rewrite id_left ; apply id_right.
    - apply homset_property.
    - rewrite (bifunctor_rightid Mon_V).
      rewrite (bifunctor_leftid Mon_V).
      rewrite ! id_left.
      rewrite ! id_right.
      apply idpath.
    - apply homset_property.
    - rewrite id_right.
      rewrite (bifunctor_rightid Mon_V).
      apply id_left.
    - apply homset_property.
    - rewrite id_right.
      rewrite (bifunctor_leftid Mon_V).
      apply id_left.
    - apply homset_property.
  Qed.

  Definition ptdptdob_to_ptdob_fmonoidal_lax
    : fmonoidal_lax
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptd_ob_mon Mon_V)
        (ptdptdob_to_ptdob Mon_V).
  Proof.
    exists ptdptdob_to_ptdob_fmonoidal_data.
    exact ptdptdob_to_ptdob_fmonoidal_laxlaws.
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal_lax
    : fmonoidal_lax
        (ptd_ob_mon Mon_V)
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptdob_to_ptdptdob Mon_V).
  Proof.
    exists ptdob_to_ptdptdob_fmonoidal_data.
    exact ptdob_to_ptdptdob_fmonoidal_laxlaws.
  Defined.

  Definition ptdptdob_to_ptdob_fmonoidal_stronglaws
    : fmonoidal_stronglaws
        (fmonoidal_preservestensordata ptdptdob_to_ptdob_fmonoidal_lax)
        (fmonoidal_preservesunit ptdptdob_to_ptdob_fmonoidal_lax).
  Proof.
    split ; (
              (try intro ; intros) ;
              repeat (use tpair) ;
              [ exact (identity _)
              | abstract (apply id_right)
              | abstract (use total2_paths_f ;
                [ apply id_right | apply homset_property ])
              | abstract (use total2_paths_f ;
                [ apply id_right | apply homset_property ])
              ]).
  Defined.

(** TODO: separate data and their verification that should be opaque *)
  Definition ptdob_to_ptdptdob_fmonoidal_stronglaws
    : fmonoidal_stronglaws
        (fmonoidal_preservestensordata ptdob_to_ptdptdob_fmonoidal_lax)
        (fmonoidal_preservesunit ptdob_to_ptdptdob_fmonoidal_lax).
  Proof.
    split; (
              (try intro ; intros) ;
              repeat (use tpair) ;
              [ exact (identity _)
              | apply id_right
              | abstract (use total2_paths_f ;
                [ apply id_right | apply homset_property ])
              | abstract (
                    use total2_paths_f ;
                    [ use total2_paths_f ; [apply id_right | apply V] | apply homset_property ]
                  )
              | abstract (
                    use total2_paths_f ;
                    [ use total2_paths_f ; [apply id_right | apply V] | apply homset_property ])
              ]).
  Defined.


  Definition ptdptdob_to_ptdob_fmonoidal
    : fmonoidal
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptd_ob_mon Mon_V)
        (ptdptdob_to_ptdob Mon_V).
  Proof.
    exists ptdptdob_to_ptdob_fmonoidal_lax.
    exact ptdptdob_to_ptdob_fmonoidal_stronglaws.
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal
    : fmonoidal
        (ptd_ob_mon Mon_V)
        (ptd_ob_mon (ptd_ob_mon Mon_V))
        (ptdob_to_ptdptdob Mon_V).
  Proof.
    exists ptdob_to_ptdptdob_fmonoidal_lax.
    exact ptdob_to_ptdptdob_fmonoidal_stronglaws.
  Defined.
End PointedObjectFixpointMonoidal.
