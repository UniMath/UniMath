(** the coslice category I/V for a monoidal category is again monoidal

The coslice objects have a morphism from the monoidal unit I to an object of V. Since I is often not a terminal object 1 of V,
one cannot speak of pointed objects here; I suggest to call them monoidal-pointed objects.

author: Ralph Matthes 2022
 *)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.coslicecat.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section A.

Context {V : category} (Mon_V : monoidal V).

Let cosliced : disp_cat V := coslice_cat_disp V I_{ Mon_V}.

Definition monoidal_pointed_objects_disp_tensor_data : disp_bifunctor_data Mon_V cosliced cosliced cosliced.
Proof.
  use make_disp_bifunctor_data.
  - intros v w pv pw. exact (luinv^{Mon_V}_{I_{ Mon_V}} · pv ⊗^{Mon_V} pw).
  - intros v w w' g pv pw pw' Hypg. cbn in Hypg. cbn.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- Hypg.
    unfold functoronmorphisms1.
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0, bifunctor_leftcomp.
  - intros v v' w f pv pv' pw Hypf. cbn.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- Hypf.
    do 2 rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    rewrite assoc'.
    apply maponpaths.
     apply pathsinv0, bifunctor_rightcomp.
Defined.

Lemma monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor : is_disp_bifunctor monoidal_pointed_objects_disp_tensor_data.
Proof.
  repeat split; red; intros; apply V.
Qed.

Definition monoidal_pointed_objects_disp_tensor : disp_tensor cosliced Mon_V
  := monoidal_pointed_objects_disp_tensor_data,,monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor.

Lemma monoidal_pointed_objects_disp_data_verif :
  disp_leftunitor_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_leftunitorinv_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_rightunitor_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_rightunitorinv_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_associator_data monoidal_pointed_objects_disp_tensor
    × disp_associatorinv_data monoidal_pointed_objects_disp_tensor.
Proof.
  repeat split; red.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_rightid.
    rewrite id_left.
    rewrite assoc'.
    rewrite monoidal_leftunitornat.
    rewrite assoc.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v pv. cbn.
    rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    rewrite bifunctor_rightid.
    rewrite id_right.
    rewrite monoidal_leftunitorinvnat.
    apply idpath.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    rewrite assoc'.
    rewrite monoidal_rightunitornat.
    rewrite assoc.
    rewrite <- unitors_coincide_on_unit.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    rewrite <- monoidal_rightunitorinvnat.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply unitorsinv_coincide_on_unit.
  - intros v w u pv pw pu. cbn.
    rewrite assoc'.
    apply maponpaths.
    unfold functoronmorphisms1.
    repeat rewrite bifunctor_rightcomp.
    repeat rewrite bifunctor_leftcomp.
    repeat rewrite assoc'.
    rewrite <- monoidal_associatornatleft.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat rewrite assoc'.
    rewrite <- monoidal_associatornatleftright.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply (z_iso_inv_to_right _ _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, monoidal_triangle_identity_inv. }
    repeat rewrite <- bifunctor_rightcomp.
    apply maponpaths.
    rewrite unitorsinv_coincide_on_unit.
    apply monoidal_rightunitorinvnat.
  - intros v w u pv pw pu. cbn.
    rewrite assoc'.
    apply maponpaths.
    repeat rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    repeat rewrite bifunctor_rightcomp.
    repeat rewrite bifunctor_leftcomp.
    repeat rewrite assoc'.
    rewrite monoidal_associatorinvnatright.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat rewrite assoc'.
    rewrite monoidal_associatorinvnatleftright.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { rewrite unitorsinv_coincide_on_unit.
         apply maponpaths.
         apply monoidal_triangle_identity_inv. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat rewrite <- bifunctor_leftcomp.
    apply maponpaths.
    apply monoidal_leftunitorinvnat.
Qed.

Definition monoidal_pointed_objects_disp_data : disp_monoidal_data cosliced Mon_V.
Proof.
  exists monoidal_pointed_objects_disp_tensor.
  use tpair.
  - apply identity.
  - exact monoidal_pointed_objects_disp_data_verif.
Defined.

Lemma monoidal_pointed_objects_disp_laws : disp_monoidal_laws monoidal_pointed_objects_disp_data.
Proof.
  red; repeat split; try red; intros; apply V.
Qed.

Definition monoidal_pointed_objects_disp : disp_monoidal cosliced Mon_V
  := monoidal_pointed_objects_disp_data,,monoidal_pointed_objects_disp_laws.

Definition monoidal_pointed_objects : monoidal (coslice_cat_total V I_{Mon_V})
  := total_monoidal monoidal_pointed_objects_disp.

Definition forget_monoidal_pointed_objects_data : fmonoidal_data monoidal_pointed_objects Mon_V (pr1_category cosliced).
Proof.
  split; red; intros; cbn; apply identity.
Defined.

Lemma forget_monoidal_pointed_objects_laxlaws : fmonoidal_laxlaws forget_monoidal_pointed_objects_data.
Proof.
  repeat split; red; intros; cbn.
  - rewrite id_left; apply id_right.
  - rewrite id_left; apply id_right.
  - do 2 rewrite id_right.
    rewrite bifunctor_leftid.
    rewrite bifunctor_rightid.
    rewrite id_right; apply id_left.
  - rewrite bifunctor_rightid. rewrite id_left. apply id_left.
  - rewrite bifunctor_leftid. rewrite id_left. apply id_left.
Qed.

Definition forget_monoidal_pointed_objects_lax_monoidal : fmonoidal_lax monoidal_pointed_objects Mon_V (pr1_category cosliced)
  := forget_monoidal_pointed_objects_data,,forget_monoidal_pointed_objects_laxlaws.

Definition forget_monoidal_pointed_objects_monoidal : fmonoidal monoidal_pointed_objects Mon_V (pr1_category cosliced).
Proof.
  exists forget_monoidal_pointed_objects_lax_monoidal.
  split; red; intros; apply identity_is_z_iso.
Defined.

End A.

Section CosliceToCosliceRecursive.

  Local Definition ptd_ob {V : category} (Mon_V : monoidal V)
    := coslice_cat_total V I_{ Mon_V}.

  Local Definition ptd_ob_mon {V : category} (Mon_V : monoidal V)
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

  Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

  Definition unit_ptdob_data
    : nat_trans_data
        (functor_identity (ptd_ob Mon_V))
        (functor_composite ptdob_to_ptdptdob ptdptdob_to_ptdob).
  Proof.
    intro v.
    exists (identity _).
    apply id_right.
  Defined.

  Definition unit_ptdob_is_nat_trans
    : is_nat_trans _ _ unit_ptdob_data.
  Proof.
    intro ; intros.
    use total2_paths_f.
    2: { apply homset_property. }
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
    [
      simpl ;
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

End CosliceToCosliceRecursive.

Section CosliceToCosliceRecursiveMonoidal.

  Context {V : category} (Mon_V : monoidal V).

  Definition ptdptdob_to_ptdob_fmonoidal_data
    : fmonoidal_data (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptd_ob_mon Mon_V) (ptdptdob_to_ptdob Mon_V).
  Proof.
    split.
    - intros f g.
      exists (identity _).
      apply id_right.
    - exists (identity _).
      apply id_right.
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal_data
    : fmonoidal_data (ptd_ob_mon Mon_V) (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptdob_to_ptdptdob Mon_V).
  Proof.
    split.
    - intros f g.
      exists (identity _).
      use total2_paths_f.
      2: { apply homset_property. }
      apply id_right.
    - exists (identity _).
      use total2_paths_f.
      2: { apply homset_property. }
      apply id_right.
  Defined.

  Lemma ptdptdob_to_ptdob_fmonoidal_laxlaws
    : fmonoidal_laxlaws ptdptdob_to_ptdob_fmonoidal_data.
  Proof.
    repeat split ; (intro ; intros ; use total2_paths_f ; [ cbn | apply homset_property ]).
    - rewrite id_left ; apply id_right.
    - rewrite id_left ; apply id_right.
    - rewrite bifunctor_rightid.
      rewrite bifunctor_leftid.
      rewrite ! id_left.
      rewrite ! id_right.
      apply idpath.
    - rewrite id_right.
      rewrite bifunctor_rightid.
      apply id_left.
    - rewrite id_right.
      rewrite bifunctor_leftid.
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
    - rewrite bifunctor_rightid.
      rewrite bifunctor_leftid.
      rewrite ! id_left.
      rewrite ! id_right.
      apply idpath.
    - apply homset_property.
    - rewrite id_right.
      rewrite bifunctor_rightid.
      apply id_left.
    - apply homset_property.
    - rewrite id_right.
      rewrite bifunctor_leftid.
      apply id_left.
    - apply homset_property.
  Qed.

  Definition ptdptdob_to_ptdob_fmonoidal_lax
    : fmonoidal_lax (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptd_ob_mon Mon_V) (ptdptdob_to_ptdob Mon_V).
  Proof.
    exists ptdptdob_to_ptdob_fmonoidal_data.
    exact ptdptdob_to_ptdob_fmonoidal_laxlaws.
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal_lax
    : fmonoidal_lax (ptd_ob_mon Mon_V) (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptdob_to_ptdptdob Mon_V).
  Proof.
    exists ptdob_to_ptdptdob_fmonoidal_data.
    exact ptdob_to_ptdptdob_fmonoidal_laxlaws.
  Defined.

  Definition ptdptdob_to_ptdob_fmonoidal_stronglaws
    : fmonoidal_stronglaws (fmonoidal_preservestensordata ptdptdob_to_ptdob_fmonoidal_lax)
                           (fmonoidal_preservesunit ptdptdob_to_ptdob_fmonoidal_lax).
  Proof.
    split ; (
              (try intro ; intros) ;
              repeat (use tpair) ;
              [ exact (identity _)
              | apply id_right
              | use total2_paths_f ;
                [ apply id_right | apply homset_property ]
              | use total2_paths_f ;
                [ apply id_right | apply homset_property ]
              ]).
  Qed. (* Could be defined, but not necessairy for me *)

  Definition ptdob_to_ptdptdob_fmonoidal_stronglaws
    : fmonoidal_stronglaws (fmonoidal_preservestensordata ptdob_to_ptdptdob_fmonoidal_lax)
                           (fmonoidal_preservesunit ptdob_to_ptdptdob_fmonoidal_lax).
  Proof.
    split ; (
              (try intro ; intros) ;
              repeat (use tpair) ;
              [ exact (identity _)
              | apply id_right
              | use total2_paths_f ;
                [ apply id_right | apply homset_property ]
              | use total2_paths_f ;
                [ apply id_right | apply homset_property ]
              | use total2_paths_f ;
                [ apply id_right | apply homset_property ]
              ]).
  Qed. (* Could be defined, but not necessairy for me *)

  Definition ptdptdob_to_ptdob_fmonoidal
    : fmonoidal (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptd_ob_mon Mon_V) (ptdptdob_to_ptdob Mon_V).
  Proof.
    exists ptdptdob_to_ptdob_fmonoidal_lax.
    exact ptdptdob_to_ptdob_fmonoidal_stronglaws.
  Defined.

  Definition ptdob_to_ptdptdob_fmonoidal
    : fmonoidal (ptd_ob_mon Mon_V) (ptd_ob_mon (ptd_ob_mon Mon_V)) (ptdob_to_ptdptdob Mon_V).
  Proof.
    exists ptdob_to_ptdptdob_fmonoidal_lax.
    exact ptdob_to_ptdptdob_fmonoidal_stronglaws.
  Defined.

End CosliceToCosliceRecursiveMonoidal.
