(** **********************************************************

Ralph Matthes

2021
*)

(** **********************************************************

Contents :

- build monoidal category for the pointed endofunctors

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.

Local Open Scope cat.

Section PointedFunctors_as_monoidal_category.

  Context {C : precategory}.
  Variable hs : has_homsets C.

  Local Notation "'Ptd'" := (precategory_Ptd C hs).

  Definition tensor_pointedfunctors:
    precategory_Ptd C hs ⊠ precategory_Ptd C hs ⟶ precategory_Ptd C hs.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro PF1PF2.
      induction PF1PF2 as [PF1 PF2].
      exact (ptd_composite C hs PF1 PF2).
    + intros PF1PF2 PF1'PF2' α1α2.
      induction α1α2 as [α1 α2].
      cbn in *.
      exists (horcomp α1 α2).
      red; intro c.
      cbn.
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        rewrite <- assoc.
        rewrite nat_trans_ax.
        rewrite assoc.
        apply cancel_postcomposition.
        apply ptd_mor_commutes.
      }
      rewrite <- assoc.
      rewrite <- functor_comp.
      etrans.
      { do 2 apply maponpaths.
        apply ptd_mor_commutes. }
      apply idpath.
  - split; red; cbn.
    + intro PF1PF2.
      (* UniMath.MoreFoundations.Tactics.show_id_type. *)
      apply eq_ptd_mor; try assumption.
      cbn.
      apply nat_trans_eq; try assumption; intro c.
      etrans.
      { apply horcomp_id_left. }
      apply idpath.
    + intros PF1PF2 PF1'PF2' PF1''PF2'' α1α2 α1'α2'.
      apply eq_ptd_mor; try assumption.
      cbn.
      apply nat_trans_eq; try assumption; intro c.
      cbn.
      repeat rewrite <- assoc.
      apply maponpaths.
      rewrite functor_comp.
      do 2 rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply nat_trans_ax.
Defined.

(** a preparation for the lemma afterwards *)
Lemma ptd_mor_z_iso_from_underlying_mor {F G : Ptd} (α : ptd_mor C F G):
  is_nat_z_iso(pr1 α) -> is_z_isomorphism(C:=Ptd) α.
Proof.
  intro Hyp.
  use tpair.
  - use tpair.
    apply nat_z_iso_to_trans_inv.
    + exact (_ ,, Hyp).
    + cbn. red; intro c.
      cbn.
      apply pathsinv0.
      apply (z_iso_inv_on_left _ _ _ _ (make_z_iso _ _ (Hyp c))).
      cbn.
      apply pathsinv0.
      apply ptd_mor_commutes.
  - red; split; apply eq_ptd_mor; try assumption; apply nat_trans_eq;
      try assumption; intro c; cbn.
    + apply (z_iso_inv_after_z_iso (make_z_iso _ _ (Hyp c))).
    + apply (z_iso_after_z_iso_inv (make_z_iso _ _ (Hyp c))).
Defined.

Definition left_unitor_of_pointedfunctors:
  left_unitor tensor_pointedfunctors (id_Ptd C hs).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro PF.
      exists (λ_functor (pr1 PF)).
      red; intro c.
      cbn.
      rewrite functor_id.
      rewrite id_right.
      apply id_right.
    * intros PF PF' α.
      apply eq_ptd_mor; try assumption.
      apply nat_trans_eq; try assumption.
      intro c. cbn.
      rewrite functor_id.
      rewrite id_left.
      do 2 rewrite id_right.
      apply idpath.
  + red. intro PF. cbn.
    apply ptd_mor_z_iso_from_underlying_mor.
    intro c.
    cbn.
    apply identity_is_z_iso.
Defined.

Definition right_unitor_of_pointedfunctors:
  right_unitor tensor_pointedfunctors (id_Ptd C hs).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro PF.
      exists (ρ_functor (pr1 PF)).
      red; intro c.
      cbn.
      rewrite id_right.
      apply id_left.
    * intros PF PF' α.
      apply eq_ptd_mor; try assumption.
      apply nat_trans_eq; try assumption.
      intro c. cbn.
      do 2 rewrite id_left.
      apply id_right.
  + red. intro PF. cbn.
    apply ptd_mor_z_iso_from_underlying_mor.
    intro c.
    cbn.
    apply identity_is_z_iso.
Defined.

Definition associator_of_pointedfunctors: associator tensor_pointedfunctors.
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro PFtriple.
      induction PFtriple as [[PF1 PF2] PF3].
      exists (α_functor (pr1 PF1) (pr1 PF2) (pr1 PF3)).
      red; intro c.
      cbn.
      rewrite id_right.
      rewrite functor_comp.
      apply assoc.
    * intros PFtriple PFtriple' αtriple.
      apply eq_ptd_mor; try assumption.
      apply nat_trans_eq; try assumption.
      intro c. cbn.
      rewrite id_right.
      rewrite id_left.
      rewrite functor_comp.
      rewrite <- assoc.
      apply idpath.
  + red. intro PFtriple. cbn.
    apply ptd_mor_z_iso_from_underlying_mor.
    intro c.
    cbn.
    apply identity_is_z_iso.
Defined.

Lemma triangle_eq_of_pointedfunctors:
  triangle_eq tensor_pointedfunctors (id_Ptd C hs)
              left_unitor_of_pointedfunctors
              right_unitor_of_pointedfunctors
              associator_of_pointedfunctors.
Proof.
  intros PF1 PF2.
  apply eq_ptd_mor; try assumption.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply nat_trans_eq; try assumption.
  intro c.
  cbn.
  do 3 rewrite id_left.
  apply idpath.
Qed.

Lemma pentagon_eq_of_pointedfunctors:
  pentagon_eq tensor_pointedfunctors associator_of_pointedfunctors.
Proof.
  intros PF1 PF2 PF3 PF4.
  apply eq_ptd_mor; try assumption.
  apply nat_trans_eq; try assumption.
  intro c.
  cbn.
  do 4 rewrite functor_id.
  do 5 rewrite id_left.
  apply idpath.
Qed.

Definition monoidal_precat_of_pointedfunctors: monoidal_precat.
Proof.
  use mk_monoidal_precat.
  - exact Ptd.
  - apply tensor_pointedfunctors.
  - apply id_Ptd.
  - exact left_unitor_of_pointedfunctors.
  - exact right_unitor_of_pointedfunctors.
  - exact associator_of_pointedfunctors.
  - exact triangle_eq_of_pointedfunctors.
  - exact pentagon_eq_of_pointedfunctors.
Defined.

Definition forgetful_functor_from_ptd_as_strong_monoidal_functor: strong_monoidal_functor monoidal_precat_of_pointedfunctors (monoidal_precat_of_endofunctors hs).
Proof.
  use tpair.
  - apply (mk_lax_monoidal_functor monoidal_precat_of_pointedfunctors (monoidal_precat_of_endofunctors hs) (functor_ptd_forget C hs) (nat_trans_id _) (nat_trans_id _)).
    + intros PF1 PF2 PF3.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      do 3 rewrite functor_id.
      rewrite assoc.
      apply idpath.
    + intro PF.
      split; apply nat_trans_eq; try assumption; intro c; cbn.
      * rewrite functor_id.
        do 3 rewrite id_right.
        apply idpath.
      * do 3 rewrite id_right.
        apply idpath.
  - split; [apply (nat_trafo_z_iso_if_pointwise_z_iso C C hs);
                       apply is_nat_z_iso_nat_trans_id
                      | apply (is_nat_z_iso_nat_trans_id ((functor_composite
          (PrecategoryBinProduct.pair_functor (functor_ptd_forget C hs) (functor_ptd_forget C hs))
          (functorial_composition C C C hs hs))))].
Defined.

End PointedFunctors_as_monoidal_category.
