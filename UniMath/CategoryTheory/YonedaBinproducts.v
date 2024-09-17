(** ****************************************************************************

Yoneda commutes with binary products up to iso ([iso_yoneda_binproducts]).

Written by: Elisabeth Bonnevier, 2019

********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section iso_yoneda_binproducts.

Context {C : category} (PC : BinProducts C) (X Y : C).

Let yon : C ⟶ [C^op, HSET] := yoneda C.

(** First we create a natural transformation from Yon(X × Y) to Yon(X) × Yon(Y). *)
Definition yon_binprod_nat_trans
  : (yon (BinProductObject _ (PC X Y)) : _ ⟶ _)
    ⟹ (BinProductObject _ (BinProducts_PreShv (yon X) (yon Y)) : _ ⟶ _)
  := BinProductArrow _ _ (# yon (BinProductPr1 _ _)) (# yon (BinProductPr2 _ _)).

(** Second, we create a natural transformation from Yon(X) × Yon(Y) to Yon(X × Y). *)
Definition yon_binprod_inv_nat_trans_data :
  nat_trans_data (pr1 (BinProductObject _ (BinProducts_PreShv (yon X) (yon Y))))
                 (pr1 (yon (BinProductObject _ (PC X Y)))).
Proof.
  intros Z [f1 f2].
  exact (BinProductArrow _ (PC X Y) f1 f2).
Defined.

Lemma is_nat_trans_yon_binprod_inv : is_nat_trans _ _ yon_binprod_inv_nat_trans_data.
Proof.
  unfold yon_binprod_inv_nat_trans_data.
  intros Z W f.
  use funextfun; intros [g1 g2]; cbn.
  use BinProductArrowsEq; rewrite <- assoc.
  - now rewrite !BinProductPr1Commutes.
  - now rewrite !BinProductPr2Commutes.
Qed.

Definition yon_binprod_inv_nat_trans :
  nat_trans (pr1 (BinProductObject _ (BinProducts_PreShv (yon X) (yon Y))))
            (pr1 (yon (BinProductObject _ (_ X Y)))) :=
  make_nat_trans _ _ _ is_nat_trans_yon_binprod_inv.

(** We now show that the first transformation is an isomorphism by showing that the second
transformation is its inverse. *)
Lemma yon_binprod_is_inverse :
  is_inverse_in_precat (C := [C^op, HSET, has_homsets_HSET])
    yon_binprod_nat_trans
    yon_binprod_inv_nat_trans.
Proof.
  split;
  apply nat_trans_eq_alt;
  intro Z;
  apply funextfun;
  intro f.
  - symmetry.
    apply BinProductArrowEta.
  - apply dirprodeq.
    + apply BinProductPr1Commutes.
    + apply BinProductPr2Commutes.
Qed.

(** The functors Yon(X × Y) and Yon(X) × Yon(Y) are isomorphic. *)
Definition yon_binprod_z_iso
  : z_iso
    (yon (PC X Y))
    (@BinProducts_PreShv C (yon X) (yon Y))
  := make_z_iso (C := [C^op, HSET, has_homsets_HSET])
    yon_binprod_nat_trans
    yon_binprod_inv_nat_trans
    yon_binprod_is_inverse.

Definition iso_yoneda_binproducts :
  iso (yon (BinProductObject _ (PC X Y)))
      (BinProductObject (PreShv _) (BinProducts_PreShv (yon X) (yon Y)))
  := z_iso_to_iso yon_binprod_z_iso.

End iso_yoneda_binproducts.

Definition yoneda_preserves_binproduct
  (C : category)
  (BP : BinProducts C)
  : preserves_binproduct (yoneda C).
Proof.
  apply (preserves_binproduct_chosen_to_chosen BP BinProducts_PreShv).
  intros X Y.
  exact (z_iso_is_z_isomorphism (yon_binprod_z_iso BP X Y)).
Defined.
