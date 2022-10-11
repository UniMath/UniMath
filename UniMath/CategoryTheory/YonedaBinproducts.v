(** ****************************************************************************

Yoneda commutes with binary products up to iso ([iso_yoneda_binproducts]).

Written by: Elisabeth Bonnevier, 2019

********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section iso_yoneda_binproducts.

Context {C : category} (PC : BinProducts C) (X Y : C).

Let yon : C ⟶ [C^op, HSET] := yoneda C.

(** First we create a natural transformation from Yon(X × Y) to Yon(X) × Yon(Y). *)
Definition yon_binprod_nat_trans_data :
  nat_trans_data (pr1 (yon (BinProductObject _ (PC X Y))))
                 (pr1 (BinProductObject _ (BinProducts_PreShv (yon X) (yon Y)))).
Proof.
  intros Z f.
  split; [exact (f · BinProductPr1 _ _) | exact (f · BinProductPr2 _ _)].
Defined.

Lemma is_nat_trans_yon_binprod : is_nat_trans _ _ yon_binprod_nat_trans_data.
Proof.
  intros Z W f.
  use funextfun; intro g.
  now apply dirprodeq; use assoc'.
Qed.

Definition yon_binprod_nat_trans :
  nat_trans (pr1 (yon (BinProductObject _ (_ X Y))))
            (pr1 (BinProductObject _ (BinProducts_PreShv (yon X) (yon Y)))) :=
  make_nat_trans _ _ _ is_nat_trans_yon_binprod.

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
Lemma yon_binprod_is_iso :
  @is_iso [C^op, HSET, has_homsets_HSET] _ _ yon_binprod_nat_trans.
Proof.
  use is_iso_from_is_z_iso.
  exists yon_binprod_inv_nat_trans.
  split; apply (nat_trans_eq has_homsets_HSET); intro Z; use funextfun; intro f.
  - cbn; unfold yon_binprod_nat_trans_data, yon_binprod_inv_nat_trans_data.
    now rewrite <- (BinProductArrowEta _ _ _ _ _ _).
  - use dirprodeq; cbn;
    unfold yon_binprod_inv_nat_trans_data;
    [use BinProductPr1Commutes | use BinProductPr2Commutes].
Qed.

(** The functors Yon(X × Y) and Yon(X) × Yon(Y) are isomorphic. *)
Lemma iso_yoneda_binproducts :
  iso (yon (BinProductObject _ (PC X Y)))
      (BinProductObject (PreShv _) (BinProducts_PreShv (yon X) (yon Y))).
Proof.
  use make_iso.
  - use yon_binprod_nat_trans.
  - use yon_binprod_is_iso.
Defined.

End iso_yoneda_binproducts.
