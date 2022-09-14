(** the coslice category I/V for a monoidal category is again monoidal

The coslice objects have a morphism from the monoidal unit I to an object of V. Since I is often not a terminal object 1 of V,
one cannot speak of pointed objects here; I suggest to call them monoidal-pointed objects.

author: Ralph Matthes 2022
 *)

Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
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
Admitted.

Lemma monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor : is_disp_bifunctor monoidal_pointed_objects_disp_tensor_data.
Proof.
Admitted.

Definition monoidal_pointed_objects_disp_tensor : disp_tensor cosliced Mon_V
  := monoidal_pointed_objects_disp_tensor_data,,monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor.

Definition monoidal_pointed_objects_disp_data : disp_monoidal_data cosliced Mon_V.
Proof.
  exists monoidal_pointed_objects_disp_tensor.
  use tpair.
  - apply identity.
  - repeat split; cbn.
    (* 6 goals to solve *)
Admitted.

Lemma monoidal_pointed_objects_disp_laws : disp_monoidal_laws monoidal_pointed_objects_disp_data.
Proof.
Admitted.

Definition monoidal_pointed_objects_disp : disp_monoidal cosliced Mon_V
  := monoidal_pointed_objects_disp_data,,monoidal_pointed_objects_disp_laws.

Definition monoidal_pointed_objects : monoidal (coslice_cat_total V I_{Mon_V})
  := total_monoidal monoidal_pointed_objects_disp.

End A.
