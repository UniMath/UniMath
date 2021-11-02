(** *** Going into the opposite direction of [UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal] *)
(** We fix a bicategory and an object of it and construct the monoidal category of endomorphisms.

Written by Ralph Matthes in 2019.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.

Local Open Scope cat.
(*

Section Monoidal_Precat_From_Prebicat.

Local Open Scope bicategory_scope.
Import Bicat.Notations.

Context {C : bicat}.
Context (c0: ob C).

Definition precategory_data_from_prebicat_and_ob: precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (C⟦c0,c0⟧).
    + apply prebicat_cells.
  - intro c; apply id2.
  - intros a b c; apply vcomp2.
Defined.

Lemma is_precategory_data_from_prebicat_and_ob: is_precategory precategory_data_from_prebicat_and_ob.
Proof.
  use make_is_precategory.
  - intros a b f; apply id2_left.
  - intros a b f; apply id2_right.
  - intros a b c d f g h; apply vassocr.
  - intros a b c d f g h; apply pathsinv0; apply vassocr.
Qed.

Definition precategory_from_prebicat_and_ob: precategory := _,, is_precategory_data_from_prebicat_and_ob.

Local Notation EndC := precategory_from_prebicat_and_ob.

Definition tensor_from_prebicat_and_ob: precategory_from_prebicat_and_ob ⊠ precategory_from_prebicat_and_ob ⟶ precategory_from_prebicat_and_ob.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro ab.
      exact (pr1 ab · pr2 ab).
    + intros ab1 ab2 f.
      exact (hcomp (pr1 f) (pr2 f)).
  - abstract ( split; [ intro c; apply hcomp_identity |
                        intros a b c f g; apply hcomp_vcomp ] ).
Defined.

Local Notation tensor := tensor_from_prebicat_and_ob.

Local Definition build_left_unitor: left_unitor tensor (id c0).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro c.
      apply lunitor.
    * abstract ( intros a b f; apply lunitor_natural ).
  + intro c; apply is_z_iso_lunitor.
Defined.

Local Definition build_right_unitor: right_unitor tensor (id c0).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro c.
      apply runitor.
    * abstract ( intros a b f; apply runitor_natural ).
  + intro c; apply is_z_iso_runitor.
Defined.

Definition nat_trans_associator: assoc_left tensor ⟹ assoc_right tensor.
Proof.
  (* very slow with library elements:
  set (aux := rassociator_transf(C := C) c0 c0 c0 c0).
  set (aux' := pre_whisker (precategory_binproduct_unassoc _ _ _) aux).
  use mk_nat_trans.
  - intro c. exact (pr1 aux' c).
  - apply (pr2 aux').
   *)
  (* still very slow with new additions to library:
  set (aux := rassociator_transf'(C := C) c0 c0 c0 c0).
  use mk_nat_trans.
  - intro c. exact (pr1 aux c).
  - abstract ( apply (pr2 aux) ).
   *)
  (* now def. by Anders Mörtberg: *)
  exists rassociator_fun'.
  abstract (intros f g x; apply hcomp_rassoc).
Defined.

Local Definition build_associator: associator tensor.
Proof.
  use make_nat_z_iso.
  - exact nat_trans_associator.
  - intro c; apply is_z_iso_rassociator.
Defined.

Definition monoidal_precat_from_prebicat_and_ob: monoidal_precat.
Proof.
  use (mk_monoidal_precat precategory_from_prebicat_and_ob tensor_from_prebicat_and_ob (id c0) build_left_unitor build_right_unitor build_associator).
  - abstract ( intros a b; apply pathsinv0; apply unit_triangle ).
  - abstract ( intros a b c d; apply pathsinv0; apply associativity_pentagon ).
Defined.

End Monoidal_Precat_From_Prebicat.

Section AddHomsets.

Context {C : bicat}.
Context (c0: ob C).

Lemma precategory_from_prebicat_and_ob_has_homsets: has_homsets (precategory_from_prebicat_and_ob c0).
Proof.
  red. intros.
  apply (cellset_property(C:=C)).
Qed.

End AddHomsets.
 *)
