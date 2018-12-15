(** * The displayed category of types of a given h-level *)

(** ** Contents

  - Definitions
    - [disp_hlevel]: The displayed category of types of [hlevel] n
    - [disp_prop]: The displayed category of propositions
    - [disp_HSET]: The displayed category of sets
  - Equivalence of the total category of [disp_HSET] with [HSET_univalent_category]
 *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

(** ** Definitions *)

(** *** [disp_hlevel]: The displayed category of types of [hlevel] n *)

Definition disp_hlevel (n : nat) : disp_precat type_precat :=
  disp_full_sub type_precat (isofhlevel n).

(** *** [disp_prop]: The displayed category of propositions *)

Definition disp_prop : disp_precat type_precat := disp_hlevel 1.

(** *** [disp_HSET]: The displayed category of sets *)

Definition disp_HSET : disp_precat type_precat := disp_hlevel 2.

(** ** Equivalence of the total category of [disp_HSET] with [HSET_univalent_category] *)

Definition disp_HSET_equiv_HSET_adjunction_data :
  adjunction_data (total_precategory disp_HSET) HSET_univalent_category.
Proof.
  use tpair; [|use tpair].
  - use mk_functor.
    + use mk_functor_data.
      * exact (idfun _).
      * intros ? ? f; exact (pr1 f).
    + split.
      * intro; reflexivity.
      * intros ? ? ?; reflexivity.
  - use mk_functor.
    + use mk_functor_data.
      * exact (idfun _).
      * intros ? ? f; exact (f,, tt).
    + split.
      * intro; reflexivity.
      * intros ? ? ?; reflexivity.
  - split.
    + use mk_nat_trans.
      * intros x.
        use tpair.
        -- exact (idfun _).
        -- exact tt.
      * (** [is_nat_trans] *)
        intros ? ? ?.
        apply subtypeEquality'.
        -- unfold funcomp; apply funextfun; intro; reflexivity.
        -- apply isapropunit.
    + use mk_nat_trans.
      * intros ?; exact (idfun _).
      * intros ? ? ?; apply funextfun; intro; reflexivity.
Defined.

(** The displayed category of sets over [type_precat] is equivalent to the
    direct definition of [HSET] as a category. *)
Lemma disp_HSET_equiv_HSET :
  forms_equivalence disp_HSET_equiv_HSET_adjunction_data.
Proof.
  split.
  - intros ?; apply identity_is_iso.
  - intros ?; apply identity_is_iso.
Qed.

Lemma disp_HSET_adj_equivalence_of_precats_left :
  adj_equivalence_of_precats (left_functor disp_HSET_equiv_HSET_adjunction_data).
Proof.
  use mk_adj_equivalence_of_precats.
  - exact (right_functor disp_HSET_equiv_HSET_adjunction_data).
  - exact (adjunit disp_HSET_equiv_HSET_adjunction_data).
  - exact (adjcounit disp_HSET_equiv_HSET_adjunction_data).
  - use mk_form_adjunction.
    + intro; reflexivity.
    + intro; reflexivity.
  - apply disp_HSET_equiv_HSET.
Defined.

Local Definition isaset' (X : UU) : hProp := (isaset X,, isapropisaset _).

Lemma has_homsets_disp_HSET : has_homsets (total_precategory disp_HSET).
Proof.
  intros ? ?.
  apply (equivalence_homtype_property (right_functor disp_HSET_equiv_HSET_adjunction_data) (adj_equivalence_of_precats_inv disp_HSET_adj_equivalence_of_precats_left) isaset' has_homsets_HSET).
Qed.