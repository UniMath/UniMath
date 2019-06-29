(** ** (Co)limits in full subprecategories

If

 * C has (co)limits of shape F,
 * C' : ob C → UU is a proposition on the objects of C, and
 * C' is closed under the formation of (co)limits of shape F,

then the full subcategory on C'-objects has (co)limits of shape F.

Such proofs are mostly just a lot of insertions of

 * [precategory_object_from_sub_precategory_object]
 * [precategory_morphism_from_sub_precategory_morphism]

and their "inverses"

 * [precategory_morphisms_in_subcat]
 * [precategory_object_in_subcat].

Author: Langston Barrett (@siddharthist) (March 2018)

*)

(** ** Contents

- Limits
  - Binary products
- Colimits
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

(** ** The subcategory inclusion reflects limits *)

Corollary reflects_all_limits_sub_precategory_inclusion
          {C : precategory} (C' : hsubtype (ob C)) :
  reflects_all_limits (sub_precategory_inclusion C (full_sub_precategory C')).
Proof.
  apply fully_faithful_reflects_all_limits.
  apply fully_faithful_sub_precategory_inclusion.
Defined.

Section Limits.

(** ** Limits *)

(** *** Terminal objects *)

(** As long as the predicate holds for the terminal object, it's terminal in the full subcategory. *)
Lemma terminal_in_full_subcategory {C : precategory} (C' : hsubtype (ob C))
        (TC : Terminal C) (TC' : C' (TerminalObject TC)) :
  Terminal (full_sub_precategory C').
Proof.
  use tpair.
  - use precategory_object_in_subcat.
    + exact (TerminalObject TC).
    + assumption.
  - cbn.
    intros X.
    use make_iscontr.
    + use morphism_in_full_subcat.
      apply TerminalArrow.
    + intro; apply eq_in_sub_precategory; cbn.
      apply TerminalArrowUnique.
Defined.

(** *** Binary products *)

Lemma bin_products_in_full_subcategory {C : category} (C' : hsubtype (ob C))
      (BPC : BinProducts C)
      (all : ∏ c1 c2 : ob C, C' c1 -> C' c2 -> C' (BinProductObject _ (BPC c1 c2))) :
  BinProducts (full_sub_precategory C').
Proof.
  intros c1' c2'.
  pose (c1'_in_C := (precategory_object_from_sub_precategory_object _ _ c1')).
  pose (c2'_in_C := (precategory_object_from_sub_precategory_object _ _ c2')).
  use tpair; [use tpair|]; [|use make_dirprod|].
  - use precategory_object_in_subcat.
    + apply (BinProductObject _ (BPC c1'_in_C c2'_in_C)).
    + apply all.
      * exact (pr2 c1').
      * exact (pr2 c2').
  - use morphism_in_full_subcat; apply BinProductPr1.
  - use morphism_in_full_subcat; apply BinProductPr2.
  - cbn.
    unfold isBinProduct.
    intros bp' f g.
    use tpair.
    + use tpair.
      * use precategory_morphisms_in_subcat;
          [apply BinProductArrow|exact tt];
          apply (precategory_morphism_from_sub_precategory_morphism _ (full_sub_precategory C'));
          assumption.
      * cbn.
        use make_dirprod; apply eq_in_sub_precategory.
        { apply BinProductPr1Commutes. }
        { apply BinProductPr2Commutes. }
    + intros otherarrow.
      (** This is where we use the condition that C has homsets. *)
      apply subtypePath.
      { intro. apply isapropdirprod;
          apply is_set_sub_precategory_morphisms, homset_property.
      }
      {
        apply eq_in_sub_precategory.
        cbn.
        apply BinProductArrowUnique.
        - exact (maponpaths pr1 (dirprod_pr1 (pr2 otherarrow))).
        - exact (maponpaths pr1 (dirprod_pr2 (pr2 otherarrow))).
      }
Defined.

(** *** General limits *)

(** Lift a diagram from a full subcategory into the parent category *)
Definition lift_diagram_full_subcategory {C : precategory} {C' : hsubtype (ob C)} {g : graph}
      (d : diagram g (full_sub_precategory C')) :
  diagram g C.
Proof.
  use tpair.
  - intros v.
    apply (precategory_object_from_sub_precategory_object _ (full_sub_precategory C')).
    exact (dob d v).
  - intros u v e.
    apply (precategory_morphism_from_sub_precategory_morphism _ (full_sub_precategory C')).
    exact (dmor d e).
Defined.

(** Equivalence between cones in the parent category and those in the subcategory *)
Definition cone_in_full_subcategory {C : precategory} {g : graph} (C' : hsubtype (ob C))
      {d : diagram g (full_sub_precategory C')}
      (c : ob C)
      (tip : C' c) :
  cone (lift_diagram_full_subcategory d) c ≃ cone d (c,, tip).
Proof.
  unfold cone.
  use weqbandf.
  - apply weqonsecfibers; intros x.
    cbn beta.
    (** The following line works because of the computational behavior of
        [lift_diagram_full_subcategory], namely:
        <<
        (∏ v : vertex g, C' (dob (lift_diagram_full_subcategory d) v))
        → C' c
        → ∏ v : vertex g,
            pr1 (dob d v) = dob (lift_diagram_full_subcategory d) v
        >>
      *)
    apply (@weq_hom_in_subcat_from_hom_in_precat C C' (c,, tip) (dob d x)).
  - intro legs.
    cbn beta.
    apply weqonsecfibers; intros u;
      apply weqonsecfibers; intros v;
      apply weqonsecfibers; intros e.
    cbn.
    apply invweq.
    refine (subtypeInjectivity _ _ _ _).
    intro; apply propproperty.
Defined.

(** A full subcategory has a limit of a given shape if the proposition holds
    for the tip of the lifted limit diagram in the parent category. *)
Lemma lim_cone_in_full_subcategory {C : precategory} (C' : hsubtype (ob C))
      {g : graph} {d : diagram g (full_sub_precategory C')}
      (LC : Lims_of_shape g C) :
  C' (lim (LC (lift_diagram_full_subcategory d))) -> LimCone d.
Proof.
  intro.
  pose (Z := LC (lift_diagram_full_subcategory d)).
  unfold LimCone.
  use tpair.
  - use tpair.
    + use precategory_object_in_subcat.
      * eapply lim; eassumption.
      * assumption.
    + apply cone_in_full_subcategory, limCone.
  - apply (reflects_all_limits_sub_precategory_inclusion C' g d).
    apply (pr2 Z).
Qed.

(** ** Colimits *)

(** *** Initial objects *)

(** As long as the predicate holds for the initial object, it's initial in the full subcategory. *)
Lemma initial_in_full_subcategory {C : precategory} (C' : hsubtype (ob C))
      (IC : Initial C) (IC' : C' (InitialObject IC)) :
  Initial (full_sub_precategory C').
Proof.
  use tpair.
  - use precategory_object_in_subcat.
    + exact (InitialObject IC).
    + assumption.
  - cbn.
    intros X.
    use make_iscontr.
    + use morphism_in_full_subcat.
      apply InitialArrow.
    + intro; apply eq_in_sub_precategory; cbn.
      apply InitialArrowUnique.
Defined.

(** *** Binary coproducts *)

Lemma bin_coproducts_in_full_subcategory {C : category} (C' : hsubtype (ob C))
      (BPC : BinCoproducts C)
      (all : ∏ c1 c2 : ob C, C' c1 -> C' c2 -> C' (BinCoproductObject _ (BPC c1 c2))) :
  BinCoproducts (full_sub_precategory C').
Proof.
  intros c1' c2'.
  pose (c1'_in_C := (precategory_object_from_sub_precategory_object _ _ c1')).
  pose (c2'_in_C := (precategory_object_from_sub_precategory_object _ _ c2')).
  use tpair; [use tpair|]; [|use make_dirprod|].
  - use precategory_object_in_subcat.
    + apply (BinCoproductObject _ (BPC c1'_in_C c2'_in_C)).
    + apply all.
      * exact (pr2 c1').
      * exact (pr2 c2').
  - use morphism_in_full_subcat; apply BinCoproductIn1.
  - use morphism_in_full_subcat; apply BinCoproductIn2.
  - cbn.
    unfold isBinCoproduct.
    intros bp' f g.
    use tpair.
    + use tpair.
      * use precategory_morphisms_in_subcat;
          [apply BinCoproductArrow|exact tt];
          apply (precategory_morphism_from_sub_precategory_morphism _ (full_sub_precategory C'));
          assumption.
      * cbn.
        use make_dirprod; apply eq_in_sub_precategory.
        { apply BinCoproductIn1Commutes. }
        { apply BinCoproductIn2Commutes. }
    + intros otherarrow.
      (** This is where we use the condition that C has homsets. *)
      apply subtypePath.
      { intro. apply isapropdirprod;
          apply is_set_sub_precategory_morphisms, homset_property.
      }
      {
        apply eq_in_sub_precategory.
        cbn.
        apply BinCoproductArrowUnique.
        - exact (maponpaths pr1 (dirprod_pr1 (pr2 otherarrow))).
        - exact (maponpaths pr1 (dirprod_pr2 (pr2 otherarrow))).
      }
Defined.

End Limits.
