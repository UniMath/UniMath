(* ************************************************************************* *)
(** Discreteness for Bicategories.                                           *)
(* ************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Adjunctions.

Local Open Scope cat.

(* ------------------------------------------------------------------------- *)
(** Miscellanea.                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma is_z_isomorphism_weq_is_iso {C:category} {a b} (f : C⟦a,b⟧)
  : is_z_isomorphism f ≃ is_iso f.
Proof.
  apply weqimplimpl.
  - apply is_iso_from_is_z_iso.
  - apply is_z_iso_from_is_iso.
  - apply isaprop_is_z_isomorphism, C.
  - apply isaprop_is_iso.
Defined.

(* ------------------------------------------------------------------------- *)
(** Discrete space of 2-cells.                                               *)
(* ------------------------------------------------------------------------- *)

Definition idto2cell {C : prebicat_data} {a b} {f g : C⟦a,b⟧}
  : (f = g) → f ==> g
  := paths_rect (C ⟦ a, b ⟧)
                f
                (λ (g0 : C ⟦ a, b ⟧) (_ : f = g0), f ==> g0)
                (id₂ f)
                g.

Definition has_trivial_2cells (C : prebicat_data)
  : UU
  := ∏ a b (f g : C⟦a,b⟧), isweq (λ p : f = g, idto2cell p).

Definition has_trivial_2cells_equality {C : prebicat_data}
           (disc : has_trivial_2cells C)
           {a b} {f g : C⟦a,b⟧}
  : (f ==> g) -> (f = g)
  := invmap (make_weq (λ p : f = g, idto2cell p) (disc a b f g)).

Definition is_discrete_bicategory (C : prebicat_data)
  : UU
  :=   (∏ a b (f g : C⟦a,b⟧), isaprop (f ==> g))
     × has_trivial_2cells C.

Definition is_discrete_bicategory_cellprop {C : prebicat_data}
           (disc : is_discrete_bicategory C)
  : (∏ a b (f g : C⟦a,b⟧), isaprop (f ==> g))
  := pr1 disc.

Coercion is_discrete_bicategory_trivial_2cells {C : prebicat_data}
         (disc : is_discrete_bicategory C)
  : has_trivial_2cells C
  := pr2 disc.

(* ------------------------------------------------------------------------- *)
(** Discreteness of the discrete bicategory associated to a category.        *)
(* ------------------------------------------------------------------------- *)

Lemma has_trivial_2cells_discrete_prebicat (C : category)
  : has_trivial_2cells (discrete_prebicat C).
Proof.
  intros a b f g.
  use weqhomot.
  - exact (idweq (f = g)).
  - intro e. induction e. apply idpath.
Qed.

Lemma is_discrete_discrete_bicategory (C : category)
  : is_discrete_bicategory (discrete_prebicat C).
Proof.
  split.
  - intros. cbn in a, b, f, g. apply homset_property.
  - apply has_trivial_2cells_discrete_prebicat.
Qed.

(* ------------------------------------------------------------------------- *)
(** 1-category associated to a discrete bicategory.                          *)
(* ------------------------------------------------------------------------- *)

Definition precategory_of_discrete_bicategory {C : prebicat_data}
           (disc : is_discrete_bicategory C)
  : precategory.
Proof.
  use tpair.
  - exact C.
  - repeat split; intros; apply disc.
    + apply lunitor.
    + apply runitor.
    + apply lassociator.
    + apply rassociator.
Defined.

Lemma is_discrete_bicategory_has_homsets {C : prebicat_data}
      (disc : is_discrete_bicategory C)
  : has_homsets C.
Proof.
  intros a b f g.
  refine (isofhlevelweqb 1 _ _).
  - apply (make_weq idto2cell), disc.
  - apply (is_discrete_bicategory_cellprop disc).
Qed.

Definition category_of_discrete_bicategory {C : prebicat_data}
           (disc : is_discrete_bicategory C)
  : category.
Proof.
  use tpair.
  - exact (precategory_of_discrete_bicategory disc).
  - exact (is_discrete_bicategory_has_homsets disc).
Defined.

Lemma is_discrete_bicategory_iscontr_is_invertible_2cell {C : bicat}
      (disc : is_discrete_bicategory C)
      {a b : C} {f g : C ⟦ a, b ⟧}
      (x : f ==> g)
  : iscontr (is_invertible_2cell x).
Proof.
  induction (has_trivial_2cells_equality disc x).
  apply unique_exists with x.
  - split; apply (is_discrete_bicategory_cellprop disc).
  - intro. apply isapropdirprod; apply C.
  - intros. apply (is_discrete_bicategory_cellprop disc).
Qed.

Lemma is_adjointequivalence_discrete_weq_iso {C : bicat}
      (disc : is_discrete_bicategory C)
      {a b} (f : C⟦a,b⟧)
  : left_adjoint_equivalence f
    ≃
    is_iso (C := category_of_discrete_bicategory disc) f.
Proof.
  eapply weqcomp.
  2: apply is_z_isomorphism_weq_is_iso.
  unfold left_adjoint_equivalence, is_z_isomorphism.
  eapply weqcomp.
  { apply weqfibtototal. intro. apply weqdirprodcomm. }
  eapply weqcomp.
  { apply (weqtotal2asstol _
             (λ x : (∑ y : left_adjoint_data f, left_equivalence_axioms y),
               left_adjoint_axioms (pr1 x))). }
  eapply weqcomp.
  { apply weqpr1. induction z as [la le].
    apply (isofhleveldirprod 0); cbn; apply (is_discrete_bicategory_cellprop disc). }
  eapply weqcomp.
  { apply weqtotal2asstor. }
  apply weqfibtototal. intro g.
  unfold is_inverse_in_precat.
  eapply weqcomp.
  { apply weqpr1.
    induction z as [η ε].
    apply (isofhleveldirprod 0); cbn;
      apply (is_discrete_bicategory_iscontr_is_invertible_2cell disc). }
  apply weqdirprodf.
  { eapply weqcomp. 2: apply weqpathsinv0.
    apply invweq.
    apply (make_weq _ (is_discrete_bicategory_trivial_2cells disc _ _ _ _)). }
  apply invweq.
  apply (make_weq _ (is_discrete_bicategory_trivial_2cells disc _ _ _ _)).
Defined.