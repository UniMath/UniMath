(* ************************************************************************* *)
(** Discreteness for Bicategories.                                           *)
(* ************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.

Local Open Scope cat.

Definition isaprop_2cells
           (B : bicat)
  : UU
  := ∏ (x y : B)
       (f g : x --> y)
       (α β : f ==> g),
     α = β.

Definition is_discrete_bicat
           (B : bicat)
  : UU
  := is_univalent_2_1 B
     ×
     locally_groupoid B
     ×
     isaprop_2cells B.

(**
 Discrete bicategory from a category
 *)
Definition isaprop_2cells_discrete_bicat
           (C : category)
  : isaprop_2cells (discrete_bicat C).
Proof.
  intro ; intros.
  apply homset_property.
Qed.

Definition locally_groupoid_discrete_bicat
           (C : category)
  : locally_groupoid (discrete_bicat C).
Proof.
  intros x y f g α.
  use make_is_invertible_2cell.
  - exact (!α).
  - apply isaprop_2cells_discrete_bicat.
  - apply isaprop_2cells_discrete_bicat.
Defined.

Definition is_univalent_2_1_discrete_bicat
           (C : category)
  : is_univalent_2_1 (discrete_bicat C).
Proof.
  intros x y f g.
  use gradth.
  - exact (λ p, pr1 p).
  - abstract
      (intro p ; cbn ;
       apply homset_property).
  - abstract
      (intro p ;
       use subtypePath ;
       [ intro ;
         apply isaprop_is_invertible_2cell
       | apply homset_property ]).
Defined.

Definition discrete_bicat_is_discrete_bicat
           (C : category)
  : is_discrete_bicat (discrete_bicat C).
Proof.
  repeat split.
  - exact (is_univalent_2_1_discrete_bicat C).
  - exact (locally_groupoid_discrete_bicat C).
  - exact (isaprop_2cells_discrete_bicat C).
Defined.

(**
 Category from a discrete bicategory
 *)
Definition discrete_bicat_to_precategory_data
           {B : bicat}
           (HB : is_discrete_bicat B)
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact B.
    + exact (λ x y, x --> y).
  - exact (λ x, id₁ x).
  - exact (λ x y z f g, f · g).
Defined.

Definition discrete_bicat_is_precategory
           {B : bicat}
           (HB : is_discrete_bicat B)
  : is_precategory (discrete_bicat_to_precategory_data HB).
Proof.
  use make_is_precategory.
  - intros x y f.
    use (isotoid_2_1 (pr1 HB)).
    apply lunitor_invertible_2cell.
  - intros x y f.
    use (isotoid_2_1 (pr1 HB)).
    apply runitor_invertible_2cell.
  - intros w x y z f g h.
    use (isotoid_2_1 (pr1 HB)).
    apply lassociator_invertible_2cell.
  - intros w x y z f g h.
    use (isotoid_2_1 (pr1 HB)).
    apply rassociator_invertible_2cell.
Qed.

Definition discrete_bicat_to_precategory
           {B : bicat}
           (HB : is_discrete_bicat B)
  : precategory.
Proof.
  use make_precategory.
  - exact (discrete_bicat_to_precategory_data HB).
  - exact (discrete_bicat_is_precategory HB).
Defined.

Definition discrete_bicat_locally_set
           {B : bicat}
           (HB : is_discrete_bicat B)
           (x y : B)
  : isaset (x --> y).
Proof.
  intros f g.
  use (isofhlevelweqb _ (make_weq (idtoiso_2_1 f g) (pr1 HB _ _ f g))).
  use invproofirrelevance.
  intros α β.
  use subtypePath.
  {
    intro.
    apply isaprop_is_invertible_2cell.
  }
  apply HB.
Qed.

Definition discrete_bicat_to_category
           {B : bicat}
           (HB : is_discrete_bicat B)
  : category.
Proof.
  use make_category.
  - exact (discrete_bicat_to_precategory HB).
  - exact (discrete_bicat_locally_set HB).
Defined.

(**
 Adjoint equivalences in discrete bicategories
 *)
Definition discrete_left_adj_equiv_to_z_iso
           {B : bicat}
           (HB : is_discrete_bicat B)
           {x y : B}
           {f : x --> y}
           (Hf : left_adjoint_equivalence f)
  : @is_z_isomorphism (discrete_bicat_to_category HB) x y f.
Proof.
  exists (left_adjoint_right_adjoint Hf).
  split.
  + abstract
      (use (isotoid_2_1 (pr1 HB)) ;
       exact (inv_of_invertible_2cell (left_equivalence_unit_iso Hf))).
  + abstract
      (use (isotoid_2_1 (pr1 HB)) ;
       exact (left_equivalence_counit_iso Hf)).
Defined.

Definition z_iso_to_discrete_left_adj_equiv
           {B : bicat}
           (HB : is_discrete_bicat B)
           {x y : B}
           {f : x --> y}
           (Hf : @is_z_isomorphism (discrete_bicat_to_category HB) x y f)
  : left_adjoint_equivalence f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
  - exact (inv_from_z_iso (make_z_iso' _ Hf)).
  - abstract
      (apply idtoiso_2_1 ;
       refine (!_) ;
       exact (z_iso_inv_after_z_iso (make_z_iso' _ Hf))).
  - abstract
      (apply idtoiso_2_1 ;
       exact (z_iso_after_z_iso_inv (make_z_iso' _ Hf))).
  - apply HB.
  - apply HB.
  - apply HB.
  - apply HB.
Defined.

Definition discrete_left_adj_equiv_weq_z_iso
           {B : bicat}
           (HB : is_discrete_bicat B)
           (x y : B)
  : @z_iso (discrete_bicat_to_category HB) x y ≃ adjoint_equivalence x y.
Proof.
  use make_weq.
  - exact (λ f, _ ,, z_iso_to_discrete_left_adj_equiv HB (pr2 f)).
  - use gradth.
    + exact (λ f, make_z_iso' _ (discrete_left_adj_equiv_to_z_iso HB f)).
    + abstract
        (intro Hf ;
         use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
         apply idpath).
    + abstract
        (intro Hf ;
         use subtypePath ;
         [ intro ;
           apply isaprop_left_adjoint_equivalence ;
           apply HB
         | ] ;
         apply idpath).
Defined.

Definition discrete_bicat_univalent_2_0
           {B : bicat}
           (HB : is_discrete_bicat B)
           (H : is_univalent (discrete_bicat_to_category HB))
  : is_univalent_2_0 B.
Proof.
  intros x y.
  use weqhomot.
  - exact (discrete_left_adj_equiv_weq_z_iso HB x y ∘ make_weq _ (H x y))%weq.
  - abstract
      (intro p ;
       induction p ;
       use subtypePath ;
       [ intro ;
         apply isaprop_left_adjoint_equivalence ;
         apply HB
       | ] ;
       apply idpath).
Defined.

Definition discrete_bicat_to_category_is_univalent
           {B : bicat}
           (HB : is_discrete_bicat B)
           (H : is_univalent_2_0 B)
  : is_univalent (discrete_bicat_to_category HB).
Proof.
  intros x y.
  use weqhomot.
  - exact (invweq (discrete_left_adj_equiv_weq_z_iso HB x y) ∘ make_weq _ (H x y))%weq.
  - abstract
      (intro p ;
       induction p ;
       use subtypePath ;
       [ intro ;
         apply isaprop_is_z_isomorphism
       | ] ;
       apply idpath).
Defined.

Definition discrete_bicat_weq_univalence
           {B : bicat}
           (HB : is_discrete_bicat B)
  : is_univalent_2_0 B ≃ is_univalent (discrete_bicat_to_category HB).
Proof.
  use weqimplimpl.
  - exact (discrete_bicat_to_category_is_univalent HB).
  - exact (discrete_bicat_univalent_2_0 HB).
  - apply isaprop_is_univalent_2_0.
  - apply isaprop_is_univalent.
Defined.
