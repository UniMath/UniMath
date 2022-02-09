(*********************************************************************

 Limits of univalent groupoids

 1. Pullbacks

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Open Scope cat.

(** 1. Pullbacks *)
Definition grpds_iso_comma_pb_cone
           {C₁ C₂ C₃ : grpds}
           (F : C₁ --> C₃)
           (G : C₂ --> C₃)
  : pb_cone F G.
Proof.
  use make_pb_cone.
  - exact (univalent_iso_comma (pr1 F) (pr1 G)
           ,,
           is_pregroupoid_iso_comma _ _ (pr2 C₁) (pr2 C₂)).
  - refine (_ ,, tt).
    apply iso_comma_pr1.
  - refine (_ ,, tt).
    apply iso_comma_pr2.
  - use make_invertible_2cell.
    + refine (_ ,, tt).
      apply iso_comma_commute.
    + apply locally_groupoid_grpds.
Defined.

Section IsoCommaUMP.
  Context {C₁ C₂ C₃ : grpds}
          (F : C₁ --> C₃)
          (G : C₂ --> C₃).

  Definition pb_ump_1_grpds_iso_comma
    : pb_ump_1 (grpds_iso_comma_pb_cone F G).
  Proof.
    intro q.
    use make_pb_1cell.
    - refine (_ ,, tt).
      use iso_comma_ump1.
      + exact (pr1 (pb_cone_pr1 q)).
      + exact (pr1 (pb_cone_pr2 q)).
      + exact (grpds_2cell_to_nat_iso (pr1 (pb_cone_cell q))).
    - use make_invertible_2cell.
      + refine (_ ,, tt).
        apply iso_comma_ump1_pr1.
      + apply locally_groupoid_grpds.
    - use make_invertible_2cell.
      + refine (_ ,, tt).
        apply iso_comma_ump1_pr2.
      + apply locally_groupoid_grpds.
    - abstract
        (use subtypePath ; [ intro ; apply isapropunit | ] ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ; unfold pb_cone_cell ;
         rewrite (functor_on_inv_from_iso (pr1 G)) ;
         rewrite (functor_id (pr1 F)) ;
         rewrite !id_left, id_right ;
         refine (!(id_right _) @ _) ;
         apply maponpaths ;
         use inv_iso_unique' ;
         unfold precomp_with ;
         cbn ;
         rewrite id_right ;
         apply functor_id).
  Defined.

  Section CellUMP.
    Let p := grpds_iso_comma_pb_cone F G.

    Context {q : grpds}
            (φ ψ : q --> p)
            (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
            (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
            (r : (φ ◃ pb_cone_cell p)
                 • lassociator _ _ _
                 • (β ▹ G)
                 • rassociator _ _ _
                 =
                 lassociator _ _ _
                 • (α ▹ F)
                 • rassociator _ _ _
                 • (ψ ◃ pb_cone_cell p)).

    Definition pb_ump_2_grpds_nat_trans
      : φ ==> ψ.
    Proof.
      refine (_ ,, tt).
      use (iso_comma_ump2 _ _ _ _ (pr1 α) (pr1 β)).
      abstract
        (intros x ;
         pose (nat_trans_eq_pointwise (maponpaths pr1 r) x) as z ;
         cbn in z ;
         unfold iso_comma_commute_nat_trans_data in z ;
         rewrite !id_left, !id_right in z ;
         exact z).
    Defined.

    Definition pb_ump_2_grpds_nat_trans_pr1
      : pb_ump_2_grpds_nat_trans ▹ pb_cone_pr1 _ = α.
    Proof.
      use subtypePath ; [ intro ; apply isapropunit | ].
      apply iso_comma_ump2_pr1.
    Qed.

    Definition pb_ump_2_grpds_nat_trans_pr2
      : pb_ump_2_grpds_nat_trans ▹ _ = β.
    Proof.
      use subtypePath ; [ intro ; apply isapropunit | ].
      apply iso_comma_ump2_pr2.
    Qed.
  End CellUMP.

  Definition pb_ump_2_grpds_iso_comma
    : pb_ump_2 (grpds_iso_comma_pb_cone F G).
  Proof.
    intros C φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use subtypePath ; [ intro ; apply isapropunit | ] ;
         exact (iso_comma_ump_eq
                  _ _ _ _ _ _
                  (maponpaths pr1 (pr12 τ₁))
                  (maponpaths pr1 (pr22 τ₁))
                  (maponpaths pr1 (pr12 τ₂))
                  (maponpaths pr1 (pr22 τ₂)))).
    - simple refine (_ ,, _).
      + exact (pb_ump_2_grpds_nat_trans φ ψ α β r).
      + split.
        * exact (pb_ump_2_grpds_nat_trans_pr1 φ ψ α β r).
        * exact (pb_ump_2_grpds_nat_trans_pr2 φ ψ α β r).
  Defined.

  Definition grpds_iso_comma_has_pb_ump
    : has_pb_ump (grpds_iso_comma_pb_cone F G).
  Proof.
    split.
    - exact pb_ump_1_grpds_iso_comma.
    - exact pb_ump_2_grpds_iso_comma.
  Defined.
End IsoCommaUMP.

Definition has_pb_grpds
  : has_pb grpds.
Proof.
  intros C₁ C₂ C₃ F G.
  simple refine (_ ,, _).
  - exact (grpds_iso_comma_pb_cone F G).
  - exact (grpds_iso_comma_has_pb_ump F G).
Defined.
