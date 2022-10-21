(* In this file we show that for any category C,
   the monoidal category of pointedfunctors of C is equivalent to
   the monoidal category of pointed-objects in the monoidal category of pointed functors of C.

   By equivalence, we mean that these two monoidal categories
   are (internally) equivalent as objects in the bicategory of monoidal categories
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.Bicategories.Core.Bicat.

(* The monoidal categories of endofunctors that we compare are defined in the following files: *)
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsWhiskeredMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.

(* The notion of internal adjoint equivalences in a bicategory is defined in: *)
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

(* The necessairy bicategories *)
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfWhiskeredMonCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.

Local Open Scope cat.

Section PointedFunctorsIdempotentGeneralMonoidalCats.

  Context {V : category} (Mon_V : monoidal V).

  Definition adj_equivalence_ptdfunctor_in_cat
    : adjoint_equivalence
        (B := bicat_of_cats)
        (coslice_cat_total V (monoidal_unit Mon_V))
        (coslice_cat_total (coslice_cat_total V (monoidal_unit Mon_V)) (monoidal_unit (monoidal_pointed_objects Mon_V))).
  Proof.
    use make_adjoint_equivalence.
    - exact (ptdob_to_ptdptdob Mon_V).
    - exact (ptdptdob_to_ptdob Mon_V).
    - exact (unit_ptdob Mon_V).
    - exact (counit_ptdob Mon_V).
    - use nat_trans_eq.
      { apply homset_property. }
      intro.
      use total2_paths_f.
      2: { apply homset_property. }
      use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      rewrite ! id_right.
      apply idpath.
    - use nat_trans_eq.
      { apply homset_property. }
      intro.
      use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      rewrite ! id_right.
      apply idpath.
    - repeat (use tpair).
      + intro.
        exists (identity _).
        apply id_right.
      + intro ; intros.
        use total2_paths_f.
        2: { apply homset_property. }
        etrans. { apply id_right. }
        apply (! id_left _).
      + apply nat_trans_eq.
        { apply homset_property. }
        intro.
        use total2_paths_f.
        2: { apply homset_property. }
        apply id_right.
      + apply nat_trans_eq.
        { apply homset_property. }
        intro.
        use total2_paths_f.
        2: { apply homset_property. }
        apply id_right.
    - repeat (use tpair).
      + intro.
        exists (identity _).
        use total2_paths_f.
        2: { apply homset_property. }
        simpl.
        rewrite (! pr22 x).
        rewrite id_left.
        apply id_right.
      + intro ; intros.
        use total2_paths_f.
        2: { apply homset_property. }
        etrans. { apply id_right. }
        apply (! id_left _).
      + apply nat_trans_eq.
        { apply homset_property. }
        intro.
        use total2_paths_f.
        2: { apply homset_property. }
        apply id_right.
      + apply nat_trans_eq.
        { apply homset_property. }
        intro.
        use total2_paths_f.
        2: { apply homset_property. }
        apply id_right.
  Defined.

  Definition disp_left_adjoint_data_ptdfunctor_in_moncat
    : disp_left_adjoint_data
            (D := bidisp_monbicat_disp_prebicat)
            adj_equivalence_ptdfunctor_in_cat
            (ptdob_to_ptdptdob_fmonoidal Mon_V).
  Proof.
    exists (ptdptdob_to_ptdob_fmonoidal Mon_V).
    split.
      + use tpair.
        * intro ; intros.
          abstract (
              use total2_paths_f ;
              [
                simpl ;
                rewrite bifunctor_leftid ;
                rewrite bifunctor_rightid ;
                rewrite ! id_right ;
                apply idpath
              | apply homset_property
              ]
            ).
        * abstract (use total2_paths_f ; [apply idpath | apply homset_property ]).
      + use tpair.
        * intro ; intros.
          abstract (
              use total2_paths_f ;
              [
                use total2_paths_f ;
                [
                  simpl ;
                  rewrite bifunctor_leftid ;
                  rewrite bifunctor_rightid ;
                  rewrite ! id_right ;
                  apply idpath
                | apply homset_property
                ]
              | apply homset_property
              ]
            ).
        * abstract (
              use total2_paths_f ;
              [
                use total2_paths_f ;
                [
                  simpl ;
                  rewrite ! id_right ;
                  apply idpath
                | apply homset_property
                ]
              | apply homset_property
              ]
            ).
  Defined.

  Lemma disp_left_adjoint_axioms_ptdfunctor_in_moncat
    :  disp_left_adjoint_axioms
         adj_equivalence_ptdfunctor_in_cat
         disp_left_adjoint_data_ptdfunctor_in_moncat.
  Proof.
    split.
        * use total2_paths_f.
          2: { apply homset_property. }
          repeat (apply funextsec ; intro).
          apply homset_property.
        * use total2_paths_f.
          2: { apply homset_property. }
          repeat (apply funextsec ; intro).
          apply homset_property.
  Qed.

  Lemma disp_left_equivalence_axioms_ptdfunctor_in_moncat
    :  disp_left_equivalence_axioms
         adj_equivalence_ptdfunctor_in_cat
         disp_left_adjoint_data_ptdfunctor_in_moncat.
  Proof.
    repeat (use tpair).
    - intro ; intro.
      use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      rewrite bifunctor_rightid.
      rewrite bifunctor_leftid.
      apply idpath.
    - use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      rewrite ! id_right.
      apply idpath.
    - use total2_paths_f.
      2: { apply homset_property. }
      repeat (apply funextsec ; intro).
      apply homset_property.
    - use total2_paths_f.
      2: { apply homset_property. }
      repeat (apply funextsec ; intro).
      apply homset_property.
    - intro ; intro.
      use total2_paths_f.
      2: { apply homset_property. }
      repeat (apply funextsec ; intro).
      use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      rewrite bifunctor_rightid.
      rewrite bifunctor_leftid.
      rewrite ! id_right.
      apply idpath.
    - use total2_paths_f.
      2: { apply homset_property. }
      use total2_paths_f.
      2: { apply homset_property. }
      simpl.
      apply idpath.
    - use total2_paths_f.
      2: { apply homset_property. }
      repeat (apply funextsec ; intro).
      apply homset_property.
    - use total2_paths_f.
      2: { apply homset_property. }
      repeat (apply funextsec ; intro).
      apply homset_property.
  Qed.

  Definition disp_adj_equivalence_ptdfunctor_in_moncat
    : disp_left_adjoint_equivalence
            (D := bidisp_monbicat_disp_prebicat)
            adj_equivalence_ptdfunctor_in_cat
             (ptdob_to_ptdptdob_fmonoidal Mon_V).
  Proof.
    exists disp_left_adjoint_data_ptdfunctor_in_moncat.
    exists disp_left_adjoint_axioms_ptdfunctor_in_moncat.
    exact disp_left_equivalence_axioms_ptdfunctor_in_moncat.
  Defined.

  Definition adj_equivalence_ptdfunctor_in_moncat
    : adjoint_equivalence
        (B := monbicat)
        (_ ,, monoidal_pointed_objects Mon_V)
        (_ ,, monoidal_pointed_objects (monoidal_pointed_objects Mon_V)).
  Proof.
    use (invmap (adjoint_equivalence_total_disp_weq _ _) _).
    exists adj_equivalence_ptdfunctor_in_cat.
    exists (ptdob_to_ptdptdob_fmonoidal Mon_V).
    exact disp_adj_equivalence_ptdfunctor_in_moncat.
  Defined.

End PointedFunctorsIdempotentGeneralMonoidalCats.

Definition adj_equivalence_ptdfunctor (C : category)
  : adjoint_equivalence
      (B := monbicat)
      (_ ,, pointedfunctors_moncat C)
      (_ ,, monoidal_pointed_objects (pointedfunctors_moncat C))
  := adj_equivalence_ptdfunctor_in_moncat (monoidal_of_endofunctors C).
