(*******************************************************************

 Comprehension bicategories

 In this file we define comprehension bicategories and properties
 of comprehension bicategories.

 1. Comprehension bicategories
 2. Variances of comprehension bicategories

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

(**
 1. Comprehension bicategories
 *)
Definition comprehension_bicat_structure
           (B : bicat)
  : UU
  := ∑ (D : disp_bicat B)
       (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B)),
     global_cleaving D × global_cartesian_disp_psfunctor χ.

Definition make_comprehension_bicat_structure
           (B : bicat)
           (D : disp_bicat B)
           (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B))
           (HD : global_cleaving D)
           (Hχ : global_cartesian_disp_psfunctor χ)
  : comprehension_bicat_structure B
  := D ,, χ ,, HD ,, Hχ.

(** Projections of a comprehension bicategory *)
Definition ty_of
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : disp_bicat B
  := pr1 comp_B.

Definition comp_of
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : disp_psfunctor (ty_of comp_B) (cod_disp_bicat B) (id_psfunctor B)
  := pr12 comp_B.

Definition ty_of_global_cleaving
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : global_cleaving (ty_of comp_B)
  := pr122 comp_B.

Definition comp_of_global_cartesian
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : global_cartesian_disp_psfunctor (comp_of comp_B)
  := pr222 comp_B.

(**
 2. Variances of comprehension bicategories
 *)
Definition is_covariant
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_opcleaving D
     × lwhisker_opcartesian D
     × rwhisker_opcartesian D
     × local_opcartesian_disp_psfunctor χ.

Definition is_contravariant
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_cleaving D
     × lwhisker_cartesian D
     × rwhisker_cartesian D
     × local_cartesian_disp_psfunctor χ.

Definition comprehension_bicat
  : UU
  := ∑ (B : bicat)
       (comp_B : comprehension_bicat_structure B),
     is_covariant comp_B.

Definition contravariant_comprehension_bicat
  : UU
  := ∑ (B : bicat)
       (comp_B : comprehension_bicat_structure B),
     is_contravariant comp_B.
