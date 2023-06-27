(* Defines the full subcategory of SET, consisting of the sets {0, ..., n-1} and their functions. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.

Definition finite_set_skeleton_precat : precategory.
Proof.
  use make_precategory.
  - use make_precategory_data.
    + use make_precategory_ob_mor.
      * exact nat.
      * exact (λ m n, stn m → stn n).
    + intro.
      exact (idfun _).
    + do 3 intro.
      exact funcomp.
  - do 3 split.
Defined.

Definition finite_set_skeleton_category : category.
Proof.
  use make_category.
  - exact finite_set_skeleton_precat.
  - do 2 intro.
    prove_hlevel 1.
    apply isasetstn.
Defined.
