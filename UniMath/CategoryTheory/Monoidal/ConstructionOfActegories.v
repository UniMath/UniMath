(**
  Construction of actegories:
  - the monoidal category acting on itself
  - lifting an action from the target of a strong monoidal functor to its source

Reconstructs the results from [UniMath.Bicategories.MonoidalCategories.ConstructionOfActions]
in the whiskered setting.

author: Ralph Matthes 2022
 *)


Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
(* Import ActegoryNotations. *)

Section A.

Context {V : category} (Mon_V : monoidal V).

Definition action_on_itself: actegory Mon_V V.
Proof.
  use tpair.
  - use make_actegory_data.
    + exact (monoidal_tensor Mon_V).
    + exact (lu^{Mon_V}).
    + exact (luinv^{Mon_V}).
    + exact (α^{Mon_V}).
    + exact (αinv^{Mon_V}).
  - split; [| split; [| split]].
    + apply monoidal_leftunitorlaw.
    + apply monoidal_associatorlaw.
    + apply monoidal_triangleidentity.
    + apply monoidal_pentagonidentity.
Defined.

(* TODO: action lifting *)



End A.
