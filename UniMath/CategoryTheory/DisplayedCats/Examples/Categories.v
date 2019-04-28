(** * The category of categories, displayed over types *)

(** ** Contents

  - Definitions
    - [disp_precategories]: The displayed precategory of precategories
    - [disp_homtype_hlevel]: The displayed precategory of precategories with homtypes of hlevel [n]
    - [disp_categories]: The displayed precategory of categories
    - [disp_univalent_categories]: The displayed category of univalent categories
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.categories.Type.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

(** ** Definitions *)

(** *** [disp_precategories]: The displayed precategory of precategories *)

Definition disp_precategories : disp_precat type_precat.
  use tpair. (** TODO: constructor *)
  - use tpair. (** TODO: constructor *)
    + use make_disp_precat_ob_mor.
      * (** c.f. [precategory_ob_mor] *)
        intros ob; exact (ob -> ob -> UU).
      * (** c.f. [functor_data] *)
        intros obX ? homX homY f.
        exact (∏ x1 x2 : obX, homX x1 x2 -> homY (f x1) (f x2)).
    + use make_dirprod; cbn.
      * (** identity functor *)
        intros ? ? ? ? ?; assumption.
      * (** functor composition *)
        intros ? ? ? ? ? ? ? ? functor_mor_x_y functor_mor_y_z.
        intros x1 x2 f12.
        apply functor_mor_y_z.
        apply functor_mor_x_y.
        assumption.
  - use make_dirprod; [|use make_dirprod; [|use make_dirprod]]. (** TODO: constructor *)
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn.
      intros obX obY f homX homY.
  - use make_dirprod.

(** *** [disp_homtype_hlevel]: The displayed precategory of precategories with homtypes of hlevel [n] *)

Definition object_hlevel (n : nat) (C : precategory) : hProp :=
  make_hProp _ (isapropisofhlevel n (ob C)).

(* TODO: someday, [has_homsets] should be rephrased in terms of this *)
Definition homtype_hlevel (n : nat) (C : precategory) : hProp :=
  make_hProp (∏ a b : C, isofhlevel n (C ⟦ a, b ⟧))
            (impred _ _ (λ _, impred _ _ (λ _, isapropisofhlevel n _))).

(** *** [disp_categories]: The displayed precategory of categories *)
(** *** [disp_univalent_categories]: The displayed category of univalent categories *)