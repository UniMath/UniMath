(** * Grothendick toposes *)
(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.

Local Open Scope cat.

Section def_grothendiecktopos.

  Variable C : category.

  (** Here (pr1 D) is the precategory which is equivalent to the precategory of sheaves on the
      Grothendieck topology (pr2 D). *)
  Definition Grothendieck_topos : UU :=
    ∑ D : category × Grothendieck_topology C,
      adj_equiv (pr1 D) (sheaf_cat (pr2 D)).

  (** Accessor functions *)
  Coercion Grothendieck_topos_category (GT : Grothendieck_topos) : category :=
    pr11 GT.

  Definition Grothendieck_topos_Grothendieck_topology (GT : Grothendieck_topos) :
    Grothendieck_topology C := pr21 GT.

  Definition Grothendieck_topos_functor (GT : Grothendieck_topos) :
    functor GT (sheaf_cat (Grothendieck_topos_Grothendieck_topology GT)) :=
    pr2 GT.

  Definition Grothendieck_topos_equivalence (GT : Grothendieck_topos) :
    adj_equivalence_of_cats (Grothendieck_topos_functor GT) := pr2 GT.

End def_grothendiecktopos.
