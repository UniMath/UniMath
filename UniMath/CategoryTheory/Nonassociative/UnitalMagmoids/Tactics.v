(********************************************************************************

 Tactics for Unital Magmoids

 Author: B. Szilvasy
 October 2026

 Provides the [submagmoid] tactic and [unital_magmoid] hint database
 for inferring [is_{linear,positive,...}] from submagmoids.  Use the
 notation [ummsolve] for an expression that requires a proof.

 Contents:
 1. The [unital_magmoid] tactic

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** The [unital_magmoid] tactic *)

Section mor_hints.
  Context {M : unital_magmoid} (a b : M).
  Definition is_linear_l_mor (f : a -->{_l} b) : is_linear f := submm_mor_property _l f.
  Definition is_thunkable_t_mor (f : a -->{_t} b) : is_thunkable f := submm_mor_property _t f.
  Definition is_intermediate_i_mor (f : a -->{_i} b) : is_intermediate f := submm_mor_property _i f.
  Definition is_linear_lt_mor (f : a -->{_lt} b) : is_linear f := pr1 (submm_mor_property _lt f).
  Definition is_thunkable_lt_mor (f : a -->{_lt} b) : is_thunkable f := pr2 (submm_mor_property _lt f).
  Definition is_linear_lti_mor (f : a -->{_lti} b) : is_linear f := pr11 (submm_mor_property _lti f).
  Definition is_thunkable_lti_mor (f : a -->{_lti} b) : is_thunkable f := pr21 (submm_mor_property _lti f).
  Definition is_intermediate_lti_mor (f : a -->{_lti} b) : is_intermediate f := pr2 (submm_mor_property _lti f).
End mor_hints.

Section ob_hints.
  Context {M : unital_magmoid}.
  Definition is_positive_p_ob (a : sub_ob M ^⊕) : is_positive a := sub_ob_property ^⊕ a.
  Definition is_negative_n_ob (a : sub_ob M ^⊖) : is_negative a := sub_ob_property ^⊖ a.
End ob_hints.

Create HintDb unital_magmoid.
Hint Resolve @is_linear_l_mor : unital_magmoid.
Hint Resolve @is_thunkable_t_mor : unital_magmoid.
Hint Resolve @is_intermediate_i_mor : unital_magmoid.
Hint Resolve @is_linear_lt_mor : unital_magmoid.
Hint Resolve @is_thunkable_lt_mor : unital_magmoid.
Hint Resolve @is_linear_lti_mor : unital_magmoid.
Hint Resolve @is_thunkable_lti_mor : unital_magmoid.
Hint Resolve @is_intermediate_lti_mor : unital_magmoid.
Hint Resolve @is_positive_p_ob : unital_magmoid.
Hint Resolve @is_negative_n_ob : unital_magmoid.

Ltac submagmoid :=
  repeat (assumption || split);
  solve
    [ apply is_linear_l_mor
    | apply is_thunkable_t_mor
    | apply is_intermediate_i_mor
    | apply is_linear_lt_mor
    | apply is_thunkable_lt_mor
    | apply is_linear_lti_mor
    | apply is_thunkable_lti_mor
    | apply is_intermediate_lti_mor
    | apply is_positive_p_ob
    | apply is_negative_n_ob ].
Notation ummsolve := ltac:(submagmoid) (only parsing).
