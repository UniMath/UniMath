
(** * Displayed Category from a category with display maps

Definition of the displayed category of display maps over a category [C]

Given a category with display maps [C], we define a displayed 
category over [C]. Objects over [c:C] are display maps into [c].

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Codomain.
Require Import TypeTheory.Displayed_Cats.Fibrations.
Require Import TypeTheory.Displayed_Cats.DisplayedCatFromCwDM.
Require Import TypeTheory.OtherDefs.DM.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** * Definition of a cartesian displayed functor *)

(* TODO: upstream to with definition of fibrations/cartesianness *)
Definition is_cartesian_functor_over
  {C C' : Precategory} {F : functor C C'}
  {D : disp_precat C} {D' : disp_precat C'} (FF : functor_over F D D') : UU
:= ∏  {c c' : C} {f : c' --> c}
      {d : D c} {d' : D c'} (ff : d' -->[f] d),
  is_cartesian ff -> is_cartesian (#FF ff).

Definition comprehension_cat_structure (C : Precategory) : UU 
  := ∑ (D : disp_precat C) (H : is_fibration D)
     (F : functor_over (functor_identity _ ) D (cod_disp C)),
     is_cartesian_functor_over F.

Arguments comprehension_cat_structure _ : clear implicits.

Section Comp_Cat_of_DM_Structure.

Context {C : Precategory}.

(* TODO: change name [dm_sub_pb] to something more comprehensible, e.g. [dm_struct]. *)
Variable (H : dm_sub_pb C).

Definition comprehension_of_dm_structure_data
  : functor_over_data (functor_identity C) (DM_disp H) (cod_disp C).
Proof.
  use tpair.
  + intros x d. cbn in *.
    exact (pr1 d).
  + cbn. intros x y xx yy f ff. 
    exact ff.
Defined.

Definition comprehension_of_dm_structure_axioms
  : functor_over_axioms comprehension_of_dm_structure_data.
Proof.
  cbn; repeat split; cbn.
  + intros.
    apply subtypeEquality.
    { intro. apply homset_property. }
    apply idpath.
  + intros.
    apply subtypeEquality.
    { intro. apply homset_property. }
    apply idpath.
Qed.

Definition comprehension_of_dm_structure
  : functor_over _ _ _ := _ ,, comprehension_of_dm_structure_axioms.

Lemma is_cartesian_comprehension_of_dm_structure
  : is_cartesian_functor_over comprehension_of_dm_structure.
Proof.
  (* sketch:
  - show that for a fubctor out of a (cloven) fibration, it’s enough to show that *some* (resp. the chosen) cartesian lifts are preserved
  - show that the chosen ones are preserved here, using [pullback_cartesian_in_cod_disp].
  *)
  intros c c' f d d' ff G.
  apply pullback_cartesian_in_cod_disp.
  try refine (isPullback_of_dm_sub_pb _ _ _).
Abort.

Definition total_comprehension_of_dm_structure
  : functor _ _ := total_functor comprehension_of_dm_structure.

Lemma comprehension_of_dm_structure_triangle_commutes 
: functor_composite total_comprehension_of_dm_structure (pr1_precat _)
  = pr1_precat _ . 
Proof. 
  apply subtypeEquality.
  { intro. apply isaprop_is_functor. apply homset_property. }
  apply idpath.
Qed.

End Comp_Cat_of_DM_Structure.



