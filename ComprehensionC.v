
(** * Displayed category from a category with display maps

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

Definition is_cartesian_functor_over {C C' : Precategory} {F : functor C C'}
           {D : disp_precat C} {D' : disp_precat C'} (FF : functor_over F D D') : UU
  := Π  {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d),
     is_cartesian ff -> is_cartesian (#FF ff).



Section fix_category.

Context {C : Precategory}.

Definition comprehension_cat : UU 
  := Σ (D : disp_precat C) (H : is_fibration D)
     (F : functor_over (functor_identity _ ) D (cod_disp C)),
     is_cartesian_functor_over F.


Variable (H : dm_sub_pb C).

Let X : disp_precat C := DM_disp H.

Let Y : disp_precat C := cod_disp C.

Definition U_data : functor_over_data (functor_identity C) X Y.
Proof.
  use tpair.
  + intros x d. cbn in *.
    exact (pr1 d).
  + cbn. intros. 
    exact X0.
Defined.

Definition U_prop : functor_over_axioms U_data.
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

Definition U : functor_over _ _ _ := _ ,, U_prop.

Definition totalU : functor _ _ := total_functor U.

Lemma comprehensionC_triangle_commutes 
: functor_composite totalU (pr1_precat _) = pr1_precat _ . 
Proof. 
  apply subtypeEquality.
  { intro. apply isaprop_is_functor. apply homset_property. }
  apply idpath.
Qed.

(*
Lemma foo : is_cartesian_functor_over U.
Proof.
  intros c c' f d d' ff G.
  cbn in *.
  intros c'' g d'' hh.
  destruct d as [[d k] H1].
  destruct d' as [[d' k'] H2].
  cbn in *.
  destruct ff as [f' H3].
  cbn in *.
  unfold is_cartesian in G. cbn in G.
  destruct d'' as [d'' k''].
  cbn in *.
  destruct hh as [h H4]. cbn in *.

Lemma foo : is_cartesian_functor_over U.
Proof.
  intros c c' f d d' ff G.
  cbn in *.
  intros c'' g d'' hh.
  specialize (G c'' g).
  transparent assert (XR : (X c'')).
  { cbn.  unfold DM_over. 
    use tpair.
    - use tpair.
      + use (@pb_ob_of_DM _ H _ _ d' _ g).
      + cbn. use (@pb_mor_of_DM _ H _ _ d' _ g).
    - cbn.    
      apply (pr2 (@pb_DM_of_DM _ H _ _ _ _ _ )).
  } 
  specialize (G XR).
  cbn in G.
  
  * 
    pb_DM_of_DM
  apply G.
Abort.  
*)

End fix_category.


