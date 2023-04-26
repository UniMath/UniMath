(*
Definition of the arrow category given a category C
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

From Model Require Import morphism_class.
From Model.model Require Import wfs.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Arrow_Disp.

Context (C:category).

Definition arrow_base := category_binproduct C C.

Definition arrow_disp : disp_cat arrow_base.
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ xy, pr1 xy --> pr2 xy).
  - simpl.
    intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
  - simpl.
    intros.
    use homset_property.
  - simpl. 
    intros.
    now rewrite id_left, id_right.
  - simpl.
    intros.
    rewrite assoc, <- X.
    symmetry.
    now rewrite <- assoc, <- X0, assoc.
Defined.

Definition arrow : category := total_category arrow_disp.

End Arrow_Disp.

Definition arrow_dom {C : category} (f : arrow C) : C := pr11 f.
Definition arrow_cod {C : category} (f : arrow C) : C := pr21 f.
Coercion arrow_mor {C : category} (f : arrow C) := pr2 f.

Definition arrow_mor00 {C : category} {f g : arrow C} (F : f --> g) := pr11 F. 
Definition arrow_mor11 {C : category} {f g : arrow C} (F : f --> g) := pr21 F. 
Definition arrow_mor_comm {C : category} {f g : arrow C} (F : f --> g) := pr2 F. 

Coercion mor_to_arrow_ob {C : category} {x y : C} (f : x --> y) : arrow C :=
    (make_dirprod x y,, f).

Definition mors_to_arrow_mor {C : category} {a b x y : C} (f : a --> b) (g : x --> y) 
    (h : a --> x) (k : b --> y) (H : g ∘ h = k ∘ f) : (mor_to_arrow_ob f) --> (mor_to_arrow_ob g).
Proof.
  use tpair.
  - exact (make_dirprod h k).
  - exact H.
Defined.
