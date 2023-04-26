(*
Definition of the "three category" of a category C, i.e.
the category of diagrams of shape A --> B --> C
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Three_disp.

Context (C : category).

(* Can't use SIP since morphism data is not propositional (∑-type)
   For example in SET, we could have a map in
   the arrow category sending everything to one element, factorize
   it through (self, id), we may have multiple morphisms in the middle,
   so long as the one element maps properly... 
   
   So we have to do things the long way: *)
Definition three_disp_ob_mor : disp_cat_ob_mor (arrow C).
Proof.
  use make_disp_cat_ob_mor.
  - exact ((λ xy, ∑ z (xz : (arrow_dom xy) --> z) (zy : z --> (arrow_cod xy)), xz · zy = arrow_mor xy)).
  - (* double commutative square *)
    simpl.
    intros xy ab H0 H1 fff.
    destruct H0 as [z [xz [zy]]].
    destruct H1 as [c [ac [cb]]].
    destruct fff as [[f0 f1]].
    exact (∑ (f : z --> c), (xz · f = f0 · ac) × (zy · f1 = f · cb)).
Defined.

Definition three_id_comp : disp_cat_id_comp _ three_disp_ob_mor.
Proof.
  split.
  - simpl.
    intros.
    (* middle morphism is also identity *)
    exists (identity _).
    split; now rewrite id_left, id_right.
  - simpl.
    intros.
    destruct X as [f0 [H0 H1]].
    destruct X0 as [g0 [K0 K1]].
    (* middle map of composite is composite of middle maps *)
    exists (f0 · g0).
    split.
    * rewrite assoc, H0, <- assoc.
      etrans. apply maponpaths.
      exact K0.
      now rewrite assoc.
    * rewrite <- assoc, <- K1, assoc, assoc.
      apply cancel_postcomposition.
      exact H1.
Defined.

Definition three_data : disp_cat_data _ :=
    (three_disp_ob_mor,, three_id_comp).

Definition three_axioms : disp_cat_axioms _ three_data.
Proof.
  repeat apply tpair; intros.
  (* very cool from CategoryTheory/DisplayedCats/Codomain.v: cod_disp_axioms *)
  - (* subtypePath: equality in ∑-types if pr2 is a predicate *)
    apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }

    (* left identity in base category *)
    simpl.
    etrans. apply id_left.

    destruct ff as [ff H].
    apply pathsinv0.
    
    (* todo: understand this *)
    etrans. 
    use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply id_right.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply assoc.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> w)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply isaset_total2.
    * apply homset_property.
    * intro.
      apply isasetdirprod; apply isasetaprop; apply homset_property.    
Defined.

Definition three_disp : disp_cat (arrow C) :=
    (three_data,, three_axioms).

Definition three : category := total_category three_disp.

End Three_disp.

Definition three_ob0 {C : category} (xyz : three C) : C := pr111 xyz.
Definition three_ob1 {C : category} (xyz : three C) : C := pr12 xyz.
Definition three_ob2 {C : category} (xyz : three C) : C := pr211 xyz.
Definition three_mor01 {C : category} (xyz : three C) := pr122 xyz.
Definition three_mor12 {C : category} (xyz : three C) := pr1 (pr222 xyz).
Definition three_mor02 {C : category} (xyz : three C) := arrow_mor (pr1 xyz).
Definition three_comp {C : category} (xyz : three C) := pr2 (pr222 xyz).
Definition three_mor00 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr111 fff.
Definition three_mor11 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr12 fff.
Definition three_mor22 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr211 fff.
Definition three_mor_comm {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr22 fff.
