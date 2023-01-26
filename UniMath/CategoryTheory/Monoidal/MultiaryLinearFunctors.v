(** the morphisms of actegories extended to multiary functors *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section IAryLinearFunctors.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

Section TheDefinitions.

  Context {I: UU} {C : I -> category} {D : category} (ActC : ∏ i: I, actegory Mon_V (C i)) (ActD : actegory Mon_V D) (F: functor (product_category C) D).

  (** (Weak) Linear I-ary functors **)
  (* Linear  I-ary functor data *)

  Definition I_lineator_data : UU := ∏ (v : V) (x : product_category C), D ⟦ v ⊗_{ActD} F x, F (fun (i: I) => v ⊗_{ActC i} (x i)) ⟧.
  Identity Coercion I_lineator_data_funclass : I_lineator_data >-> Funclass.

  (** Properties **)
  Definition I_lineator_nat_left (ld : I_lineator_data)
    := ∏ (v : V) (x1 x2 : product_category C) (g : (product_category C)⟦x1,x2⟧),
      v ⊗^{ActD}_{l} # F g · ld v x2 = ld v x1 · # F (fun (i: I) => v ⊗^{ActC i}_{l} (g i)).

  Definition I_lineator_nat_right (ld : I_lineator_data)
    := ∏ (v1 v2 : V) (x : product_category C) (f : V⟦v1,v2⟧),
      f ⊗^{ActD}_{r} F x · ld v2 x = ld v1 x · # F (fun (i: I) => f ⊗^{ActC i}_{r} (x i)).

  Definition I_preserves_unitor (ld : I_lineator_data)
    := ∏ (x : product_category C), ld I_{Mon_V} x · # F (fun (i: I) => au^{ActC i}_{x i}) = au^{ActD}_{F x}.

  Definition I_preserves_unitorinv (ld : I_lineator_data)
    := ∏ (x : product_category C), auinv^{ActD}_{F x} · ld I_{Mon_V} x = # F (fun (i: I) => auinv^{ActC i}_{x i}).

  Definition I_preserves_actor (ld : I_lineator_data) : UU :=
    ∏ (v w : V) (x : product_category C),  ld (v ⊗_{Mon_V} w) x · #F (fun (i: I) => aα^{ActC i}_{v,w,x i}) =
                            aα^{ActD}_{v,w,F x} · v ⊗^{ActD}_{l} (ld w x) · ld v (fun (i: I) => w ⊗_{ActC i} (x i)).

  Definition I_preserves_actorinv  (ld : I_lineator_data) : UU :=
    ∏ (v w : V) (x : product_category C), aαinv^{ActD}_{v,w,F x} · ld (v ⊗_{Mon_V} w) x =
                           v ⊗^{ActD}_{l} (ld w x) · ld v (fun (i: I) => w ⊗_{ActC i} (x i)) · #F (fun (i: I) => aαinv^{ActC i}_{v,w,x i}).

  (* the order of the entries follows that of [fmonoidal_laxlaws] *)
  Definition I_lineator_laxlaws (ld : I_lineator_data) : UU :=
    I_lineator_nat_left ld × I_lineator_nat_right ld × I_preserves_actor ld × I_preserves_unitor ld.

  Lemma isaprop_I_lineator_laxlaws (ld : I_lineator_data) : isaprop (I_lineator_laxlaws ld).
  Proof.
    apply isapropdirprod; [| apply isapropdirprod ; [| apply isapropdirprod]];
      repeat (apply impred; intro); apply D.
  Qed.

  Definition I_lineator_lax : UU := ∑ (ld : I_lineator_data), I_lineator_laxlaws ld.

End TheDefinitions.

End IAryLinearFunctors.
