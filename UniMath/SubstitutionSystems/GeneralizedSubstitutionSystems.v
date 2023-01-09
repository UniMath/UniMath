(** a generalization of heterogeneous substitution systems to monoidal categories in place of endofunctor categories

author: Ralph Matthes 2022
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
(* Require Import UniMath.CategoryTheory.Core.Isos. *)
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
(* Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered. *)
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.


Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
(* Import ActegoryNotations. *)

Section hss.

  Context {V : category} (Mon_V : monoidal V).

  Local Definition PtdV : category := coslice_cat_total V I_{Mon_V}.
  Local Definition Mon_PtdV : monoidal PtdV := monoidal_pointed_objects Mon_V.

  Context (H : V ⟶ V).
  Context (θ : pointedtensorialstrength Mon_V H).

  Section TheProperty.

    Context (t : V) (η : I_{Mon_V} --> t) (τ : H t --> t).

  Definition gbracket_property_parts {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) : UU :=
    (ru^{Mon_V}_{z} · f = z ⊗^{Mon_V}_{l} η · h) ×
      (θ (z,,e) t · #H h · τ =  z ⊗^{Mon_V}_{l} τ · h).

  Definition gbracket_parts_at {z : V} (e : I_{Mon_V} --> z) (f : z --> t) : UU :=
    ∃! h : z ⊗_{Mon_V} t --> t, gbracket_property_parts e f h.

  Definition gbracket : UU :=
    ∏ (Z : PtdV) (f : pr1 Z --> t), gbracket_parts_at (pr2 Z) f.

  Lemma isaprop_gbracket : isaprop gbracket.
  Proof.
    apply impred_isaprop; intro Z.
    apply impred_isaprop; intro f.
    apply isapropiscontr.
  Qed.

  End TheProperty.

  Definition ghss : UU := ∑ (t : V) (η : I_{Mon_V} --> t) (τ : H t --> t), gbracket t η τ.
  Coercion carrierghss (t : ghss) : V := pr1 t.

  Definition eta_from_alg (t : ghss) : I_{Mon_V} --> t := pr12 t.
  Definition tau_from_alg (t : ghss) : H t --> t := pr122 t.

  Local Notation η := eta_from_alg.
  Local Notation τ := tau_from_alg.

  Definition gfbracket (t : ghss) (Z : PtdV) (f : pr1 Z --> t) : pr1 Z ⊗_{Mon_V} t --> t :=
    pr1 (pr1 (pr222 t Z f)).

  Notation "⦃ f ⦄_{ Z }" := (gfbracket _ Z f)(at level 0).

  Lemma gfbracket_unique (t : ghss) {Z : PtdV} (f : pr1 Z --> t)
    : ∏ α : pr1 Z ⊗_{Mon_V} t --> t, gbracket_property_parts t (η t) (τ t) (pr2 Z) f α
   → α = ⦃f⦄_{Z}.
  Proof.
    intros α Hyp.
    apply path_to_ctr.
    assumption.
  Qed.

  Lemma gfbracket_η (t : ghss) {Z : PtdV} (f : pr1 Z --> t) :
    ru^{Mon_V}_{pr1 Z} · f = pr1 Z ⊗^{Mon_V}_{l} η t · ⦃f⦄_{Z}.
  Proof.
    exact (pr1 ((pr2 (pr1 (pr222 t Z f))))).
  Qed.

  Lemma gfbracket_τ (t : ghss) {Z : PtdV} (f : pr1 Z --> t) :
    θ Z t · #H ⦃f⦄_{Z} · τ t =  pr1 Z ⊗^{Mon_V}_{l} τ t · ⦃f⦄_{Z}.
  Proof.
    exact (pr2 ((pr2 (pr1 (pr222 t Z f))))).
  Qed.

  (* TODO: state and prove analogues of fbracket_natural and compute_fbracket *)

End hss.
