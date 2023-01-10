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

  Section FixAGhss.

  Context (gh : ghss).

  Definition eta_from_alg : I_{Mon_V} --> gh := pr12 gh.
  Definition tau_from_alg : H gh --> gh := pr122 gh.

  Local Notation η := eta_from_alg.
  Local Notation τ := tau_from_alg.

  Definition gfbracket (Z : PtdV) (f : pr1 Z --> gh) : pr1 Z ⊗_{Mon_V} gh --> gh :=
    pr1 (pr1 (pr222 gh Z f)).

  Notation "⦃ f ⦄_{ Z }" := (gfbracket Z f)(at level 0).

  Lemma gfbracket_unique {Z : PtdV} (f : pr1 Z --> gh)
    : ∏ α : pr1 Z ⊗_{Mon_V} gh --> gh, gbracket_property_parts gh η τ (pr2 Z) f α
   → α = ⦃f⦄_{Z}.
  Proof.
    intros α Hyp.
    apply path_to_ctr.
    assumption.
  Qed.

  Lemma gfbracket_η {Z : PtdV} (f : pr1 Z --> gh) :
    ru^{Mon_V}_{pr1 Z} · f = pr1 Z ⊗^{Mon_V}_{l} η · ⦃f⦄_{Z}.
  Proof.
    exact (pr1 ((pr2 (pr1 (pr222 gh Z f))))).
  Qed.

  Lemma gfbracket_τ {Z : PtdV} (f : pr1 Z --> gh) :
    θ Z gh · #H ⦃f⦄_{Z} · τ =  pr1 Z ⊗^{Mon_V}_{l} τ · ⦃f⦄_{Z}.
  Proof.
    exact (pr2 ((pr2 (pr1 (pr222 gh Z f))))).
  Qed.

  (* TODO: state and prove analogues of fbracket_natural and compute_fbracket *)

  (** we are constructing a monoid in the monoidal base category *)

  Definition Ptd_from_ghss : PtdV := (pr1 gh,,η).

  Definition mu_from_ghss : gh ⊗_{Mon_V} gh --> gh := ⦃identity gh⦄_{Ptd_from_ghss}.

  Local Notation μ := mu_from_ghss.

  Definition μ_0 : I_{Mon_V} --> gh := η.

  Definition μ_0_ptd : I_{Mon_PtdV} --> Ptd_from_ghss.
  Proof.
    exists μ_0.
    cbn. apply id_left.
  Defined.

  Definition μ_1 : I_{Mon_V} ⊗_{Mon_V} gh --> gh := ⦃μ_0⦄_{I_{Mon_PtdV}}.

  Lemma μ_1_is_instance_of_left_unitor : μ_1 = lu^{Mon_V}_{gh}.
  Proof.
    apply pathsinv0, (gfbracket_unique(Z:=I_{Mon_PtdV})).
    split.
    - cbn. unfold μ_0.
      rewrite monoidal_leftunitornat.
      apply cancel_postcomposition.
      apply pathsinv0, unitors_coincide_on_unit.
    - etrans.
      { apply cancel_postcomposition.
        apply pointedtensorialstrength_preserves_unitor.
        apply lineator_preservesunitor. }
      cbn.
      apply pathsinv0, monoidal_leftunitornat.
  Qed.

  Lemma ghss_first_monoidlaw : ru^{Mon_V}_{gh} = gh ⊗^{Mon_V}_{l} η · μ.
  Proof.
    etrans.
    2: { apply (gfbracket_η(Z:=(pr1 gh,,η))). }
    apply pathsinv0, id_right.
  Qed.


  Lemma ghss_second_monoidlaw_aux : ru^{ Mon_V }_{ I_{ Mon_V}} · η = I_{ Mon_V} ⊗^{ Mon_V}_{l} η · (η ⊗^{ Mon_V}_{r} gh · μ).
  Proof.
  Admitted.

  Lemma ghss_second_monoidlaw : lu^{Mon_V}_{gh} = η ⊗^{Mon_V}_{r} gh · μ.
  Proof.
    etrans.
    { apply pathsinv0, μ_1_is_instance_of_left_unitor. }
    apply pathsinv0, (gfbracket_unique(Z:=I_{Mon_PtdV})).
    split.
    - exact ghss_second_monoidlaw_aux.
    - admit.
  Admitted.

  Definition gh_squared : PtdV := Ptd_from_ghss ⊗_{Mon_PtdV} Ptd_from_ghss.

  Definition μ_2 : gh ⊗_{Mon_V} gh --> gh := μ.

  Definition μ_2_ptd : gh_squared --> Ptd_from_ghss.
  Proof.
    exists μ_2.
    cbn. unfold μ_2.
    (* use [ghss_second_monoidlaw_aux] *)
  Admitted.

  Definition μ_3 : (gh ⊗_{Mon_V} gh) ⊗_{Mon_V} gh --> gh := ⦃μ_2⦄_{gh_squared}.

  Lemma ghss_third_monoidlaw : μ ⊗^{Mon_V}_{r} gh · μ = α_{Mon_V} gh gh gh · gh ⊗^{Mon_V}_{l} μ · μ.
  Proof.
    transitivity  μ_3.
    - apply (gfbracket_unique(Z:=gh_squared)).
      split.
      + admit.
      + admit.
    - apply pathsinv0, (gfbracket_unique(Z:=gh_squared)).
      split.
      + admit.
      + admit.
  Admitted.

  End FixAGhss.

End hss.
