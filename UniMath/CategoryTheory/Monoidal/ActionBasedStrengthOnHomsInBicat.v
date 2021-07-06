(** Constructs instance of action-based strength for the actions of the endomorphisms by precomposition on fixed hom-categories of a bicategory

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.PointedFunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActions.
Require Import UniMath.CategoryTheory.Monoidal.ActionOfEndomorphismsInBicat.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCatsWithoutUnivalence.

Import Bicat.Notations.

Local Open Scope cat.

Section ActionBased_Strength_Between_Homs_In_Bicat.

Context {C : bicat}.
Context (c0 d0 d0': ob C).
Context {Mon_M : monoidal_precat}.

Local Definition Mon_endo: monoidal_precat := swapping_of_monoidal_precat (monoidal_precat_from_prebicat_and_ob c0).
Local Definition homprecat : precategory := hom c0 d0.
Local Definition homprecat' : precategory := hom c0 d0'.

Context (U: strong_monoidal_functor Mon_M Mon_endo).

Local Definition F_U := pr11 U.
Local Definition ϵ_U := pr112 U.
Local Definition μ_U := pr122 (pr1 U).
Local Definition ab_strength_domain_action : action Mon_M :=  lifted_action Mon_M U (action_from_precomp c0 d0').
Local Definition ab_strength_target_action : action Mon_M :=  lifted_action Mon_M U (action_from_precomp c0 d0).

Context (F: homprecat' ⟶ homprecat).

Definition ab_strength_on_homs_in_bicat: UU := actionbased_strength Mon_M ab_strength_domain_action ab_strength_target_action F.

Context (ab_str : ab_strength_on_homs_in_bicat).

Local Definition θ := pr1 ab_str.

Definition triangle_eq := actionbased_strength_triangle_eq Mon_M ab_strength_domain_action ab_strength_target_action F (pr1 ab_str).
Definition pentagon_eq := actionbased_strength_pentagon_eq Mon_M ab_strength_domain_action ab_strength_target_action F (pr1 ab_str).

Lemma triangle_eq_readable: triangle_eq =
  ∏ a : C ⟦ c0, d0' ⟧, θ (a,, monoidal_precat_unit Mon_M) • # F (id₂ a ⋆⋆  ϵ_U • lunitor a) =
                       id₂ (F a) ⋆⋆ ϵ_U • lunitor (F a).
Proof.
  apply idpath.
Qed.

Lemma triangle_eq_nice: triangle_eq <->
  ∏ X : C ⟦ c0, d0' ⟧, θ (X,, monoidal_precat_unit Mon_M) • # F ((ϵ_U ▹ X) • lunitor X) = (ϵ_U ▹ F X) • lunitor (F X).
Proof.
  split.
  - intro Heq.
    intro X.
    set (HeqX := Heq X).
    cbn in HeqX.
    do 2 rewrite hcomp_identity_right in HeqX.
    assumption.
  - intro Heq.
    intro X.
    cbn.
    do 2 rewrite hcomp_identity_right.
    apply Heq.
Qed.

Lemma pentagon_eq_readable: pentagon_eq =
  ∏ (a : C ⟦ c0, d0' ⟧) (x y : monoidal_precat_precat Mon_M),
                        (lassociator (U y) (U x) (F a) • id₂ (F a) ⋆⋆ μ_U (x,, y))
                          • θ (a,, monoidal_precat_tensor Mon_M (x, y)) =
                        (θ (a,, x) ⋆⋆ # F_U (id₁ y) • θ (F_U x · a,, y))
                          • # F (lassociator (U y) (U x) a • id₂ a ⋆⋆ μ_U (x,, y)).
Proof.
  apply idpath.
Qed.

(** the variables chosen in the following make the link with the notion of signature in the TYPES'15 paper by Ahrens and Matthes more visible - but Z is written insted of (Z,e), and likewise for Z' *)
Lemma pentagon_eq_nice: pentagon_eq <->
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : monoidal_precat_precat Mon_M),
    (lassociator (U Z) (U Z') (F X) • (μ_U (Z',, Z) ▹ F X)) • θ (X,, monoidal_precat_tensor Mon_M (Z', Z)) =
    ((F_U Z ◃ θ (X,, Z')) • θ (F_U Z' · X,, Z)) • # F (lassociator (U Z) (U Z') X • (μ_U (Z',, Z) ▹ X)).
Proof.
  split.
  - intro Heq.
    intros X Z' Z.
    assert (Heqinst := Heq X Z' Z).
    clear Heq.
    revert Heqinst.
    cbn.
    rewrite (functor_id (pr11 U)).
    do 2 rewrite hcomp_identity_right.
    unfold identity. cbn.
    rewrite hcomp_identity_left.
    intro Heqinst.
    assumption.
  - intro Heq.
    intros X Z' Z.
    cbn.
    rewrite (functor_id (pr11 U)).
    unfold identity. cbn.
    do 2 rewrite hcomp_identity_right.
    rewrite hcomp_identity_left.
    apply Heq.
Qed.
(* very slow verification *)

End ActionBased_Strength_Between_Homs_In_Bicat.

Section Instantiation_To_FunctorCategory_And_PointedEndofunctors.

Context (C : precategory) (hs : has_homsets C).
Context (D : precategory) (hsD : has_homsets D).
Context (D' : precategory) (hsD' : has_homsets D').

Context (H : functor [C, D', hsD'] [C, D, hsD]).

Local Definition forget := swapping_of_strong_monoidal_functor(forgetful_functor_from_ptd_as_strong_monoidal_functor_alt hs).

(* the following in order to understand why [forgetful_functor_from_ptd_as_strong_monoidal_functor_alt] is needed here *)
Local Definition monprecat1 := swapping_of_monoidal_precat
                        (EndofunctorsMonoidal.monoidal_precat_of_endofunctors hs).
Local Definition monprecat2 := Mon_endo (C:=bicat_of_cats_nouniv) (C,,hs).

(*
Lemma same_precategory : pr1 monprecat1 = pr1 monprecat2.
Proof.
  UniMath.MoreFoundations.Tactics.show_id_type.
  unfold monprecat1, monprecat2.
  unfold EndofunctorsMonoidal.monoidal_precat_of_endofunctors, Mon_endo.
  cbn.
The unachievable goal is then:
                  [C, C, hs] = precategory_from_prebicat_and_ob (C,, hs)
*)

Lemma same_precategory_data : pr11 monprecat1 = pr11 monprecat2.
Proof.
  apply idpath.
Qed.

Lemma same_tensor_data : pr112 monprecat1 = pr112 monprecat2.
Proof.
  unfold monprecat1, monprecat2.
  unfold EndofunctorsMonoidal.monoidal_precat_of_endofunctors, Mon_endo.
  cbn.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  use functor_data_eq.
  - intro x.
    cbn.
  (* The goal is then: pr2 x ∙ pr1 = pr2 x ∙ pr1 x *)
    apply idpath.
  - intros C1 C2 f. cbn. unfold HorizontalComposition.horcomp.
    induction f as [f g].
    cbn.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply nat_trans_eq; try assumption.
    intros. cbn.
    induction C1 as [C1 C1']. induction C2 as [C2 C2']. cbn in f, g.
    cbn.
    change (f (pr1 C1' x) · # (pr1 C2) (g x) = # (pr1 C1) (g x) · f (pr1 C2' x)).
    apply pathsinv0.
    apply nat_trans_ax.
Qed.

(* cannot be typechecked any longer
Lemma same_I : pr222 monprecat1 = pr222 monprecat2.
*)

Definition ab_strength_for_functors_and_pointed_functors : UU := ab_strength_on_homs_in_bicat(C:=bicat_of_cats_nouniv) (C,,hs) (D,,hsD) (D',,hsD') forget H.

(** TODO: compare with def. in Signatures.v *)

End Instantiation_To_FunctorCategory_And_PointedEndofunctors.
