(** Constructs instance of action-based strength for the actions of the endomorphisms by precomposition on fixed hom-categories of a bicategory

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require Import UniMath.SubstitutionSystems.Signatures.

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
  - intros Heq X Z' Z.
    assert (Heqinst := Heq X Z' Z).
    clear Heq.
    revert Heqinst.
    simpl.
    rewrite (functor_id (pr11 U)).
    intro Heqinst.
    refine (!_ @ Heqinst @ _).
    + cbn.
      apply maponpaths_2.
      apply maponpaths.
      exact (hcomp_identity_right _ _ (F X) (ConstructionOfActions.μ Mon_M U (Z',, Z))).
    + etrans.
      {
        do 2 apply maponpaths_2.
        apply hcomp_identity_left.
      }
      cbn.
      do 3 apply maponpaths.
      apply hcomp_identity_right.
  - intros Heq X Z' Z.
    simpl.
    rewrite (functor_id (pr11 U)).
    refine (_ @ Heq _ _ _ @ _).
    + cbn.
      apply maponpaths_2.
      apply maponpaths.
      apply hcomp_identity_right.
    + refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply hcomp_identity_left.
      }
      cbn.
      do 3 apply maponpaths.
      apply hcomp_identity_right.
Qed.

Definition μ_UZ'Zinv (Z' Z : monoidal_precat_precat Mon_M):=
  nat_z_iso_to_trans_inv (μ_U,,pr22 U) (Z',,Z).

Lemma pentagon_eq_nicer: pentagon_eq <->
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : monoidal_precat_precat Mon_M),
                         (lassociator (U Z) (U Z') (F X) • (μ_U (Z',, Z) ▹ F X)) •
                         θ (X,, monoidal_precat_tensor Mon_M (Z', Z)) •
                         # F ((μ_UZ'Zinv Z' Z ▹ X) • rassociator (U Z) (U Z') X) =
                         ((F_U Z ◃ θ (X,, Z')) • θ (F_U Z' · X,, Z)).
Proof.
  split.
  - intro Heq.
    assert (Heq' := pr1 pentagon_eq_nice Heq).
    clear Heq.
    intros X Z' Z.
    assert (Heqinst := Heq' X Z' Z).
    clear Heq'.
    rewrite Heqinst.
    clear Heqinst.
    etrans.
    2: { apply id2_right. }
    rewrite <- vassocr.
    apply maponpaths.
    apply pathsinv0.
    etrans.
    2: { apply (functor_comp(C:=hom c0 d0')(C':=hom c0 d0)). }
    apply pathsinv0.
    apply (functor_id_id (hom c0 d0') (hom c0 d0)).
    cbn.
    rewrite <- vassocr.
    apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)).
    rewrite id2_right.
    rewrite vassocr.
    etrans.
    2: { apply id2_left. }
    apply maponpaths_2.
    rewrite rwhisker_vcomp.
    etrans.
    { apply maponpaths.
      apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (μ_U,,pr22 U) (Z',,Z))).
    }
    apply id2_rwhisker.
  - intro Heq.
    apply (pr2 pentagon_eq_nice).
    intros X Z' Z.
    assert (Heqinst := Heq X Z' Z).
    clear Heq.
    etrans.
    2: { apply maponpaths_2.
         exact Heqinst. }
    clear Heqinst.
    repeat rewrite <- vassocr.
    do 2 apply maponpaths.
    etrans.
    { apply pathsinv0. apply id2_right. }
    apply maponpaths.
    etrans.
    2: { apply (functor_comp(C:=hom c0 d0')(C':=hom c0 d0)). }
    apply pathsinv0.
    apply (functor_id_id (hom c0 d0') (hom c0 d0)).
    cbn.
    rewrite vassocr.
    etrans.
    { apply maponpaths_2. apply vassocl. }
    rewrite rassociator_lassociator.
    rewrite id2_right.
    rewrite rwhisker_vcomp.
    etrans.
    { apply maponpaths.
      apply (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso (μ_U,,pr22 U) (Z',,Z))).
    }
    apply id2_rwhisker.
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

Section Signature_From_ActionBased_Strength.

  Context (ab_str : ab_strength_for_functors_and_pointed_functors).

  Local Definition θ' := pr1 ab_str.

  (* adapt typing of [θ'] for use in [Signature] *)
  Definition θ_for_signature : θ_source(hs:=hs) H ⟹ θ_target H.
  Proof.
    use make_nat_trans.
    - intro x. exact (θ' x).
    - intros x x' f.
      (* UniMath.MoreFoundations.Tactics.show_id_type. *)
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      assert (Heq := nat_trans_ax θ' x x' f).
      assert (Heqc := nat_trans_eq_weq hsD _ _ Heq c).
      clear Heq.
      cbn in Heqc.
      (* term precomposed with θ' x' c in goal and [Heqc]: *)
      assert (Heq0 : pr1(# H (pr1 f)) ((pr12 x) c) · # (pr1(H (pr1 x'))) ((pr12 f) c) =
                     # (pr1 (H (pr1 x))) ((pr112 f) c) · pr1 (# H (pr1 f)) (pr1 (pr12 x') c)).
      { apply pathsinv0. apply nat_trans_ax. }
      etrans.
      { apply cancel_postcomposition. exact Heq0. }
      clear Heq0.
      etrans.
      { exact Heqc. }
      apply maponpaths.
      generalize c.
      apply nat_trans_eq_pointwise.
      apply maponpaths.
      apply pathsinv0.
      apply HorizontalComposition.horcomp_post_pre.
  Defined.

  Definition signature_from_ab_strength : Signature C hs D hsD D' hsD'.
  Proof.
    exists H.
    exists θ_for_signature.
    split.
    - red. intro X.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      assert (HypX := pr1 (triangle_eq_nice _ _ _ _ _ _) (pr12 ab_str) X).
      unfold θ in HypX. fold θ' in HypX.
      assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
      cbn in Heqc.
      rewrite (functor_id (H X)) in Heqc.
      rewrite id_left in Heqc.
      etrans.
      2: { exact Heqc. }
      clear HypX Heqc.
      apply maponpaths.
      apply nat_trans_eq_pointwise.
      clear c.
      apply maponpaths.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      apply pathsinv0.
      rewrite id_right.
      apply functor_id.
    - red. intros X Z Z'.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      rewrite id_left.
      assert (HypX := pr1 (pentagon_eq_nicer _ _ _ _ _ _) (pr22 ab_str) X Z' Z).
      unfold θ in HypX. fold θ' in HypX.
      assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
      clear HypX.
      cbn in Heqc.
      rewrite (functor_id (H X)) in Heqc.
      do 2 rewrite id_left in Heqc.
      etrans.
      2: { exact Heqc. }
      clear Heqc.
      apply maponpaths.
      apply nat_trans_eq_pointwise.
      clear c.
      apply maponpaths.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      rewrite id_right.
      apply pathsinv0.
      apply functor_id.
  Defined.

End Signature_From_ActionBased_Strength.
End Instantiation_To_FunctorCategory_And_PointedEndofunctors.

Section ActionBased_Strength_From_Signature.

  Context (C : precategory) (hs : has_homsets C).
  Context (D : precategory) (hsD : has_homsets D).
  Context (D' : precategory) (hsD' : has_homsets D').
  Context (sig : Signature C hs D hsD D' hsD').

  Local Definition forget' := swapping_of_strong_monoidal_functor(forgetful_functor_from_ptd_as_strong_monoidal_functor_alt hs).
  Local Definition H := pr1 sig.
  Local Definition θ'' := pr12 sig.

  (* the following lemma cannot be stated:
  Lemma θ_for_ab_strength_aux : is_nat_trans
    (actionbased_strength_dom (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
       (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
       (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget') H)
    (actionbased_strength_codom (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
       (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
       (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget') H)
    (λ x : ActionBasedStrength.A (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
             (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
           ⊠ ActionBasedStrength.V (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs)), θ'' x).
   *)

  Lemma aux0 (x : ActionBasedStrength.A (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
        (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
        ⊠ ActionBasedStrength.V (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))) :
 ActionBasedStrength.A' (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
    (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget')
  ⟦ actionbased_strength_dom (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
      (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
      (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget') H x,
  actionbased_strength_codom (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
    (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
    (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget') H x ⟧
  =
  functor_composite_data (pr12 x) (pr1 (H (pr1 x))) ⟹  pr1 (pr11  H (pr12 x ∙ pr1 x)).
  Proof.
    apply idpath.
  Defined.

  Definition θ_for_ab_strength_data
    : nat_trans_data
        (actionbased_strength_dom
           (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
           (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
           (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget')
           H)
        (actionbased_strength_codom
           (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
           (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
           (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget')
           H).
  Proof.
    intro x.
    exact (eqweqmap (!aux0 x) (θ'' x)).
  Defined.

  Definition θ_for_ab_strength_ax
    : is_nat_trans _ _ θ_for_ab_strength_data.
  Proof.
    intros x x' f.
    apply nat_trans_eq; try assumption.
    intro c.
    assert (Heq := nat_trans_ax θ'' x x' f).
    assert (Heqc := nat_trans_eq_weq hsD _ _ Heq c).
    clear Heq.
    (* term precomposed with [θ'' x' c] in [Heqc] and goal: *)
    assert (Heq0 : pr1(# H (pr1 f)) ((pr12 x) c) · # (pr1(H (pr1 x'))) ((pr12 f) c) =
                   # (pr1 (H (pr1 x))) ((pr112 f) c) · pr1 (# H (pr1 f)) (pr1 (pr12 x') c)).
    { apply pathsinv0. apply nat_trans_ax. }
    etrans.
    { apply cancel_postcomposition. apply pathsinv0. exact Heq0. }
    clear Heq0.
    cbn in Heqc.
    cbn.
    etrans.
    {
      exact Heqc. (* does not work when aux0 is opaque *)
    }
    apply maponpaths.
    generalize c.
    apply nat_trans_eq_pointwise.
    apply maponpaths.
    apply (HorizontalComposition.horcomp_post_pre _ _ _ _ _ _ _ (pr12 f) (pr1 f)).
  Qed.

  Definition θ_for_ab_strength :
    actionbased_strength_dom
      (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
      (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
      (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget')
      H
    ⟹
    actionbased_strength_codom
      (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
      (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget')
      (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget')
      H.
  Proof.
    use make_nat_trans.
    - exact θ_for_ab_strength_data.
    - exact θ_for_ab_strength_ax.
  Defined.

  Lemma θ_for_ab_strength_law1 : actionbased_strength_triangle_eq (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
    (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') (forget C hs))
    (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) (forget C hs)) H θ_for_ab_strength.
  Proof.
    red. intro X.
    assert (HypX := Sig_strength_law1 _ _ _ _ _ _ sig X).
    fold θ'' in HypX.
    fold H in HypX.
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    rewrite (functor_id (H X)).
    do 2 rewrite id_left.
    assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
    clear HypX.
    cbn in Heqc.
    etrans.
    2: { exact Heqc. }
    clear Heqc.
    apply maponpaths.
    apply nat_trans_eq_pointwise.
    clear c.
    apply maponpaths.
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    do 2 rewrite id_right.
    apply functor_id.
  Time Qed. (* 5.172 seconds *)
  (* slow verification *)

  Print actionbased_strength_pentagon_eq.

  Definition test
             (Mon_V : monoidal_precat)
             (actn actn' : action Mon_V)
             (F : ActionBasedStrength.A Mon_V actn ⟶ ActionBasedStrength.A' Mon_V actn')
             (z : actionbased_strength_nat Mon_V actn actn' F)
             (p : ∏ (X : ActionBasedStrength.A Mon_V actn)
                    (Y HX : ActionBasedStrength.V Mon_V),
                  ActionBasedStrength.χ' Mon_V actn' ((F X, Y), HX)
                  · z (X, ActionBasedStrength.tensor Mon_V (Y, HX))
                  =
                  # (ActionBasedStrength.odot' Mon_V actn') (z (X, Y) #, id₁ HX)
                  · z (ActionBasedStrength.odot Mon_V actn (X, Y), HX)
                  · # F (ActionBasedStrength.χ Mon_V actn ((X, Y), HX)))
    : actionbased_strength_pentagon_eq Mon_V actn actn' F z.
  Proof.
    exact p.
  Qed.

  Lemma θ_for_ab_strength_law2
    : actionbased_strength_pentagon_eq
        (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
        (ab_strength_domain_action
           (C:=bicat_of_cats_nouniv)
           (C ,, hs) (D' ,, hsD')
           (forget C hs))
        (ab_strength_target_action
           (C:=bicat_of_cats_nouniv)
           (C ,, hs) (D ,, hsD)
           (forget C hs))
        H
        θ_for_ab_strength.
  Proof.
    intros X Z' Z.
    cbn.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    simpl.
    assert (HypX := pr1 (θ_Strength2_int_nicer _ _ _ _ _ _ _ _)
                        (Sig_strength_law2 _ _ _ _ _ _ sig) X Z Z').
    fold θ'' in HypX.
    fold H in HypX.
    assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
    clear HypX.
    cbn in Heqc.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply id_right.
      }
      apply id_left.
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply functor_id.
      }
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply functor_id.
        }
        apply functor_id.
      }
      apply id_left.
    }
    refine (!_).
    refine (Heqc @ _).
    clear Heqc.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_left.
    }
    apply maponpaths.
    apply nat_trans_eq_pointwise.
    clear c.
    apply maponpaths.
    apply nat_trans_eq; try (exact hsD').
    intro c.
    cbn.
    rewrite id_right.
    rewrite id_left.
    apply pathsinv0.
    apply functor_id.
  Time Qed. (* *)
  (* potentially non-terminating verification on certain Coq installations *)

  Definition ab_strength_from_signature : ab_strength_for_functors_and_pointed_functors C hs D hsD D' hsD' H.
  Proof.
    exists θ_for_ab_strength.
    split.
    - exact θ_for_ab_strength_law1.
    - exact θ_for_ab_strength_law2.
Defined.

End ActionBased_Strength_From_Signature.
