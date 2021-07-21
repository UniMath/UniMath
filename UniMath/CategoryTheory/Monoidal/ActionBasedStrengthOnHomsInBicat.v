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
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.PointedFunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActions.
Require Import UniMath.CategoryTheory.Monoidal.ActionOfEndomorphismsInBicat.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrongFunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCatsWithoutUnivalence.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.



Import Bicat.Notations.

Local Open Scope cat.

Section ActionBased_Strength_Between_Homs_In_Bicat.

Context {C : bicat}.
Context (c0 d0 d0': ob C).
Context {Mon_M : monoidal_precat}.

Local Definition Mon_endo: monoidal_precat := swapping_of_monoidal_precat (monoidal_precat_from_prebicat_and_ob c0).

Context (U: strong_monoidal_functor Mon_M Mon_endo).

Local Definition F_U := pr11 U.
Local Definition ϵ_U := pr112 U.
Local Definition μ_U := pr122 (pr1 U).
Local Definition ab_strength_domain_action : action Mon_M (hom c0 d0') :=  lifted_action Mon_M U (action_from_precomp c0 d0').
Local Definition ab_strength_target_action : action Mon_M (hom c0 d0) :=  lifted_action Mon_M U (action_from_precomp c0 d0).

Context (F: hom c0 d0' ⟶ hom c0 d0).

Definition ab_strength_on_homs_in_bicat: UU := actionbased_strength Mon_M ab_strength_domain_action ab_strength_target_action F.

Context (ab_str : ab_strength_on_homs_in_bicat).

Local Definition θ := pr1 ab_str.

Definition triangle_eq := actionbased_strength_triangle_eq Mon_M
  ab_strength_domain_action ab_strength_target_action F (pr1 ab_str).
Definition pentagon_eq := actionbased_strength_pentagon_eq Mon_M
  ab_strength_domain_action ab_strength_target_action F (pr1 ab_str).

Lemma triangle_eq_readable: triangle_eq =
  ∏ a : C ⟦ c0, d0' ⟧, θ (a,, monoidal_precat_unit Mon_M) • # F (id₂ a ⋆⋆  ϵ_U • lunitor a) =
                       id₂ (F a) ⋆⋆ ϵ_U • lunitor (F a).
Proof.
  apply idpath.
Qed.

Definition triangle_eq_nice : UU :=
  ∏ X : C ⟦ c0, d0' ⟧, θ (X,, monoidal_precat_unit Mon_M) • # F ((ϵ_U ▹ X) • lunitor X) =
                       (ϵ_U ▹ F X) • lunitor (F X).

Lemma triangle_eq_implies_triangle_eq_nice : triangle_eq -> triangle_eq_nice.
Proof.
  intro Heq.
  intro X.
  set (HeqX := Heq X).
  cbn in HeqX.
  do 2 rewrite hcomp_identity_right in HeqX.
  assumption.
Qed.

Lemma triangle_eq_nice_implies_triangle_eq : triangle_eq_nice -> triangle_eq.
Proof.
  intro Heq.
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


(** the variables chosen in the following make the link with the notion of signature
    in the TYPES'15 paper by Ahrens and Matthes more visible - but Z is written insted
    of (Z,e), and likewise for Z' *)

Definition pentagon_eq_nice : UU :=
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : monoidal_precat_precat Mon_M),
    (lassociator (U Z) (U Z') (F X) • (μ_U (Z',, Z) ▹ F X)) • θ (X,, monoidal_precat_tensor Mon_M (Z', Z)) =
    ((F_U Z ◃ θ (X,, Z')) • θ (F_U Z' · X,, Z)) • # F (lassociator (U Z) (U Z') X • (μ_U (Z',, Z) ▹ X)).

Lemma pentagon_eq_implies_pentagon_eq_nice : pentagon_eq -> pentagon_eq_nice.
Proof.
  intros Heq X Z' Z.
  assert (Heqinst := Heq X Z' Z).
  clear Heq.
  revert Heqinst.
  simpl.
  rewrite (functor_id (pr11 U)).
  intro Heqinst.
  refine (!_ @ Heqinst @ _).
  - cbn.
    apply maponpaths_2.
    apply maponpaths.
    exact (hcomp_identity_right _ _ (F X) (ConstructionOfActions.μ Mon_M U (Z',, Z))).
  - etrans.
    {
      do 2 apply maponpaths_2.
      apply hcomp_identity_left.
    }
    cbn.
    do 3 apply maponpaths.
    apply hcomp_identity_right.
Qed.

Lemma pentagon_eq_nice_implies_pentagon_eq : pentagon_eq_nice -> pentagon_eq.
Proof.
  intros Heq X Z' Z.
  simpl.
  rewrite (functor_id (pr11 U)).
  refine (_ @ Heq _ _ _ @ _).
  - cbn.
    apply maponpaths_2.
    apply maponpaths.
    apply hcomp_identity_right.
  - refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply hcomp_identity_left.
    }
    cbn.
    do 3 apply maponpaths.
    apply hcomp_identity_right.
Qed.

Definition μ_UZ'Zinv (Z' Z : monoidal_precat_precat Mon_M) :
  hom c0 c0 ⟦ monoidal_functor_map_codom Mon_M Mon_endo (pr11 U) (Z',, Z),
              monoidal_functor_map_dom Mon_M Mon_endo (pr11 U) (Z',, Z) ⟧
  := nat_z_iso_to_trans_inv (μ_U,,pr22 U) (Z',,Z).

Definition pentagon_eq_nicer : UU :=
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : monoidal_precat_precat Mon_M),
                         (lassociator (U Z) (U Z') (F X) • (μ_U (Z',, Z) ▹ F X)) •
                         θ (X,, monoidal_precat_tensor Mon_M (Z', Z)) •
                         # F ((μ_UZ'Zinv Z' Z ▹ X) • rassociator (U Z) (U Z') X) =
                         ((F_U Z ◃ θ (X,, Z')) • θ (F_U Z' · X,, Z)).

Lemma pentagon_eq_nice_implies_pentagon_eq_nicer : pentagon_eq_nice -> pentagon_eq_nicer.
Proof.
  intro Heq'.
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
Qed.


Lemma pentagon_eq_nicer_implies_pentagon_eq_nice : pentagon_eq_nicer -> pentagon_eq_nice.
Proof.
  intro Heq.
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
(* slow verification *)


End ActionBased_Strength_Between_Homs_In_Bicat.

Section Instantiation_To_FunctorCategory_And_PointedEndofunctors.

Context (C : precategory) (hs : has_homsets C).
Context (D : precategory) (hsD : has_homsets D).
Context (D' : precategory) (hsD' : has_homsets D').

Local Definition forget := swapping_of_strong_monoidal_functor(forgetful_functor_from_ptd_as_strong_monoidal_functor_alt hs).


(* the following in order to understand why [forgetful_functor_from_ptd_as_strong_monoidal_functor_alt] is needed here *)
Local Definition monprecat1 : monoidal_precat := swapping_of_monoidal_precat (EndofunctorsMonoidal.monoidal_precat_of_endofunctors hs).
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
  - intros C1 C2 f. cbn. unfold horcomp.
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

Local Definition Mon_endo': monoidal_precat := swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs).
Local Definition domain_action : action Mon_endo' (hom(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD'))
    := ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget.
Local Definition target_action : action Mon_endo' (hom(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD))
    := ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget.


Section Signature_From_ActionBased_Strength.

Section IndividualFunctorsWithABStrength.

  Context (H : functor [C, D', hsD'] [C, D, hsD]).


  Definition ab_strength_for_functors_and_pointed_functors : UU := ab_strength_on_homs_in_bicat(C:=bicat_of_cats_nouniv) (C,,hs) (D,,hsD) (D',,hsD') forget H.

  Context (ab_str : ab_strength_for_functors_and_pointed_functors).

  Local Definition θ' := pr1 ab_str.

  (* adapt typing of [θ'] for use in [Signature] *)
  Definition θ_for_signature_nat_trans_data : nat_trans_data (θ_source(hs:=hs) H) (θ_target H).
  Proof.
    intro x. exact (θ' x).
  Defined.

  Lemma θ_for_signature_is_nat_trans : is_nat_trans _ _ θ_for_signature_nat_trans_data.
  Proof.
    intros x x' f.
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
    apply horcomp_post_pre.
  Qed.

  Definition θ_for_signature : θ_source(hs:=hs) H ⟹ θ_target H
    := (θ_for_signature_nat_trans_data,,θ_for_signature_is_nat_trans).

  Lemma signature_from_ab_strength_laws : θ_Strength1_int θ_for_signature × θ_Strength2_int θ_for_signature.
    split.
    - red. intro X.
      apply nat_trans_eq; try assumption.
      intro c.
      cbn.
      assert (HypX := triangle_eq_implies_triangle_eq_nice _ _ _ _ _ _ (pr12 ab_str) X).
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
      assert (HypX := pentagon_eq_nice_implies_pentagon_eq_nicer _ _ _ _ _ _
                      (pentagon_eq_implies_pentagon_eq_nice _ _ _ _ _ _ (pr22 ab_str)) X Z' Z).
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
  Qed.

  Definition signature_from_ab_strength : Signature C hs D hsD D' hsD'.
  Proof.
    exists H.
    exists θ_for_signature.
    exact signature_from_ab_strength_laws.
  Defined.

End IndividualFunctorsWithABStrength.

Section IndividualStrongFunctors.

  Context (FF : actionbased_strong_functor Mon_endo' domain_action target_action).

  Definition signature_from_strong_functor : Signature C hs D hsD D' hsD' :=
    signature_from_ab_strength (pr1 FF) (pr2 FF).

End IndividualStrongFunctors.

Section Morphisms.

  Context {FF GG : actionbased_strong_functor Mon_endo' domain_action target_action}.
  Context (sη : Strong_Functor_Category_Mor Mon_endo' domain_action target_action FF GG).

  Lemma signature_mor_from_ab_strength_mor_diagram (X : [C, D', hsD']) (Y : precategory_Ptd C hs) :
    Signature_category_mor_diagram (C,, hs) (D,, hsD) (D',, hsD')
      (signature_from_strong_functor FF) (signature_from_strong_functor GG) (pr1 sη) X Y.
  Proof.
    red.
    cbn.
    assert (Hyp := pr2 sη X Y).
    red in Hyp. cbn in Hyp.
    etrans.
    { exact Hyp. }
    clear Hyp.
    apply maponpaths_2.
    apply pathsinv0.
    apply (horcomp_post_pre _ _ (D,,hsD)).
  Qed.

  Definition signature_mor_from_ab_strength_mor :
    SignatureMor (C,,hs) (D,,hsD) (D',,hsD') (signature_from_strong_functor FF) (signature_from_strong_functor GG).
  Proof.
    exists (pr1 sη).
    exact signature_mor_from_ab_strength_mor_diagram.
  Defined.

End Morphisms.

Definition ActionBasedStrongFunctorCategoryToSignatureCategory_data : functor_data
   (Strong_Functor_precategory Mon_endo' domain_action target_action
                               (functor_category_has_homsets _ _ hsD))
   (Signature_precategory (C,,hs) (D,,hsD) (D',,hsD')).
Proof.
  use make_functor_data.
  - exact signature_from_strong_functor.
  - intros FF GG sη. exact (signature_mor_from_ab_strength_mor sη).
Defined.

Lemma ActionBasedStrongFunctorCategoryToSignatureCategory_is_functor :
  is_functor ActionBasedStrongFunctorCategoryToSignatureCategory_data.
Proof.
  split.
  - intro FF.
    apply SignatureMor_eq; try apply (functor_category_has_homsets _ _ hsD).
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
    intro H.
    apply nat_trans_eq; try assumption.
    intro c.
    apply idpath.
  - intros FF GG HH sη sη'.
    apply SignatureMor_eq; try apply (functor_category_has_homsets _ _ hsD).
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
    intro H.
    apply nat_trans_eq; try assumption.
    intro c.
    apply idpath.
Qed.

Definition ActionBasedStrongFunctorCategoryToSignatureCategory : functor
   (Strong_Functor_precategory Mon_endo' domain_action target_action
                               (functor_category_has_homsets _ _ hsD))
   (Signature_precategory (C,,hs) (D,,hsD) (D',,hsD'))
  := (_,,ActionBasedStrongFunctorCategoryToSignatureCategory_is_functor).

End Signature_From_ActionBased_Strength.


Section ActionBased_Strength_From_Signature.

Section IndividualSignatures.

  Context (sig : Signature C hs D hsD D' hsD').
  Local Definition H := pr1 sig.
  Local Definition θ'' := pr12 sig.

  Local Lemma aux0 ( x : [C, D', hsD'] ⊠ ActionBasedStrength.V Mon_endo') :
    hom(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD)
       ⟦ actionbased_strength_dom Mon_endo' target_action H x,
         actionbased_strength_codom Mon_endo' domain_action H x ⟧
    = functor_composite_data (pr12 x) (pr1 (H (pr1 x))) ⟹  pr1 (pr11  H (pr12 x ∙ pr1 x)).
  Proof.
    apply idpath.
  Defined.

  Definition θ_for_ab_strength_data
    : nat_trans_data (actionbased_strength_dom Mon_endo' target_action H)
                     (actionbased_strength_codom Mon_endo' domain_action H).
  Proof.
    intro x.
    exact (eqweqmap (!aux0 x) (θ'' x)).
  Defined.

  Definition θ_for_ab_strength_ax : is_nat_trans _ _ θ_for_ab_strength_data.
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
    induction f as [f1 f2].
    apply (horcomp_post_pre _ _ (D',,hsD') _ _ _ _ (pr1 f2) f1).
  Qed.

  Definition θ_for_ab_strength : actionbased_strength_nat Mon_endo' domain_action target_action H.
  Proof.
    use make_nat_trans.
    - exact θ_for_ab_strength_data.
    - exact θ_for_ab_strength_ax.
  Defined.
  (* very slow processing of both steps then verification *)

  Lemma θ_for_ab_strength_law1 :
    actionbased_strength_triangle_eq Mon_endo' domain_action target_action H θ_for_ab_strength.
  Proof.
    red. intro X.
    assert (HypX := Sig_strength_law1 sig X).
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

  Lemma θ_for_ab_strength_law2
    : actionbased_strength_pentagon_eq Mon_endo' domain_action target_action H θ_for_ab_strength.
  Proof.
    intros X Z' Z.
    cbn.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    simpl.
    assert (HypX := θ_Strength2_int_implies_θ_Strength2_int_nicer _
                        (Sig_strength_law2 sig) X Z Z').
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
  Time Qed. (* 78.153 secs *)


  Definition ab_strength_from_signature :
    ab_strength_for_functors_and_pointed_functors H.
  Proof.
    exists θ_for_ab_strength.
    split.
    - exact θ_for_ab_strength_law1.
    - exact θ_for_ab_strength_law2.
  Defined.

  Definition ab_strong_functor_from_signature :
    actionbased_strong_functor Mon_endo' domain_action target_action
    := (H,,ab_strength_from_signature).

End IndividualSignatures.

Section Morphisms.

  Context {sig1 sig2 : Signature C hs D hsD D' hsD'}.
  Context (f : SignatureMor (C,,hs) (D,,hsD) (D',,hsD') sig1 sig2).

  Lemma ab_strength_mor_from_signature_mor_is_nat_trans : is_nat_trans _ _ (pr1 f).
  Proof.
    red.
    intros F F' g.
    cbn.
    assert (Hyp := pr21 f F F' g).
    exact Hyp.
  Qed.

  Definition ab_strength_mor_from_signature_mor_nat_trans :
    ActionBasedStrongFunctorCategory.F Mon_endo' domain_action target_action
                                       (ab_strong_functor_from_signature sig1)
    ⟹ ActionBasedStrongFunctorCategory.F Mon_endo' domain_action target_action
                                       (ab_strong_functor_from_signature sig2).
  Proof.
    exists (pr1 f).
    exact ab_strength_mor_from_signature_mor_is_nat_trans.
  Defined.

  Lemma ab_strength_mor_from_signature_mor_diagram
        (a : hom(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD'))
        (v : ActionBasedStrongFunctorCategory.V Mon_endo') :
   Strong_Functor_Category_mor_diagram Mon_endo' domain_action target_action
    (ab_strong_functor_from_signature sig1)
    (ab_strong_functor_from_signature sig2)
    ab_strength_mor_from_signature_mor_nat_trans a v.
  Proof.
    red.
    cbn.
    assert (Hyp := pr2 f a v).
    red in Hyp. cbn in Hyp.
    etrans.
    { exact Hyp. }
    clear Hyp.
    apply maponpaths_2.
    apply (horcomp_post_pre _ _ (D,,hsD)).
  Qed.

  Definition ab_strength_mor_from_signature_mor : Strong_Functor_Category_Mor
    Mon_endo' domain_action target_action
    (ab_strong_functor_from_signature sig1)
    (ab_strong_functor_from_signature sig2).
  Proof.
    exists ab_strength_mor_from_signature_mor_nat_trans.
    exact ab_strength_mor_from_signature_mor_diagram.
  Defined.

End Morphisms.

Definition SignatureCategoryToActionBasedStrongFunctorCategory_data :
  functor_data (Signature_precategory (C,,hs) (D,,hsD) (D',,hsD'))
               (Strong_Functor_precategory Mon_endo' domain_action target_action
                                           (functor_category_has_homsets _ _ hsD)).
Proof.
  use make_functor_data.
  - intro sig. exact (ab_strong_functor_from_signature sig).
  - intros sig1 sig2 f. exact (ab_strength_mor_from_signature_mor f).
Defined.

Lemma SignatureCategoryToActionBasedStrongFunctorCategory_is_functor :
  is_functor SignatureCategoryToActionBasedStrongFunctorCategory_data.
Proof.
  split.
  - intro H.
    apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets _ _ hsD).
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
    intro X.
    apply nat_trans_eq; try assumption.
    intro c.
    apply idpath.
  - intros F G H f g.
    apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets _ _ hsD).
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
    intro X.
    apply nat_trans_eq; try assumption.
    intro c.
    apply idpath.
Qed.

Definition SignatureCategoryToActionBasedStrongFunctorCategory : functor
  (Signature_precategory (C,,hs) (D,,hsD) (D',,hsD'))
  (Strong_Functor_precategory Mon_endo' domain_action target_action
                              (functor_category_has_homsets _ _ hsD))
  := (_,,SignatureCategoryToActionBasedStrongFunctorCategory_is_functor).


End ActionBased_Strength_From_Signature.

(* the following lemma cannot be used later *)
Lemma roundtrip1_ob_as_equality (sig : Signature C hs D hsD D' hsD') : signature_from_strong_functor (ab_strong_functor_from_signature sig) = sig.
Proof.
  use total2_paths_f.
  - apply idpath.
  - cbn.
    use total2_paths_f.
    + apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
      intro x; apply idpath.
    + apply dirprodeq.
      * apply isaprop_θ_Strength1_int.
      * apply isaprop_θ_Strength2_int.
Defined.

Definition roundtrip1_ob_nat_trans_data : nat_trans_data
  (functor_identity (Signature_precategory (C,, hs) (D,, hsD) (D',, hsD')))
  (SignatureCategoryToActionBasedStrongFunctorCategory ∙ ActionBasedStrongFunctorCategoryToSignatureCategory).
Proof.
  intro sig. cbn.
  use tpair.
  - use make_nat_trans.
    + intro X. exact (identity (pr1 sig X)).
    + intros X1 X2 f.
      etrans.
      { apply id_right. }
      etrans.
      2: { apply pathsinv0. apply id_left. }
      apply idpath.
  - intros X Y. red.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    etrans.
    { apply id_right. }
    etrans.
    2: { apply cancel_postcomposition.
         cbn.
         apply pathsinv0.
         apply id_left.
    }
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0.
         apply (functor_id(H sig X)).
    }
    apply pathsinv0.
    apply id_left.
Defined.

Definition roundtrip1_ob_nat_trans_data_pointwise_inv (sig : Signature_precategory (C,, hs) (D,, hsD) (D',, hsD')) :
  SignatureMor (C,, hs) (D,, hsD) (D',, hsD')
               (signature_from_strong_functor (ab_strong_functor_from_signature sig)) sig.
Proof.
  use tpair.
  - use make_nat_trans.
    + intro X. exact (identity (pr1 sig X)).
    + intros X1 X2 f.
      etrans.
      { apply id_right. }
      etrans.
      2: { apply pathsinv0. apply id_left. }
      apply idpath.
  - intros X Y. red.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    etrans.
    { apply id_right. }
    etrans.
    2: { apply cancel_postcomposition.
         cbn.
         apply pathsinv0.
         apply id_left.
    }
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0.
         apply (functor_id(H sig X)).
    }
    apply pathsinv0.
    apply id_left.
Defined.

Definition roundtrip1_ob_data_is_nat_z_iso : is_nat_z_iso roundtrip1_ob_nat_trans_data.
Proof.
  intro sig.
  exists (roundtrip1_ob_nat_trans_data_pointwise_inv sig).
  abstract (split; apply SignatureMor_eq;
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD);
    intro X;
    cbn;
    apply (id_left(C:=[C, D, hsD]))).
Defined.

Lemma roundtrip1_ob_data_is_nat_trans : is_nat_trans _ _ roundtrip1_ob_nat_trans_data.
Proof.
  intros sig1 sig2 f.
  apply SignatureMor_eq; try apply (functor_category_has_homsets C D hsD).
  apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
  intro X.
  etrans.
  { cbn. apply (id_right(C:=[C, D, hsD])). }
  etrans.
  2: { cbn. apply pathsinv0. apply (id_left(C:=[C, D, hsD])). }
  apply idpath.
Qed.

Definition roundtrip1_ob_nat_trans :
  (functor_identity (Signature_precategory (C,, hs) (D,, hsD) (D',, hsD'))) ⟹
  SignatureCategoryToActionBasedStrongFunctorCategory ∙ ActionBasedStrongFunctorCategoryToSignatureCategory
  := (roundtrip1_ob_nat_trans_data,,roundtrip1_ob_data_is_nat_trans).


(* the following lemma cannot be used later *)
Lemma roundtrip2_ob_as_equality (FF : actionbased_strong_functor Mon_endo' domain_action target_action) : ab_strong_functor_from_signature (signature_from_strong_functor FF) = FF.
Proof.
  use total2_paths_f.
  - apply idpath.
  - cbn.
    use total2_paths_f.
    + apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
      intro x; apply idpath.
    + apply dirprodeq.
      * apply isaprop_actionbased_strength_triangle_eq.
        apply (functor_category_has_homsets _ _ hsD).
      * apply isaprop_actionbased_strength_pentagon_eq.
        apply (functor_category_has_homsets _ _ hsD).
Qed.

Definition roundtrip2_ob_nat_trans_data : nat_trans_data
  (ActionBasedStrongFunctorCategoryToSignatureCategory ∙ SignatureCategoryToActionBasedStrongFunctorCategory)
  (functor_identity (Strong_Functor_precategory Mon_endo' domain_action target_action (functor_category_has_homsets C D hsD))).
Proof.
  intro FF. cbn.
  use tpair.
  - use make_nat_trans.
    + intro X. exact (identity (pr1 FF X)).
    + intros X1 X2 f.
      etrans.
      { apply id_right. }
      etrans.
      2: { apply pathsinv0. apply id_left. }
      apply idpath.
  - intros X Y. red.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    etrans.
    { apply id_right. }
    etrans.
    2: { apply cancel_postcomposition.
         cbn.
         apply pathsinv0.
         apply id_right.
    }
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0.
         apply (functor_id(pr1 FF X)).
    }
    apply pathsinv0.
    apply id_left.
Defined.

Definition roundtrip2_ob_nat_trans_data_pointwise_inv
           (FF : Strong_Functor_precategory Mon_endo' domain_action target_action
                                            (functor_category_has_homsets C D hsD)) :
  Strong_Functor_Category_Mor Mon_endo' domain_action target_action FF
                              (ab_strong_functor_from_signature (signature_from_strong_functor FF)).
Proof.
  use tpair.
  - use make_nat_trans.
    + intro X. exact (identity (pr1 FF X)).
    + intros X1 X2 f.
      etrans.
      { apply id_right. }
      etrans.
      2: { apply pathsinv0. apply id_left. }
      apply idpath.
  - intros X Y. red.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    etrans.
    { apply id_right. }
    etrans.
    2: { apply cancel_postcomposition.
         cbn.
         apply pathsinv0.
         apply id_right.
    }
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0.
         apply (functor_id(pr1 FF X)).
    }
    apply pathsinv0.
    apply id_left.
Defined.

Definition roundtrip2_ob_data_is_nat_z_iso : is_nat_z_iso roundtrip2_ob_nat_trans_data.
Proof.
  intro FF.
  exists (roundtrip2_ob_nat_trans_data_pointwise_inv FF).
  abstract (split; apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets _ _ hsD);
    apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD);
    intro X;
    cbn;
    apply (id_left(C:=[C, D, hsD]))).
Defined.

Lemma roundtrip2_ob_data_is_nat_trans : is_nat_trans _ _ roundtrip2_ob_nat_trans_data.
Proof.
  intros FF GG sη.
  apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets C D hsD).
  apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
  intro X.
  etrans.
  { cbn. apply (id_right(C:=[C, D, hsD])). }
  etrans.
  2: { cbn. apply pathsinv0. apply (id_left(C:=[C, D, hsD])). }
  apply idpath.
Qed.

Definition roundtrip2_ob_nat_trans :
  ActionBasedStrongFunctorCategoryToSignatureCategory ∙ SignatureCategoryToActionBasedStrongFunctorCategory
  ⟹ functor_identity
  (Strong_Functor_precategory Mon_endo' domain_action target_action (functor_category_has_homsets C D hsD))
  := (roundtrip2_ob_nat_trans_data,,roundtrip2_ob_data_is_nat_trans).

Definition EquivalenceSignaturesABStrongFunctors:
  adj_equivalence_of_precats SignatureCategoryToActionBasedStrongFunctorCategory.
Proof.
  use make_adj_equivalence_of_precats.
  - exact ActionBasedStrongFunctorCategoryToSignatureCategory.
  - exact roundtrip1_ob_nat_trans.
  - exact roundtrip2_ob_nat_trans.
  - split.
    + intro sig. cbn.
      apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets C D hsD).
      apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
      intro X.
      cbn.
      apply (id_left(C:=[C, D, hsD])).
    + intro FF. cbn.
      apply SignatureMor_eq; try apply (functor_category_has_homsets C D hsD).
      apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
      intro X.
      cbn.
      apply (id_left(C:=[C, D, hsD])).
  - split.
    + intro sig.
      apply (z_iso_to_iso (_,,roundtrip1_ob_data_is_nat_z_iso sig)).
    + intro FF.
      apply (z_iso_to_iso (_,,roundtrip2_ob_data_is_nat_z_iso FF)).
Defined.

 (* the following lemma can only come from univalence of the involved categories *)
Lemma SignatureCategoryAndActionBasedStrongFunctorCategory_z_iso_law :
  is_inverse_in_precat(C:=bicat_of_cats_nouniv)
                      (a:=Signature_category (C,,hs) (D,,hsD) (D',,hsD'))
                      (b:=Strong_Functor_category Mon_endo' domain_action target_action
                                                  (functor_category_has_homsets _ _ hsD))
                      SignatureCategoryToActionBasedStrongFunctorCategory
                      ActionBasedStrongFunctorCategoryToSignatureCategory.
Proof.
Abort.

(*
Definition SignatureCategoryAndActionBasedStrongFunctorCategory_z_iso :
  z_iso(C:=bicat_of_cats_nouniv) (Signature_category (C,,hs) (D,,hsD) (D',,hsD'))
                      (Strong_Functor_category Mon_endo' domain_action target_action
                                               (functor_category_has_homsets _ _ hsD)).
Proof.
  exists SignatureCategoryToActionBasedStrongFunctorCategory.
  exists ActionBasedStrongFunctorCategoryToSignatureCategory.
  exact SignatureCategoryAndActionBasedStrongFunctorCategory_z_iso_law.
Defined.
*)

End Instantiation_To_FunctorCategory_And_PointedEndofunctors.
