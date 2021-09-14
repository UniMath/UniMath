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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFromBicategory.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrongFunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCatsWithoutUnivalence.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.CategoryTheory.Core.Univalence.


Import Bicat.Notations.

Local Open Scope cat.

Section ActionBased_Strength_Between_Homs_In_Bicat.

Context {C : bicat}.
Context (c0 d0 d0': ob C).
Context {Mon_M : monoidal_precat}.

Local Definition Mon_endo: monoidal_precat
  := swapping_of_monoidal_precat (monoidal_precat_from_prebicat_and_ob c0).

Context (U: strong_monoidal_functor Mon_M Mon_endo).

Local Definition ab_strength_domain_action : action Mon_M (hom c0 d0')
  := lifted_action Mon_M U (action_from_precomp c0 d0').
Local Definition ab_strength_target_action : action Mon_M (hom c0 d0)
  := lifted_action Mon_M U (action_from_precomp c0 d0).

Context (F: hom c0 d0' ⟶ hom c0 d0).

Definition ab_strength_on_homs_in_bicat: UU
  := actionbased_strength Mon_M ab_strength_domain_action ab_strength_target_action F.

Identity Coercion ab_strength_on_homs_in_bicat_to_actionbased_strength :
  ab_strength_on_homs_in_bicat  >-> actionbased_strength.

Context (ab_str : ab_strength_on_homs_in_bicat).

Definition triangle_eq := actionbased_strength_triangle_eq Mon_M
  ab_strength_domain_action ab_strength_target_action F ab_str.
Definition pentagon_eq := actionbased_strength_pentagon_eq Mon_M
  ab_strength_domain_action ab_strength_target_action F ab_str.

Lemma triangle_eq_readable : triangle_eq = ∏ a : C ⟦ c0, d0' ⟧,
  ab_str (a,, monoidal_precat_unit Mon_M) • # F (id₂ a ⋆⋆ (strong_monoidal_functor_ϵ_inv U) • lunitor a) =
  id₂ (F a) ⋆⋆ (strong_monoidal_functor_ϵ_inv U) • lunitor (F a).
Proof.
  apply idpath.
Qed.

Definition triangle_eq_nice : UU := ∏ X : C ⟦ c0, d0' ⟧,
  ab_str (X,, monoidal_precat_unit Mon_M) • # F (strong_monoidal_functor_ϵ_inv U ▹ X • lunitor X) =
  strong_monoidal_functor_ϵ_inv U ▹ F X • lunitor (F X).

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

Lemma pentagon_eq_readable : pentagon_eq =
  ∏ (a : C ⟦ c0, d0' ⟧) (x y : Mon_M),
                        (lassociator (U y) (U x) (F a) • id₂ (F a) ⋆⋆ lax_monoidal_functor_μ U (x,, y))
                          • ab_str (a,, monoidal_precat_tensor Mon_M (x, y)) =
                        ab_str (a,, x) ⋆⋆ # U (id₁ y) • ab_str (U x · a,, y)
                          • # F (lassociator (U y) (U x) a • id₂ a ⋆⋆ lax_monoidal_functor_μ U (x,, y)).
Proof.
  apply idpath.
Qed.


(** the variables chosen in the following make the link with the notion of signature
    in the TYPES'15 paper by Ahrens and Matthes more visible - but Z is written insted
    of (Z,e), and likewise for Z' *)

Definition pentagon_eq_nice : UU :=
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : Mon_M),
    lassociator (U Z) (U Z') (F X) • (lax_monoidal_functor_μ U (Z',, Z) ▹ F X) • ab_str (X,, monoidal_precat_tensor Mon_M (Z', Z)) =
    U Z ◃ ab_str (X,, Z') • ab_str (U Z' · X,, Z) • # F (lassociator (U Z) (U Z') X • (lax_monoidal_functor_μ U (Z',, Z) ▹ X)).

Lemma pentagon_eq_implies_pentagon_eq_nice : pentagon_eq -> pentagon_eq_nice.
Proof.
  intros Heq X Z' Z.
  assert (Heqinst := Heq X Z' Z).
  clear Heq.
  revert Heqinst.
  simpl.
  rewrite (functor_id U).
  intro Heqinst.
  refine (!_ @ Heqinst @ _).
  - cbn.
    apply maponpaths_2.
    apply maponpaths.
    exact (hcomp_identity_right _ _ (F X) (lax_monoidal_functor_μ U (Z',, Z))).
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
  rewrite (functor_id U).
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

Definition μ_UZ'Zinv (Z' Z : Mon_M) :
  hom c0 c0 ⟦ monoidal_functor_map_codom Mon_M Mon_endo U (Z',, Z),
              monoidal_functor_map_dom Mon_M Mon_endo U (Z',, Z) ⟧
  := strong_monoidal_functor_μ_inv U (Z',,Z).

Definition pentagon_eq_nicer : UU :=
  ∏ (X : C ⟦ c0, d0' ⟧) (Z' Z : Mon_M),
                         lassociator (U Z) (U Z') (F X) • (lax_monoidal_functor_μ U (Z',, Z) ▹ F X) •
                         ab_str (X,, monoidal_precat_tensor Mon_M (Z', Z)) •
                         # F ((μ_UZ'Zinv Z' Z ▹ X) • rassociator (U Z) (U Z') X) =
                         U Z ◃ ab_str (X,, Z') • ab_str (U Z' · X,, Z).

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
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (strong_monoidal_functor_μ U) (Z',,Z))).
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
    apply (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso (strong_monoidal_functor_μ U) (Z',,Z))).
  }
  apply id2_rwhisker.
Qed.
(* slow verification *)


End ActionBased_Strength_Between_Homs_In_Bicat.

Section Instantiation_To_FunctorCategory_And_PointedEndofunctors.

Section a_different_type_for_the_forgetful_functor_from_ptd.
  Context {C : precategory}.
  Context (hs : has_homsets C).

  Definition functor_ptd_forget_alt
    : precategory_Ptd C hs
      ⟶
      precategory_from_prebicat_and_ob(C:=pr1 bicat_of_cats_nouniv) (C,, hs).
  Proof.
    use make_functor.
    - exists (λ a, pr1 a).
      exact (λ a b f, pr1 f).
    - abstract (split; intros; red; intros; apply idpath).
  Defined.

  Local Definition aux : monoidal_functor_map (monoidal_precat_of_pointedfunctors hs)
                                              (monoidal_precat_from_prebicat_and_ob(C:=pr1 bicat_of_cats_nouniv) (C,, hs)) functor_ptd_forget_alt.
  Proof.
    red.
    use make_nat_trans.
    - intro x. cbn. apply nat_trans_id.
    - abstract
        (red ; intros ; apply nat_trans_eq; try assumption ;
         intro y ; cbn ; rewrite id_left ; rewrite id_right ; apply nat_trans_ax).
  Defined.

  Definition forgetful_functor_from_ptd_as_strong_monoidal_functor_alt
   : strong_monoidal_functor (monoidal_precat_of_pointedfunctors hs)
                                              (monoidal_precat_from_prebicat_and_ob (C:=pr1 bicat_of_cats_nouniv) (C,,hs)).
  Proof.
    use tpair.
    - apply (mk_lax_monoidal_functor (monoidal_precat_of_pointedfunctors hs)
                       (monoidal_precat_from_prebicat_and_ob (C:=pr1 bicat_of_cats_nouniv) (C,, hs))
                       functor_ptd_forget_alt (nat_trans_id _) aux).
      + abstract
          (intros PF1 PF2 PF3 ;
           apply nat_trans_eq; try assumption ;
           intro c ;
           cbn ;
           do 2 rewrite functor_id ;
           repeat rewrite id_right ;
           apply functor_id).
      + abstract
          (intro PF ;
           split; apply nat_trans_eq; try assumption; intro c; cbn ;
             [ do 3 rewrite id_right ;
               apply pathsinv0 ;
               apply functor_id
             | do 3 rewrite id_right ;
               apply idpath]).
    - split ;
        [ apply (nat_trafo_z_iso_if_pointwise_z_iso C C hs);
          apply is_nat_z_iso_nat_trans_id
        | red ; intro c ;
          exists (nat_trans_id _) ;
          split; cbn ;
          [ apply nat_trans_eq; try assumption; intro c'; cbn ;
            apply id_left
          | apply nat_trans_eq; try assumption; intro c'; cbn ;
            apply id_left ]].
  Defined.

End a_different_type_for_the_forgetful_functor_from_ptd.

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

Local Definition Mon_endo' : monoidal_precat := swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs).
Local Definition domain_action : action Mon_endo' (hom(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD'))
    := ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget.
Local Definition target_action : action Mon_endo' (hom(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD))
    := ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget.


Section Signature_From_ActionBased_Strength.

Section IndividualFunctorsWithABStrength.

  Context (H : functor [C, D', hsD'] [C, D, hsD]).


  Definition ab_strength_for_functors_and_pointed_functors : UU
    := ab_strength_on_homs_in_bicat(C:=bicat_of_cats_nouniv) (C,,hs) (D,,hsD) (D',,hsD') forget H.

  Definition ab_strength_for_functors_and_pointed_functors_to_actionbased_strength
             (ab_str : ab_strength_for_functors_and_pointed_functors) :
    actionbased_strength (swapping_of_monoidal_precat (monoidal_precat_of_pointedfunctors hs))
                         (ab_strength_domain_action(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD') forget)
                         (ab_strength_target_action(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD) forget) H
    := ab_str.
  Coercion ab_strength_for_functors_and_pointed_functors_to_actionbased_strength :
    ab_strength_for_functors_and_pointed_functors >-> actionbased_strength.

  Context (ab_str : ab_strength_for_functors_and_pointed_functors).

  (* adapt typing of [pr1 ab_str] for use in [Signature] *)
  Definition θ_for_signature_nat_trans_data : nat_trans_data (θ_source(hs:=hs) H) (θ_target H).
  Proof.
    intro x. exact (ab_str x).
  Defined.

  Lemma θ_for_signature_is_nat_trans : is_nat_trans _ _ θ_for_signature_nat_trans_data.
  Proof.
    intros x x' f.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    assert (Heq := nat_trans_ax ab_str x x' f).
    assert (Heqc := nat_trans_eq_weq hsD _ _ Heq c).
    clear Heq.
    cbn in Heqc.
    (* term precomposed with θ' x' c in goal and [Heqc]: *)
    assert (Heq0 : pr1(# H (pr1 f)) (pr12 x c) · # (pr1(H (pr1 x'))) (pr12 f c) =
                     # (pr1 (H (pr1 x))) (pr12 f c) · pr1(# H (pr1 f)) (pr12 x' c)).
    { apply pathsinv0. apply nat_trans_ax. }
    etrans.
    { apply cancel_postcomposition. exact Heq0. }
    clear Heq0.
    etrans.
    { exact Heqc. }
    clear Heqc.
    apply maponpaths.
    apply nat_trans_eq_pointwise.
    apply maponpaths.
    apply pathsinv0.
    apply horcomp_post_pre.
  Time Qed. (* very slow verification *)

  Definition θ_for_signature : θ_source (hs:=hs) H ⟹ θ_target H
    := (θ_for_signature_nat_trans_data,,θ_for_signature_is_nat_trans).

  Lemma signature_from_ab_strength_law1 : θ_Strength1_int θ_for_signature.
    red. intro X.
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    assert (HypX := triangle_eq_implies_triangle_eq_nice _ _ _ _ _ _ (ab_strength_triangle _ ab_str) X).
    assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
    cbn in Heqc.
    intermediate_path (# (pr1 (H X)) (id₁ c) · id₁ (pr1(pr1 H X) c)).
    2: {  etrans.
          { apply id_right. }
          apply (functor_id (H X)).
    }
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
    etrans.
    { apply id_right. }
    apply functor_id.
  Qed.

 Lemma signature_from_ab_strength_law2 : θ_Strength2_int θ_for_signature.
    intros X Z Z'.
    apply nat_trans_eq; try (apply hsD).
    intro c.
    assert (HypX := pentagon_eq_nice_implies_pentagon_eq_nicer _ _ _ _ _ _
                    (pentagon_eq_implies_pentagon_eq_nice _ _ _ _ _ _
                     (ab_strength_pentagon _ ab_str)) X Z' Z).
    assert (Heqc := nat_trans_eq_weq hsD _ _ HypX c).
    clear HypX.
    etrans.
    2: { apply assoc. }
    etrans.
    2: { apply maponpaths.
         simpl in Heqc.
         exact Heqc. }
    clear Heqc.
    etrans.
    2: { apply pathsinv0. apply id_left. }
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0.
         apply remove_id_left.
         - etrans.
           { apply id_left. }
           apply functor_id.
         - apply idpath.
    }
    simpl.
    apply maponpaths.
    apply nat_trans_eq_pointwise.
    clear c.
    apply maponpaths.
    apply nat_trans_eq; try (apply hsD').
    intro c.
    etrans.
    2: { apply pathsinv0.
         apply id_right. }
    apply pathsinv0.
    simpl.
    apply functor_id.
 Time Qed.

  Definition signature_from_ab_strength : Signature C hs D hsD D' hsD'.
  Proof.
    exists H.
    exists θ_for_signature.
    split.
    - exact signature_from_ab_strength_law1.
    - exact signature_from_ab_strength_law2.
  Defined.

End IndividualFunctorsWithABStrength.

Section IndividualStrongFunctors.

  Context (FF : actionbased_strong_functor Mon_endo' domain_action target_action).

  Definition signature_from_strong_functor : Signature C hs D hsD D' hsD' :=
    signature_from_ab_strength FF (pr2 FF).

End IndividualStrongFunctors.

Section Morphisms.

  Context {FF GG : actionbased_strong_functor Mon_endo' domain_action target_action}.
  Context (sη : Strong_Functor_Category_Mor Mon_endo' domain_action target_action
                                            (functor_category_has_homsets _ _ hsD) FF GG).

  Lemma signature_mor_from_ab_strength_mor_diagram (X : [C, D', hsD']) (Y : precategory_Ptd C hs) :
    Signature_category_mor_diagram (C,, hs) (D,, hsD) (D',, hsD')
      (signature_from_strong_functor FF) (signature_from_strong_functor GG) sη X Y.
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
    exists (pr1 sη). (* better not first cbn and then omission of pr1 - for the sake of efficiency *)
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

  Local Lemma aux0 ( x : [C, D', hsD'] ⊠ Mon_endo') :
    hom(C:=bicat_of_cats_nouniv) (C,, hs) (D,, hsD)
       ⟦ actionbased_strength_dom Mon_endo' target_action sig x,
         actionbased_strength_codom Mon_endo' domain_action sig x ⟧
    = functor_composite_data (pr12 x) (pr1 (sig (pr1 x))) ⟹  pr1 (sig (pr12 x ∙ pr1 x)).
  Proof.
    apply idpath.
  Defined.

  Definition θ_for_ab_strength_data
    : nat_trans_data (actionbased_strength_dom Mon_endo' target_action sig)
                     (actionbased_strength_codom Mon_endo' domain_action sig).
  Proof.
    intro x.
    exact (eqweqmap (!aux0 x) (theta sig x)).
  Defined.

  Definition θ_for_ab_strength_ax : is_nat_trans _ _ θ_for_ab_strength_data.
  Proof.
    intros x x' f.
    apply nat_trans_eq; try assumption.
    intro c.
    assert (Heq := nat_trans_ax (theta sig) x x' f).
    assert (Heqc := nat_trans_eq_weq hsD _ _ Heq c).
    clear Heq.
    (* term precomposed with [theta sig x' c] in [Heqc] and goal: *)
    assert (Heq0 : pr1(# sig (pr1 f)) (pr12 x c) · # (pr1(sig (pr1 x'))) (pr12 f c) =
                   # (pr1 (sig (pr1 x))) (pr12 f c) · pr1 (# sig (pr1 f)) (pr12 x' c)).
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

  Definition θ_for_ab_strength : actionbased_strength_nat Mon_endo' domain_action target_action sig.
  Proof.
    use make_nat_trans.
    - exact θ_for_ab_strength_data.
    - exact θ_for_ab_strength_ax.
  Defined.
  (* very slow processing of both steps then verification *)

  Lemma θ_for_ab_strength_law1 :
    actionbased_strength_triangle_eq Mon_endo' domain_action target_action sig θ_for_ab_strength.
  Proof.
    red. intro X.
    assert (HypX := Sig_strength_law1 sig X).
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    etrans.
    2: { apply pathsinv0.
         etrans.
         { apply id_right. }
         etrans.
         { apply id_right. }
         apply (functor_id (sig X)).
    }
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
    : actionbased_strength_pentagon_eq Mon_endo' domain_action target_action sig θ_for_ab_strength.
  Proof.
    intros X Z' Z.
    cbn.
    apply nat_trans_eq; try (exact hsD).
    intro c.
    simpl.
    assert (HypX := θ_Strength2_int_implies_θ_Strength2_int_nicer _
                        (Sig_strength_law2 sig) X Z Z').
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
    ab_strength_for_functors_and_pointed_functors sig.
  Proof.
    exists θ_for_ab_strength.
    split.
    - exact θ_for_ab_strength_law1.
    - exact θ_for_ab_strength_law2.
  Defined.

  Definition ab_strong_functor_from_signature :
    actionbased_strong_functor Mon_endo' domain_action target_action
    := (pr1 sig,,ab_strength_from_signature).

End IndividualSignatures.

Section Morphisms.

  Context {sig1 sig2 : Signature C hs D hsD D' hsD'}.
  Context (f : SignatureMor (C,,hs) (D,,hsD) (D',,hsD') sig1 sig2).

  Lemma ab_strength_mor_from_signature_mor_is_nat_trans :
    is_nat_trans _ _ (pr11 f).
  Proof.
    red.
    intros F F' g.
    cbn.
    assert (Hyp := pr21 f F F' g).
    exact Hyp.
  Qed.

  Definition ab_strength_mor_from_signature_mor_nat_trans :
     ab_strong_functor_from_signature sig1 ⟹ ab_strong_functor_from_signature sig2.
  Proof.
    exists (pr11 f).
    exact ab_strength_mor_from_signature_mor_is_nat_trans.
  Defined.

  Lemma ab_strength_mor_from_signature_mor_diagram
        (a : hom(C:=bicat_of_cats_nouniv) (C,, hs) (D',, hsD'))
        (v : Mon_endo') :
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
    (functor_category_has_homsets _ _ hsD)
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

(* the following lemma cannot be used in the construction of the equivalence of precategories *)
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
    + intro X. exact (identity (pr1(pr1 sig) X)).
    + intros X1 X2 f.
      etrans.
      { apply (id_right (# (pr11 sig) f)). }
      etrans.
      2: { apply pathsinv0. apply (id_left (# (pr11 sig) f)). }
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
         apply (functor_id (pr11 sig X)).
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
    + intro X. exact (identity (pr11 sig X)).
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
         apply (functor_id (pr11 sig X)).
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


(* the following lemma cannot be used in the construction of the equivalence of precategories *)
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
    + intro X. exact (identity (pr1 (pr1 FF) X)).
    + intros X1 X2 f.
      etrans.
      { apply (id_right (#(pr11 FF) f)). }
      etrans.
      2: { apply pathsinv0. apply (id_left (#(pr11 FF) f)). }
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
         apply (functor_id (pr11 FF X)).
    }
    apply pathsinv0.
    apply id_left.
Defined.

Definition roundtrip2_ob_nat_trans_data_pointwise_inv
           (FF : Strong_Functor_precategory Mon_endo' domain_action target_action
                                            (functor_category_has_homsets C D hsD)) :
  Strong_Functor_Category_Mor Mon_endo' domain_action target_action (functor_category_has_homsets C D hsD) FF
                              (ab_strong_functor_from_signature (signature_from_strong_functor FF)).
Proof.
  use tpair.
  - use make_nat_trans.
    + intro X. exact (identity (pr11 FF X)).
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
         apply (functor_id (pr11 FF X)).
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
    + intro sig.
      apply Strong_Functor_Category_Mor_eq; try apply (functor_category_has_homsets C D hsD).
      cbn.
      apply nat_trans_eq; try apply (functor_category_has_homsets _ _ hsD).
      intro X.
      cbn.
      apply (id_left(C:=[C, D, hsD])).
    + intro FF.
      apply SignatureMor_eq; try apply (functor_category_has_homsets C D hsD).
      cbn.
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

(* source and target category of the functors are deemed to be univalent if parameter category D is *)
Definition Signature_category_is_univalent (univD : is_univalent D) :
  is_univalent (Signature_category (C,,hs) (D,,hsD) (D',,hsD')).
Proof.
  set (univalentD := make_univalent_category D (make_is_univalent (pr1 univD) hsD)).
  exact (is_univalent_Signature_precategory (C,, hs) univalentD (D',, hsD')).
Defined.

(** the remainder of this file documents failing efforts *)

(*

(* some hopeless efforts *)
Lemma Strong_Functor_category_is_univalent (univD : is_univalent D) :
  is_univalent (Strong_Functor_category Mon_endo' domain_action target_action
                                        (functor_category_has_homsets _ _ hsD)).
Proof.
  set (univalentD := make_univalent_category D (make_is_univalent (pr1 univD) hsD)).
  set (univalentA' := make_univalent_category [C, D, hsD] (make_is_univalent (pr1(is_univalent_functor_category C D (pr1 univD,,hsD))) (functor_category_has_homsets _ _ hsD))).
  change (is_univalent
              (Strong_Functor_category Mon_endo' domain_action target_action (homset_property univalentA'))).
  assert (target_action' := target_action).
  change (action Mon_endo' (hom(C:=bicat_of_cats_nouniv) (C,, hs) (univalent_category_to_category univalentD))) in target_action'.

(*
    exact (is_univalent_Strong_Functor_precategory Mon_endo' [C, D', hsD'] univalentA' domain_action target_action').
*)


 (* the following lemma can only come from univalence of the involved categories *)
Lemma SignatureCategoryAndActionBasedStrongFunctorCategory_z_iso_law :
  is_inverse_in_precat(C:=bicat_of_cats_nouniv)
                      (a:=Signature_category (C,,hs) (D,,hsD) (D',,hsD'))
                      (b:=Strong_Functor_category Mon_endo' domain_action target_action
                                                  (functor_category_has_homsets _ _ hsD))
                      SignatureCategoryToActionBasedStrongFunctorCategory
                      ActionBasedStrongFunctorCategoryToSignatureCategory.
Proof.

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


*)
End Instantiation_To_FunctorCategory_And_PointedEndofunctors.

(*
Section Instantiation_To_FunctorCategory_And_PointedEndofunctors_Univalence.
  Context (C : category) (D : univalent_category) (D' : category).
  Definition BothCategoriesUnivalent:
  is_univalent (Signature_category C D D') ×
               is_univalent (Strong_Functor_category (Mon_endo' C (homset_property C))
                                                     (domain_action C (homset_property C) D' (homset_property D'))
                                                     (target_action C (homset_property C) D (homset_property D))
                                                     (functor_category_has_homsets _ _ (homset_property D))).
  Proof.
    split.
    - exact (is_univalent_Signature_precategory C D D').
    - set (univalentA' := make_univalent_category [C, D, homset_property D]
                           (is_univalent_functor_category C D (univalent_category_is_univalent D))).
      change (is_univalent (Strong_Functor_category (Mon_endo' C (homset_property C))
                                                    (domain_action C (homset_property C) D' (homset_property D'))
                                                    (target_action C (homset_property C) D (homset_property D))
                                                    (homset_property univalentA'))).
      (* for checking purposes: *)
      assert (target := target_action C (homset_property C) D (homset_property D)).
      (* the following works but does not help in the sequel:
      change (action (Mon_endo' C (homset_property C)) (hom(C:=bicat_of_cats_nouniv) C (univalent_category_to_category D))) in target. *)
      assert (test1 : pr1 univalentA' = [C, D, homset_property D]).
      { apply idpath. }
      clear test1.
      set (test2 := pr22 univalentA').
      cbn in test2. unfold functor_category_has_homsets in test2.
      set (test3 := pr2 bicat_of_cats_nouniv C (univalent_category_to_category D)).
      cbn in test3. unfold isaset_cells_prebicat_of_cats_nouniv in test3.
      assert (test4 : test3 = test2).
      { apply idpath. } (* okay thanks to changes in UniMath/Bicategories/Core/Examples/BicatOfCatsWithoutUnivalence.v
       and UniMath/CategoryTheory/FunctorCategory.v  *)
      clear test2 test3 test4.
      (* does not terminate:
      change (action (Mon_endo' C (homset_property C)) (univalentA')) in target. *)

      (*
      assert (Hyp: action (Mon_endo' C (homset_property C)) (hom(C:=bicat_of_cats_nouniv) C (univalent_category_to_category D)) <->
                   action (Mon_endo' C (homset_property C)) (univalentA')).
      { split.
        intro act.
        induction act as [odot [ρ [χ [triangle pentagon]]]].
        exists odot.
        exists ρ.
        (* does not terminate: exists χ. *)
      }
*)
      set (what_we_want_without_last_argument := is_univalent_Strong_Functor_precategory (Mon_endo' C (homset_property C))
                                                     (hom(C:=bicat_of_cats_nouniv) C D')
                                                     univalentA'
                                                     (domain_action C (homset_property C) D' (homset_property D'))).
      (* does not terminate
      set (what_we_want :=  what_we_want_without_last_argument (target_action C (homset_property C) D (homset_property D))).
       *)

                                     (*
      exact what_we_want.
  Defined.*)


  End Instantiation_To_FunctorCategory_And_PointedEndofunctors_Univalence.
*)
