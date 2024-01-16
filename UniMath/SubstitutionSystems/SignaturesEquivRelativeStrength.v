From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(** material that was previously located in [Signatures.v]

the relation between (semantic) signatures and relative strength (considered in TYPES 2015 post-proceedings paper
by Ahrens and Matthes)

 *)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrength.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsMonoidal.

Local Open Scope subsys.
Section homogeneous_case.

Context (C : category).

Local Lemma auxH1 (H : functor [C, C] [C, C]) (X : functor C C) :
  # H
    (nat_trans_comp
       (X
        ∘ nat_z_iso_to_trans_inv
            (make_nat_z_iso (functor_identity C) (functor_identity C)
               (nat_trans_id (functor_identity_data C))
               (is_nat_z_iso_nat_trans_id (functor_identity C))))
       (nat_trans_id (pr1 X) ø functor_identity_data C)) =
  identity (H (functor_identity C ∙ X)).
Proof.
  apply functor_id_id.
  apply nat_trans_eq_alt; intro c.
  cbn.
  rewrite id_right.
  apply functor_id.
Qed.

Local Lemma auxH2aux (X : functor C C) (Z Z': precategory_Ptd C):
  nat_trans_comp
       (X ∘ identity (functor_compose (pr1 Z) (pr1 Z')))
       (identity(C:=[C, C]) (X) ø (pr1 (functor_compose (pr1 Z) (pr1 Z')))) =
    identity (functor_compose (functor_compose (pr1 Z) (pr1 Z')) X).
Proof.
  apply nat_trans_eq; try apply homset_property; intro c.
  cbn.
  rewrite id_right.
  apply functor_id.
Qed.

Local Definition ptd := monoidal_cat_of_pointedfunctors C.
Local Definition endo := monoidal_cat_of_endofunctors C.
Local Definition forget := forgetful_functor_from_ptd_as_strong_monoidal_functor C.

Section relative_strength_instantiates_to_signature.

  Context (H : functor [C, C] [C, C])
          (rs : rel_strength forget H).

  Local Definition ϛ : rel_strength_nat forget H := pr1 rs.

  Local Definition ϛ_pentagon_eq : rel_strength_pentagon_eq forget H ϛ
    := pr1 (pr2 rs).

  Local Definition ϛ_rectangle_eq : rel_strength_rectangle_eq forget H ϛ
    := pr2 (pr2 rs).

  Local Definition θ : θ_source H ⟹ θ_target H
    := pre_whisker binswap_pair_functor ϛ.

  Lemma signature_from_rel_strength_laws : θ_Strength1_int θ ×
                                           θ_Strength2_int θ.
  Proof.
    split; red.
    - intro X.
      cbn.
      apply nat_trans_eq_alt; intro c.
      cbn.
      assert (Hyp := nat_trans_eq_weq (homset_property C) _ _ (ϛ_pentagon_eq X) c).
      cbn in Hyp.
      rewrite (functor_id (H X)) in Hyp.
      do 2 rewrite id_left in Hyp.
      etrans; [| exact Hyp].
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      etrans.
      { apply pathsinv0.
        apply id_left. }
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_eq_weq (homset_property C) _ _ (auxH1 H X) c).
    - intros X Z Z'.
      cbn.
      apply nat_trans_eq; try apply homset_property; intro c.
      cbn.
      rewrite id_left.
      assert (Hyp := nat_trans_eq_weq (homset_property C) _ _ (ϛ_rectangle_eq Z Z' X) c).
      cbn in Hyp.
      do 2 rewrite functor_id in Hyp.
      rewrite (functor_id (H X)) in Hyp.
      do 2 rewrite id_right in Hyp.
      do 2 rewrite id_left in Hyp.
      etrans; [| exact Hyp ].
      clear Hyp.
      apply cancel_postcomposition.
      etrans.
      { apply pathsinv0. apply id_right. }
      apply maponpaths.
      apply pathsinv0.
      etrans.
      { use (maponpaths (fun x => pr1 (# H x) c)).
        + exact (identity (functor_compose (functor_compose (pr1 Z) (pr1 Z')) X)).
        + apply auxH2aux.
      }
      rewrite functor_id.
      apply idpath.
  Qed.

  Definition signature_from_rel_strength : Signature C C C.
  Proof.
    exists H. exists θ.
    exact signature_from_rel_strength_laws.
  Defined.

End relative_strength_instantiates_to_signature.

Section strength_in_signature_is_a_relative_strength.

  Context (sig : Signature C C C).

  Local Definition H := pr1 sig.
  Local Definition θ' := pr1 (pr2 sig).
  Local Definition ϛ' : rel_strength_nat forget H := pre_whisker binswap_pair_functor θ'.

  Local Definition θ'_strength_law1 := Sig_strength_law1 sig.
  Local Definition θ'_strength_law2 := Sig_strength_law2 sig.

  Lemma rel_strength_from_signature_laws : rel_strength_pentagon_eq forget H ϛ' ×
                                           rel_strength_rectangle_eq forget H ϛ'.
  Proof.
    split.
    - intro X.
      apply nat_trans_eq_alt; intro c.
      cbn.
      assert (Hyp := nat_trans_eq_weq (homset_property C) _ _ (θ'_strength_law1 X) c).
      cbn in Hyp.
      fold θ' H in Hyp.
      rewrite (functor_id (H X)).
      do 2 rewrite id_left.
      etrans; [| exact Hyp ].
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      etrans.
      { apply pathsinv0.
        apply id_left. }
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_eq_weq (homset_property C) _ _ (auxH1 H X) c).
    - intros Z Z' X.
      apply nat_trans_eq_alt; intro c.
      cbn.
      unfold PointedFunctorsComposition.ptd_compose.
      rewrite functorial_composition_post_pre.
      assert (Hyp := nat_trans_eq_weq (homset_property C) _ _ (θ'_strength_law2 X Z Z') c).
      cbn in Hyp.
      fold θ' H in Hyp.
      do 2 rewrite functor_id.
      do 2 rewrite id_right.
      rewrite (functor_id (H X)).
      do 2 rewrite id_left.
      rewrite id_left in Hyp.
      etrans; [| exact Hyp ].
      clear Hyp.
      apply cancel_postcomposition.
      etrans; [| apply id_right ].
      apply maponpaths.
      (** now identical reasoning as in [signature_from_rel_strength_laws] *)
      etrans.
      { use (maponpaths (fun x => pr1 (# H x) c)).
        + exact (identity (functor_compose (functor_compose (pr1 Z) (pr1 Z')) X)).
        + apply auxH2aux. }
      rewrite functor_id.
      apply idpath.
  Qed.

  Definition rel_strength_from_signature : rel_strength forget H := (ϛ',,rel_strength_from_signature_laws).

End strength_in_signature_is_a_relative_strength.

End homogeneous_case.
