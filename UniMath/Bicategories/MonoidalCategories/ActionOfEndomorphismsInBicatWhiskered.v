(** Constructs the actegory with the action of the endomorphisms by precomposition on a fixed hom-category of a bicategory

Author: Ralph Matthes 2022, extended in 2023

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.
Require Import UniMath.CategoryTheory.Actegories.Examples.ActionOfEndomorphismsInCATElementary.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.

Import Bicat.Notations.
Import BifunctorNotations.

Local Open Scope cat.

Section Action_From_Precomposition.

Context {C : bicat}.
Context (c0 d0 : ob C).

Local Definition endocat : category := hom c0 c0.
Local Definition Mon_endo: monoidal endocat := monoidal_from_bicat_and_ob c0.
Local Definition homcat : category := hom c0 d0.


Definition action_from_precomp_data : bifunctor_data endocat homcat homcat.
Proof.
  use make_bifunctor_data.
  - intros v f. exact (v · f).
  - intros v f1 f2 β. exact (v ◃ β).
  - intros f v1 v2 α. exact (α ▹ f).
Defined.

(* (** we explicitly do not opacify the following definition: *) *)
Definition action_from_precomp_laws : is_bifunctor action_from_precomp_data.
Proof.
  split5.
  - intros v f. apply lwhisker_id2.
  - intros f v. apply id2_rwhisker.
  - intros v f1 f2 f3 β1 β2. apply pathsinv0, lwhisker_vcomp.
  - intros f v1 v2 v3 α1 α2. apply pathsinv0, rwhisker_vcomp.
  - intros v1 v2 f1 f2 α β. apply vcomp_whisker.
Qed. (* Defined. *)

Definition action_from_precomp : bifunctor endocat homcat homcat :=
  make_bifunctor action_from_precomp_data action_from_precomp_laws.

Definition actegory_from_precomp_data : actegory_data Mon_endo homcat.
Proof.
  exists (pr1 action_from_precomp).
  split4.
  - intro f. apply lunitor.
  - intro f. apply linvunitor.
  - intros v w f. apply rassociator.
  - intros v w f. apply lassociator.
Defined.

Lemma actegory_from_precomp_laws : actegory_laws Mon_endo actegory_from_precomp_data.
Proof.
  split5.
  - exact action_from_precomp_laws.
  - split.
    + intros f g β. cbn. apply vcomp_lunitor.
    + split.
      * cbn. apply lunitor_linvunitor.
      * cbn. apply linvunitor_lunitor.
  - split4.
    + intros v w f f' β. cbn. apply lwhisker_lwhisker_rassociator.
    + intros v v' w f α. cbn. apply pathsinv0, rwhisker_rwhisker_alt.
    + intros v w w' f α. cbn. apply rwhisker_lwhisker_rassociator.
    + split.
      * cbn. apply rassociator_lassociator.
      * cbn. apply lassociator_rassociator.
  - intros v f. cbn. apply lunitor_lwhisker.
  - intros w v v' f. cbn. apply rassociator_rassociator.
Qed.

Definition actegory_from_precomp : actegory Mon_endo homcat :=
  actegory_from_precomp_data,,actegory_from_precomp_laws.

End Action_From_Precomposition.

Section LineatorForPostcomposition.

Context {C : bicat}.
Context (c0 d0 e0 : ob C) (g : hom d0 e0).

Definition lax_lineator_postcomp_actegories_from_precomp_data :
  lineator_data (Mon_endo c0) (actegory_from_precomp c0 d0) (actegory_from_precomp c0 e0) (post_comp c0 g).
Proof.
  intros f k. apply lassociator.
Defined.

Lemma lax_lineator_postcomp_actegories_from_precomp_laws :
  lineator_laxlaws (Mon_endo c0) (actegory_from_precomp c0 d0) (actegory_from_precomp c0 e0)
    (post_comp c0 g) lax_lineator_postcomp_actegories_from_precomp_data.
Proof.
  split4; intro; intros; cbn; unfold lax_lineator_postcomp_actegories_from_precomp_data.
  - apply rwhisker_lwhisker.
  - apply pathsinv0, rwhisker_rwhisker.
  - apply inverse_pentagon_7.
  - apply lunitor_triangle.
Qed.

Definition lax_lineator_postcomp_actegories_from_precomp :
  lineator_lax (Mon_endo c0) (actegory_from_precomp c0 d0) (actegory_from_precomp c0 e0) (post_comp c0 g) :=
  _,,lax_lineator_postcomp_actegories_from_precomp_laws.

End LineatorForPostcomposition.

Section TheHomogeneousCase.

Context {C : bicat}.
Context (c0 : ob C).

(** requires [action_from_precomp] with known proofs of the laws to hold with convertibility *)
Definition action_in_actegory_from_precomp_as_self_action :
  actegory_action (Mon_endo c0) (actegory_from_precomp c0 c0) = actegory_action (Mon_endo c0) (actegory_with_canonical_self_action (Mon_endo c0)).
Proof.
  use subtypePath.
  {
    intro ; apply isaprop_is_bifunctor.
  }
  apply idpath.
Defined.

(*
Lemma actegory_from_precomp_as_self_action :
  actegory_from_precomp c0 c0 = actegory_with_canonical_self_action (Mon_endo c0).
Proof.
  use total2_paths_f.
  2: { apply isaprop_actegory_laws. }
  use total2_paths_f.
  { apply action_in_actegory_from_precomp_as_self_action. }
  use total2_paths_f.
  { apply idpath. }
  use total2_paths_f.
  { apply idpath. }
  apply idpath.
Qed. (* slow *)

(** we should no longer need the proofs of the laws after this result  - is the following command effective? *)
(* Opaque action_from_precomp_laws. *)
*)

(** on the way to what we really need is the following convertibility: *)
Lemma lax_lineators_for_actegory_from_precomp_and_self_action_agree (F : functor (endocat c0) (endocat c0)) :
  lineator_lax (Mon_endo c0) (actegory_from_precomp c0 c0) (actegory_from_precomp c0 c0) F =
    lineator_lax (Mon_endo c0) (actegory_with_canonical_self_action (Mon_endo c0))
      (actegory_with_canonical_self_action (Mon_endo c0)) F.
Proof.
  assert (actegory_with_canonical_self_action (Mon_endo c0)
          =
          actegory_from_precomp c0 c0).
  {
    use subtypePath.
    {
      intro ; apply isaprop_actegory_laws.
    }
    apply idpath.
  }
  rewrite X.
  apply idpath.
Qed. (* 44s on a modern Intel machine *)
(** in fact, we need this with reindexed actegories everywhere *)

End TheHomogeneousCase.



Section Instantiation_To_Bicategory_Of_Categories.

  Context (C D : category).

  Definition actegoryfromprecomp : actegory (Mon_endo(C:=bicat_of_cats) C)
                                           (homcat(C:=bicat_of_cats) C D)
    := actegory_from_precomp(C:=bicat_of_cats) C D.

  Lemma actegoryfromprecomp_action_pointwise_ok (v : functor C C) (f : functor C D) :
    v ⊗_{actegoryfromprecomp} f = functor_compose v f.
  Proof.
    apply idpath.
  Qed.

  (* Transparent action_from_precomp_CAT_laws. *)
  Definition actegoryfromprecomp_actions_equal_statement : UU :=
    actegory_action (monendocat_monoidal C) (actegory_from_precomp_CAT C D)
    =
    actegory_action _ actegoryfromprecomp.

Lemma actegoryfromprecomp_actions_equal : actegoryfromprecomp_actions_equal_statement.
Proof.
  apply subtypePath.
  { intro. apply isaprop_is_bifunctor. }
  apply idpath.
Qed.

(*
(** on the way to what we really need is the following convertibility: *)
Definition lax_lineators_for_actegoryfromprecomp_and_CAT_version_agree_statement (F : functor [C, D] [C, D]) : UU :=
  lineator_lax (monendocat_monoidal C) actegoryfromprecomp actegoryfromprecomp F =
    lineator_lax (monendocat_monoidal C) (actegory_from_precomp_CAT C D) (actegory_from_precomp_CAT C D) F.
(* type-checking not seen to terminate!! *)

Lemma lax_lineators_for_actegoryfromprecomp_and_CAT_version_agree (F : functor [C, D] [C, D]) :
  lax_lineators_for_actegoryfromprecomp_and_CAT_version_agree_statement F.
Proof.
  Time (apply idpath). (* very slow: __ on a modern Intel machine *)
Time Qed. (* __ on a modern Intel machine *)
(** in fact, we need this with reindexed actegories everywhere *)
*)

Section DistributionOfCoproducts.

Section BinaryCoproduct.

  Context (BCP : BinCoproducts D).

  Definition BCP_homcat_CAT : BinCoproducts (homcat(C:=bicat_of_cats) C D).
  Proof.
    apply BinCoproducts_functor_precat.
    exact BCP.
  Defined.

  (*
  Definition actfromprecomp_bincoprod_distributor_data :
    actegory_bincoprod_distributor_data (Mon_endo(C:=bicat_of_cats) C) BCP_homcat_CAT actegoryfromprecomp.
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_data. (* slow *)
  Defined.

  Lemma actfromprecomp_bincoprod_distributor_law :
    actegory_bincoprod_distributor_iso_law _ _ _ actfromprecomp_bincoprod_distributor_data.
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_law. (* very slow *)
  Qed.

  Because type checking is so slow, we redo the construction and proof: *)

  Definition actfromprecomp_bincoprod_distributor_data :
    actegory_bincoprod_distributor_data (Mon_endo(C:=bicat_of_cats) C) BCP_homcat_CAT actegoryfromprecomp.
  Proof.
    intros F G1 G2.
    use make_nat_trans.
    - intro c. apply identity.
    - abstract (intros c c' f; rewrite id_left; apply id_right).
  Defined.

  Definition actfromprecomp_bincoprod_distributor_data_is_instance_up_to_eq :
    actfromprecomp_bincoprod_distributor_data = fun F => precomp_bincoprod_distributor_data BCP F.
  Proof.
    apply funextsec; intro F.
    apply funextsec; intro G1.
    apply funextsec; intro G2.
    apply nat_trans_eq; [ apply D |].
    intro x.
    apply idpath.
  Qed.

  Lemma actfromprecomp_bincoprod_distributor_law :
    actegory_bincoprod_distributor_iso_law _ _ _ actfromprecomp_bincoprod_distributor_data.
  Proof.
    intros F G.
    split.
    - apply nat_trans_eq; [apply D |].
      intro c.
      cbn.
      rewrite id_left.
      apply pathsinv0, BinCoproduct_endo_is_identity.
      + apply BinCoproductIn1Commutes.
      + apply BinCoproductIn2Commutes.
    - etrans.
      { apply postcompWithBinCoproductArrow. }
      etrans.
      2: { apply pathsinv0, BinCoproductArrowEta. }
      apply maponpaths_12;
        (rewrite id_right; apply nat_trans_eq; [apply D |]; intro c; apply id_right).
  Qed.

  Definition actfromprecomp_bincoprod_distributor :
    actegory_bincoprod_distributor (Mon_endo(C:=bicat_of_cats) C) BCP_homcat_CAT actegoryfromprecomp :=
    _,,actfromprecomp_bincoprod_distributor_law.

End BinaryCoproduct.

Section Coproduct.

  Context {I : UU} (CP : Coproducts I D).

  Definition CP_homcat_CAT : Coproducts I (homcat(C:=bicat_of_cats) C D).
  Proof.
    apply Coproducts_functor_precat.
    exact CP.
  Defined.

  Definition actfromprecomp_coprod_distributor_data :
    actegory_coprod_distributor_data (Mon_endo(C:=bicat_of_cats) C) CP_homcat_CAT actegoryfromprecomp.
  Proof.
    intros F Gs.
    cbn.
    use make_nat_trans.
    - intro c. apply identity.
    - abstract (intros c c' f; rewrite id_left; apply id_right).
  Defined.

  Definition actfromprecomp_coprod_distributor_data_is_instance_up_to_eq :
    actfromprecomp_coprod_distributor_data = fun F => precomp_coprod_distributor_data CP F.
  Proof.
    apply funextsec; intro F.
    apply funextsec; intro Gs.
    apply nat_trans_eq; [ apply D |].
    intro x.
    apply idpath.
  Qed.

  Lemma actfromprecomp_coprod_distributor_law :
    actegory_coprod_distributor_iso_law _ _ _ actfromprecomp_coprod_distributor_data.
  Proof.
    intros F Gs.
    split.
    - apply nat_trans_eq; [apply D |].
      intro c.
      cbn.
      rewrite id_left.
      apply pathsinv0, Coproduct_endo_is_identity.
      intro i.
      unfold coproduct_nat_trans_data.
      cbn in Gs.
      apply (CoproductInCommutes I D (λ i0 : I, Gs i0 (pr1 F c)) (CP _) _
               (λ i0 : I, coproduct_nat_trans_in_data I C D CP Gs i0 (pr1 F c)) i).
    - etrans.
      { apply postcompWithCoproductArrow. }
      etrans.
      2: { apply pathsinv0, CoproductArrowEta. }
      apply maponpaths, funextsec; intro i;
        (rewrite id_right; apply nat_trans_eq; [apply D |]; intro c; apply id_right).
  Qed.

  Definition actfromprecomp_coprod_distributor :
    actegory_coprod_distributor (Mon_endo(C:=bicat_of_cats) C) CP_homcat_CAT actegoryfromprecomp :=
    _,,actfromprecomp_coprod_distributor_law.

End Coproduct.

End DistributionOfCoproducts.

End Instantiation_To_Bicategory_Of_Categories.
