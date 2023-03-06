(** Studies the actegory stemming from the self action of the endofunctors on [C] by precomposition

author: Ralph Matthes, 2023
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Actegories.Examples.ActionOfEndomorphismsInCATWhiskeredElementary.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.

Local Open Scope cat.

Section FixACategory.

Context (C : category).

Local Definition Mon_endo : monoidal [C, C] := monendocat_monoidal C.

Definition SelfActCAT : actegory Mon_endo [C, C] := actegory_with_canonical_self_action Mon_endo.

End FixACategory.

Section LineatorForPostcomposition.

  Context (C : category) (G : functor C C).

  Definition lax_lineator_postcomp_SelfActCAT_data :
    lineator_data (Mon_endo C) (SelfActCAT C) (SelfActCAT C) (post_comp_functor G).
  Proof.
    intros F K. cbn.
    apply rassociator_CAT.
  Defined.

  Lemma lax_lineator_postcomp_SelfActCAT_laws :
    lineator_laxlaws (Mon_endo C) (SelfActCAT C) (SelfActCAT C) (post_comp_functor G)
      lax_lineator_postcomp_SelfActCAT_data.
  Proof.
    split4.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      do 3 rewrite id_left.
      apply functor_id.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left.
      apply functor_id.
  Qed.

  (** the following definition may not be usable because of its tight typing *)
  Definition lax_lineator_postcomp_SelfActCAT :
    lineator_lax (Mon_endo C) (SelfActCAT C) (SelfActCAT C) (post_comp_functor G) :=
    _,,lax_lineator_postcomp_SelfActCAT_laws.

End LineatorForPostcomposition.

Section LineatorForPostcomposition_alt.

  Context (C D : category) (G : functor D C).

  Definition lax_lineator_postcomp_SelfActCAT_alt_data :
    lineator_data (Mon_endo C) (actegory_from_precomp_CAT C D) (SelfActCAT C) (post_comp_functor G).
  Proof.
    intros F K. cbn.
    apply rassociator_CAT.
  Defined.

  Lemma lax_lineator_postcomp_SelfActCAT_alt_laws :
    lineator_laxlaws (Mon_endo C) (actegory_from_precomp_CAT C D) (SelfActCAT C) (post_comp_functor G)
      lax_lineator_postcomp_SelfActCAT_alt_data.
  Proof.
    split4.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      do 3 rewrite id_left.
      apply functor_id.
    - intro; intros.
      apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left.
      apply functor_id.
  Qed.

  (** the following definition is peculiar since it relates different constructions of actegories *)
  Definition lax_lineator_postcomp_SelfActCAT_alt :
    lineator_lax (Mon_endo C) (actegory_from_precomp_CAT C D) (SelfActCAT C) (post_comp_functor G) :=
    _,,lax_lineator_postcomp_SelfActCAT_alt_laws.

End LineatorForPostcomposition_alt.

Section DistributionOfCoproducts.

  Context (C : category).

Section BinaryCoproduct.

  Context (BCP : BinCoproducts C).

  Let BCPCD : BinCoproducts [C, C] := BinCoproducts_functor_precat C C BCP.

  Definition SelfActCAT_bincoprod_distributor_data :
    actegory_bincoprod_distributor_data (Mon_endo C) BCPCD (SelfActCAT C).
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_data.
  Defined.

  Goal ∏ F G1 G2 c, pr1 (SelfActCAT_bincoprod_distributor_data F G1 G2) c = identity _.
  Proof.
    intros.
    apply idpath.
  Qed.

  Lemma SelfActCAT_bincoprod_distributor_law :
    actegory_bincoprod_distributor_iso_law _ _ _ SelfActCAT_bincoprod_distributor_data.
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_law.
  Qed.

  Definition SelfActCAT_bincoprod_distributor :
    actegory_bincoprod_distributor (Mon_endo C) BCPCD (SelfActCAT C) :=
    _,,SelfActCAT_bincoprod_distributor_law.

End BinaryCoproduct.

Section Coproduct.

  Context {I : UU} (CP : Coproducts I C).

  Let CPCD : Coproducts I [C, C] := Coproducts_functor_precat I C C CP.

  Definition SelfActCAT_coprod_distributor_data :
    actegory_coprod_distributor_data (Mon_endo C) CPCD (SelfActCAT C).
  Proof.
    intros F Gs.
    apply precomp_coprod_distributor_data.
  Defined.

  Lemma SelfActCAT_coprod_distributor_law :
    actegory_coprod_distributor_iso_law _ _ _ SelfActCAT_coprod_distributor_data.
  Proof.
    intros F Gs.
    apply precomp_coprod_distributor_law.
  Qed.

  Definition SelfActCAT_CAT_coprod_distributor :
    actegory_coprod_distributor (Mon_endo C) CPCD (SelfActCAT C) :=
    _,,SelfActCAT_coprod_distributor_law.

End Coproduct.

End DistributionOfCoproducts.
