(** Constructs the actegory with the action of the endomorphisms on [C] by precomposition on a fixed functor category with source category [C]

   a general construction is available for bicategories and a fixed object therein

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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsWhiskeredMonoidalElementary.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.

Local Open Scope cat.

Section Action_From_Precomposition.

  (*
  Import BifunctorNotations.
  Import MonoidalNotations.
  Import ActegoryNotations.
   *)

  Context (C D : category).

Local Definition Mon_endo: monoidal [C, C] := monendocat_monoidal C.

Definition action_from_precomp_CAT_data : bifunctor_data [C, C] [C, D] [C, D].
Proof.
  use make_bifunctor_data.
  - intros v f. exact (functor_compose v f).
  - intros v f1 f2 β. exact (lwhisker_CAT v  β).
  - intros f v1 v2 α. exact (rwhisker_CAT f α).
Defined.

(** we explicitly do not opacify the following definition: *)
Definition action_from_precomp_CAT_laws : is_bifunctor action_from_precomp_CAT_data.
Proof.
  repeat split.
  - intros v f. apply lwhisker_id2_CAT.
  - intros f v. apply id2_rwhisker_CAT.
  - intros v f1 f2 f3 β1 β2. apply pathsinv0, lwhisker_vcomp_CAT.
  - intros f v1 v2 v3 α1 α2. apply pathsinv0, rwhisker_vcomp_CAT.
  - intros v1 v2 f1 f2 α β. apply vcomp_whisker_CAT.
Defined.

Definition action_from_precomp_CAT : bifunctor [C, C] [C, D] [C, D] :=
  make_bifunctor action_from_precomp_CAT_data action_from_precomp_CAT_laws.

Definition actegory_from_precomp_CAT_data : actegory_data Mon_endo [C, D].
Proof.
  exists action_from_precomp_CAT.
  repeat split.
  - intro f. apply lunitor_CAT.
  - intro f. apply linvunitor_CAT.
  - intros v w f. apply rassociator_CAT.
  - intros v w f. apply lassociator_CAT.
Defined.

Lemma actegory_from_precomp_CAT_laws : actegory_laws Mon_endo actegory_from_precomp_CAT_data.
Proof.
  repeat split.
  - intros f g β. cbn. apply vcomp_lunitor_CAT.
  - cbn. apply lunitor_linvunitor_CAT.
  - cbn. apply linvunitor_lunitor_CAT.
  - intros v w f f' β. cbn. apply lwhisker_lwhisker_rassociator_CAT.
  - intros v v' w f α. cbn. apply pathsinv0, rwhisker_rwhisker_alt_CAT.
  - intros v w w' f α. cbn. apply rwhisker_lwhisker_rassociator_CAT.
  - cbn. apply rassociator_lassociator_CAT.
  - cbn. apply lassociator_rassociator_CAT.
  - intros v f. cbn. apply lunitor_lwhisker_CAT.
  - intros w v v' f. cbn. apply rassociator_rassociator_CAT.
Qed.

Definition actegory_from_precomp_CAT : actegory Mon_endo [C, D] :=
  actegory_from_precomp_CAT_data,,actegory_from_precomp_CAT_laws.

End Action_From_Precomposition.

Section TheHomogeneousCase.

  Context (C : category).

(** requires [action_from_precomp_CAT] with known proofs of the laws *)
Definition action_in_actegory_from_precomp_CAT_as_self_action :
  actegory_action (Mon_endo C) (actegory_from_precomp_CAT C C) = actegory_action (Mon_endo C) (actegory_with_canonical_self_action (Mon_endo C)).
Proof.
  apply idpath.
Defined.

Lemma actegory_from_precomp_CAT_as_self_action :
  actegory_from_precomp_CAT C C = actegory_with_canonical_self_action (Mon_endo C).
Proof.
  use total2_paths_f.
  2: { apply isaprop_actegory_laws. }
  use total2_paths_f.
  { apply action_in_actegory_from_precomp_CAT_as_self_action. }
  use total2_paths_f.
  { apply idpath. }
  use total2_paths_f.
  { apply idpath. }
  apply idpath.
Qed.

(** we should no longer need the proofs of the laws after this result  - is the following command effective? *)
Opaque action_from_precomp_CAT_laws.

End TheHomogeneousCase.

Section DistributionOfCoproducts.

  (* TODO *)

End DistributionOfCoproducts.
