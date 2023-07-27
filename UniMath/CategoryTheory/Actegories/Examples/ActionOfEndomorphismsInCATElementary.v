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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.

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
  - intros v f. exact (functor_composite v f).
  - intros v f1 f2 β. exact (lwhisker_CAT v β).
  - intros f v1 v2 α. exact (rwhisker_CAT f α).
Defined.

(* (** we explicitly do not opacify the following definition: *) *)
Definition action_from_precomp_CAT_laws : is_bifunctor action_from_precomp_CAT_data.
Proof.
  split5.
  - intros v f. apply lwhisker_id2_CAT.
  - intros f v. apply id2_rwhisker_CAT.
  - intros v f1 f2 f3 β1 β2. apply pathsinv0, lwhisker_vcomp_CAT.
  - intros f v1 v2 v3 α1 α2. apply pathsinv0, rwhisker_vcomp_CAT.
  - intros v1 v2 f1 f2 α β. apply vcomp_whisker_CAT.
Qed. (* Defined. *)

Definition action_from_precomp_CAT : bifunctor [C, C] [C, D] [C, D] :=
  make_bifunctor action_from_precomp_CAT_data action_from_precomp_CAT_laws.

Definition actegory_from_precomp_CAT_data : actegory_data Mon_endo [C, D].
Proof.
  exists action_from_precomp_CAT_data.
  split4.
  - intro f. apply lunitor_CAT.
  - intro f. apply linvunitor_CAT.
  - intros v w f. apply rassociator_CAT.
  - intros v w f. apply lassociator_CAT.
Defined.

Lemma actegory_from_precomp_CAT_laws : actegory_laws Mon_endo actegory_from_precomp_CAT_data.
Proof.
  split5.
  - exact action_from_precomp_CAT_laws.
  - split3.
    + intros f g β. apply vcomp_lunitor_CAT.
    + apply lunitor_linvunitor_CAT.
    + apply linvunitor_lunitor_CAT.
  - split4.
    + intros v w f f' β. apply lwhisker_lwhisker_rassociator_CAT.
    + intros v v' w f α. apply pathsinv0, rwhisker_rwhisker_alt_CAT.
    + intros v w w' f α. apply rwhisker_lwhisker_rassociator_CAT.
    + split.
      * apply rassociator_lassociator_CAT.
      * apply lassociator_rassociator_CAT.
  - intros v f. apply lunitor_lwhisker_CAT.
  - intros w v v' f. apply rassociator_rassociator_CAT.
Qed.

Definition actegory_from_precomp_CAT : actegory Mon_endo [C, D] :=
  actegory_from_precomp_CAT_data,,actegory_from_precomp_CAT_laws.

End Action_From_Precomposition.

Section TheHomogeneousCase.

  Context (C : category).

(* (** requires [action_from_precomp_CAT] with known proofs of the laws to be even convertibility *) *)
Definition action_in_actegory_from_precomp_CAT_as_self_action :
  actegory_action (Mon_endo C) (actegory_from_precomp_CAT C C) =
    actegory_action (Mon_endo C) (actegory_with_canonical_self_action (Mon_endo C)).
Proof.
  apply subtypePath.
  { intro; apply isaprop_is_bifunctor. }
  apply idpath.
Defined.

(* (** only possible if the previous is convertibility *)
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
Qed. *)

(* (** we should no longer need the proofs of the laws after this result  - is the following command effective? *)
Opaque action_from_precomp_CAT_laws. *)

(** on the way to what we really need is the following convertibility: *)
Lemma lax_lineators_for_actegory_from_precomp_CAT_and_self_action_agree (F : functor [C, C] [C, C]) :
  lineator_lax (Mon_endo C) (actegory_from_precomp_CAT C C) (actegory_from_precomp_CAT C C) F =
    lineator_lax (Mon_endo C) (actegory_with_canonical_self_action (Mon_endo C))
      (actegory_with_canonical_self_action (Mon_endo C)) F.
Proof.
  apply idpath.
Qed.
(** in fact, we need this with reindexed actegories everywhere *)

End TheHomogeneousCase.

Section LineatorForPostcomposition.

  Context (C D E : category) (G : functor D E).

  Definition lax_lineator_postcomp_actegories_from_precomp_CAT_data :
    lineator_data (Mon_endo C) (actegory_from_precomp_CAT C D) (actegory_from_precomp_CAT C E) (post_comp_functor G).
  Proof.
    intros F K. cbn.
    apply rassociator_CAT.
  Defined.

  Lemma lax_lineator_postcomp_actegories_from_precomp_CAT_laws :
    lineator_laxlaws (Mon_endo C) (actegory_from_precomp_CAT C D) (actegory_from_precomp_CAT C E) (post_comp_functor G)
      lax_lineator_postcomp_actegories_from_precomp_CAT_data.
  Proof.
    split4.
    - intro; intros.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      rewrite id_left; apply id_right.
    - intro; intros.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      do 3 rewrite id_left.
      apply functor_id.
    - intro; intros.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      rewrite id_left.
      apply functor_id.
  Qed.

  Definition lax_lineator_postcomp_actegories_from_precomp_CAT :
    lineator_lax (Mon_endo C) (actegory_from_precomp_CAT C D) (actegory_from_precomp_CAT C E) (post_comp_functor G) :=
    _,,lax_lineator_postcomp_actegories_from_precomp_CAT_laws.

End LineatorForPostcomposition.

Section LineatorForConstConstFunctor.

  Context {C D E : category} (ActD : actegory (Mon_endo C) D) (e0: E).

  Definition constconst_functor_lax_lineator_data : lineator_data (Mon_endo C)
    ActD (actegory_from_precomp_CAT C E) (constant_functor D [C,E] (constant_functor C E e0)).
  Proof.
    intros F d. apply nat_trans_id.
  Defined.

  Lemma constconst_functor_lax_lineator_laws :
    lineator_laxlaws _ _ _  _ constconst_functor_lax_lineator_data.
  Proof.
    split4.
    - intro; intros; apply (nat_trans_eq E); intro c; apply idpath.
    - intro; intros; apply (nat_trans_eq E); intro c; apply idpath.
    - intro; intros; apply (nat_trans_eq E); intro c. apply pathsinv0, id_right.
    - intro; intros; apply (nat_trans_eq E); intro c. apply id_right.
  Qed.

  Definition constconst_functor_lax_lineator : lineator_lax (Mon_endo C)
    ActD (actegory_from_precomp_CAT C E) (constant_functor D [C,E] (constant_functor C E e0))
    := _,,constconst_functor_lax_lineator_laws.

End LineatorForConstConstFunctor.

Section DistributionOfCoproducts.

  Context (C D : category).

Section BinaryCoproduct.

  Context (BCP : BinCoproducts D).

  Let BCPCD : BinCoproducts [C, D] := BinCoproducts_functor_precat C D BCP.

  Definition actegory_from_precomp_CAT_bincoprod_distributor_data :
    actegory_bincoprod_distributor_data (Mon_endo C) BCPCD (actegory_from_precomp_CAT C D).
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_data.
  Defined.

  (** a sanity check *)
  Goal ∏ F G1 G2 c, pr1 (actegory_from_precomp_CAT_bincoprod_distributor_data F G1 G2) c = identity _.
  Proof.
    intros.
    apply idpath.
  Qed.

  Lemma actegory_from_precomp_CAT_bincoprod_distributor_law :
    actegory_bincoprod_distributor_iso_law _ _ _ actegory_from_precomp_CAT_bincoprod_distributor_data.
  Proof.
    intro F.
    apply precomp_bincoprod_distributor_law.
  Qed.

  Definition actegory_from_precomp_CAT_bincoprod_distributor :
    actegory_bincoprod_distributor (Mon_endo C) BCPCD (actegory_from_precomp_CAT C D) :=
    _,,actegory_from_precomp_CAT_bincoprod_distributor_law.

End BinaryCoproduct.

Section Coproduct.

  Context {I : UU} (CP : Coproducts I D).

  Let CPCD : Coproducts I [C, D] := Coproducts_functor_precat I C D CP.

  Definition actegory_from_precomp_CAT_coprod_distributor_data :
    actegory_coprod_distributor_data (Mon_endo C) CPCD (actegory_from_precomp_CAT C D).
  Proof.
    intros F Gs.
    apply precomp_coprod_distributor_data.
  Defined.

  Lemma actegory_from_precomp_CAT_coprod_distributor_law :
    actegory_coprod_distributor_iso_law _ _ _ actegory_from_precomp_CAT_coprod_distributor_data.
  Proof.
    intros F Gs.
    apply precomp_coprod_distributor_law.
  Qed.

  Definition actegory_from_precomp_CAT_coprod_distributor :
    actegory_coprod_distributor (Mon_endo C) CPCD (actegory_from_precomp_CAT C D) :=
    _,,actegory_from_precomp_CAT_coprod_distributor_law.

End Coproduct.

End DistributionOfCoproducts.
