(** links the homogeneous instance of lax lineators with the linears based on the self action

    this is w.r.t. the elementary notion of the monoidal category of endofunctors, not
    the instance to the bicategory of categories of the general bicategorical constructions

Author: Ralph Matthes 2023

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.
Require Import UniMath.CategoryTheory.Actegories.Examples.ActionOfEndomorphismsInCATElementary.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
(* Require Import UniMath.SubstitutionSystems.EquivalenceSignaturesWithActegoryMorphisms. *)

Import MonoidalNotations.

Local Open Scope cat.

Section FixACategory.

  Context (C : category).

 Local Definition endoCAT : category := [C, C].
 Local Definition Mon_endo_CAT : monoidal endoCAT := monendocat_monoidal C.
 Local Definition ptdendo_CAT : category := coslice_cat_total endoCAT I_{Mon_endo_CAT}.
 Local Definition Mon_ptdendo_CAT : monoidal ptdendo_CAT := monoidal_pointed_objects Mon_endo_CAT.
 Local Definition actegoryPtdEndosOnFunctors_CAT (E : category) : actegory Mon_ptdendo_CAT [C,E]
   := reindexed_actegory Mon_endo_CAT (actegory_from_precomp_CAT C E) Mon_ptdendo_CAT
        (forget_monoidal_pointed_objects_monoidal Mon_endo_CAT).

 (* not possible without some transparent proofs
 Local Lemma actegoryPtdEndosOnFunctors_CAT_as_actegory_with_canonical_pointed_action :
   actegoryPtdEndosOnFunctors_CAT C = actegory_with_canonical_pointed_action Mon_endo_CAT.
 Proof.
   unfold actegoryPtdEndosOnFunctors_CAT.
   unfold actegory_from_precomp_CAT.
   rewrite actegory_from_precomp_as_self_action_CAT.
   apply idpath.
 Qed.
*)

 Local Lemma action_in_actegoryPtdEndosOnFunctors_CAT_as_actegory_with_canonical_pointed_action :
   actegory_action Mon_ptdendo_CAT (actegoryPtdEndosOnFunctors_CAT C) =
     actegory_action Mon_ptdendo_CAT (actegory_with_canonical_pointed_action Mon_endo_CAT).
 Proof.
   use total2_paths_f.
   2: { apply WhiskeredBifunctors.isaprop_is_bifunctor. }
   cbn.
   apply idpath.
 Qed. (* > 16 times faster than for
[EquivalenceSignaturesWithActegoryMorphisms.action_in_actegoryPtdEndosOnFunctors_as_actegory_with_canonical_pointed_action] *)

 (* commented for reasons of time consumption (easily more than 3 minutes compilation time)

Local Lemma lax_lineators_data_from_reindexed_precomp_CAT_and_reindexed_self_action_agree (H : functor [C, C] [C, C]) :
   lineator_data Mon_ptdendo_CAT (actegoryPtdEndosOnFunctors_CAT C) (actegoryPtdEndosOnFunctors_CAT C) H ≃
     lineator_data Mon_ptdendo_CAT (actegory_with_canonical_pointed_action Mon_endo_CAT)
       (actegory_with_canonical_pointed_action Mon_endo_CAT) H.
Proof.
  use weq_iso.
  - intro ld.
    intros Z F.
    cbn.
    set (ldinst := ld Z F).
    cbn in ldinst.
    exact ldinst.
  - intro ld.
    intros Z F.
    cbn.
    set (ldinst := ld Z F).
    cbn in ldinst.
    exact ldinst.
  - abstract (intro ld; (* apply funextsec; intro; simpl; apply funextsec; intro; *) apply idpath).
  - abstract (intro ld; apply idpath). (* both cases are very slow *)
Defined. (* 57s on modern Intel machine *)
*)

(* commented for reasons of time consumption (easily more than 30 minutes compilation time) - no longer needed with the modified definition [MultiSortedSigToStrength'] of signature functor

 Local Lemma lax_lineators_from_reindexed_precomp_CAT_and_reindexed_self_action_agree (H : functor [C, C] [C, C]) :
   lineator_lax Mon_ptdendo_CAT (actegoryPtdEndosOnFunctors_CAT C) (actegoryPtdEndosOnFunctors_CAT C) H ≃
     lineator_lax Mon_ptdendo_CAT (actegory_with_canonical_pointed_action Mon_endo_CAT)
       (actegory_with_canonical_pointed_action Mon_endo_CAT) H.
 Proof.
   use (weqbandf (lax_lineators_data_from_reindexed_precomp_CAT_and_reindexed_self_action_agree H)).
   intro ld.
   use weqimplimpl.
   4: { apply isaprop_lineator_laxlaws. }
   3: { apply isaprop_lineator_laxlaws. }
   - intro Hyps.
     split4.
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypnatleft_inst := eqtohomot (maponpaths pr1 (pr1 Hyps v x1 x2 g)) c);
       cbn; cbn in Hypnatleft_inst;
         exact Hypnatleft_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypnatright_inst := eqtohomot (maponpaths pr1 (pr12 Hyps v1 v2 x f)) c);
       cbn; cbn in Hypnatright_inst;
         exact Hypnatright_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypactor_inst := eqtohomot (maponpaths pr1 (pr122 Hyps v w x)) c);
       cbn; cbn in Hypactor_inst;
         exact Hypactor_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypunitor_inst := eqtohomot (maponpaths pr1 (pr222 Hyps x)) c);
       cbn; cbn in Hypunitor_inst;
         exact Hypunitor_inst).
   - intro Hyps.
     split4.
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypnatleft_inst := eqtohomot (maponpaths pr1 (pr1 Hyps v x1 x2 g)) c);
       cbn; cbn in Hypnatleft_inst;
         exact Hypnatleft_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypnatright_inst := eqtohomot (maponpaths pr1 (pr12 Hyps v1 v2 x f)) c);
       cbn; cbn in Hypnatright_inst;
         exact Hypnatright_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypactor_inst := eqtohomot (maponpaths pr1 (pr122 Hyps v w x)) c);
       cbn; cbn in Hypactor_inst;
         exact Hypactor_inst).
     + abstract (intro; intros;
       apply (nat_trans_eq C);
       intro c;
       assert (Hypunitor_inst := eqtohomot (maponpaths pr1 (pr222 Hyps x)) c);
       cbn; cbn in Hypunitor_inst;
         exact Hypunitor_inst).
 Defined. (* instantaneous, but the abstracted parts require 26-42min on a modern Intel machine, depending on if UniMath master was merged *)

*)

End FixACategory.
