(** this file is a follow-up of [Multisorted_alt], where the semantic signatures [Signature] are replaced by functors with tensorial strength

    the concept of binding signatures is inherited, as well as the reasoning about omega-cocontinuity
    the strength notion is based on lax lineators where endofunctors act on possibly non-endofunctors, but the
    signature functor generated from a multi-sorted binding signature falls into the special case of endofunctors,
    and the lineator notion can be transferred (through weak equivalence) to the strength notion of
    monoidal heterogeneous substitution systems (MHSS)

    accordingly a MHSS is constructed and a monad obtained through it, cf. [MultiSortedMonadConstruction_actegorical]

author: Ralph Matthes, 2023

notice: this file does not correspond to [Multisorted] but to [Multisorted_alt], even though this is not indicated in the name
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require UniMath.SubstitutionSystems.SortIndexing.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.



(** for the additions in 2023 *)
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Actegories.Examples.ActionOfEndomorphismsInCATElementary.
Require Import UniMath.CategoryTheory.Actegories.Examples.SelfActionInCATElementary.
(* Require Import UniMath.SubstitutionSystems.EquivalenceSignaturesWithActegoryMorphisms. *)
Require Import UniMath.SubstitutionSystems.EquivalenceLaxLineatorsHomogeneousCase.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require UniMath.SubstitutionSystems.BindingSigToMonad_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

Local Open Scope cat.

(* These should be global *)
Arguments Signature_Functor {_ _ _} _.
Arguments BinProduct_of_functors {_ _} _ _ _.

Section MBindingSig.

(** Preamble copied from [Multisorted_alt] *)

(* Interestingly we only need that [sort] is a 1-type *)
Context (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Context (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

(** This represents "sort → C" *)
Let sortToC : category := [path_pregroupoid sort Hsort,C].

Goal sortToC = SortIndexing.sortToC sort Hsort C.
Proof.
  apply idpath.
Qed.

Let BPsortToCC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

Goal BPsortToCC = SortIndexing.BPsortToCC sort Hsort _ BP.
Proof.
  apply idpath.
Qed. (* slow *)

(* Assumptions needed to prove ω-cocontinuity of the functor *)
Context (EsortToCC : Exponentials BPsortToCC)
          (HC : Colims_of_shape nat_graph C).
(* The EsortToCC assumption says that [sortToC,C] has exponentials. It
   could be reduced to exponentials in C, but we only have the case
   for C = Set formalized in

     CategoryTheory.Categories.HSET.Structures.Exponentials_functor_HSET

*)

(** end of Preamble copied from [Multisorted_alt] *)

Local Definition sortToC2 := [sortToC, sortToC].
Local Definition sortToC3 := [sortToC2, sortToC2].
Local Definition sortToCC := [sortToC, C].
Local Definition sortToC21C := [sortToC2, sortToCC].

Let ops : MultiSortedSig sort → hSet := ops sort.
Let arity : ∏ M : MultiSortedSig sort, ops M → list (list sort × sort) × sort
    := arity sort.


Local Definition sorted_option_functor := sorted_option_functor sort Hsort C TC BC CC.
Local Definition projSortToC : sort -> sortToCC := projSortToC sort Hsort C.
Local Definition option_list : list sort → sortToC2 := option_list sort Hsort C TC BC CC.
Local Definition exp_functor : list sort × sort -> sortToC21C
  := exp_functor sort Hsort C TC BC CC.
Local Definition exp_functor_list : list (list sort × sort) -> sortToC21C
  := exp_functor_list sort Hsort C TC BP BC CC.
Local Definition hat_exp_functor_list : list (list sort × sort) × sort -> sortToC3
  := hat_exp_functor_list sort Hsort C TC BP BC CC.
Local Definition MultiSortedSigToFunctor : MultiSortedSig sort -> sortToC3 := MultiSortedSigToFunctor sort Hsort C TC BP BC CC.
Local Definition CoproductsMultiSortedSig : ∏ M : MultiSortedSig sort,
       Coproducts (ops M) sortToC2 := CoproductsMultiSortedSig sort Hsort C CC.


(** * Construction of the lineator for the endofunctor on [C^sort,C^sort]
      derived from a multisorted signature *)
Section strength_through_actegories.

  Local Definition endoCAT : category := EquivalenceLaxLineatorsHomogeneousCase.endoCAT sortToC.
  Local Definition Mon_endo_CAT : monoidal endoCAT := EquivalenceLaxLineatorsHomogeneousCase.Mon_endo_CAT sortToC.
  Local Definition ptdendo_CAT : category := EquivalenceLaxLineatorsHomogeneousCase.ptdendo_CAT sortToC.
  Local Definition Mon_ptdendo_CAT : monoidal ptdendo_CAT := monoidal_pointed_objects Mon_endo_CAT.

  Local Definition ActPtd_CAT (E : category) : actegory Mon_ptdendo_CAT [sortToC,E] :=
    EquivalenceLaxLineatorsHomogeneousCase.actegoryPtdEndosOnFunctors_CAT sortToC E.
  Local Definition ActPtd_CAT_Endo := ActPtd_CAT sortToC.
  Local Definition ActPtd_CAT_FromSelf : actegory Mon_ptdendo_CAT sortToC2
    := actegory_with_canonical_pointed_action Mon_endo_CAT.

  Local Definition pointedstrengthfromprecomp_CAT (E : category) :=
    lineator_lax Mon_ptdendo_CAT ActPtd_CAT_Endo (ActPtd_CAT E).
  (** we are only interested in [E] to have value either [sortToC] or [C] *)

  Local Definition pointedstrengthfromselfaction_CAT :=
    lineator_lax Mon_ptdendo_CAT ActPtd_CAT_FromSelf ActPtd_CAT_FromSelf.

  Let pointedlaxcommutator_CAT (G : sortToC2) : UU :=
        BindingSigToMonad_actegorical.pointedlaxcommutator_CAT G.

  Local Definition δCCCATEndo (M : MultiSortedSig sort) :
    actegory_coprod_distributor Mon_ptdendo_CAT (CoproductsMultiSortedSig M) ActPtd_CAT_Endo.
  Proof.
    use reindexed_coprod_distributor.
    use actegory_from_precomp_CAT_coprod_distributor.
  Defined.

  Local Definition δCCCATfromSelf (M : MultiSortedSig sort) :
    actegory_coprod_distributor Mon_ptdendo_CAT (CoproductsMultiSortedSig M) ActPtd_CAT_FromSelf.
  Proof.
    use reindexed_coprod_distributor.
    use SelfActCAT_CAT_coprod_distributor.
  Defined.

  Definition ptdlaxcommutatorCAT_option_functor (s : sort) :
    pointedlaxcommutator_CAT (sorted_option_functor s).
  Proof.
    use BindingSigToMonad_actegorical.ptdlaxcommutator_genopt.
  Defined.

  Definition ptdlaxcommutatorCAT_option_list (xs : list sort) :
    pointedlaxcommutator_CAT (option_list xs).
  Proof.
    induction xs as [[|n] xs].
    + induction xs.
      apply unit_relativelaxcommutator.
    + induction n as [|n IH].
      * induction xs as [m []].
        apply ptdlaxcommutatorCAT_option_functor.
      * induction xs as [m [k xs]].
        use composedrelativelaxcommutator.
        -- exact (ptdlaxcommutatorCAT_option_functor m).
        -- exact (IH (k,,xs)).
  Defined.

  Definition StrengthCAT_exp_functor (lt : list sort × sort) :
    pointedstrengthfromprecomp_CAT C (exp_functor lt).
  Proof.
    induction lt as [l t]; revert l.
    use list_ind.
    - cbn. (* in [MultiSorted_alt], the analogous construction [Sig_exp_functor] has a composition
              with the strength of the identity functor since [Gθ_Signature] needs a composition *)
      use reindexed_lax_lineator.
      exact (lax_lineator_postcomp_actegories_from_precomp_CAT _ _ _ (projSortToC t)).
    - intros x xs H; simpl.
      use comp_lineator_lax.
      3: { use reindexed_lax_lineator.
           2: { exact (lax_lineator_postcomp_actegories_from_precomp_CAT _ _ _ (projSortToC t)). }
      }
      use reindexedstrength_from_commutator.
      exact (ptdlaxcommutatorCAT_option_list (cons x xs)).
  Defined.

  Definition StrengthCAT_exp_functor_list (xs : list (list sort × sort)) :
    pointedstrengthfromprecomp_CAT C (exp_functor_list xs).
  Proof.
    induction xs as [[|n] xs].
    - induction xs.
      use reindexed_lax_lineator.
      apply constconst_functor_lax_lineator.
    - induction n as [|n IH].
      + induction xs as [m []].
        exact (StrengthCAT_exp_functor m).
      + induction xs as [m [k xs]].
        apply (lax_lineator_binprod Mon_ptdendo_CAT ActPtd_CAT_Endo (ActPtd_CAT C)).
        * apply StrengthCAT_exp_functor.
        * exact (IH (k,,xs)).
  Defined.

  (* the strength for hat_exp_functor_list *)
  Definition StrengthCAT_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
    pointedstrengthfromprecomp_CAT sortToC (hat_exp_functor_list xst).
  Proof.
    use comp_lineator_lax.
    - exact (ActPtd_CAT C).
    - apply StrengthCAT_exp_functor_list.
    - use reindexed_lax_lineator.
      apply lax_lineator_postcomp_actegories_from_precomp_CAT.
  Defined.

  Definition MultiSortedSigToStrengthCAT (M : MultiSortedSig sort) :
    pointedstrengthfromprecomp_CAT sortToC (MultiSortedSigToFunctor M).
  Proof.
    unfold MultiSortedSigToFunctor, MultiSorted_alt.MultiSortedSigToFunctor.
    set (Hyps := λ (op : ops M), StrengthCAT_hat_exp_functor_list (arity M op)).
    apply (lax_lineator_coprod Mon_ptdendo_CAT ActPtd_CAT_Endo ActPtd_CAT_Endo Hyps (CoproductsMultiSortedSig M)).
    apply δCCCATEndo.
  Defined.

  (* commented for reasons of upstream time consumption - no longer needed since we can get everything with [MultiSortedSigToFunctor']

  Definition MultiSortedSigToStrengthFromSelfCAT (M : MultiSortedSig sort) :
    pointedstrengthfromselfaction_CAT (MultiSortedSigToFunctor M).
  Proof.
    apply EquivalenceLaxLineatorsHomogeneousCase.lax_lineators_from_reindexed_precomp_CAT_and_reindexed_self_action_agree.
    apply MultiSortedSigToStrengthCAT.
  Defined.
   *)


  (* can the following be preserved somehow?
  (** this yields an alternative definition for the semantic signature *)
  Definition MultiSortedSigToSignature_alt (M : MultiSortedSig sort) : Signature sortToC sortToC sortToC.
  Proof.
    apply weqSignatureLaxMorphismActegoriesHomogeneous_alt.
    exists (MultiSortedSigToFunctor M).
    apply lax_lineators_from_reindexed_precomp_and_reindexed_self_action_agree.
    apply MultiSortedSigToStrength.
  Defined.

  Local Lemma functor_in_MultiSortedSigToSignature_alt_ok (M : MultiSortedSig) :
  Signature_Functor (MultiSortedSigToSignature_alt M) = MultiSortedSigToFunctor M.
  Proof.
    apply idpath.
  Qed.
  (** however, the computational behaviour of the lineator will not be available *)
   *)


  (** *** we now adapt the definitions to [MultiSortedSigToFunctor'] *)
  Local Definition MultiSortedSigToFunctor' : MultiSortedSig sort -> sortToC3 := MultiSortedSigToFunctor' sort Hsort C TC BP BC CC.
  Local Definition hat_exp_functor_list'_optimized : list (list sort × sort) × sort -> sortToC3
    := hat_exp_functor_list'_optimized sort Hsort C TC BP BC CC.
  Local Definition hat_exp_functor_list'_piece : (list sort × sort) × sort -> sortToC3
    := hat_exp_functor_list'_piece sort Hsort C TC BC CC.

  Definition StrengthCAT_hat_exp_functor_list'_piece (xt : (list sort × sort) × sort) :
    pointedstrengthfromselfaction_CAT (hat_exp_functor_list'_piece xt).
  Proof.
    unfold hat_exp_functor_list'_piece, ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_piece.
    use comp_lineator_lax.
    2: { refine (reindexedstrength_from_commutator Mon_endo_CAT Mon_ptdendo_CAT (forget_monoidal_pointed_objects_monoidal Mon_endo_CAT)
                   _ (SelfActCAT sortToC)).
         exact (ptdlaxcommutatorCAT_option_list (pr1 (pr1 xt))).
    }
    use reindexed_lax_lineator.
    apply (lax_lineator_postcomp_SelfActCAT).
    Defined.

  Definition StrengthCAT_hat_exp_functor_list'_optimized (xst : list (list sort × sort) × sort) :
    pointedstrengthfromselfaction_CAT (hat_exp_functor_list'_optimized xst).
  Proof.
    induction xst as [xs t].
    induction xs as [[|n] xs].
    - induction xs.
      use reindexed_lax_lineator.
      use comp_lineator_lax. (* the next two lines go through [actegory_from_precomp_CAT] *)
      2: { apply constconst_functor_lax_lineator. }
      apply lax_lineator_postcomp_SelfActCAT_alt.
    - induction n as [|n IH].
      + induction xs as [m []].
        apply StrengthCAT_hat_exp_functor_list'_piece.
      + induction xs as [m [k xs]].
        apply (lax_lineator_binprod Mon_ptdendo_CAT ActPtd_CAT_FromSelf ActPtd_CAT_FromSelf).
        * apply StrengthCAT_hat_exp_functor_list'_piece.
        * exact (IH (k,,xs)).
  Defined.

  Definition MultiSortedSigToStrength' (M : MultiSortedSig sort) :
    pointedstrengthfromselfaction_CAT (MultiSortedSigToFunctor' M).
  Proof.
    unfold MultiSortedSigToFunctor', ContinuityOfMultiSortedSigToFunctor.MultiSortedSigToFunctor'.
    set (Hyps := λ (op : ops M), StrengthCAT_hat_exp_functor_list'_optimized (arity M op)).
    apply (lax_lineator_coprod Mon_ptdendo_CAT ActPtd_CAT_FromSelf ActPtd_CAT_FromSelf Hyps (CoproductsMultiSortedSig M)).
    apply δCCCATfromSelf.
  Defined.

End strength_through_actegories.

End MBindingSig.
