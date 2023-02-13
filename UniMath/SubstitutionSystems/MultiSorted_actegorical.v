(** this file is a follow-up of [Multisorted_alt], where the semantic signatures [Signature] are replaced by functors with tensorial strength

    the concept of binding signatures is inherited, as well as the reasoning about omega-cocontinuity
    the strength notion is based on lax lineators where endofunctors act on possibly non-endofunctors, but the
    signature functor generated from a multi-sorted binding signature falls into the special case of endofunctors,
    and the lineator notion can be transferred (through weak equivalence) to the strength notion of
    generalized heterogeneous substitution systems (GHSS)

    accordingly a GHSS is constructed and a monad obtained through it, cf. [MultiSortedMonadConstruction_actegorical]

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
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.



(** for the additions in 2023 *)
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.Examples.ActionOfEndomorphismsInCATWhiskeredElementary.
(* Require Import UniMath.SubstitutionSystems.EquivalenceSignaturesWithActegoryMorphisms. *)
Require Import UniMath.SubstitutionSystems.EquivalenceLaxLineatorsHomogeneousCase.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.


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

(** Define the discrete category of sorts *)
Let sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

(* Assumptions needed to prove ω-cocontinuity of the functor *)
Context (expSortToCC : Exponentials BPC)
          (HC : Colims_of_shape nat_graph C).
(* The expSortToCC assumption says that [sortToC,C] has exponentials. It
   could be reduced to exponentials in C, but we only have the case
   for C = Set formalized in

     CategoryTheory.categories.HSET.Structures.Exponentials_functor_HSET

*)

(** end of Preamble copied from [Multisorted_alt] *)

Local Definition sortToC1 := [sortToC, sortToC].
Local Definition sortToC2 := [sortToC1, sortToC1].
Local Definition sortToCC := [sortToC, C].
Local Definition sortToC1C := [sortToC1, sortToCC].

Let ops := ops sort.
Let arity := arity sort.

Local Definition exp_functor_list : list (list sort × sort) -> sortToC1C
  := exp_functor_list sort Hsort C TC BP BC CC.
Local Definition hat_exp_functor_list : list (list sort × sort) × sort -> sortToC2
  := hat_exp_functor_list sort Hsort C TC BP BC CC.
Local Definition MultiSortedSigToFunctor : MultiSortedSig sort -> sortToC2 := MultiSortedSigToFunctor sort Hsort C TC BP BC CC.
Local Definition CoproductsMultiSortedSig : ∏ M : MultiSortedSig sort,
       Coproducts (ops M) sortToC1 := CoproductsMultiSortedSig sort Hsort C CC.


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
  Local Definition ActPtd_CAT_FromSelf : actegory Mon_ptdendo_CAT sortToC1
    := actegory_with_canonical_pointed_action Mon_endo_CAT.

  Local Definition pointedstrengthfromprecomp_CAT (E : category) := lineator_lax Mon_ptdendo_CAT ActPtd_CAT_Endo (ActPtd_CAT E).
  (** we are only interested in [E] to have value either [sortToC] or [C] *)

  Local Definition pointedstrengthfromselfaction_CAT := lineator_lax Mon_ptdendo_CAT ActPtd_CAT_FromSelf ActPtd_CAT_FromSelf.


  Local Definition δCCCATEndo (M : MultiSortedSig sort) : actegory_coprod_distributor Mon_ptdendo_CAT (CoproductsMultiSortedSig M) ActPtd_CAT_Endo.
  Proof.
    use lifted_coprod_distributor.
    use actegory_from_precomp_CAT_coprod_distributor.
  Defined.

  Definition StrengthCAT_exp_functor_list (xs : list (list sort × sort)) :
    pointedstrengthfromprecomp_CAT C (exp_functor_list xs).
  Proof.
  Admitted. (* this requires the development of all the constituents before TODO! *)



  (* the strength for hat_exp_functor_list *)
  Definition StrengthCAT_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
    pointedstrengthfromprecomp_CAT sortToC (hat_exp_functor_list xst).
  Proof.
    use comp_lineator_lax.
    - exact (ActPtd_CAT C).
    - apply StrengthCAT_exp_functor_list.
    - use lifted_lax_lineator.
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

  Definition MultiSortedSigToStrengthFromSelfCAT (M : MultiSortedSig sort) :
    pointedstrengthfromselfaction_CAT (MultiSortedSigToFunctor M).
  Proof.
    apply EquivalenceLaxLineatorsHomogeneousCase.lax_lineators_from_lifted_precomp_CAT_and_lifted_self_action_agree.
    apply MultiSortedSigToStrengthCAT.
  Defined.



  (* can the following be preserved somehow?
  (** this yields an alternative definition for the semantic signature *)
  Definition MultiSortedSigToSignature_alt (M : MultiSortedSig sort) : Signature sortToC sortToC sortToC.
  Proof.
    apply weqSignatureLaxMorphismActegoriesHomogeneous_alt.
    exists (MultiSortedSigToFunctor M).
    apply lax_lineators_from_lifted_precomp_and_lifted_self_action_agree.
    apply MultiSortedSigToStrength.
  Defined.

  Local Lemma functor_in_MultiSortedSigToSignature_alt_ok (M : MultiSortedSig) :
  Signature_Functor (MultiSortedSigToSignature_alt M) = MultiSortedSigToFunctor M.
  Proof.
    apply idpath.
  Qed.
  (** however, the computational behaviour of the lineator will not be available *)
*)


End strength_through_actegories.

End MBindingSig.
