(** this file is a follow-up of [MultisortedMonadConstruction_alt], where the semantic signatures [Signature] are replaced by functors with tensorial strength and HSS by MHSS

based on the lax lineator constructed in [Multisorted_actegories] and transferred (through weak equivalence) to the strength notion of
monoidal heterogeneous substitution systems (MHSS), a MHSS is constructed and a monad obtained through it

author: Ralph Matthes, 2023

notice: this file does not correspond to [MultisortedMonadConstruction] but to [MultisortedMonadConstruction_alt], even though this is not indicated in the name
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.All.

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
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonadsAsMonoidsElementary.
Require Import UniMath.SubstitutionSystems.EquivalenceLaxLineatorsHomogeneousCase.
Require UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.ConstructionOfGHSS.
Require UniMath.SubstitutionSystems.BindingSigToMonad_actegorical.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

(** for the instantiation to [HSET] *)
Require Import UniMath.Bicategories.PseudoFunctors.Examples.CurryingInBicatOfCats.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section MBindingSig.

(* Interestingly we only need that [sort] is a 1-type *)
Context (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Context (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

(** Define the category of sorts *)
Let sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.

Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

Let BPCsortToC : BinProducts sortToC := BinProducts_functor_precat _ C BP.
Let BPC1 : BinProducts [sortToC,sortToC] := BinProducts_functor_precat sortToC sortToC BPCsortToC.

(* Assumptions needed to prove ω-cocontinuity of the functor *)
Context (expSortToC1 : Exponentials BPC1) (** this requires exponentials in a higher space than before for [MultiSortedSigToFunctor] *)
  (HC : Colims_of_shape nat_graph C).

(* The [expSortToC1] assumption is fulfilled for C = Set, to be seen in the instantiation. *)

(** * Construction of a monad from a multisorted signature *)
Section monad.

  Local Definition sortToC1 := [sortToC, sortToC].
  Local Definition sortToC2 := [sortToC1, sortToC1].

  Let BCsortToC1 : BinCoproducts sortToC1 := BinCoproducts_functor_precat _ _ BCsortToC.
  Let ICsortToC1 : Initial sortToC1 := Initial_functor_precat _ _ (Initial_functor_precat _ _ IC).
  Local Definition HCsortToC : Colims_of_shape nat_graph sortToC.
  Proof.
    apply ColimsFunctorCategory_of_shape, HC.
  Defined.
  Local Definition HCsortToC1 : Colims_of_shape nat_graph sortToC1.
  Proof.
    apply ColimsFunctorCategory_of_shape, HCsortToC.
  Defined.

  Local Definition MultiSortedSigToFunctor' : MultiSortedSig sort -> sortToC2 := MultiSortedSigToFunctor' sort Hsort C TC BP BC CC.
  Local Definition is_omega_cocont_MultiSortedSigToFunctor' : ∏ M : MultiSortedSig sort, is_omega_cocont (MultiSortedSigToFunctor' M)
    := is_omega_cocont_MultiSortedSigToFunctor' sort Hsort C TC BP BC PC CC expSortToC1 HC.
  Local Definition MultiSortedSigToStrength' : ∏ M : MultiSortedSig sort,
        MultiSorted_actegorical.pointedstrengthfromselfaction_CAT sort Hsort C (MultiSortedSigToFunctor' M)
    := MultiSortedSigToStrength' sort Hsort C TC BP BC CC.

  Let Id_H : sortToC2 → sortToC2 := LiftingInitial_alt.Id_H sortToC BCsortToC.

 (** Construction of initial algebra for the omega-cocontinuous signature functor with lax lineator *)
  Definition DatatypeOfMultisortedBindingSig_CAT (sig : MultiSortedSig sort) :
    Initial (FunctorAlg (Id_H (MultiSortedSigToFunctor' sig))).
  Proof.
    use colimAlgInitial.
    - exact ICsortToC1.
    - apply (LiftingInitial_alt.is_omega_cocont_Id_H _ _ _ (is_omega_cocont_MultiSortedSigToFunctor' sig)).
    - apply HCsortToC1.
  Defined.

  (** the associated MHSS *)
  Definition MHSSOfMultiSortedSig_CAT (sig : MultiSortedSig sort) :
    mhss (monendocat_monoidal sortToC) (MultiSortedSigToFunctor' sig) (MultiSortedSigToStrength' sig).
  Proof.
    use (initial_alg_to_mhss (MultiSortedSigToStrength' sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact ICsortToC1.
    - apply HCsortToC1.
    - apply (is_omega_cocont_MultiSortedSigToFunctor' sig).
    - intro F. apply Initial_functor_precat.
    - intro F. apply (is_omega_cocont_pre_composition_functor F HCsortToC).
  Defined.

  (** the associated initial Sigma-monoid *)
  Definition InitialSigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Initial (SigmaMonoid (MultiSortedSigToStrength' sig)).
  Proof.
    use (SigmaMonoidFromInitialAlgebraInitial (MultiSortedSigToStrength' sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact ICsortToC1.
    - apply HCsortToC1.
    - apply (is_omega_cocont_MultiSortedSigToFunctor' sig).
    - intro F. apply Initial_functor_precat.
    - intro F. apply (is_omega_cocont_pre_composition_functor F HCsortToC).
  Defined.

  (** the associated Sigma-monoid - defined separately *)
  Definition SigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : SigmaMonoid (MultiSortedSigToStrength' sig).
  Proof.
    apply mhss_to_sigma_monoid.
    exact (MHSSOfMultiSortedSig_CAT sig).
  Defined.

(* currently obsolete because this was only for the original definition with [MultiSortedSigToFunctor]

  (** the characteristic equation of the Sigma monoid is even fulfilled w.r.t. to the original lax lineator, not only
      the one obtained through weak equivalence *)
Section CharEq.

  Context (sig : MultiSortedSig sort).
  Let σ := SigmaMonoidOfMultiSortedSig_CAT sig.
  Let st' : sortToC1 ⟦ (SigmaMonoid_carrier _ σ) ⊗_{monendocat_monoidal sortToC : bifunctor _ _ _}
                         (pr1 (MultiSortedSigToFunctor sig) (SigmaMonoid_carrier _ σ)),
                pr1 (MultiSortedSigToFunctor sig) ((SigmaMonoid_carrier _ σ) ⊗_{monendocat_monoidal sortToC}
                                                     (SigmaMonoid_carrier _ σ)) ⟧
      := pr1 (MultiSortedSigToStrengthCAT sort Hsort C TC BP BC CC sig)
           (SigmaMonoid_carrier _ σ ,, SigmaMonoid_η _ σ) (SigmaMonoid_carrier _ σ).

  Lemma SigmaMonoidOfMultiSortedSig_CAT_char_eq_ok :
    SigmaMonoid_characteristic_equation (SigmaMonoid_carrier _ σ) (SigmaMonoid_η _ σ) (SigmaMonoid_μ _ σ) (SigmaMonoid_τ _ σ) st'.
  Proof.
   Admitted. (* the proof depends on [lax_lineators_from_reindexed_precomp_CAT_and_reindexed_self_action_agree] to be defined! *)
 (*
    (** beginning of proof that depends on that currently deactivated definition *)
    assert (Hyp := SigmaMonoid_is_compatible (MultiSortedSigToStrengthFromSelfCAT sig) σ).
    hnf.
    hnf in Hyp.
    etrans.
    2: { exact Hyp. }
    clear Hyp.
    do 2 apply cancel_postcomposition.
    apply idpath.
    (* no need for extensional reasoning:
    apply (nat_trans_eq sortToC).
    intro F.
    apply (nat_trans_eq C).
    intro s.
    simpl.
    apply idpath.
     *)
  Qed.
  (** end of proof that depends on that currently deactivated definition *)
*)
End CharEq.
*)

  (** the associated monad *)
  Definition MonadOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Monad sortToC.
  Proof.
    use monoid_to_monad_CAT.
    use SigmaMonoid_to_monoid.
    - exact (MultiSortedSigToFunctor' sig).
    - exact (MultiSortedSigToStrength' sig).
    - exact (SigmaMonoidOfMultiSortedSig_CAT sig).
  Defined.

End monad.

End MBindingSig.

Section InstanceHSET.

  Context (sort : UU) (Hsort : isofhlevel 3 sort).

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Let BPCsortToHSET : BinProducts sortToHSET := BinProducts_functor_precat _ HSET BinProductsHSET.
  Let BPC1 : BinProducts [sortToHSET,sortToHSET] := BinProducts_functor_precat sortToHSET sortToHSET BPCsortToHSET.

  Definition expSortToHSET1 : Exponentials BPC1.
  Proof.
    set (aux := category_binproduct sortToHSET (path_pregroupoid sort Hsort)).
    set (BPaux' := BinProducts_functor_precat aux _ BinProductsHSET).
    assert (Hyp : Exponentials BPaux').
    { apply Exponentials_functor_HSET. }
    transparent assert (HypAdj : (equivalence_of_cats [sortToHSET, sortToHSET] [aux, SET])).
    { apply currying_hom_equivalence. }
    use (exponentials_through_adj_equivalence_univalent_cats _ _ Hyp).
    2: { apply is_univalent_functor_category.
         apply is_univalent_HSET. }
    2: { do 2 apply is_univalent_functor_category.
         apply is_univalent_HSET. }
    transparent assert (HypAdj' : (adj_equivalence_of_cats (left_functor HypAdj))).
    { apply adjointification. }
    use tpair.
    2: { apply (adj_equivalence_of_cats_inv HypAdj'). }
  Defined.

  Definition MultiSortedSigToMonadHSET_viaCAT : MultiSortedSig sort → Monad (sortToHSET).
  Proof.
    intros sig; simple refine (MonadOfMultiSortedSig_CAT sort Hsort HSET _ _ _ _ _ _ _ _ sig).
    - apply TerminalHSET.
    - apply InitialHSET.
    - apply BinProductsHSET.
    - apply BinCoproductsHSET.
    - apply ProductsHSET.
    - apply CoproductsHSET.
    - change (Exponentials BPC1). apply expSortToHSET1.
    - apply ColimsHSET_of_shape.
  Defined.

End InstanceHSET.
