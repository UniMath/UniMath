(** this file is a follow-up of [MultisortedMonadConstruction_alt], where the semantic signatures [Signature] are replaced by functors with tensorial strength and HSS by GHSS

based on the lax lineator constructed in [Multisorted_actegories] and transferred (through weak equivalence) to the strength notion of
generalized heterogeneous substitution systems (GHSS), a GHSS is constructed and a monad obtained through it

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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsWhiskeredMonoidalElementary.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonadsAsMonoidsWhiskeredElementary.
Require Import UniMath.SubstitutionSystems.EquivalenceLaxLineatorsHomogeneousCase.
Require UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.ConstructionOfGHSS.
Require UniMath.SubstitutionSystems.BindingSigToMonad_actegorical.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.

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

  Local Definition MultiSortedSigToFunctor : MultiSortedSig sort -> sortToC2 := MultiSortedSigToFunctor sort Hsort C TC BP BC CC.
  Local Definition is_omega_cocont_MultiSortedSigToFunctor : ∏ M : MultiSortedSig sort, is_omega_cocont (MultiSortedSigToFunctor M)
    := is_omega_cocont_MultiSortedSigToFunctor sort Hsort C TC BP BC PC CC expSortToCC HC.
  Local Definition MultiSortedSigToStrengthFromSelfCAT : ∏ M : MultiSortedSig sort,
        MultiSorted_actegorical.pointedstrengthfromselfaction_CAT sort Hsort C (MultiSortedSigToFunctor M)
    := MultiSortedSigToStrengthFromSelfCAT sort Hsort C TC BP BC CC.

  Let Id_H := LiftingInitial_alt.Id_H sortToC BCsortToC.

 (** Construction of initial algebra for the omega-cocontinuous signature functor with lax lineator *)
  Definition DatatypeOfMultisortedBindingSig_CAT (sig : MultiSortedSig sort) :
    Initial (FunctorAlg (Id_H (MultiSortedSigToFunctor sig))).
  Proof.
    use colimAlgInitial.
    - exact ICsortToC1.
    - apply (LiftingInitial_alt.is_omega_cocont_Id_H _ _ _ (is_omega_cocont_MultiSortedSigToFunctor sig)).
    - apply HCsortToC1.
  Defined.

  (** the associated GHSS *)
  Definition GHSSOfMultiSortedSig_CAT (sig : MultiSortedSig sort) :
    ghss (monendocat_monoidal sortToC) (MultiSortedSigToFunctor sig) (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    use (initial_alg_to_ghss (MultiSortedSigToStrengthFromSelfCAT sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact ICsortToC1.
    - apply HCsortToC1.
    - apply (is_omega_cocont_MultiSortedSigToFunctor sig).
    - intro F. apply Initial_functor_precat.
    - intro F. apply (is_omega_cocont_pre_composition_functor F HCsortToC).
  Defined.

  (** the associated initial Sigma-monoid *)
  Definition InitialSigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Initial (SigmaMonoid (MultiSortedSigToStrengthFromSelfCAT sig)).
  Proof.
    use (SigmaMonoidFromInitialAlgebraInitial (MultiSortedSigToStrengthFromSelfCAT sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact ICsortToC1.
    - apply HCsortToC1.
    - apply (is_omega_cocont_MultiSortedSigToFunctor sig).
    - intro F. apply Initial_functor_precat.
    - intro F. apply (is_omega_cocont_pre_composition_functor F HCsortToC).
  Defined.

  (** the associated Sigma-monoid - defined separately *)
  Definition SigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : SigmaMonoid (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    apply ghhs_to_sigma_monoid.
    exact (GHSSOfMultiSortedSig_CAT sig).
  Defined.

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
   (* Admitted. the proof depends on [lax_lineators_from_lifted_precomp_CAT_and_lifted_self_action_agree] to be defined! *)
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

End CharEq.

  (** the associated monad *)
  Definition MonadOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Monad sortToC.
  Proof.
    use monoid_to_monad_CAT.
    use SigmaMonoid_to_monoid.
    - exact (MultiSortedSigToFunctor sig).
    - exact (MultiSortedSigToStrengthFromSelfCAT sig).
    - exact (SigmaMonoidOfMultiSortedSig_CAT sig).
  Defined.

End monad.

End MBindingSig.

Section InstanceHSET.

  Context (sort : UU) (Hsort : isofhlevel 3 sort).

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Definition MultiSortedSigToMonadHSET_viaCAT : MultiSortedSig sort → Monad (sortToHSET).
  Proof.
    intros sig; simple refine (MonadOfMultiSortedSig_CAT sort Hsort HSET _ _ _ _ _ _ _ _ sig).
    - apply TerminalHSET.
    - apply InitialHSET.
    - apply BinProductsHSET.
    - apply BinCoproductsHSET.
    - apply ProductsHSET.
    - apply CoproductsHSET.
    - apply Exponentials_functor_HSET.
    - apply ColimsHSET_of_shape.
  Defined.

End InstanceHSET.
