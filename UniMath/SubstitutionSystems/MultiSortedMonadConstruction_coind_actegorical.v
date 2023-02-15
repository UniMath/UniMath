(** the coinductive analogue of [MultiSortedMonadConstruction_actegorical]

author: Ralph Matthes 2023
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
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

(** for the additions in 2023 *)
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Chains.CoAdamek.
Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.
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
Require Import UniMath.SubstitutionSystems.ContinuitySignature.MultiSortedSignatureFunctorEquivalence.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section Upstream.

  Context (C : category) (BC : BinCoproducts C).
  Local Definition Id_H := LiftingInitial_alt.Id_H C BC.

  Definition is_omega_cont_Id_H (H: [C, C] ⟶ [C, C]) :
    is_omega_cont H -> is_omega_cont (Id_H H).
  Proof.
    (* apply is_omega_cont_BinCoproduct_of_functors.  does not exist since it requires distributivity *)
    (* then apply is_omega_cont_constant_functor *)
  Admitted.

End Upstream.

Section MBindingSig.

Context (sort : UU) (Hsort_set : isaset sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Context (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

Let Hsort := hlevelntosn 2 _ Hsort_set.

(** Define the discrete category of sorts *)
Let sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.

Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

(* Assumptions needed to prove ω-continuity of the functor *)
Context (HcoC : Lims_of_shape conat_graph C)
 (HCcommuteBP : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
 (HCcommuteCC : ∏ I : SET, ω_limits_distribute_over_I_coproducts C I HcoC (CC (pr1 I) (pr2 I))).



(** * Construction of a monad from a multisorted signature *)
Section monad.

  Local Definition sortToC1 := [sortToC, sortToC].
  Local Definition sortToC2 := [sortToC1, sortToC1].

  Let BCsortToC1 : BinCoproducts sortToC1 := BinCoproducts_functor_precat _ _ BCsortToC.
  (* Let ICsortToC1 : Initial sortToC1 := Initial_functor_precat _ _ (Initial_functor_precat _ _ IC).*)
  Let TCsortToC1 : Terminal sortToC1 := Terminal_functor_precat _ _ (Terminal_functor_precat _ _ TC).

  Local Definition HcoCsortToC : Lims_of_shape conat_graph sortToC.
  Proof.
    apply LimsFunctorCategory_of_shape, HcoC.
  Defined.
  Local Definition HcoCsortToC1 : Lims_of_shape conat_graph sortToC1.
  Proof.
    apply LimsFunctorCategory_of_shape, HcoCsortToC.
  Defined.

  Local Definition MultiSortedSigToFunctor : MultiSortedSig sort -> sortToC2 := MultiSortedSigToFunctor sort Hsort C TC BP BC CC.

  Local Definition is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort) :
    is_omega_cont (MultiSortedSigToFunctor M) :=
    is_omega_cont_MultiSortedSigToFunctor sort Hsort_set C TC IC
      BP BC PC CC M HcoC HCcommuteBP HCcommuteCC.

  Local Definition MultiSortedSigToStrengthFromSelfCAT : ∏ M : MultiSortedSig sort,
        MultiSorted_actegorical.pointedstrengthfromselfaction_CAT sort Hsort C (MultiSortedSigToFunctor M)
    := MultiSortedSigToStrengthFromSelfCAT sort Hsort C TC BP BC CC.

  Let Id_H := Id_H sortToC BCsortToC.


  (** Construction of terminal coalgebra for the omega-continuous signature functor with lax lineator *)
  Definition coindCodatatypeOfMultisortedBindingSig_CAT (sig : MultiSortedSig sort) :
    Terminal (CoAlg_category (Id_H (MultiSortedSigToFunctor sig))).
  Proof.
    use limCoAlgTerminal.
    - exact TCsortToC1.
    - apply is_omega_cont_Id_H.
      apply (is_omega_cont_MultiSortedSigToFunctor sig).
    - apply HcoCsortToC1.
  Defined.

  Definition coindGHSSOfMultiSortedSig_CAT (sig : MultiSortedSig sort) :
    ghss (monendocat_monoidal sortToC) (MultiSortedSigToFunctor sig) (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    use (terminal_coalg_to_ghss (MultiSortedSigToStrengthFromSelfCAT sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact (pr1 (coindCodatatypeOfMultisortedBindingSig_CAT sig)).
    - exact (pr2 (coindCodatatypeOfMultisortedBindingSig_CAT sig)).
  Defined.

  (** the associated Sigma-monoid *)
  Definition coindSigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : SigmaMonoid (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    apply ghhs_to_sigma_monoid.
    exact (coindGHSSOfMultiSortedSig_CAT sig).
  Defined.

  (** the associated monad *)
  Definition coindMonadOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Monad sortToC.
  Proof.
    use monoid_to_monad_CAT.
    use SigmaMonoid_to_monoid.
    - exact (MultiSortedSigToFunctor sig).
    - exact (MultiSortedSigToStrengthFromSelfCAT sig).
    - exact (coindSigmaMonoidOfMultiSortedSig_CAT sig).
  Defined.

End monad.

End MBindingSig.

Section InstanceHSET.

  Context (sort : UU) (Hsort_set : isaset sort).

  Let Hsort := hlevelntosn 2 _ Hsort_set.

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Definition coindMultiSortedSigToMonadHSET_viaCAT : MultiSortedSig sort → Monad (sortToHSET).
  Proof.
    intros sig; simple refine (coindMonadOfMultiSortedSig_CAT sort Hsort_set HSET _ _ _ _ _ _ _ _ _ sig).
    - apply TerminalHSET.
    - apply InitialHSET.
    - apply BinProductsHSET.
    - apply BinCoproductsHSET.
    - apply ProductsHSET.
    - apply CoproductsHSET.
    - apply LimsHSET_of_shape.
    - apply propcoproducts_commute_binproductsHSET.
    - apply I_coproduct_distribute_over_omega_limits_HSET.
  Defined.

End InstanceHSET.
