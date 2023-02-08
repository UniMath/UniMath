Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
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
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

Local Open Scope cat.

Section OmegaLimitsCommutingWithCoproductsHSET.

  Definition HSET_ω_limits : ∏ coch : cochain HSET, LimCone coch.
  Proof.
    intro coch.
    apply LimConeHSET.
  Defined.

  Definition I_coproduct_distribute_over_omega_limits_HSET (I : HSET)
    : ω_limits_distribute_over_I_coproducts HSET I HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)).
  Proof.
    intro ind.
    use make_is_z_isomorphism.
    - intros [f p].
      assert (q0 : ∏ n : nat, S n = n + 1 ).
      {
        intro n ; induction n.
        - apply idpath.
        - admit.
      }

      assert (q : ∏ n : nat, pr1 (f n) = pr1 (f (n + 1))).
      { exact (λ n, ! base_paths _ _ (p (n+1) n (q0 n))). }

      assert (q' : ∏ n : nat, pr1 (f n) = pr1 (f (S n))).
      {
        intro n.
        refine (q n @ _).
        apply (maponpaths (λ z, pr1 (f z))).
        exact (! q0 n).
      }

      exists (pr1 (f 0)).
      use tpair.
      + intro n.
        assert (h : pr1 (f 0) = pr1 (f n)).
        {
          induction n.
          - apply idpath.
          - exact (IHn @ q' n).
        }
        induction (! h).
        exact (pr2 (f n)).
      + intros n m h.
        admit.
    - split ; apply funextsec ; intro x ; use total2_paths_f ; admit.
  Admitted.

End OmegaLimitsCommutingWithCoproductsHSET.

Lemma is_omega_cont_MultiSortedSigToFunctor_HSET
       (sort : UU) (Hsort : isofhlevel 3 sort)
      (M : MultiSortedSig sort)
  : is_omega_cont (MultiSortedSigToFunctor sort Hsort HSET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET M).
Proof.
  use is_omega_cont_MultiSortedSigToFunctor.
  - exact InitialHSET.
  - exact ProductsHSET.
  - intro ; apply LimConeHSET.
  - exact I_coproduct_distribute_over_omega_limits_HSET.
  - admit.
Admitted.
