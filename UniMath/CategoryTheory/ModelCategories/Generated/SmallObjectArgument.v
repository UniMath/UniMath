Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.

Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import UniMath.CategoryTheory.ModelCategories.NWFS.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.GenericFreeMonoidSequence.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.CategoryTheory.ModelCategories.Helpers.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LNWFSClosed.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LNWFSSmallnessReduction.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.OneStepMonadSmall.


Local Open Scope Cat.
Local Open Scope cat.


Section SmallObjectArgument.

Context {C : category}.
Context (J : morphism_class C).
Context (CC : Colims C).

Definition one_step_comonad_as_LNWFS : total_category (LNWFS C).
Proof.
  exists (one_step_factorization J CC).
  exact (one_step_comonad J CC).
Defined.

Definition LNWFS_pointed (L : total_category (LNWFS C)) :
    pointed (@LNWFS_tot_monoidal C) :=
  (_,, LNWFS_tot_l_point L).

Local Definition Ff_mon : monoidal_cat :=
  (_,, @Ff_monoidal C).
Local Definition LNWFS_mon : monoidal_cat :=
  (_,, @LNWFS_tot_monoidal C).

Import BifunctorNotations.
Import MonoidalNotations.

Lemma osc_preserves_diagram_on 
    (HJ : class_presentable J) :
  ∏ B, T_preserves_diagram_on 
        LNWFS_tot_monoidal
        (LNWFS_pointed one_step_comonad_as_LNWFS) 
        (ChainsLNWFS CC)
        (CoequalizersLNWFS CC)
        B.
Proof.
  intro B.
  intros CC' cl' cc'.

  set (L1 := LNWFS_pointed one_step_comonad_as_LNWFS).
  set (d := (free_monoid_coeq_sequence_diagram_on 
    LNWFS_tot_monoidal 
    L1 
    (CoequalizersLNWFS CC)
    B
  )).
  set (CL := ChainsLNWFS CC d).
  set (dbase := mapdiagram (pr1_category _) d).

  use (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim CC L1 d _ cl' cc').
  use (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim CC (pr11 L1)).
  use (FR_slice_omega_small_if_L_omega_small).
  use (L1_small_if_K_small).
  apply (K_small_if_J_small).
  exact HJ.
Qed.

Lemma free_monoid_coeq_sequence_converges_for_osc 
    (HJ : class_presentable J) :
  free_monoid_coeq_sequence_converges_on _
    (LNWFS_pointed one_step_comonad_as_LNWFS) 
    (ChainsLNWFS CC)
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal).
Proof.
  apply T_preserves_diagram_impl_convergence_on.
  exact (osc_preserves_diagram_on HJ).
Qed.

Theorem small_object_argument 
    (HJ : class_presentable J) :
  total_category (NWFS C).
Proof.
  set (lnwfs_monoid := 
    Tinf_monoid 
      (@LNWFS_tot_monoidal C)
      (LNWFS_pointed one_step_comonad_as_LNWFS)
      (ChainsLNWFS CC)
      (CoequalizersLNWFS CC)
      (free_monoid_coeq_sequence_converges_for_osc HJ)
      (LNWFS_rt_coeq CC)
      (LNWFS_rt_chain CC)
      (osc_preserves_diagram_on HJ)
  ).

  exact (_,, LNWFS_tot_monoid_is_NWFS lnwfs_monoid).
Defined.

End SmallObjectArgument.
