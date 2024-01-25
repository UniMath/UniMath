(*
The Algebraic Small Object Argument

The Algebraic Small Object Argument by Richard Garner
is a refinement of the (Classical) Small Object Argument 
by Quillen. The ASOA can be used to construct a NWFS
starting from a sufficiently well-behaved morphism class J.
The construction uses a convergent transfinite sequence,
the "Free Monoid Sequence". This sequence can be used to
construct a monoid in a category, and since a monoid in the
LNWFS category is a NWFS, we require some smallness properties
on this category and on J to apply it and construct a NWFS.
This is done in the files in this directory.

A brief description of the files in this directory, all
only used to prove the Algebraic Small Object Argument:
- MonoidalHelpers.v:
  Some helper definitions used throughout the construction.

- LiftingWithClass.v and OneStepMonad.v:
  One can define a functorial factorization from the morphism
  class J: the "one step factorization" F1. In fact, this 
  factorization always admits an LNWFS structure, so we denote
  it with L1 instead. 
  
  This will be the starting point, from which we apply the 
  transfinite construction.

- FFMonoidalStructure.v:
  Defines a monoidal structure on the category of Functorial
  Factorizations (FF). This monoidal structure can be lifted 
  to one in LNWFS, and is defined in such a way that a monoid 
  in this structure corresponds with a NWFS. Also a proof
  that a monoid in this monoidal structure corresponds
  with an object of RNWFS.

- LNWFSHelpers.v:
  Useful lemmas related to the LNWFS category, used throughout
  the construction.

- LNWFSMonoidalStucture.v:
  Lemmas proving that the monoidal structure on FF in fact
  lifts to one in LNWFS. Also a proof that a monoid
  in LNWFS corresponds with an object of NWFS.

- LNWFSCocomplete.v:
  We show that FF is cocomplete, and that LNWFS is also
  cocomplete, with colimits lying over those in FF.
  The main use cases are that LNWFS has all chains and coequalizers,
  which is necessary for the ASOA.

- LNWFSClosed.v:
  We show that the monoidal structure on LNWFS is closed under
  (connected) colimits. 
  Again the main use cases are that it is closed under chains and
  coequalizers, needed for the ASOA.

- GenericFreeMonoid.v:
  Theory attempting to construct a free monoid from an adjunction.
  This is the way Garner initially defines the construction, but I ended
  up finding it easier to take a more direct approach, constructing
  the monoid directly. Also definitions for the category
  of monoid algebras.

- GenericFreeMonoidSequence.v:
  A file containing the definition of the free monoid sequence,
  in a monoidal category "V", as well as a proof that it 
  converges, given a smallness requirement
  on the object "T", defining the sequence. Also contains
  the construction of the monoid one obtains from the sequence
  whenever it converges.

- LNWFSSmallnessReduction.v:
  The smallness requirement on T in V (for which we use L1 in LNWFS),
  can be reduced to one only depending on the left functor
  of F1.

- OneStepMonadSmall.v:
  This smallness requirement that we reduced above can be reduced
  even further, to one only depending on the morphism class
  J, used to define F1.

- SmallObjectArgument.v (this file):
  We put all the above results together, allowing us to
  construct a NWFS, given a basic smallness requirement
  on J.

Important sources:
- Cofibrantly generated natural weak factorisation systems by Richard Garner
- Understanding the small object argument by Richard Garner
- My thesis: https://studenttheses.uu.nl/handle/20.500.12932/45658
- A unified treatment of transfinite constructions for free 
    algebras, free monoids, colimits, associated sheaves, 
    and so on
  by Kelly.

*)

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
