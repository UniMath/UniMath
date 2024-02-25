Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Local Open Scope cat.

Definition rt_preserves_chains
    {C : category} (V : monoidal C)
    (CMon := (C,, V) : monoidal_cat) :=
  ∏ (A : C), preserves_colimits_of_shape
      (monoidal_right_tensor (A : CMon)) nat_graph.

Definition rt_preserves_coequalizers
    {C : category} (V : monoidal C)
    (CMon := (C,, V) : monoidal_cat) :=
  ∏ (A : C), preserves_colimits_of_shape
      (monoidal_right_tensor (A : CMon)) Coequalizer_graph.
