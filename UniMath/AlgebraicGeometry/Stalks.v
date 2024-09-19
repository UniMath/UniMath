Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.AlgebraicGeometry.CategoryOfOpens.
Require Import UniMath.AlgebraicGeometry.Sheaves.Presheaves.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Topology.Topology.

Local Open Scope subtype.
Local Open Scope cat.

Section Stalks.

  Context {C : category}.
  Context (CC : Colims C).

  Section Stalk.

    Context {X : TopologicalSpace}.
    Context (P : presheaf C X).
    Context (x : X).

    Definition stalk_graph
      : graph.
    Proof.
      use tpair.
      - exact (∑ (U : Open (T := X)), U x).
      - exact (λ U V, pr1 V ⊆ pr1 U).
    Defined.

    Definition stalk_diagram
      : diagram stalk_graph C.
    Proof.
      use tpair.
      - intro U.
        exact (P (pr1 U)).
      - exact (λ _ _, # P).
    Defined.

    Definition stalk
      : C
      := colim (CC _ stalk_diagram).

  End Stalk.

  Section StalkMorphism.

    Context {X : TopologicalSpace}.
    Context (P Q : presheaf C X).
    Context (f : presheaf_morphism P Q).
    Context (x : X).

    Definition morphism_to_stalk_morphism
      : C⟦stalk P x, stalk Q x⟧.
    Proof.
      use colimOfArrows.
      - intro U.
        exact (f _).
      - abstract exact (λ U V H, nat_trans_ax f _ _ _).
    Defined.

  End StalkMorphism.

End Stalks.
