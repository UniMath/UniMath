Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Test.Opens.

Local Open Scope cat.

Section Presheaves.

  Context (C : category).
  Context (T : TopologicalSpace).

  Definition presheaf_cat
    : category
    := [(topological_space_category T)^op, C].

  Definition presheaf_mor_comp_app
    (P Q R : presheaf_cat)
    (F : presheaf_cat⟦P, Q⟧)
    (G : presheaf_cat⟦Q, R⟧)
    (U : Open)
    : (F · G : nat_trans _ _) U = ((F : nat_trans _ _) U) · ((G : nat_trans _ _) U)
    := idpath _.

  Definition presheaf_mor_eq
    (P Q : presheaf_cat)
    (F G : presheaf_cat⟦P, Q⟧)
    (H : ∏ U, (F : nat_trans _ _) U = (G : nat_trans _ _) U)
    : F = G
    := nat_trans_eq_alt _ _ _ _ H.

End Presheaves.

Definition pushforward
  {C : category}
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  (P : presheaf_cat C T)
  : presheaf_cat C T'
  := functor_opp (continuous_to_functor F) ∙ (P : _ ⟶ _).

Definition pushforward_id
  {C : category}
  {T : TopologicalSpace}
  (P : presheaf_cat C T)
  : z_iso (pushforward (identity (C := top_cat) T) P) P.
Proof.
  apply z_iso_from_nat_z_iso.
  refine (post_whisker_nat_z_iso (G2 := functor_identity _) _ (P : _ ⟶ _)).
  refine (
    make_nat_z_iso _ _ _
    (op_nt_is_z_iso
      (f := functor_identity (topological_space_category T)) _
      (pr2 (nat_z_iso_inv (_ : nat_z_iso _ _))))).
  apply identity_to_functor_is_identity.
Defined.

Definition pushforward_comp
  {C : category}
  {T T' T'' : TopologicalSpace}
  (F : continuous_function T T')
  (F' : continuous_function T' T'')
  (P : presheaf_cat C T)
  : z_iso (pushforward ((F : top_cat⟦_, _⟧) · F') P) (pushforward F' (pushforward F P)).
Proof.
  apply z_iso_from_nat_z_iso.
  refine (nat_z_iso_comp _ (nat_z_iso_inv (nat_z_iso_functor_comp_assoc (C2 := (topological_space_category T')^op) _ _ P))).
  refine (post_whisker_nat_z_iso _ (P : _ ⟶ _)).
  refine (nat_z_iso_comp _ (nat_z_iso_inv (functor_comp_op_nat_z_iso _ _))).
  refine (
    make_nat_z_iso _ _ _
    (op_nt_is_z_iso _
      (pr2 (nat_z_iso_inv (_ : nat_z_iso _ _))))).
  apply composite_to_functor_is_comp.
Defined.
