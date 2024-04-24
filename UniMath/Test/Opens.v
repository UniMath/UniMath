Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope subtype.
Local Open Scope cat.

Definition topological_space_category
  (T : TopologicalSpace)
  : category.
Proof.
  use make_category.
  - use make_precategory.
    + use make_precategory_data.
      * use make_precategory_ob_mor.
        -- exact (Open (T := T)).
        -- intros U V.
          exact (U ⊆ V).
      * exact (λ U x H, H).
      * exact (λ U V W HUV HVW x Hx, HVW _ (HUV _ Hx)).
    + abstract (
        use make_is_precategory_one_assoc;
        trivial
      ).
  - abstract (
      intros U V;
      apply isasetaprop;
      apply impred;
      intro;
      apply impredfun;
      apply propproperty
    ).
Defined.

Lemma is_univalent_topological_space_category
  (T : TopologicalSpace)
  : is_univalent (topological_space_category T).
Proof.
  intros U V.
  apply isweqimplimpl.
  - intro H.
    apply subtypePath.
    {
      intro.
      apply propproperty.
    }
    apply (invmap (hsubtype_univalence _ _)).
    split.
    + apply (pr1 H _).
    + apply (pr12 H _).
  - apply isaset_total2.
    + apply isasethsubtype.
    + intro.
      apply isasetaprop.
      apply propproperty.
  - apply isofhleveltotal2.
    + apply isaprop_subtype_containedIn.
    + intro f.
      apply isaprop_is_z_isomorphism.
Qed.

Definition continuous_to_functor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : topological_space_category T' ⟶ topological_space_category T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

Definition continuous_identity
  (T : TopologicalSpace)
  : continuous_function T T
  := identity (T : top_cat).

Definition identity_to_functor_is_identity
  (T : TopologicalSpace)
  : nat_z_iso (continuous_to_functor (continuous_identity T)) (functor_identity _).
Proof.
  use make_nat_z_iso.
  - exact (nat_trans_id (functor_identity _)).
  - intro.
    exists (λ x y, y).
    abstract easy.
Defined.

Definition composite_to_functor_is_comp
  {T T' T'' : TopologicalSpace}
  (F : top_cat⟦T, T'⟧)
  (F' : top_cat⟦T', T''⟧)
  : nat_z_iso (continuous_to_functor (F · F')) ((continuous_to_functor F') ∙ (continuous_to_functor F)).
Proof.
  use make_nat_z_iso.
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - intro.
    exists (λ x y, y).
    abstract easy.
Defined.
