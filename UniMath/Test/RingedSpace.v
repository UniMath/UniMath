Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

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
  := identity (T : total_category disp_top).

Definition identity_to_functor_is_identity
  (T : TopologicalSpace)
  : z_iso (C := [_, _]) (functor_identity _) (continuous_to_functor (continuous_identity T)).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (functor_identity _)).
  - exact (nat_trans_id (functor_identity _)).
  - abstract (
      now split;
      apply (nat_trans_eq (homset_property _))
    ).
Defined.

Definition composite_to_functor_is_comp
  {T T' T'' : TopologicalSpace}
  (F : (total_category disp_top)⟦T, T'⟧)
  (F' : (total_category disp_top)⟦T', T''⟧)
  : z_iso (C := [_, _]) (continuous_to_functor (F · F')) ((continuous_to_functor F') ∙ (continuous_to_functor F)).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - abstract (
      now split;
      apply (nat_trans_eq (homset_property _))
    ).
Defined.

Section Sheaves.

  Context (D : category).

  Definition D_presheaf
    (T : TopologicalSpace)
    : UU
    := (topological_space_category T)^op ⟶ D.

  Definition D_presheaf_pullback
    {T T' : TopologicalSpace}
    (F : continuous_function T T')
    (P : D_presheaf T)
    : D_presheaf T'
    := functor_opp (continuous_to_functor F) ∙ P.

  Definition space_with_local_data_disp_cat
    : disp_cat (total_category disp_top).
  Proof.
    use tpair.
    - use tpair.
      + exists D_presheaf.
        intros T T' P P' F.
        exact ((P' : _ ⟶ _) ⟹ (D_presheaf_pullback F P : _ ⟶ _)).
      + split.
        * intros T P.
          exact (post_whisker (nat_trans_id (functor_identity _) : functor_opp (functor_identity _) ⟹ functor_opp (continuous_to_functor (identity T))) P).
        * intros X Y Z F F' P P' P'' H H'.
          apply (nat_trans_comp _ _ _ H').
          apply (nat_trans_comp _ _ _ (pre_whisker _ H)).
          refine (post_whisker (G := functor_opp (continuous_to_functor F') ∙ functor_opp (continuous_to_functor F)) (nat_trans_id (functor_opp (continuous_to_functor (F · F')))) P).
    - repeat split.
      + intros T T' F P P' H.
        apply nat_trans_eq_alt.
        intro t.
        cbn.
      simpl.
      use tpair.
  Defined.

End Sheaves.
